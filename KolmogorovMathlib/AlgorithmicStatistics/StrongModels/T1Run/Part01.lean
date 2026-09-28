import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1SparseSelector
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingStreams
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingRun.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingRun

/-!
# The state of the marking run

`T1RunState` is what the T1 marking run carries: the current candidate list, the strings
marked by each of the three streams, the models already seen on the `C'` and `C''` streams,
the successive versions of the candidate list, and the rebuild counters and charges.
`T1RunState.toProd`, `.ofProd` and `t1RunStateEquiv` transport an encoding onto it, and
`T1RunListUpdateData` and `T1RunCounterUpdateData` are the tuples one marking step updates.

`t1InitialCurrent` and `t1InitialRunState` are the initial state; `t1RunMarked`,
`t1RunUnmarked` and `t1RunSaturated` are the three derived quantities the transitions
consult — the marked strings, their complement in canonical order
(`t1RunUnmarked_eq_canonicalFinsetList`), and whether the quota of marked candidates has been
reached (`t1RunSaturated_iff`).

The transitions themselves are in `T1Run/Transitions`, their computability in
`T1Run/StatePrimrec` and `T1Run/Computable`, and their semantics in `T1Run/Part03` and
`T1Run/Histories`.
-/



namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- The state of the marking run: the current candidate list, the strings marked by
each of the three streams, the parts of `C'` and `C''` already seen, the earlier
versions of the candidate list, and the four counters. -/
structure T1RunState where
  current : List BitString
  bMarked : List BitString
  cMarked : List BitString
  dMarked : List BitString
  seenCPrime : List BitString
  seenCDouble : List BitString
  versions : List (List BitString)
  external : Nat
  saturation : Nat
  totalC : Nat
  totalD : Nat

/-- The product type matching the fields of `T1RunState`, used to give the state an
encoding. -/
abbrev T1RunStateData :=
  List BitString × List BitString × List BitString × List BitString × List BitString ×
    List BitString × List (List BitString) × Nat × Nat × Nat × Nat

/-- The fields of a run state as a nested tuple. -/
def T1RunState.toProd (s : T1RunState) : T1RunStateData :=
  (s.current, s.bMarked, s.cMarked, s.dMarked, s.seenCPrime,
   s.seenCDouble, s.versions, s.external, s.saturation, s.totalC, s.totalD)

/-- The run state assembled from a nested tuple of fields. -/
def T1RunState.ofProd (p : T1RunStateData) : T1RunState :=
  { current := p.1, bMarked := p.2.1, cMarked := p.2.2.1, dMarked := p.2.2.2.1,
    seenCPrime := p.2.2.2.2.1, seenCDouble := p.2.2.2.2.2.1, versions := p.2.2.2.2.2.2.1,
    external := p.2.2.2.2.2.2.2.1, saturation := p.2.2.2.2.2.2.2.2.1,
    totalC := p.2.2.2.2.2.2.2.2.2.1, totalD := p.2.2.2.2.2.2.2.2.2.2 }

/-- The bijection between run states and their tuple of fields, which transports the
encoding. -/
def t1RunStateEquiv : Equiv T1RunState T1RunStateData where
  toFun := T1RunState.toProd
  invFun := T1RunState.ofProd
  left_inv s := by cases s; rfl
  right_inv p := by
    rcases p with ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩
    rfl

instance : Primcodable T1RunState := Primcodable.ofEquiv _ t1RunStateEquiv

/-- The tuple of a run state together with the five lists updated in one marking
step. -/
abbrev T1RunListUpdateData :=
  T1RunState × List BitString × List BitString × List BitString ×
    List BitString × List BitString

/-- The tuple of a run state together with the four counters updated in one marking
step. -/
abbrev T1RunCounterUpdateData :=
  T1RunState × Nat × Nat × Nat × Nat

/-- The initial candidate list: the first `2 ^ (k - epsilon)` strings of length `n`
in canonical order. -/
def t1InitialCurrent (n k epsilon : Nat) : List BitString :=
  (canonicalFinsetList (stringsOfLength n)).take (2 ^ (k - epsilon))

/-- The initial state of the marking run: the initial candidate list, nothing marked
or seen, and all counters zero. -/
def t1InitialRunState (n k epsilon : Nat) : T1RunState :=
  let initial := t1InitialCurrent n k epsilon
  { current := initial
  , bMarked := []
  , cMarked := []
  , dMarked := []
  , seenCPrime := []
  , seenCDouble := []
  , versions := [initial]
  , external := 0
  , saturation := 0
  , totalC := 0
  , totalD := 0 }

/-- The strings marked so far by any of the three streams, without repetitions. -/
def t1RunMarked (s : T1RunState) : List BitString :=
  (s.bMarked ++ s.cMarked ++ s.dMarked).eraseDups

/-- Whether at least `quota` of the current candidates have been marked by the `C`
or `D` streams. -/
def t1RunSaturated (s : T1RunState) (quota : Nat) : Bool :=
  let intersection := s.current.filter
    (fun x => decide (x ∈ s.cMarked) || decide (x ∈ s.dMarked))
  decide (quota ≤ intersection.length)

/-- The strings of length `n` that are still unmarked, in canonical order. -/
def t1RunUnmarked (n : Nat) (s : T1RunState) : List BitString :=
  (canonicalFinsetList (stringsOfLength n)).filter
    (fun x => !decide (x ∈ t1RunMarked s))

private theorem t1RunListUpdateData_mk_primrec
    {α : Type} [Primcodable α]
    {s : α → T1RunState}
    {b c d cp cd : α → List BitString}
    (hs : Primrec s) (hb : Primrec b) (hc : Primrec c)
    (hd : Primrec d) (hcp : Primrec cp) (hcd : Primrec cd) :
    Primrec (fun a => (s a, b a, c a, d a, cp a, cd a) :
      α → T1RunListUpdateData) :=
  hs.pair (hb.pair (hc.pair (hd.pair (hcp.pair hcd))))

private theorem t1RunCounterUpdateData_mk_primrec
    {α : Type} [Primcodable α]
    {s : α → T1RunState} {external saturation totalC totalD : α → Nat}
    (hs : Primrec s) (hext : Primrec external)
    (hsat : Primrec saturation) (htc : Primrec totalC)
    (htd : Primrec totalD) :
    Primrec (fun a =>
      (s a, external a, saturation a, totalC a, totalD a) :
        α → T1RunCounterUpdateData) :=
  hs.pair (hext.pair (hsat.pair (htc.pair htd)))

/-- The input of one step of the marking run: the parameters of the construction,
the current state and the incoming marking event. -/
structure T1RunStepInput where
  cSparse : Nat
  n : Nat
  k : Nat
  epsilon : Nat
  quota : Nat
  s : T1RunState
  event : T1MarkEvent

/-- The fields of a step input as a nested tuple. -/
def T1RunStepInput.toProd (input : T1RunStepInput) :
    Nat × Nat × Nat × Nat × Nat × T1RunState × T1MarkEvent :=
  (input.cSparse, input.n, input.k, input.epsilon, input.quota, input.s, input.event)

/-- The step input assembled from a nested tuple of fields. -/
def T1RunStepInput.ofProd
    (p : Nat × Nat × Nat × Nat × Nat × T1RunState × T1MarkEvent) :
    T1RunStepInput :=
  { cSparse := p.1
  , n := p.2.1
  , k := p.2.2.1
  , epsilon := p.2.2.2.1
  , quota := p.2.2.2.2.1
  , s := p.2.2.2.2.2.1
  , event := p.2.2.2.2.2.2 }

/-- The bijection between step inputs and their tuple of fields, which transports
the encoding. -/
def t1RunStepInputEquiv :
    T1RunStepInput ≃
      Nat × Nat × Nat × Nat × Nat × T1RunState × T1MarkEvent where
  toFun := T1RunStepInput.toProd
  invFun := T1RunStepInput.ofProd
  left_inv i := by cases i; rfl
  right_inv p := by rcases p with ⟨p1, p2, p3, p4, p5, p6, p7⟩; rfl

/-- The input of a whole marking run: the machine code and the numerical parameters
of the construction. -/
structure T1RunInput where
  c : Nat.Partrec.Code
  cDesc : Nat
  cSparse : Nat
  n : Nat
  k : Nat
  epsilon : Nat
  quota : Nat
  t : Nat

/-- The fields of a run input as a nested tuple. -/
def T1RunInput.toProd (input : T1RunInput) :
    Nat.Partrec.Code × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (input.c, input.cDesc, input.cSparse, input.n, input.k, input.epsilon, input.quota, input.t)

/-- The run input assembled from a nested tuple of fields. -/
def T1RunInput.ofProd
    (p : Nat.Partrec.Code × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :
    T1RunInput :=
  { c := p.1
  , cDesc := p.2.1
  , cSparse := p.2.2.1
  , n := p.2.2.2.1
  , k := p.2.2.2.2.1
  , epsilon := p.2.2.2.2.2.1
  , quota := p.2.2.2.2.2.2.1
  , t := p.2.2.2.2.2.2.2 }

/-- The bijection between run inputs and their tuple of fields, which transports the
encoding. -/
def t1RunInputEquiv :
    T1RunInput ≃
      Nat.Partrec.Code × Nat × Nat × Nat × Nat × Nat × Nat × Nat where
  toFun := T1RunInput.toProd
  invFun := T1RunInput.ofProd
  left_inv i := by cases i; rfl
  right_inv p := by rcases p with ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩; rfl

/-! ### Exact transition equations for semantic proofs -/

/-- State immediately before the mandatory rebuild caused by a `B` event. -/
noncomputable def t1RunBSetPrepared
    (n : Nat) (s : T1RunState) (w : BitString) : T1RunState :=
  { s with
    bMarked := s.bMarked ++
      (canonicalPointListOfCode w).filter (fun x => x.length = n) }

/-- State immediately before the mandatory rebuild caused by a `C''` batch. -/
noncomputable def t1RunCDoublePrepared
    (n : Nat) (s : T1RunState) (batch : List BitString) : T1RunState :=
  let activated :=
    ((batch.filter fun w => w ∈ s.seenCPrime).flatMap
      canonicalPointListOfCode).filter (fun x => x.length = n)
  { s with
    cMarked := s.cMarked ++ activated
    seenCDouble := s.seenCDouble ++ batch }

/-- State obtained by recording a `C'` code without activating its points. -/
def t1RunCPrimeSeenPrepared
    (s : T1RunState) (w : BitString) : T1RunState :=
  { s with seenCPrime := s.seenCPrime ++ [w] }

/-- State obtained after an active `C'` event has marked and charged its
length-`n` points, but before the optional saturation rebuild. -/
noncomputable def t1RunCPrimePrepared
    (n : Nat) (s : T1RunState) (w : BitString) : T1RunState :=
  let points :=
    (canonicalPointListOfCode w).filter (fun x => x.length = n)
  { t1RunCPrimeSeenPrepared s w with
    cMarked := s.cMarked ++ points
    totalC := s.totalC +
      (s.current.filter fun x => x ∈ points).length }

/-- State after a `D` string has been marked and charged, but before the
optional saturation rebuild. -/
noncomputable def t1RunDPrepared
    (n : Nat) (s : T1RunState) (x : BitString) : T1RunState :=
  { s with
    dMarked := s.dMarked ++ (if x.length = n then [x] else [])
    totalD := s.totalD + (if x ∈ s.current then 1 else 0) }

/-- Equality of the five fields that carry exact marking-event history. -/
def T1RunMarkingDataEq (s s' : T1RunState) : Prop :=
  s.bMarked = s'.bMarked ∧
  s.cMarked = s'.cMarked ∧
  s.dMarked = s'.dMarked ∧
  s.seenCPrime = s'.seenCPrime ∧
  s.seenCDouble = s'.seenCDouble

/-- Agreement of the marking data of two states is reflexive. -/
theorem T1RunMarkingDataEq.refl (s : T1RunState) :
    T1RunMarkingDataEq s s := by
  simp [T1RunMarkingDataEq]

/-- Agreement of the marking data of two states is symmetric. -/
theorem T1RunMarkingDataEq.symm {s s' : T1RunState}
    (h : T1RunMarkingDataEq s s') :
    T1RunMarkingDataEq s' s := by
  rcases h with ⟨hb, hc, hd, hcp, hcd⟩
  exact ⟨hb.symm, hc.symm, hd.symm, hcp.symm, hcd.symm⟩

/-- Agreement of the marking data of two states is transitive. -/
theorem T1RunMarkingDataEq.trans {s s' s'' : T1RunState}
    (h₁ : T1RunMarkingDataEq s s')
    (h₂ : T1RunMarkingDataEq s' s'') :
    T1RunMarkingDataEq s s'' := by
  rcases h₁ with ⟨hb₁, hc₁, hd₁, hcp₁, hcd₁⟩
  rcases h₂ with ⟨hb₂, hc₂, hd₂, hcp₂, hcd₂⟩
  exact ⟨hb₁.trans hb₂, hc₁.trans hc₂, hd₁.trans hd₂,
    hcp₁.trans hcp₂, hcd₁.trans hcd₂⟩

/-- The initial candidate list has no repetitions. -/
theorem t1InitialCurrent_nodup (n k epsilon : Nat) :
    (t1InitialCurrent n k epsilon).Nodup := by
  unfold t1InitialCurrent
  exact (List.take_sublist _ _).nodup (canonicalFinsetList_nodup _)

/-- The initial candidates are strings of length `n`. -/
theorem t1InitialCurrent_subset_stringsOfLength (n k epsilon : Nat) :
    (t1InitialCurrent n k epsilon).toFinset ⊆
      stringsOfLength n := by
  intro x hx
  rw [List.mem_toFinset] at hx
  exact mem_canonicalFinsetList.mp
    ((List.mem_of_mem_take hx))

/-- For `epsilon ≤ k ≤ n` the initial candidate list has exactly `2 ^ (k - epsilon)`
entries. -/
theorem t1InitialCurrent_length {n k epsilon : Nat}
    (hεk : epsilon ≤ k) (hkn : k ≤ n) :
    (t1InitialCurrent n k epsilon).length =
      2 ^ (k - epsilon) := by
  unfold t1InitialCurrent
  rw [List.length_take]
  have h_len : (canonicalFinsetList (stringsOfLength n)).length = 2 ^ n := by
    rw [length_canonicalFinsetList, card_stringsOfLength]
  rw [h_len]
  exact Nat.min_eq_left (Nat.pow_le_pow_right (by decide) (by omega))

/-- The marked strings are the union of the three marked lists. -/
theorem t1RunMarked_toFinset (s : T1RunState) :
    (t1RunMarked s).toFinset =
      s.bMarked.toFinset ∪ s.cMarked.toFinset ∪
        s.dMarked.toFinset := by
  ext x
  simp [t1RunMarked, mem_eraseDups_bitString]

/-- The list of unmarked strings has no repetitions. -/
theorem t1RunUnmarked_nodup (n : Nat) (s : T1RunState) :
    (t1RunUnmarked n s).Nodup := by
  exact (List.filter_sublist).nodup
    (canonicalFinsetList_nodup (stringsOfLength n))

/-- The unmarked strings are the length-`n` strings minus the marked ones. -/
theorem t1RunUnmarked_toFinset (n : Nat) (s : T1RunState) :
    (t1RunUnmarked n s).toFinset =
      stringsOfLength n \ (t1RunMarked s).toFinset := by
  ext x
  simp [t1RunUnmarked]

/-- The list of unmarked strings is the canonical listing of that difference. -/
theorem t1RunUnmarked_eq_canonicalFinsetList
    (n : Nat) (s : T1RunState) :
    t1RunUnmarked n s =
      canonicalFinsetList
        (stringsOfLength n \ (t1RunMarked s).toFinset) := by
  rw [← t1RunUnmarked_toFinset]
  exact (canonicalFinsetList_of_sorted
    (t1RunUnmarked n s) (t1RunUnmarked_nodup n s)
    ((Finset.pairwise_sort (stringsOfLength n) bitStringLE).sublist
      List.filter_sublist)).symm

/-- For a repetition-free candidate list, saturation means that at least `quota`
candidates are marked by the `C` or `D` streams. -/
theorem t1RunSaturated_iff
    (s : T1RunState) (quota : Nat) (hcurrent : s.current.Nodup) :
    t1RunSaturated s quota = true ↔
      quota ≤
        (s.current.toFinset ∩
          (s.cMarked.toFinset ∪ s.dMarked.toFinset)).card := by
  let hits := s.current.filter
    (fun x => decide (x ∈ s.cMarked) || decide (x ∈ s.dMarked))
  have hhits : hits.Nodup := hcurrent.filter _
  have hcard :
      hits.length =
        (s.current.toFinset ∩
          (s.cMarked.toFinset ∪ s.dMarked.toFinset)).card := by
    calc
      hits.length = hits.toFinset.card :=
        (List.toFinset_card_of_nodup hhits).symm
      _ = (s.current.toFinset ∩
          (s.cMarked.toFinset ∪ s.dMarked.toFinset)).card := by
        congr 1
        ext x
        simp [hits]
  simp [t1RunSaturated, hits, hcard]

end Kolmogorov
