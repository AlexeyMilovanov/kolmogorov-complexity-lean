/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Effective

/-!
# Non-adaptive (truth-table) oracle machines

* `NonAdaptiveOn c e x`: within its clock `clock e |x|`, the clocked coded machine `(c, e)` makes
  the same queries on `x` under every oracle, so its queries can be computed before any answer is
  used (a truth-table reduction).
* `card_queries_le`, `card_querySet_le_of_nonAdaptive`: at most one query per step, hence a
  non-adaptive machine has at most `clock e |x|` possible queries on `x`.
* `PolyTimeTT B` (`P^B_tt`): the sets decided with oracle `B` by a machine that halts within
  `p(|x|)` steps and makes the queries of the empty oracle, under every oracle;
  `exists_clocked_tt` turns such a machine into a clocked coded machine, non-adaptive on every
  input.  The class is not degenerate: `PolyTimeTT B ⊆ PolyTimeOracle B` and `B ∈ PolyTimeTT B`
  (`self_mem_polyTimeTT`, by the machine `copyOTM` that asks its input).
* `nonAdaptiveB`: a primitive recursive decision procedure for `NonAdaptiveOn (decodeCode m) e x`
  (`nonAdaptiveB_iff`, `nonAdaptiveB_computable`): the queries depend only on the oracle's
  restriction to the finite set of possible queries, so it suffices to compare the queries made
  with the finite oracles `L ⊆ queryListCode m e x` with those made with the empty oracle.
-/

namespace Kolmogorov.RandomStrings

/-! ### Non-adaptivity and the number of queries -/

/-- The clocked coded machine `(c, e)` is *non-adaptive on `x`*: within the clock it makes the
same queries on `x` under every oracle as with the empty oracle. -/
def NonAdaptiveOn (c : OTMCode) (e : ℕ) (x : BitString) : Prop :=
  ∀ B : Set BitString, queries c.toOTM B x (clock e x.length) =
    queries c.toOTM ∅ x (clock e x.length)

/-- At most one query per step: during `t` steps at most `t` strings are queried. -/
theorem card_queries_le (M : OTM) (B : Set BitString) (x : BitString) (t : ℕ) :
    (queries M B x t).card ≤ t := by
  unfold queries
  calc ((Finset.range t).biUnion fun s => (askedAt M (run M B x s)).toFinset).card
      ≤ ∑ s ∈ Finset.range t, (askedAt M (run M B x s)).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ Finset.range t, 1 := Finset.sum_le_sum fun s _ => by
        rw [Option.card_toFinset]; cases askedAt M (run M B x s) <;> simp
    _ = t := by simp

/-- For a machine that is non-adaptive on `x`, the possible queries are the queries made with the
empty oracle. -/
theorem querySet_eq_of_nonAdaptive {c : OTMCode} {e : ℕ} {x : BitString} (h : NonAdaptiveOn c e x) :
    querySet c.toOTM x (clock e x.length) = queries c.toOTM ∅ x (clock e x.length) := by
  ext z
  rw [querySet, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨B, hB⟩
    rwa [h B] at hB
  · intro hz
    exact ⟨∅, hz⟩

/-- For a machine that is non-adaptive on `x`, the possible queries are the queries made with any
oracle. -/
theorem queries_eq_querySet_of_nonAdaptive {c : OTMCode} {e : ℕ} {x : BitString}
    (h : NonAdaptiveOn c e x) (B : Set BitString) :
    queries c.toOTM B x (clock e x.length) = querySet c.toOTM x (clock e x.length) := by
  rw [querySet_eq_of_nonAdaptive h, h B]

/-- A machine that is non-adaptive on `x` has at most `clock e |x| + 1` possible queries on `x`. -/
theorem card_querySet_le_of_nonAdaptive {c : OTMCode} {e : ℕ} {x : BitString}
    (h : NonAdaptiveOn c e x) :
    (querySet c.toOTM x (clock e x.length)).card ≤ clock e x.length + 1 := by
  rw [querySet_eq_of_nonAdaptive h]
  exact (card_queries_le _ _ _ _).trans (Nat.le_succ _)

/-! ### Polynomial-time truth-table reductions -/

/-- `P^B_tt`: the sets decided with oracle `B` by an oracle machine which, under *every* oracle
`B'`, halts on `x` within `p(|x|)` steps and makes within `p(|x|)` steps the same queries as with
the empty oracle (the queries do not depend on the answers: a polynomial-time truth-table
reduction). -/
def PolyTimeTT (B : Set BitString) : Set (Set BitString) :=
  {A | ∃ (M : OTM) (p : Polynomial ℕ),
    (∀ (B' : Set BitString) (x : BitString), ∃ t ≤ p.eval x.length, Halted M (run M B' x t)) ∧
    (∀ (B' : Set BitString) (x : BitString),
      queries M B' x (p.eval x.length) = queries M ∅ x (p.eval x.length)) ∧
    ∀ x, x ∈ A ↔ Accepts M B x}

/-- `P^B_tt ⊆ P^B`. -/
theorem polyTimeTT_subset_polyTimeOracle (B : Set BitString) : PolyTimeTT B ⊆ PolyTimeOracle B := by
  rintro A ⟨M, p, hp, -, hA⟩
  exact ⟨M, p, fun x => hp B x, hA⟩

/-- A halted configuration asks nothing. -/
theorem askedAt_eq_none_of_halted (M : OTM) (c : Config M) (h : Halted M c) :
    askedAt M c = none := by
  unfold askedAt
  rw [ite_eq_left h]

/-- After the machine halts no further queries are made. -/
theorem queries_eq_of_halted (M : OTM) (B : Set BitString) (x : BitString) {t T : ℕ} (hle : t ≤ T)
    (h : Halted M (run M B x t)) : queries M B x T = queries M B x t := by
  refine Finset.Subset.antisymm (fun z hz => ?_) (queries_mono M B x hle)
  obtain ⟨s, hs, hz⟩ := (mem_queries M B x T z).1 hz
  refine (mem_queries M B x t z).2 ⟨s, ?_, hz⟩
  by_contra hst
  rw [run_of_halted_le M B x (not_lt.1 hst) h, askedAt_eq_none_of_halted M _ h] at hz
  simp at hz

/-- Two machines asking the same strings at every step make the same queries. -/
theorem queries_eq_of_askedAt (M M' : OTM) (B : Set BitString) (x : BitString) (t : ℕ)
    (h : ∀ s, askedAt M (run M B x s) = askedAt M' (run M' B x s)) :
    queries M B x t = queries M' B x t := by
  unfold queries
  exact Finset.biUnion_congr rfl fun s _ => by rw [h s]

/-- Any set in `P^B_tt` is decided with oracle `B` by a clocked coded machine that is
non-adaptive on every input. -/
theorem exists_clocked_tt (B A : Set BitString) (h : A ∈ PolyTimeTT B) :
    ∃ (c : OTMCode) (e : ℕ), (∀ x, NonAdaptiveOn c e x) ∧ ClockedDecides c e B A := by
  obtain ⟨M, p, hp, hq, hA⟩ := h
  obtain ⟨c, hc⟩ := exists_code M
  obtain ⟨e, he⟩ := exists_clock_ge p
  have hcq : ∀ (B' : Set BitString) (x : BitString) (t : ℕ),
    queries c.toOTM B' x t = queries M B' x t :=
    fun B' x t => queries_eq_of_askedAt _ _ B' x t fun s => ((hc B' x s).2.2.2).symm
  have hclk : ∀ (B' : Set BitString) (x : BitString),
      queries M B' x (clock e x.length) = queries M B' x (p.eval x.length) := by
    intro B' x
    obtain ⟨t, ht, hh⟩ := hp B' x
    rw [queries_eq_of_halted M B' x (ht.trans (he _)) hh, queries_eq_of_halted M B' x ht hh]
  refine ⟨c, e, fun x B' => ?_, fun x => ?_⟩
  · rw [hcq, hcq, hclk, hclk, hq]
  · obtain ⟨t, ht, hh⟩ := hp B x
    rw [hA x]
    constructor
    · intro hacc
      have h1 := (accepts_iff_of_halted M B x t hh).1 hacc
      exact ⟨t, ht.trans (he _), (hc B x t).2.1.1 h1⟩
    · rintro ⟨s, -, h'⟩
      exact ⟨s, (hc B x s).2.1.2 h'⟩

/-! ### Non-vacuity: every oracle set is in its own `P^B_tt` -/

/-- States of the machine `copyOTM`. -/
inductive CopyQ
  | read
  | move
  | acc
  | rej
  deriving DecidableEq

instance : Fintype CopyQ :=
  ⟨{CopyQ.read, CopyQ.move, CopyQ.acc, CopyQ.rej}, fun q => by cases q <;> simp⟩

/-- The machine that copies its input into the query buffer (one `push` and one move right per
input bit), asks it at the first blank, and accepts iff the answer is positive. -/
def copyOTM : OTM where
  Q := CopyQ
  start := .read
  accept := .acc
  reject := .rej
  δ q a := match q, a with
    | .read, some b => .push .move b
    | .read, none => .ask .acc .rej
    | .move, a => .step .read a .right
    | .acc, a => .step .acc a .stay
    | .rej, a => .step .rej a .stay

/-- The tape of the `copyOTM` machine initially contains the input bitstring. -/
theorem copyOTM_tape (x : BitString) (i : ℕ) : (init copyOTM x).tape (i : ℤ) = x[i]? := by
  simp [init]

/-- The `copyOTM` machine has not halted if its state is either reading or moving. -/
theorem copyOTM_not_halted (c : Config copyOTM) (h : c.q = CopyQ.read ∨ c.q = CopyQ.move) :
    ¬ Halted copyOTM c := by
  rintro (h' | h') <;> rcases h with h | h <;> rw [h] at h' <;> cases h'

/-- The `copyOTM` machine transitions from reading to moving when taking a step. -/
theorem copyOTM_step_read (B : Set BitString) (x : BitString) (i : ℕ) (hi : i < x.length) :
    step copyOTM B ⟨CopyQ.read, (init copyOTM x).tape, (i : ℤ), x.take i⟩ =
      ⟨CopyQ.move, (init copyOTM x).tape, (i : ℤ), x.take (i + 1)⟩ := by
  rw [step_eq_push copyOTM B ⟨CopyQ.read, (init copyOTM x).tape, (i : ℤ), x.take i⟩
    (copyOTM_not_halted _ (Or.inl rfl)) (q' := CopyQ.move) (b := x[i]) ?_]
  · rw [List.take_add_one, List.getElem?_eq_getElem hi]
    rfl
  · change copyOTM.δ CopyQ.read ((init copyOTM x).tape (i : ℤ)) = _
    rw [copyOTM_tape, List.getElem?_eq_getElem hi]
    rfl

/-- The `copyOTM` machine transitions from moving to reading when taking a step. -/
theorem copyOTM_step_move (B : Set BitString) (x : BitString) (i : ℕ) (buf : BitString) :
    step copyOTM B ⟨CopyQ.move, (init copyOTM x).tape, (i : ℤ), buf⟩ =
      ⟨CopyQ.read, (init copyOTM x).tape, ((i + 1 : ℕ) : ℤ), buf⟩ := by
  rw [step_eq_step copyOTM B ⟨CopyQ.move, (init copyOTM x).tape, (i : ℤ), buf⟩
    (copyOTM_not_halted _ (Or.inr rfl)) (q' := CopyQ.read) (a := (init copyOTM x).tape (i : ℤ))
    (mv := .right) rfl]
  simp [moveHead]

/-- The `copyOTM` machine is in the reading state at even step numbers. -/
theorem copyOTM_run_even (B : Set BitString) (x : BitString) (i : ℕ) (hi : i ≤ x.length) :
    run copyOTM B x (2 * i) = ⟨CopyQ.read, (init copyOTM x).tape, (i : ℤ), x.take i⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, run, run, ih (by omega),
      copyOTM_step_read B x i (by omega), copyOTM_step_move]

/-- The `copyOTM` machine is in the moving state at odd step numbers. -/
theorem copyOTM_run_odd (B : Set BitString) (x : BitString) (i : ℕ) (hi : i < x.length) :
    run copyOTM B x (2 * i + 1) =
      ⟨CopyQ.move, (init copyOTM x).tape, (i : ℤ), x.take (i + 1)⟩ := by
  rw [run, copyOTM_run_even B x i hi.le, copyOTM_step_read B x i hi]

open Classical in
/-- The `copyOTM` machine reaches the accept or reject state based on whether the input is in
the oracle set after exactly $2 |x| + 1$ steps. -/
theorem copyOTM_run_last (B : Set BitString) (x : BitString) :
    run copyOTM B x (2 * x.length + 1) =
      ⟨if x ∈ B then copyOTM.accept else copyOTM.reject, (init copyOTM x).tape, (x.length : ℤ),
        []⟩ := by
  rw [run, copyOTM_run_even B x x.length le_rfl,
    step_eq_ask copyOTM B ⟨CopyQ.read, (init copyOTM x).tape, (x.length : ℤ), x.take x.length⟩
      (copyOTM_not_halted _ (Or.inl rfl)) (q₁ := copyOTM.accept) (q₂ := copyOTM.reject) ?_]
  · rw [List.take_length]
  · change copyOTM.δ CopyQ.read ((init copyOTM x).tape (x.length : ℤ)) = _
    rw [copyOTM_tape, List.getElem?_eq_none le_rfl]
    rfl

/-- The `copyOTM` machine halts within $2 |x| + 1$ steps. -/
theorem copyOTM_halted (B : Set BitString) (x : BitString) :
    Halted copyOTM (run copyOTM B x (2 * x.length + 1)) := by
  classical
  rw [copyOTM_run_last]
  by_cases hx : x ∈ B
  · exact Or.inl (ite_eq_left hx)
  · exact Or.inr (ite_eq_right hx)

/-- The `copyOTM` machine accepts an input string exactly when it belongs to the oracle set. -/
theorem copyOTM_accepts_iff (B : Set BitString) (x : BitString) : Accepts copyOTM B x ↔ x ∈ B := by
  classical
  rw [accepts_iff_of_halted copyOTM B x _ (copyOTM_halted B x), copyOTM_run_last]
  by_cases hx : x ∈ B
  · exact ⟨fun _ => hx, fun _ => ite_eq_left hx⟩
  · refine ⟨fun h => ?_, fun h => absurd h hx⟩
    have h' := (ite_eq_right hx).symm.trans h
    cases h'

/-- The execution of the `copyOTM` machine during its first $2 |x|$ steps is independent of
the oracle. -/
theorem copyOTM_run_indep (B B' : Set BitString) (x : BitString) (s : ℕ) (hs : s ≤ 2 * x.length) :
    run copyOTM B x s = run copyOTM B' x s := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' s
  · rw [copyOTM_run_even B x i (by omega), copyOTM_run_even B' x i (by omega)]
  · rw [copyOTM_run_odd B x i (by omega), copyOTM_run_odd B' x i (by omega)]

/-- `P^B_tt` is not degenerate: `B ∈ P^B_tt` (ask the input). -/
theorem self_mem_polyTimeTT (B : Set BitString) : B ∈ PolyTimeTT B := by
  have hp : ∀ n : ℕ, (2 * Polynomial.X + 1 : Polynomial ℕ).eval n = 2 * n + 1 := fun n => by
    simp
  refine ⟨copyOTM, 2 * Polynomial.X + 1,
    fun B' x => ⟨2 * x.length + 1, (hp _).ge, copyOTM_halted B' x⟩, fun B' x => ?_,
    fun x => (copyOTM_accepts_iff B x).symm⟩
  rw [hp]
  unfold queries
  exact Finset.biUnion_congr rfl fun s hs => by
    rw [copyOTM_run_indep B' ∅ x s (by simp at hs; omega)]

/-! ### Deciding non-adaptivity -/

/-- The queries within `T` steps depend only on the oracle's restriction to these queries. -/
theorem queries_eq_of_agree (M : OTM) (B B' : Set BitString) (x : BitString) (T : ℕ)
    (h : ∀ z ∈ queries M B x T, (z ∈ B ↔ z ∈ B')) : queries M B x T = queries M B' x T := by
  unfold queries
  refine Finset.biUnion_congr rfl fun s hs => ?_
  rw [run_eq_of_agree M B B' x s fun z hz =>
    h z (queries_mono M B x (Finset.mem_range.1 hs).le hz)]

/-- The queries within `T` steps depend only on the oracle's restriction to the possible
queries. -/
theorem queries_eq_of_agree_querySet (M : OTM) (B B' : Set BitString) (x : BitString) (T : ℕ)
    (h : ∀ z ∈ querySet M x T, (z ∈ B ↔ z ∈ B')) : queries M B x T = queries M B' x T :=
  queries_eq_of_agree M B B' x T fun z hz =>
    h z (by rw [querySet, Set.Finite.mem_toFinset]; exact ⟨B, hz⟩)

/-- The queries made by the coded machine `decodeCode m` with the finite oracle `{z | z ∈ ans}` on
`x` during the first `T` steps, as a list. -/
def queriesC (m : ℕ) (ans : List BitString) (x : BitString) (T : ℕ) : List BitString :=
  (List.range T).flatMap fun s =>
    bif askB m (runC m ans x s) then [(runC m ans x s).buf] else []

/-- A string is in the list of queries made by the coded machine exactly when it is queried by
the corresponding oracle Turing machine. -/
theorem mem_queriesC (m : ℕ) (ans : List BitString) (x : BitString) (T : ℕ) (z : BitString) :
    z ∈ queriesC m ans x T ↔ z ∈ queries (decodeCode m).toOTM {w | w ∈ ans} x T := by
  rw [mem_queries]
  simp only [queriesC, List.mem_flatMap, List.mem_range]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [askedAt_eq_of_rep m _ _ (runC_represents m ans x s)]
  cases askB m (runC m ans x s) <;> simp [eq_comm]

/-- The list of queries made by the coded machine, when converted to a `Finset`, equals the set
of queries made by the oracle Turing machine. -/
theorem queriesC_toFinset (m : ℕ) (ans : List BitString) (x : BitString) (T : ℕ) :
    (queriesC m ans x T).toFinset = queries (decodeCode m).toOTM {w | w ∈ ans} x T := by
  ext z
  rw [List.mem_toFinset, mem_queriesC]

/-- The set of elements belonging to the empty list is the empty set. -/
theorem setOf_mem_nil : {w : BitString | w ∈ ([] : List BitString)} = ∅ := by
  ext w
  simp

/-- The test that the queries made with the finite oracle `L` within `T` steps are the queries
made with the empty oracle. -/
def sameQueriesB (m : ℕ) (x : BitString) (T : ℕ) (L : List BitString) : Bool :=
  subB (queriesC m L x T) (queriesC m [] x T) && subB (queriesC m [] x T) (queriesC m L x T)

/-- The boolean check `sameQueriesB` returns true exactly when the queries made with a finite
oracle equal the queries made with the empty oracle. -/
theorem sameQueriesB_iff (m : ℕ) (x : BitString) (T : ℕ) (L : List BitString) :
    sameQueriesB m x T L = true ↔
      queries (decodeCode m).toOTM {w | w ∈ L} x T = queries (decodeCode m).toOTM ∅ x T := by
  rw [← queriesC_toFinset, ← setOf_mem_nil, ← queriesC_toFinset]
  simp only [sameQueriesB, Bool.and_eq_true, subB_iff]
  constructor
  · rintro ⟨h1, h2⟩
    ext z
    simp only [List.mem_toFinset]
    exact ⟨h1 z, h2 z⟩
  · intro h
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · have hz' : z ∈ (queriesC m L x T).toFinset := List.mem_toFinset.2 hz
      rw [h] at hz'
      exact List.mem_toFinset.1 hz'
    · have hz' : z ∈ (queriesC m [] x T).toFinset := List.mem_toFinset.2 hz
      rw [← h] at hz'
      exact List.mem_toFinset.1 hz'

/-- The decision procedure for non-adaptivity: for every sublist `L` of the possible queries, the
queries made with the finite oracle `L` are those made with the empty oracle. -/
def nonAdaptiveB (m e : ℕ) (x : BitString) : Bool :=
  allB (allSub (queryListCode m e x)) (sameQueriesB m x (clock e x.length))

/-- The boolean check `nonAdaptiveB` returns true exactly when the coded machine is non-adaptive
on the given input. -/
theorem nonAdaptiveB_iff (m e : ℕ) (x : BitString) :
    nonAdaptiveB m e x = true ↔ NonAdaptiveOn (decodeCode m) e x := by
  classical
  rw [nonAdaptiveB, allB_iff]
  constructor
  · intro h B
    obtain ⟨L, hL, hLT⟩ := exists_allSub (queryListCode m e x)
      ((queryListCode m e x).toFinset.filter fun z => z ∈ B)
      fun z hz => List.mem_toFinset.1 (Finset.mem_filter.1 hz).1
    have hag : ∀ z ∈ querySet (decodeCode m).toOTM x (clock e x.length),
        (z ∈ B ↔ z ∈ {w | w ∈ L}) := by
      intro z hz
      rw [querySet_eq_toFinset] at hz
      change z ∈ B ↔ z ∈ L
      rw [← List.mem_toFinset (l := L), hLT, Finset.mem_filter]
      exact ⟨fun hB => ⟨hz, hB⟩, fun h' => h'.2⟩
    rw [queries_eq_of_agree_querySet _ _ _ _ _ hag]
    exact (sameQueriesB_iff m x _ L).1 (h L hL)
  · intro h L _
    exact (sameQueriesB_iff m x _ L).2 (h _)

/-! ### Primitive recursiveness -/

/-- The function `queriesC` is primitive recursive. -/
theorem queriesC_primrec :
    Primrec fun p : ℕ × List BitString × BitString × ℕ => queriesC p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hrun : Primrec fun q : (ℕ × List BitString × BitString × ℕ) × ℕ =>
      runC q.1.1 q.1.2.1 q.1.2.2.1 q.2 :=
    runC_primrec.comp ((Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp (Primrec.snd.comp
      Primrec.fst)).pair ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
        Primrec.fst))).pair Primrec.snd)))
  have hinner : Primrec₂ fun (q : ℕ × List BitString × BitString × ℕ) (s : ℕ) =>
      bif askB q.1 (runC q.1 q.2.1 q.2.2.1 s) then [(runC q.1 q.2.1 q.2.2.1 s).buf] else [] :=
    (Primrec.cond (askB_primrec.comp (Primrec.fst.comp Primrec.fst) hrun)
      (Primrec.list_cons.comp (CC.primrec_buf.comp hrun) (Primrec.const []))
      (Primrec.const [])).to₂
  exact (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.snd.comp (Primrec.snd.comp
    Primrec.snd))) hinner).of_eq fun _ => rfl

attribute [local irreducible] queriesC subB in
/-- The function `sameQueriesB` is primitive recursive. -/
theorem sameQueriesB_primrec :
    Primrec fun p : (ℕ × BitString × ℕ) × List BitString =>
      sameQueriesB p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  have hL : Primrec fun p : (ℕ × BitString × ℕ) × List BitString =>
      queriesC p.1.1 p.2 p.1.2.1 p.1.2.2 :=
    queriesC_primrec.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.snd.comp (Primrec.snd.comp
        Primrec.fst)))))
  have h0 : Primrec fun p : (ℕ × BitString × ℕ) × List BitString =>
      queriesC p.1.1 [] p.1.2.1 p.1.2.2 :=
    queriesC_primrec.comp ((Primrec.fst.comp Primrec.fst).pair ((Primrec.const []).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.snd.comp (Primrec.snd.comp
        Primrec.fst)))))
  exact (Primrec.and.comp (subB_primrec.comp hL h0) (subB_primrec.comp h0 hL)).of_eq fun _ => rfl

attribute [local irreducible] sameQueriesB allSub queryListCode clock in
/-- The function `nonAdaptiveB` is primitive recursive. -/
theorem nonAdaptiveB_primrec : Primrec fun p : ℕ × ℕ × BitString =>
      nonAdaptiveB p.1 p.2.1 p.2.2 := by
  have hT : Primrec fun p : ℕ × ℕ × BitString => clock p.2.1 p.2.2.length :=
    clock_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldr (f := fun p : ℕ × ℕ × BitString =>
      allSub (queryListCode p.1 p.2.1 p.2.2))
    (g := fun _ => true)
    (h := fun p q => sameQueriesB p.1 p.2.2 (clock p.2.1 p.2.2.length) q.1 && q.2)
    (allSub_primrec.comp queryListCode_primrec) (Primrec.const true)
    (Primrec.and.comp (sameQueriesB_primrec.comp (((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair (hT.comp Primrec.fst))).pair
        (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

/-- The function `nonAdaptiveB` is computable. -/
theorem nonAdaptiveB_computable :
    Computable fun p : ℕ × ℕ × BitString => nonAdaptiveB p.1 p.2.1 p.2.2 :=
  nonAdaptiveB_primrec.to_comp

/-! `Family.tt` and the tt-case of the paper are in `AFG/Instances.lean`. -/

end Kolmogorov.RandomStrings

