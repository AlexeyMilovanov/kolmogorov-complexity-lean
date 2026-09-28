import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.MonotoneComplexity.SimpleTreeApproximation
import KolmogorovMathlib.MonotoneComplexity.TreeAllocation

/-!
# Realising a simple tree approximation by a computable nested allocation

A simple tree approximation prescribes, stage by stage, dyadic masses at the nodes of the tree;
here those masses are turned into actual sets of strings. An
`EffectiveNestedTreeAllocation` is a computable sequence of tree allocations, each refining the
previous one, whose atoms have the prescribed masses, and
`exists_effectiveNestedTreeAllocation` builds one for every simple tree approximation.

### Outline

* `TreeAllocation.stageZero` and the doubling estimate `two_mul_q_le` on the numerators of the
  approximation;
* the path recursion `pathStep` / `pathAllocStep`, which computes the allocation at every node
  along a path from that of the parent, and its iterative reformulation;
* a primitive-recursion toolkit for the resulting loop, the intended value of the path vector,
  and its computability, ending in `computable_pathAlloc`, `computable_pathAtoms` and
  `computable_mem_pathAtoms`.
-/

namespace Kolmogorov

/-- The allocation at stage zero: the root holds the single empty atom and nothing else is
allocated. -/
def TreeAllocation.stageZero (q : BitString → ℕ)
    (hq_root : q [] = 1) (hq_front : ∀ x, 0 < x.length → q x = 0) : TreeAllocation q 0 where
  atoms x := if x = [] then [[]] else []
  atoms_length x p hp := by
    change p ∈ (if x = [] then [[]] else []) at hp
    split at hp
    · simp only [List.mem_singleton] at hp; subst hp; rfl
    · contradiction
  atoms_nodup x := by
    split
    · exact List.nodup_singleton _
    · exact List.nodup_nil
  atoms_card x := by
    split
    · next h => subst h; simp [hq_root]
    · next h =>
      have h1 : 0 < x.length := by cases x <;> simp_all
      simp [hq_front x h1]
  atoms_root p hp := by
    change p ∈ (if [] = ([] : BitString) then [[]] else [])
    rw [if_pos rfl]
    have hp' : p = [] := by cases p <;> simp_all
    subst hp'
    exact List.mem_singleton.mpr rfl
  atoms_child x b p hp := by
    change p ∈ (if x ++ [b] = [] then [[]] else []) at hp
    change p ∈ (if x = [] then [[]] else [])
    have h1 : ¬(x ++ [b] = []) := by simp
    rw [if_neg h1] at hp
    contradiction
  atoms_disjoint x p hp := by
    change p ∈ (if x ++ [false] = [] then [[]] else []) at hp
    have h1 : ¬(x ++ [false] = []) := by simp
    rw [if_neg h1] at hp
    contradiction

/-- The numerators of a simple tree approximation at least double from one stage to the next. -/
theorem two_mul_q_le {a : BitString → ENNReal} {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation a q) (s : ℕ) (x : BitString) :
    2 * q s x ≤ q (s + 1) x := by
  exact two_mul_le_of_dyadicValue_le (hq.2.2.2.1 s x)

/-- A computable sequence of tree allocations, each refining the previous one, realising the
numerators `q`. -/
structure EffectiveNestedTreeAllocation (q : ℕ → BitString → ℕ) where
  stage : ∀ s, TreeAllocation (q s) s
  refines        : ∀ s x p, p ∈ refineAtoms ((stage s).atoms x) → p ∈ (stage (s + 1)).atoms x
  mem_computable : Computable fun z : (ℕ × BitString) × BitString =>
                     decide (z.2 ∈ (stage z.1.1).atoms z.1.2)

/-! ### The path-state recursion

Computing the stage-`s` allocation at a node `x` needs the stage-`(s-1)` allocations at every
prefix of `x` *and* at each of their siblings.  We therefore carry, along the path to `x`, the
finite vector of pairs `(allocation at the prefix, allocation at its sibling)`; one layer of the
recursion turns the stage-`s` vector into the stage-`(s+1)` vector. -/

/-- One entry of the path vector: the allocation at a node together with the allocation at its
sibling. -/
abbrev PathEntry := List BitString × List BitString

/-- One layer of the path recursion: `pathStep r d cp bs prev parent` produces the entries for the
nodes `cp ++ bs.take 1`, `cp ++ bs.take 2`, … of the next stage, where `prev` holds the previous
stage's entries for those very nodes, `parent` is the next stage's allocation at `cp`, `r` is the
next stage's numerator function, and `d` is the next stage's depth bound. -/
def pathStep (r : BitString → ℕ) (d : ℕ) :
    BitString → BitString → List PathEntry → List BitString → List PathEntry
  | _, [], _, _ => []
  | cp, b :: bs, prev, parent =>
      let pc := prev.headD ([], [])
      let Mf := refineAtoms (cond b pc.2 pc.1)
      let Mt := refineAtoms (cond b pc.1 pc.2)
      let pool := parent.filter (fun p => decide (p ∉ Mf ∧ p ∉ Mt))
      let nf := r (cp ++ [false]) - Mf.length
      let cf := Mf ++ pool.take nf
      let ct := Mt ++ (pool.drop nf).take (r (cp ++ [true]) - Mt.length)
      let opath := if d < cp.length + 1 then [] else cond b ct cf
      let osib := if d < cp.length + 1 then [] else cond b cf ct
      (opath, osib) :: pathStep r d (cp ++ [b]) bs prev.tail opath

/-- One stage of the allocation along a path: the root receives all strings of the new length and
the path recursion distributes them. -/
def pathAllocStep (q : ℕ → BitString → ℕ) (s : ℕ) (x : BitString)
    (prev : List PathEntry) : List PathEntry :=
  (exactLengthPrograms (s + 1), []) ::
    pathStep (q (s + 1)) (s + 1) [] x prev.tail (exactLengthPrograms (s + 1))

/-- The allocation along the path to `x` after `s` stages, as a list of entries, one per node of
the path. -/
def pathAlloc (q : ℕ → BitString → ℕ) (s : ℕ) (x : BitString) : List PathEntry :=
  match s with
  | 0 => ([[]], []) :: List.replicate x.length ([], [])
  | s + 1 => pathAllocStep q s x (pathAlloc q s x)

/-- The canonical stage-`s` tree allocation of a simple tree approximation, built by extending the
previous stage. -/
def canonicalStage {a : BitString → ENNReal} {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation a q) : ∀ s, TreeAllocation (q s) s
  | 0 => TreeAllocation.stageZero (q 0) (hq.1 0) (fun x hx => hq.2.2.1 0 x hx)
  | s + 1 => (canonicalStage hq s).extend (hq.1 (s + 1)) (hq.2.1 (s + 1))
      (fun x hx => hq.2.2.1 (s + 1) x hx) (fun x => two_mul_q_le hq s x)

/-! ### An iterative form of the path recursion

`pathStep` recurses on the list of remaining bits; the loop below carries that list inside its
state, so that one layer of the path recursion becomes a fixed number of iterations of a single
state transformation.  This is the shape the computability framework can follow. -/

/-- The loop state: the bits still to be processed, the current node, the previous stage's
remaining entries, the current parent allocation, and the entries produced so far. -/
abbrev PathIterState :=
  BitString × BitString × List PathEntry × List BitString × List PathEntry

/-- The purely combinatorial content of one loop iteration: the two numerators of the children of
the current node are supplied as arguments instead of being looked up. -/
def pathIterCore (d nfalse ntrue : ℕ) (st : PathIterState) : PathIterState :=
  let b := st.1.headD false
  let cp := st.2.1
  let prev := st.2.2.1
  let parent := st.2.2.2.1
  let out := st.2.2.2.2
  let pc := prev.headD ([], [])
  let Mf := refineAtoms (cond b pc.2 pc.1)
  let Mt := refineAtoms (cond b pc.1 pc.2)
  let pool := parent.filter (fun p => decide (p ∉ Mf ∧ p ∉ Mt))
  let nf := nfalse - Mf.length
  let cf := Mf ++ pool.take nf
  let ct := Mt ++ (pool.drop nf).take (ntrue - Mt.length)
  let opath := if d < cp.length + 1 then [] else cond b ct cf
  let osib := if d < cp.length + 1 then [] else cond b cf ct
  (st.1.tail, cp ++ [b], prev.tail, opath, out ++ [(opath, osib)])

/-- One iteration of the loop implementing `pathStep`.  On a state whose first component is empty
the result is meaningless; the loop is run exactly as many times as there are bits. -/
def pathIterStep (r : BitString → ℕ) (d : ℕ) (st : PathIterState) : PathIterState :=
  pathIterCore d (r (st.2.1 ++ [false])) (r (st.2.1 ++ [true])) st

/-- The path recursion agrees with the iterated loop that carries the remaining bits in its state.
-/
theorem pathStep_eq_iter (r : BitString → ℕ) (d : ℕ) (bs cp : BitString)
    (prev : List PathEntry) (parent : List BitString) (out : List PathEntry) :
    ((pathIterStep r d)^[bs.length] (bs, cp, prev, parent, out)).2.2.2.2
      = out ++ pathStep r d cp bs prev parent := by
  induction bs generalizing cp prev parent out with
  | nil => simp [pathStep]
  | cons b bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [pathIterStep, pathIterCore, List.headD_cons, List.tail_cons]
    rw [ih]
    simp [pathStep]

/-- One allocation stage, written through the iterated loop. -/
theorem pathAllocStep_eq_iter (q : ℕ → BitString → ℕ) (s : ℕ) (x : BitString)
    (prev : List PathEntry) :
    pathAllocStep q s x prev = (exactLengthPrograms (s + 1), []) ::
      ((pathIterStep (q (s + 1)) (s + 1))^[x.length]
        (x, [], prev.tail, exactLengthPrograms (s + 1), [])).2.2.2.2 := by
  rw [pathAllocStep, pathStep_eq_iter]
  simp

/-! ### Primitive-recursion toolkit for the loop -/

section PrimrecTools
variable {α β : Type*} [Primcodable α] [Primcodable β]

/-- Taking the head of a list with a default value is primitive recursive. -/
theorem headD_primrec {f : α → List β} (hf : Primrec f) (c : β) :
    Primrec (fun a => (f a).headD c) :=
  (Primrec.option_getD.comp (Primrec.list_head?.comp hf) (Primrec.const c)).of_eq (fun a => by
    cases f a <;> simp)

/-- Deciding list membership is primitive recursive. -/
theorem mem_decide_primrec [DecidableEq β] :
    Primrec₂ (fun (L : List β) (w : β) => decide (w ∈ L)) := by
  have heq : (fun (L : List β) (w : β) => decide (w ∈ L))
      = (fun L w => L.foldr (fun x acc => (w == x) || acc) false) := by
    funext L w
    induction L with
    | nil => simp
    | cons c t ih => simp [List.foldr_cons, ih, Bool.beq_eq_decide_eq]
  rw [heq]
  exact Primrec.list_foldr Primrec.fst (Primrec.const false)
    ((Primrec.or.comp (Primrec.beq.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂)

/-- Removing from a list the elements of two other lists is primitive recursive. -/
theorem filter_notMem_primrec {f g h : α → List BitString}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun a => (f a).filter (fun p => decide (p ∉ g a ∧ p ∉ h a))) := by
  have hp := (Primrec.and.comp
      (Primrec.not.comp (mem_decide_primrec.comp (hg.comp Primrec.fst) Primrec.snd))
      (Primrec.not.comp (mem_decide_primrec.comp (hh.comp Primrec.fst) Primrec.snd))).to₂
  refine (list_filter_primrec hf hp).of_eq (fun a => ?_)
  refine List.filter_congr (fun w _ => ?_)
  exact Bool.eq_iff_iff.mpr (by simp)

end PrimrecTools

/-- Refining a list of atoms is primitive recursive. -/
theorem refineAtoms_primrec : Primrec refineAtoms := by
  have heq : ∀ L : List BitString, refineAtoms L
      = (L.map (fun p => [p ++ [false], p ++ [true]])).flatten := by
    intro L; simp [refineAtoms, List.flatMap_def]
  refine (Primrec.list_flatten.comp (Primrec.list_map Primrec.id ?_)).of_eq
    (fun L => (heq L).symm)
  exact (Primrec.list_cons.comp
    (Primrec.list_append.comp Primrec.snd (Primrec.const [false]))
    (Primrec.list_cons.comp (Primrec.list_append.comp Primrec.snd (Primrec.const [true]))
      (Primrec.const []))).to₂

/-- The core of the loop step of the path allocation is primitive recursive. -/
theorem pathIterCore_primrec :
    Primrec (fun v : (ℕ × ℕ × ℕ) × PathIterState => pathIterCore v.1.1 v.1.2.1 v.1.2.2 v.2) := by
  have hd : Primrec (fun v : (ℕ × ℕ × ℕ) × PathIterState => v.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hn0 : Primrec (fun v : (ℕ × ℕ × ℕ) × PathIterState => v.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hn1 : Primrec (fun v : (ℕ × ℕ × ℕ) × PathIterState => v.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hrem : Primrec (fun v : (ℕ × ℕ × ℕ) × PathIterState => v.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hcp : Primrec (fun v : (ℕ × ℕ × ℕ) × PathIterState => v.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hprev : Primrec (fun v : (ℕ × ℕ × ℕ) × PathIterState => v.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hparent : Primrec (fun v : (ℕ × ℕ × ℕ) × PathIterState => v.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hout : Primrec (fun v : (ℕ × ℕ × ℕ) × PathIterState => v.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hb := headD_primrec hrem false
  have hpc := headD_primrec hprev (([], []) : PathEntry)
  have hMf := refineAtoms_primrec.comp
    (Primrec.cond hb (Primrec.snd.comp hpc) (Primrec.fst.comp hpc))
  have hMt := refineAtoms_primrec.comp
    (Primrec.cond hb (Primrec.fst.comp hpc) (Primrec.snd.comp hpc))
  have hpool := filter_notMem_primrec hparent hMf hMt
  have hnf := Primrec.nat_sub.comp hn0 (Primrec.list_length.comp hMf)
  have hcf := Primrec.list_append.comp hMf (Primrec.list_take.comp hpool hnf)
  have hct := Primrec.list_append.comp hMt
    (Primrec.list_take.comp (Primrec.list_drop.comp hpool hnf)
      (Primrec.nat_sub.comp hn1 (Primrec.list_length.comp hMt)))
  have hlt := Primrec.nat_lt.comp hd (Primrec.succ.comp (Primrec.list_length.comp hcp))
  have hopath := Primrec.ite hlt (Primrec.const []) (Primrec.cond hb hct hcf)
  have hosib := Primrec.ite hlt (Primrec.const []) (Primrec.cond hb hcf hct)
  exact (Primrec.pair (Primrec.list_tail.comp hrem)
    (Primrec.pair (Primrec.list_append.comp hcp (Primrec.list_cons.comp hb (Primrec.const [])))
      (Primrec.pair (Primrec.list_tail.comp hprev)
        (Primrec.pair hopath
          (Primrec.list_append.comp hout
            (Primrec.list_cons.comp (Primrec.pair hopath hosib)
              (Primrec.const []))))))).of_eq (fun _ => rfl)

/-- The stage-`s` allocation at output node `x`, read off the last entry of the state-carrying
`pathAlloc` recursion.  Its computability is what makes the associated lower graph enumerable. -/
def pathAtoms (q : ℕ → BitString → ℕ) (s : ℕ) (x : BitString) : List BitString :=
  ((pathAlloc q s x).getLast?.map Prod.fst).getD []

/-! ### The intended value of the path vector -/

/-- The path vector for an allocation `A`, below the node `cp` and along the bits `bs`. -/
def pathVecFrom (A : BitString → List BitString) : BitString → BitString → List PathEntry
  | _, [] => []
  | cp, b :: bs => (A (cp ++ [b]), A (cp ++ [!b])) :: pathVecFrom A (cp ++ [b]) bs

/-- The full path vector for an allocation `A` along `x`. -/
def pathVec (A : BitString → List BitString) (x : BitString) : List PathEntry :=
  (A [], []) :: pathVecFrom A [] x

/-- The last entry of the path vector from a node is the allocation at the end of the path. -/
theorem pathVecFrom_getLast (A : BitString → List BitString) (bs cp : BitString) (e : PathEntry) :
    (((e :: pathVecFrom A cp bs).getLast?).map Prod.fst).getD []
      = if bs = [] then e.1 else A (cp ++ bs) := by
  induction bs generalizing cp e with
  | nil => simp [pathVecFrom]
  | cons b bs ih =>
    rw [show pathVecFrom A cp (b :: bs)
        = (A (cp ++ [b]), A (cp ++ [!b])) :: pathVecFrom A (cp ++ [b]) bs from rfl,
      List.getLast?_cons_cons, ih]
    cases bs with
    | nil => simp
    | cons c cs => simp


/-- The last entry of the path vector of `x` is the allocation at `x`. -/
theorem pathVec_getLast (A : BitString → List BitString) (x : BitString) :
    (((pathVec A x).getLast?).map Prod.fst).getD [] = A x := by
  rw [pathVec, pathVecFrom_getLast]
  cases x with
  | nil => simp
  | cons b bs => simp

/-- At stage zero the path vector is empty at every node below the root. -/
theorem pathVecFrom_stageZero (cp bs : BitString) :
    pathVecFrom (fun y => if y = [] then [[]] else []) cp bs
      = List.replicate bs.length ([], []) := by
  induction bs generalizing cp with
  | nil => rfl
  | cons b bs ih =>
    rw [show pathVecFrom (fun y => if y = [] then [[]] else []) cp (b :: bs)
        = ((if cp ++ [b] = [] then [[]] else []), (if cp ++ [!b] = [] then [[]] else [])) ::
            pathVecFrom (fun y => if y = [] then [[]] else []) (cp ++ [b]) bs from rfl, ih]
    simp [List.replicate_succ]

/-- The next stage's allocation at a child, expressed through one `stepAlloc` of the parent's. -/
theorem pathChild_eq {a : BitString → ENNReal} {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation a q) (s : ℕ) (cp : BitString) (c : Bool)
    (parent : List BitString) (hparent : parent = (canonicalStage hq (s + 1)).atoms cp) :
    (if s + 1 < cp.length + 1 then []
      else TreeAllocation.stepAlloc (q (s + 1)) (canonicalStage hq s) cp c parent)
      = (canonicalStage hq (s + 1)).atoms (cp ++ [c]) := by
  have hatoms : ∀ y : BitString, (canonicalStage hq (s + 1)).atoms y
      = if s + 1 < y.length then []
        else TreeAllocation.runAlloc (q (s + 1)) (canonicalStage hq s) [] y
          (exactLengthPrograms (s + 1)) := by
    intro y
    rw [show (canonicalStage hq (s + 1)).atoms y
        = (canonicalStage hq s).extendAtoms (q s) (q (s + 1)) s y from rfl,
      TreeAllocation.extendAtoms_eq]
  by_cases hcp : s + 1 < cp.length + 1
  · rw [if_pos hcp, hatoms (cp ++ [c]), if_pos (by simpa using hcp)]
  · rw [if_neg hcp, hatoms (cp ++ [c]), if_neg (by simpa using hcp)]
    rw [hparent, hatoms cp, if_neg (by omega)]
    rw [TreeAllocation.runAlloc_append]
    simp

/-- One path step of the allocation recursion computes the path vector of the next canonical
stage. -/
theorem pathStep_eq_pathVecFrom {a : BitString → ENNReal} {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation a q) (s : ℕ) (bs cp : BitString) (parent : List BitString)
    (hparent : parent = (canonicalStage hq (s + 1)).atoms cp) :
    pathStep (q (s + 1)) (s + 1) cp bs (pathVecFrom (canonicalStage hq s).atoms cp bs) parent
      = pathVecFrom (canonicalStage hq (s + 1)).atoms cp bs := by
  induction bs generalizing cp parent with
  | nil => rfl
  | cons b bs ih =>
    have hf := pathChild_eq hq s cp false parent hparent
    have ht := pathChild_eq hq s cp true parent hparent
    cases b with
    | false =>
      have hstep : pathStep (q (s + 1)) (s + 1) cp (false :: bs)
          (pathVecFrom (canonicalStage hq s).atoms cp (false :: bs)) parent
          = ((canonicalStage hq (s + 1)).atoms (cp ++ [false]),
              (canonicalStage hq (s + 1)).atoms (cp ++ [true])) ::
            pathStep (q (s + 1)) (s + 1) (cp ++ [false]) bs
              (pathVecFrom (canonicalStage hq s).atoms (cp ++ [false]) bs)
              ((canonicalStage hq (s + 1)).atoms (cp ++ [false])) := by
        rw [← hf, ← ht]; rfl
      rw [hstep, ih (cp ++ [false]) _ rfl]
      rfl
    | true =>
      have hstep : pathStep (q (s + 1)) (s + 1) cp (true :: bs)
          (pathVecFrom (canonicalStage hq s).atoms cp (true :: bs)) parent
          = ((canonicalStage hq (s + 1)).atoms (cp ++ [true]),
              (canonicalStage hq (s + 1)).atoms (cp ++ [false])) ::
            pathStep (q (s + 1)) (s + 1) (cp ++ [true]) bs
              (pathVecFrom (canonicalStage hq s).atoms (cp ++ [true]) bs)
              ((canonicalStage hq (s + 1)).atoms (cp ++ [true])) := by
        rw [← hf, ← ht]; rfl
      rw [hstep, ih (cp ++ [true]) _ rfl]
      rfl

/-- The iterative allocation along a path computes the path vector of the canonical stage. -/
theorem pathAlloc_eq_pathVec {a : BitString → ENNReal} {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation a q) (s : ℕ) (x : BitString) :
    pathAlloc q s x = pathVec (canonicalStage hq s).atoms x := by
  induction s with
  | zero =>
    change ([[]], []) :: List.replicate x.length ([], []) = _
    rw [pathVec, show (canonicalStage hq 0).atoms = fun y => if y = [] then [[]] else [] from rfl,
      pathVecFrom_stageZero]
    simp
  | succ s ih =>
    have hroot : (canonicalStage hq (s + 1)).atoms [] = exactLengthPrograms (s + 1) :=
      TreeAllocation.extendAtoms_nil (q (s + 1)) (canonicalStage hq s)
    change pathAllocStep q s x (pathAlloc q s x) = _
    rw [pathAllocStep, ih,
      show (pathVec (canonicalStage hq s).atoms x).tail
        = pathVecFrom (canonicalStage hq s).atoms [] x from rfl,
      pathStep_eq_pathVecFrom hq s x [] _ hroot.symm, pathVec, hroot]

/-- **Structural leaf.** The state-carrying recursion reproduces the canonical stage allocation. -/
theorem pathAtoms_eq {a : BitString → ENNReal} {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation a q) (s : ℕ) (x : BitString) :
    pathAtoms q s x = (canonicalStage hq s).atoms x := by
  rw [pathAtoms, pathAlloc_eq_pathVec hq, pathVec_getLast]

/-! ### Computability of the path recursion -/

section Computability

variable {q : ℕ → BitString → ℕ}

/-- A recursion that ignores its index is an iteration. -/
theorem natRec_eq_iterate {σ : Type*} (f : σ → σ) (st : σ) (n : ℕ) :
    (Nat.rec st (fun _ ih => f ih) n : σ) = f^[n] st := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply']; exact congrArg f ih

/-- One loop step of the path allocation is computable. -/
theorem computable_pathIterStep (hqc : Computable fun p : ℕ × BitString => q p.1 p.2) :
    Computable (fun w : ℕ × PathIterState => pathIterStep (q (w.1 + 1)) (w.1 + 1) w.2) := by
  have hs : Computable (fun w : ℕ × PathIterState => w.1 + 1) :=
    (Primrec.succ.comp Primrec.fst).to_comp
  have hcp : Computable (fun w : ℕ × PathIterState => w.2.2.1) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).to_comp
  have hq0 : Computable (fun w : ℕ × PathIterState => q (w.1 + 1) (w.2.2.1 ++ [false])) :=
    hqc.comp (Computable.pair hs
      (Primrec.list_append.to_comp.comp hcp (Computable.const [false])))
  have hq1 : Computable (fun w : ℕ × PathIterState => q (w.1 + 1) (w.2.2.1 ++ [true])) :=
    hqc.comp (Computable.pair hs
      (Primrec.list_append.to_comp.comp hcp (Computable.const [true])))
  exact (pathIterCore_primrec.to_comp.comp
    (Computable.pair (Computable.pair hs (Computable.pair hq0 hq1)) Computable.snd)).of_eq
      (fun _ => rfl)

/-- Iterating the loop step a given number of times is computable. -/
theorem computable_pathIterN (hqc : Computable fun p : ℕ × BitString => q p.1 p.2) :
    Computable (fun w : (ℕ × ℕ) × PathIterState =>
      (pathIterStep (q (w.1.1 + 1)) (w.1.1 + 1))^[w.1.2] w.2) := by
  have hstep : Computable₂ (fun (w : (ℕ × ℕ) × PathIterState) (u : ℕ × PathIterState) =>
      pathIterStep (q (w.1.1 + 1)) (w.1.1 + 1) u.2) :=
    ((computable_pathIterStep hqc).comp (Computable.pair
      (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.snd.comp Computable.snd))).to₂
  exact (Computable.nat_rec (Computable.snd.comp Computable.fst) Computable.snd hstep).of_eq
    (fun _ => natRec_eq_iterate _ _ _)

/-- One allocation stage is computable. -/
theorem computable_pathAllocStep (hqc : Computable fun p : ℕ × BitString => q p.1 p.2) :
    Computable (fun w : (ℕ × BitString) × (ℕ × List PathEntry) =>
      pathAllocStep q w.2.1 w.1.2 w.2.2) := by
  have hs : Computable (fun w : (ℕ × BitString) × (ℕ × List PathEntry) => w.2.1) :=
    (Primrec.fst.comp Primrec.snd).to_comp
  have hx : Computable (fun w : (ℕ × BitString) × (ℕ × List PathEntry) => w.1.2) :=
    (Primrec.snd.comp Primrec.fst).to_comp
  have hprev : Computable (fun w : (ℕ × BitString) × (ℕ × List PathEntry) => w.2.2.tail) :=
    (Primrec.list_tail.comp (Primrec.snd.comp Primrec.snd)).to_comp
  have hE : Computable (fun w : (ℕ × BitString) × (ℕ × List PathEntry) =>
      exactLengthPrograms (w.2.1 + 1)) :=
    (primrec_exactLengthPrograms.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))).to_comp
  have hstate : Computable (fun w : (ℕ × BitString) × (ℕ × List PathEntry) =>
      ((w.1.2 : BitString), ([] : BitString), w.2.2.tail,
        exactLengthPrograms (w.2.1 + 1), ([] : List PathEntry))) :=
    Computable.pair hx (Computable.pair (Computable.const [])
      (Computable.pair hprev (Computable.pair hE (Computable.const []))))
  have hiter := (computable_pathIterN hqc).comp
    (Computable.pair (Computable.pair hs (Primrec.list_length.to_comp.comp hx)) hstate)
  have hproj := (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to_comp.comp
    hiter
  exact (Computable.list_cons.comp (Computable.pair hE (Computable.const [])) hproj).of_eq
    (fun w => (pathAllocStep_eq_iter q w.2.1 w.1.2 w.2.2).symm)

/-- The allocation along a path is computable in the stage and the node. -/
theorem computable_pathAlloc (hqc : Computable fun p : ℕ × BitString => q p.1 p.2) :
    Computable (fun p : ℕ × BitString => pathAlloc q p.1 p.2) := by
  have hbase : Computable (fun p : ℕ × BitString =>
      ((([[]], []) : PathEntry) :: List.replicate p.2.length (([], []) : PathEntry))) :=
    (Primrec.list_cons.comp (Primrec.const _)
      (Primrec.list_replicate.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.const _))).to_comp
  refine (Computable.nat_rec Computable.fst hbase (computable_pathAllocStep hqc).to₂).of_eq ?_
  rintro ⟨s, x⟩
  induction s with
  | zero => rfl
  | succ s ih =>
    change pathAllocStep q s x _ = pathAlloc q (s + 1) x
    rw [ih]
    rfl

/-- The atoms allocated to a node at a stage are computable. -/
theorem computable_pathAtoms (hqc : Computable fun p : ℕ × BitString => q p.1 p.2) :
    Computable (fun p : ℕ × BitString => pathAtoms q p.1 p.2) := by
  have hgl : Primrec (fun l : List PathEntry => l.getLast?) :=
    (Primrec.list_head?.comp Primrec.list_reverse).of_eq (fun _ => List.head?_reverse)
  have hext : Primrec (fun l : List PathEntry => ((l.getLast?).map Prod.fst).getD []) :=
    Primrec.option_getD.comp (Primrec.option_map hgl (Primrec.fst.comp Primrec.snd).to₂)
      (Primrec.const [])
  exact (hext.to_comp.comp (computable_pathAlloc hqc)).of_eq (fun _ => rfl)

/-- **Computability leaf.** Membership in the extracted allocation is computable, provided the
numerator family `q` is.

The computability hypothesis on `q` cannot be dropped: `pathAtoms q 1 [false]` already consists of
the first `q 1 [false]` strings of length one, so an arbitrary `q` yields uncountably many distinct
membership functions.  The hypothesis is exactly the last clause of `IsSimpleTreeApproximation`, so
`exists_effectiveNestedTreeAllocation` supplies it and nothing downstream is weakened. -/
theorem computable_mem_pathAtoms (hqc : Computable fun p : ℕ × BitString => q p.1 p.2) :
    Computable fun z : (ℕ × BitString) × BitString => decide (z.2 ∈ pathAtoms q z.1.1 z.1.2) := by
  refine (mem_decide_primrec.to_comp.comp ((computable_pathAtoms hqc).comp Computable.fst)
    Computable.snd).of_eq (fun _ => ?_)
  exact Bool.eq_iff_iff.mpr (by simp)

end Computability

/-- Every simple tree approximation is realised by a computable nested tree allocation. -/
theorem exists_effectiveNestedTreeAllocation {a : BitString → ENNReal} {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation a q) :
    Nonempty (EffectiveNestedTreeAllocation q) := by
  refine ⟨{ stage := canonicalStage hq, refines := ?_, mem_computable := ?_ }⟩
  · -- refinement across stages is exactly `extend_refines`
    intro s x p hp
    dsimp [canonicalStage]
    apply TreeAllocation.extend_refines
    exact hp
  · -- membership is computable, transported along the structural leaf `pathAtoms_eq`
    refine (computable_mem_pathAtoms (q := q) hq.2.2.2.2.2).of_eq (fun z => ?_)
    rw [pathAtoms_eq hq z.1.1 z.1.2]

end Kolmogorov
