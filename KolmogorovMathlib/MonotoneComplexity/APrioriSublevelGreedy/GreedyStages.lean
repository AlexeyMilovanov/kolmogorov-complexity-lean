import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelMaxNodes
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.MonotoneComplexity.ContinuousStreamMap
import KolmogorovMathlib.MonotoneComplexity.NestedAllocation
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelGreedy.AddressState

/-!
# Greedy address assignment on the a priori sublevel trees

The stagewise construction that gives every node of the `k`-th a priori sublevel tree an address
of length `k`, assigned greedily as the tree is enumerated. `greedyInv` is the invariant a state
must satisfy; it survives the insertion of a node whose proper prefixes are already addressed
(`greedyInv_insertNode`), of a whole branch (`greedyInv_insertBranch`) and of a list of branches,
with the corresponding membership statements for the addressed nodes.

### Outline

* the stages of the construction, the hypotheses their test must satisfy, and monotonicity in
  the stage;
* primitive recursiveness of the whole construction and computability of the stages;
* the induced stream lower graph, ending in `greedyRel_isRE`, `greedyRel_covers`,
  `exists_sublevelCheck` and `exists_kaSublevel_addressRelation`: the sublevel trees admit a
  uniformly enumerable family of address relations.
-/

namespace Kolmogorov

/-- One greedy step preserves the invariant, provided every proper prefix of the new node has
already been recorded. -/
theorem greedyInv_insertNode {k : ℕ} {R : AddrList} (h : GreedyInv k R) {x : BitString}
    (hx : x ∈ kaSublevel k)
    (hpre : ∀ z, z <+: x → z ≠ x → z ∈ addrNodesFinset R) :
    GreedyInv k (insertNode k R x) := by
  unfold insertNode
  cases h1 : (decide (x = []) || decide (x ∈ addrNodes R)) with
  | true => simpa using h
  | false =>
    have hxne : x ≠ [] := by intro hh; simp [hh] at h1
    have hxnot : x ∉ addrNodes R := by intro hh; simp [hh] at h1
    have hpos : 0 < x.length := List.length_pos_iff.mpr hxne
    cases h2 : (!decide (x.dropLast = []) && isLeafIn R x.dropLast) with
    | true =>
      simp only [cond_false, cond_true]
      rw [Bool.and_eq_true] at h2
      have hdne : x.dropLast ≠ [] := by simpa using h2.1
      have hdne' : x.dropLast ≠ x := by
        intro hh
        have hl := congrArg List.length hh
        rw [List.length_dropLast] at hl
        omega
      have hdmem : ∃ p, (p, x.dropLast) ∈ R := by
        rcases mem_addrNodesFinset.mp (hpre _ (List.dropLast_prefix x) hdne') with hh | hh
        · exact absurd hh hdne
        · exact hh
      exact greedyInv_cons_reuse h hxne hxnot hx (headD_addrsAt_mem hdmem) h2.2
    | false =>
      simp only [cond_false]
      refine greedyInv_freshStep h hxne hxnot hx hpre ?_
      rcases Bool.and_eq_false_iff.mp h2 with hh | hh
      · exact Or.inl (by simpa using hh)
      · exact Or.inr hh

/-- Folding the greedy step along the initial segments of `x` preserves the invariant and records
every short enough nonempty prefix of `x`. -/
theorem greedyInv_takeFold {k : ℕ} {R : AddrList} (h : GreedyInv k R) {x : BitString}
    (hx : x ∈ kaSublevel k) (n : ℕ) :
    GreedyInv k (((List.range n).map (fun i => x.take (i + 1))).foldl (insertNode k) R) ∧
      ∀ z, z <+: x → z ≠ [] → z.length ≤ n →
        z ∈ addrNodes (((List.range n).map (fun i => x.take (i + 1))).foldl (insertNode k) R) := by
  induction n with
  | zero =>
    refine ⟨by simpa using h, ?_⟩
    intro z _ hne hlen
    exact absurd (List.length_pos_iff.mpr hne) (by omega)
  | succ n ih =>
    obtain ⟨hinv, hmem⟩ := ih
    set P := ((List.range n).map (fun i => x.take (i + 1))).foldl (insertNode k) R with hP
    have hstep : ((List.range (n + 1)).map (fun i => x.take (i + 1))).foldl (insertNode k) R
        = insertNode k P (x.take (n + 1)) := by
      rw [List.range_succ, List.map_append, List.foldl_append]
      simp [hP]
    rw [hstep]
    have hxk : x.take (n + 1) ∈ kaSublevel k :=
      kaSublevel_prefixClosed (List.take_prefix _ _) hx
    have hpre : ∀ z, z <+: x.take (n + 1) → z ≠ x.take (n + 1) → z ∈ addrNodesFinset P := by
      intro z hz hne
      by_cases hnil : z = []
      · exact mem_addrNodesFinset.mpr (Or.inl hnil)
      · have hzx : z <+: x := hz.trans (List.take_prefix _ _)
        have hlt : z.length < (x.take (n + 1)).length :=
          lt_of_le_of_ne hz.length_le (fun hh => hne (hz.eq_of_length hh))
        have hle : (x.take (n + 1)).length ≤ n + 1 := by simp
        obtain ⟨p, hp⟩ := mem_addrNodes.mp (hmem z hzx hnil (by omega))
        exact mem_addrNodesFinset.mpr (Or.inr ⟨p, hp⟩)
    refine ⟨greedyInv_insertNode hinv hxk hpre, ?_⟩
    intro z hz hne hlen
    rcases Nat.lt_or_ge z.length (n + 1) with hlt | hge
    · obtain ⟨p, hp⟩ := mem_addrNodes.mp (hmem z hz hne (by omega))
      exact mem_addrNodes.mpr ⟨p, insertNode_subset k P _ hp⟩
    · have hzlen : z.length = n + 1 := le_antisymm hlen hge
      have hzeq : z = x.take (n + 1) := by
        rw [← hzlen]; exact List.prefix_iff_eq_take.mp hz
      rw [← hzeq]
      exact mem_addrNodes_insertNode k P (by rw [← hzeq] at *; exact hne)

/-- Recording a branch of the sublevel tree preserves the greedy invariant. -/
theorem greedyInv_insertBranch {k : ℕ} {R : AddrList} (h : GreedyInv k R) {x : BitString}
    (hx : x ∈ kaSublevel k) : GreedyInv k (insertBranch k R x) :=
  (greedyInv_takeFold h hx x.length).1

/-- Recording the branch of a nonempty sublevel node makes that node a node of the state. -/
theorem mem_addrNodes_insertBranch {k : ℕ} {R : AddrList} (h : GreedyInv k R) {x : BitString}
    (hx : x ∈ kaSublevel k) (hne : x ≠ []) : x ∈ addrNodes (insertBranch k R x) :=
  (greedyInv_takeFold h hx x.length).2 x (List.prefix_refl _) hne le_rfl

/-- Recording a list of sublevel branches preserves the greedy invariant. -/
theorem greedyInv_foldl_insertBranch {k : ℕ} (xs : List BitString) :
    ∀ {R : AddrList}, GreedyInv k R → (∀ x ∈ xs, x ∈ kaSublevel k) →
      GreedyInv k (xs.foldl (insertBranch k) R) := by
  induction xs with
  | nil => intro R h _; exact h
  | cons a t ih =>
    intro R h hxs
    exact ih (greedyInv_insertBranch h (hxs a (List.mem_cons_self ..)))
      (fun x hx => hxs x (List.mem_cons_of_mem _ hx))

/-- Every nonempty node of a recorded list of sublevel branches is a node of the resulting state. -/
theorem mem_addrNodes_foldl_insertBranch {k : ℕ} (xs : List BitString) :
    ∀ {R : AddrList}, GreedyInv k R → (∀ x ∈ xs, x ∈ kaSublevel k) →
      ∀ {x : BitString}, x ∈ xs → x ≠ [] → x ∈ addrNodes (xs.foldl (insertBranch k) R) := by
  induction xs with
  | nil => intro R _ _ x hx; exact absurd hx List.not_mem_nil
  | cons a t ih =>
    intro R h hxs x hx hne
    have ha : a ∈ kaSublevel k := hxs a (List.mem_cons_self ..)
    rcases List.mem_cons.mp hx with rfl | hx'
    · obtain ⟨p, hp⟩ := mem_addrNodes.mp (mem_addrNodes_insertBranch h ha hne)
      exact mem_addrNodes.mpr ⟨p, foldl_insertBranch_subset k t _ hp⟩
    · exact ih (greedyInv_insertBranch h ha)
        (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) hx' hne

/-! ## Stages -/

section Stages

variable (chk : ℕ → BitString → ℕ → Bool)

/-- `x` has been enumerated into `kaSublevel k` by stage `s`: some string of length at most `s`
extending `x` has passed the stage-`s` test. -/
def inStageB (k s : ℕ) (x : BitString) : Bool :=
  (boundedPrograms s).any (fun z => isPrefixB x z && chk k z s)

/-- The nodes available at stage `s`, shortest first. -/
def stageNodes (k s : ℕ) : List BitString :=
  (boundedPrograms s).filter (inStageB chk k s)

/-- The greedy state after `s` stages. -/
def greedyStage (k : ℕ) : ℕ → AddrList
  | 0 => []
  | s + 1 => (stageNodes chk k (s + 1)).foldl (insertBranch k) (greedyStage k s)

/-- The address relation produced by the construction. -/
def greedyRel (k : ℕ) (p x : BitString) : Prop :=
  x = [] ∨ (k ≤ p.length ∧ ∃ s, (p.take k, x) ∈ greedyStage chk k s)

end Stages

/-! ## Hypotheses on the stage test -/

/-- The properties of the stage test used by the construction. -/
structure IsSublevelCheck (chk : ℕ → BitString → ℕ → Bool) : Prop where
  /-- Monotone in the stage. -/
  mono : ∀ k x s t, s ≤ t → chk k x s = true → chk k x t = true
  /-- Sound and complete for the sublevel tree. -/
  spec : ∀ k x, x ∈ kaSublevel k ↔ ∃ s, chk k x s = true

variable {chk : ℕ → BitString → ℕ → Bool}

/-- Anything that passes the stage test lies in the sublevel tree. -/
theorem inStageB_mem (h : IsSublevelCheck chk) {k s : ℕ} {x : BitString}
    (hx : inStageB chk k s x = true) : x ∈ kaSublevel k := by
  unfold inStageB at hx
  rw [List.any_eq_true] at hx
  obtain ⟨z, _, hcond⟩ := hx
  rw [Bool.and_eq_true] at hcond
  exact kaSublevel_prefixClosed (isPrefixB_iff.mp hcond.1) ((h.spec k z).mpr ⟨s, hcond.2⟩)

/-- The nodes available at a stage lie in the sublevel tree. -/
theorem stageNodes_mem (h : IsSublevelCheck chk) {k s : ℕ} {x : BitString}
    (hx : x ∈ stageNodes chk k s) : x ∈ kaSublevel k :=
  inStageB_mem h (List.mem_filter.mp hx).2

/-- Every stage of the greedy construction satisfies the invariant. -/
theorem greedyInv_greedyStage (h : IsSublevelCheck chk) (k s : ℕ) :
    GreedyInv k (greedyStage chk k s) := by
  induction s with
  | zero =>
    refine ⟨fun p x hm => absurd hm List.not_mem_nil, fun p x hm => absurd hm List.not_mem_nil,
      fun p x hm => absurd hm List.not_mem_nil,
      fun p x z hm _ _ => absurd hm List.not_mem_nil,
      fun p x y hm _ => absurd hm List.not_mem_nil, ?_⟩
    simp [greedyStage, addrUsed]
  | succ s ih =>
    change GreedyInv k ((stageNodes chk k (s + 1)).foldl (insertBranch k) (greedyStage chk k s))
    exact greedyInv_foldl_insertBranch _ ih (fun x hx => stageNodes_mem h hx)

/-! ## Monotonicity in the stage -/

/-- The greedy state only grows with the stage. -/
theorem greedyStage_mono (k : ℕ) {s t : ℕ} (hst : s ≤ t) {q : BitString × BitString}
    (hq : q ∈ greedyStage chk k s) : q ∈ greedyStage chk k t := by
  induction t with
  | zero => simpa [Nat.le_zero.mp hst] using hq
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with hlt | hge
    · exact foldl_insertBranch_subset k _ _ (ih (Nat.lt_succ_iff.mp hlt))
    · have hs : s = t + 1 := le_antisymm hst hge
      subst hs
      exact hq

/-- Every nonempty node of the sublevel tree eventually receives an address of length `k`. -/
theorem greedyStage_covers (h : IsSublevelCheck chk) {k : ℕ} {x : BitString}
    (hx : x ∈ kaSublevel k) (hne : x ≠ []) :
    ∃ s p, p.length = k ∧ (p, x) ∈ greedyStage chk k s := by
  obtain ⟨s0, hs0⟩ := (h.spec k x).mp hx
  refine ⟨max s0 x.length + 1, ?_⟩
  set t := max s0 x.length with ht
  have hxb : x ∈ boundedPrograms (t + 1) :=
    (mem_boundedPrograms_iff x (t + 1)).mpr
      (le_trans (le_max_right s0 x.length) (Nat.le_succ t))
  have hchks : chk k x (t + 1) = true :=
    h.mono k x s0 (t + 1) (le_trans (le_max_left s0 x.length) (Nat.le_succ t)) hs0
  have hin : inStageB chk k (t + 1) x = true := by
    unfold inStageB
    rw [List.any_eq_true]
    exact ⟨x, hxb, by simp [isPrefixB_iff.mpr (List.prefix_refl x), hchks]⟩
  have hmemlist : x ∈ stageNodes chk k (t + 1) := List.mem_filter.mpr ⟨hxb, hin⟩
  have hnodes : x ∈ addrNodes (greedyStage chk k (t + 1)) := by
    change x ∈ addrNodes ((stageNodes chk k (t + 1)).foldl (insertBranch k) (greedyStage chk k t))
    exact mem_addrNodes_foldl_insertBranch _ (greedyInv_greedyStage h k t)
      (fun y hy => stageNodes_mem h hy) hmemlist hne
  obtain ⟨p, hp⟩ := mem_addrNodes.mp hnodes
  exact ⟨p, (greedyInv_greedyStage h k (t + 1)).len _ _ hp, hp⟩

/-! ## Computability: the construction is primitive recursive -/

/-- The node list of a state is primitive recursive. -/
theorem primrec_addrNodes : Primrec addrNodes :=
  Primrec.list_map Primrec.id (Primrec.snd.comp Primrec.snd).to₂

/-- The address list of a state is primitive recursive. -/
theorem primrec_addrUsed : Primrec addrUsed :=
  Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd).to₂

/-- The boolean prefix test is primitive recursive. -/
theorem primrec_isPrefixB : Primrec₂ isPrefixB := by
  have h : Primrec (fun w : BitString × BitString => decide (w.2.take w.1.length = w.1)) :=
    primrec_decideEq.comp
      (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd) Primrec.fst
  exact h.of_eq (fun w => Bool.eq_iff_iff.mpr (by simp [isPrefixB]))

/-- The addresses at a node are primitive recursive in the state and the node. -/
theorem primrec_addrsAt : Primrec₂ addrsAt := by
  have hfil : Primrec (fun w : AddrList × BitString =>
      w.1.filter (fun q => decide (q.2 = w.2))) :=
    list_filter_primrec Primrec.fst
      (primrec_decideEq.comp (Primrec.snd.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)).to₂
  exact Primrec.list_map hfil (Primrec.fst.comp Primrec.snd).to₂

/-- The leaf test is primitive recursive. -/
theorem primrec_isLeafIn : Primrec₂ isLeafIn := by
  have hany : Primrec (fun w : AddrList × BitString =>
      (addrNodes w.1).any (fun z => isPrefixB w.2 z && !decide (z = w.2))) := by
    refine list_any_primrec (primrec_addrNodes.comp Primrec.fst) ?_
    exact (Primrec.and.comp
      (primrec_isPrefixB.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.not.comp (primrec_decideEq.comp Primrec.snd
        (Primrec.snd.comp Primrec.fst)))).to₂
  refine (Primrec.not.comp hany).of_eq (fun w => ?_)
  have hfun : (fun z => isPrefixB w.2 z && !decide (z = w.2))
      = (fun z => isPrefixB w.2 z && !(z == w.2)) := by
    funext z
    congr 1
    exact congrArg Bool.not (Bool.eq_iff_iff.mpr (by simp))
  rw [isLeafIn, hfun]

/-- The fresh address is primitive recursive in the length and the state. -/
theorem primrec_freshAddr : Primrec₂ freshAddr := by
  have hE : Primrec (fun w : ℕ × AddrList => exactLengthPrograms w.1) :=
    primrec_exactLengthPrograms.comp Primrec.fst
  have hU : Primrec (fun w : ℕ × AddrList => addrUsed w.2) := primrec_addrUsed.comp Primrec.snd
  have hfil : Primrec (fun w : ℕ × AddrList =>
      (exactLengthPrograms w.1).filter (fun p => decide (p ∉ addrUsed w.2))) := by
    refine (list_filter_primrec hE (Primrec.not.comp
      (mem_decide_primrec.comp (hU.comp Primrec.fst) Primrec.snd)).to₂).of_eq (fun w => ?_)
    exact List.filter_congr (fun z _ => Bool.eq_iff_iff.mpr (by simp))
  have hdef : Primrec (fun w : ℕ × AddrList => List.replicate w.1 false) :=
    Primrec.list_replicate.comp Primrec.fst (Primrec.const false)
  refine (Primrec.option_getD.comp (Primrec.list_head?.comp hfil) hdef).of_eq (fun w => ?_)
  unfold freshAddr
  cases hl : ((exactLengthPrograms w.1).filter (fun p => decide (p ∉ addrUsed w.2))) with
  | nil => rfl
  | cons a t => rfl

/-- The branch of a node is primitive recursive. -/
theorem primrec_branchPrefixes : Primrec branchPrefixes :=
  Primrec.list_map (Primrec.list_range.comp Primrec.list_length)
    (Primrec.list_take.comp (Primrec.succ.comp Primrec.snd) Primrec.fst).to₂

/-- Recording a node is primitive recursive. -/
theorem primrec_insertNode :
    Primrec (fun w : ℕ × AddrList × BitString => insertNode w.1 w.2.1 w.2.2) := by
  have hk : Primrec (fun w : ℕ × AddrList × BitString => w.1) := Primrec.fst
  have hR : Primrec (fun w : ℕ × AddrList × BitString => w.2.1) := Primrec.fst.comp Primrec.snd
  have hx : Primrec (fun w : ℕ × AddrList × BitString => w.2.2) := Primrec.snd.comp Primrec.snd
  have hdl : Primrec (fun w : ℕ × AddrList × BitString => w.2.2.dropLast) := by
    refine (Primrec.list_take.comp
      (Primrec.nat_sub.comp (Primrec.list_length.comp hx) (Primrec.const 1)) hx).of_eq (fun w => ?_)
    exact List.dropLast_eq_take.symm
  have hmemA : Primrec (fun w : ℕ × AddrList × BitString =>
      decide (w.2.2 ∈ addrNodes w.2.1)) :=
    (mem_decide_primrec.comp (primrec_addrNodes.comp hR) hx).of_eq
      (fun w => Bool.eq_iff_iff.mpr (by simp))
  have hc1 : Primrec (fun w : ℕ × AddrList × BitString =>
      decide (w.2.2 = []) || decide (w.2.2 ∈ addrNodes w.2.1)) :=
    Primrec.or.comp (primrec_decideEq.comp hx (Primrec.const [])) hmemA
  have hc2 : Primrec (fun w : ℕ × AddrList × BitString =>
      !decide (w.2.2.dropLast = []) && isLeafIn w.2.1 w.2.2.dropLast) :=
    Primrec.and.comp (Primrec.not.comp (primrec_decideEq.comp hdl (Primrec.const [])))
      (primrec_isLeafIn.comp hR hdl)
  have hfresh : Primrec (fun w : ℕ × AddrList × BitString => freshAddr w.1 w.2.1) :=
    primrec_freshAddr.comp hk hR
  have ht2 : Primrec (fun w : ℕ × AddrList × BitString =>
      ((addrsAt w.2.1 w.2.2.dropLast).headD (freshAddr w.1 w.2.1), w.2.2) :: w.2.1) := by
    have hhd : Primrec (fun w : ℕ × AddrList × BitString =>
        (addrsAt w.2.1 w.2.2.dropLast).headD (freshAddr w.1 w.2.1)) := by
      refine (Primrec.option_getD.comp
        (Primrec.list_head?.comp (primrec_addrsAt.comp hR hdl)) hfresh).of_eq (fun w => ?_)
      cases hl : addrsAt w.2.1 w.2.2.dropLast with
      | nil => rfl
      | cons a t => rfl
    exact Primrec.list_cons.comp (Primrec.pair hhd hx) hR
  have ht3 : Primrec (fun w : ℕ × AddrList × BitString =>
      (branchPrefixes w.2.2).map (fun z => (freshAddr w.1 w.2.1, z)) ++ w.2.1) :=
    Primrec.list_append.comp
      (Primrec.list_map (primrec_branchPrefixes.comp hx)
        (Primrec.pair (hfresh.comp Primrec.fst) Primrec.snd).to₂) hR
  exact (Primrec.cond hc1 hR (Primrec.cond hc2 ht2 ht3)).of_eq (fun w => rfl)

/-- Recording a branch is primitive recursive. -/
theorem primrec_insertBranch :
    Primrec (fun w : ℕ × AddrList × BitString => insertBranch w.1 w.2.1 w.2.2) := by
  refine (Primrec.list_foldl
    (h := fun (w : ℕ × AddrList × BitString) (u : AddrList × BitString) =>
      insertNode w.1 u.1 u.2)
    (primrec_branchPrefixes.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp Primrec.snd) ?_).of_eq (fun w => rfl)
  exact (primrec_insertNode.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
    (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))).to₂

/-! ### The stages are computable -/

/-- The stage membership test of the sublevel enumeration is computable. -/
theorem computable_inStageB
    (hchk : Computable fun w : (ℕ × BitString) × ℕ => chk w.1.1 w.1.2 w.2) :
    Computable (fun w : ℕ × ℕ × BitString => inStageB chk w.1 w.2.1 w.2.2) := by
  have hf : Computable (fun w : ℕ × ℕ × BitString => boundedPrograms w.2.1) :=
    primrec_boundedPrograms.to_comp.comp (Computable.fst.comp Computable.snd)
  have hp : Computable₂ (fun (w : ℕ × ℕ × BitString) (z : BitString) =>
      isPrefixB w.2.2 z && chk w.1 z w.2.1) := by
    have h1 : Computable (fun v : (ℕ × ℕ × BitString) × BitString => isPrefixB v.1.2.2 v.2) :=
      primrec_isPrefixB.to_comp.comp
        (Computable.snd.comp (Computable.snd.comp Computable.fst)) Computable.snd
    have h2 : Computable (fun v : (ℕ × ℕ × BitString) × BitString =>
        (fun w : (ℕ × BitString) × ℕ => chk w.1.1 w.1.2 w.2) ((v.1.1, v.2), v.1.2.1)) :=
      hchk.comp (Computable.pair
        (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
        (Computable.fst.comp (Computable.snd.comp Computable.fst)))
    exact (Primrec.and.to_comp.comp h1 h2).to₂
  exact (computable_list_any hf hp).of_eq (fun w => rfl)

/-- The nodes available at a stage are computable. -/
theorem computable_stageNodes
    (hchk : Computable fun w : (ℕ × BitString) × ℕ => chk w.1.1 w.1.2 w.2) :
    Computable (fun w : ℕ × ℕ => stageNodes chk w.1 w.2) := by
  have hf : Computable (fun w : ℕ × ℕ => boundedPrograms w.2) :=
    primrec_boundedPrograms.to_comp.comp Computable.snd
  have hp : Computable₂ (fun (w : ℕ × ℕ) (z : BitString) => inStageB chk w.1 w.2 z) := by
    have h1 : Computable (fun v : (ℕ × ℕ) × BitString =>
        (fun w : ℕ × ℕ × BitString => inStageB chk w.1 w.2.1 w.2.2) (v.1.1, v.1.2, v.2)) :=
      (computable_inStageB hchk).comp (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd))
    exact h1.to₂
  exact (computable_list_filter hf hp).of_eq (fun w => rfl)

/-- The greedy state at a stage is computable. -/
theorem computable_greedyStage
    (hchk : Computable fun w : (ℕ × BitString) × ℕ => chk w.1.1 w.1.2 w.2) :
    Computable fun w : ℕ × ℕ => greedyStage chk w.1 w.2 := by
  have hstep : Computable₂ (fun (w : ℕ × ℕ) (u : ℕ × AddrList) =>
      (stageNodes chk w.1 (u.1 + 1)).foldl (insertBranch w.1) u.2) := by
    have hf : Computable (fun v : (ℕ × ℕ) × (ℕ × AddrList) =>
        (fun w : ℕ × ℕ => stageNodes chk w.1 w.2) (v.1.1, v.2.1 + 1)) :=
      (computable_stageNodes hchk).comp (Computable.pair
        (Computable.fst.comp Computable.fst)
        (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)))
    have hg : Computable (fun v : (ℕ × ℕ) × (ℕ × AddrList) => v.2.2) :=
      Computable.snd.comp Computable.snd
    have hh : Computable₂ (fun (v : (ℕ × ℕ) × (ℕ × AddrList)) (u : AddrList × BitString) =>
        insertBranch v.1.1 u.1 u.2) := by
      have h1 : Computable (fun r : ((ℕ × ℕ) × (ℕ × AddrList)) × (AddrList × BitString) =>
          (fun w : ℕ × AddrList × BitString => insertBranch w.1 w.2.1 w.2.2)
            (r.1.1.1, r.2.1, r.2.2)) :=
        primrec_insertBranch.to_comp.comp (Computable.pair
          (Computable.fst.comp (Computable.fst.comp Computable.fst))
          (Computable.pair (Computable.fst.comp Computable.snd)
            (Computable.snd.comp Computable.snd)))
      exact h1.to₂
    exact (computable_list_foldl hf hg hh).to₂
  refine (Computable.nat_rec Computable.snd (Computable.const []) hstep).of_eq ?_
  rintro ⟨k, s⟩
  induction s with
  | zero => rfl
  | succ s ih =>
    change (stageNodes chk k (s + 1)).foldl (insertBranch k) _ = greedyStage chk k (s + 1)
    rw [ih]
    rfl

/-! ## The stream lower graph -/

/-- The address relation produced by the greedy construction is the graph of a lower
semicomputable stream map. -/
theorem greedyRel_isStreamLowerGraph (h : IsSublevelCheck chk) (k : ℕ) :
    IsStreamLowerGraph (greedyRel chk k) := by
  refine ⟨fun p => Or.inl rfl, ?_, ?_, ?_⟩
  · intro p y y' hy hy'
    rcases hy with rfl | ⟨hk, s, hmem⟩
    · exact Or.inl (List.prefix_nil.mp hy')
    · by_cases hnil : y' = []
      · exact Or.inl hnil
      · exact Or.inr ⟨hk, s, (greedyInv_greedyStage h k s).lower _ _ _ hmem hy' hnil⟩
  · intro p p' y hy hpp'
    rcases hy with rfl | ⟨hk, s, hmem⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨le_trans hk hpp'.length_le, s, ?_⟩
      obtain ⟨t, rfl⟩ := hpp'
      rwa [List.take_append_of_le_length hk]
  · intro p y y' hy hy'
    rcases hy with rfl | ⟨hk, s, hmem⟩
    · exact Or.inl List.nil_prefix
    rcases hy' with rfl | ⟨hk', s', hmem'⟩
    · exact Or.inr List.nil_prefix
    · exact (greedyInv_greedyStage h k (max s s')).chain _ _ _
        (greedyStage_mono k (le_max_left s s') hmem)
        (greedyStage_mono k (le_max_right s s') hmem')

/-- Deciding `f a ≤ g a` is computable when `f` and `g` are. -/
theorem computable_decide_natLe {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable fun a => decide (f a ≤ g a) := by
  obtain ⟨dec, hp⟩ := (Primrec.nat_le : PrimrecRel (fun a b : ℕ => a ≤ b))
  refine (hp.to_comp.comp (Computable.pair hf hg)).of_eq (fun a => ?_)
  exact Bool.eq_iff_iff.mpr (by simp)

/-- Deciding `f a = g a` is computable when `f` and `g` are. -/
theorem computable_decide_eq {α β : Type*} [Primcodable α] [Primcodable β] [DecidableEq β]
    {f g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => decide (f a = g a) := by
  obtain ⟨dec, hp⟩ := (Primrec.eq : PrimrecRel (fun a b : β => a = b))
  refine (hp.to_comp.comp (Computable.pair hf hg)).of_eq (fun a => ?_)
  exact Bool.eq_iff_iff.mpr (by simp)

/-- The relation "the length-`k` prefix of `p` is an address of `x` at some stage" is
recursively enumerable as soon as the stages are computable. -/
theorem isRE_of_stageMembership {G : ℕ → ℕ → List (BitString × BitString)}
    (hG : Computable fun w : ℕ × ℕ => G w.1 w.2) :
    IsRE (fun q : ℕ × (BitString × BitString) =>
      q.2.2 = [] ∨ (q.1 ≤ q.2.1.length ∧ ∃ s, (q.2.1.take q.1, q.2.2) ∈ G q.1 s)) := by
  have h1 : Computable fun w : (ℕ × (BitString × BitString)) × ℕ =>
      (fun v : ℕ × ℕ => G v.1 v.2) (w.1.1, w.2) :=
    hG.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  have h2 : Computable fun w : (ℕ × (BitString × BitString)) × ℕ =>
      ((w.1.2.1.take w.1.1 : BitString), w.1.2.2) :=
    Computable.pair
      (Primrec.list_take.to_comp.comp (Computable.fst.comp Computable.fst)
        (Computable.fst.comp (Computable.snd.comp Computable.fst)))
      (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hmem : Computable fun w : (ℕ × (BitString × BitString)) × ℕ =>
      decide ((w.1.2.1.take w.1.1, w.1.2.2) ∈ G w.1.1 w.2) := by
    refine (mem_decide_primrec.to_comp.comp h1 h2).of_eq (fun w => ?_)
    exact Bool.eq_iff_iff.mpr (by simp)
  have hex : IsRE (fun q : ℕ × (BitString × BitString) =>
      ∃ s, (q.2.1.take q.1, q.2.2) ∈ G q.1 s) :=
    IsRE.exists_encodable (isRE_of_computable_bool _ _ (fun w => by simp) hmem)
  have hand : IsRE (fun q : ℕ × (BitString × BitString) =>
      decide (q.1 ≤ q.2.1.length) = true ∧
      ∃ s, (q.2.1.take q.1, q.2.2) ∈ G q.1 s) :=
    hex.and_computable (computable_decide_natLe Computable.fst
      (Primrec.list_length.to_comp.comp (Computable.fst.comp Computable.snd)))
  have hnil : IsRE (fun q : ℕ × (BitString × BitString) => q.2.2 = []) :=
    isRE_of_computable_bool _ (fun q => decide (q.2.2 = [])) (fun q => by simp)
      (computable_decide_eq (Computable.snd.comp Computable.snd) (Computable.const []))
  refine (hnil.or hand).of_iff (fun q => ?_)
  simp

/-- The address relation is recursively enumerable. -/
theorem greedyRel_isRE
    (hchk : Computable fun w : (ℕ × BitString) × ℕ => chk w.1.1 w.1.2 w.2) :
    IsRE (fun q : ℕ × (BitString × BitString) => greedyRel chk q.1 q.2.1 q.2.2) :=
  isRE_of_stageMembership (computable_greedyStage hchk)

/-- Every node of the sublevel tree receives an address of length `k` in the relation. -/
theorem greedyRel_covers (h : IsSublevelCheck chk) (k : ℕ) (x : BitString)
    (hx : x ∈ kaSublevel k) : ∃ p, p.length = k ∧ greedyRel chk k p x := by
  by_cases hnil : x = []
  · exact ⟨List.replicate k false, by simp, Or.inl hnil⟩
  · obtain ⟨s, p, hlen, hmem⟩ := greedyStage_covers h hx hnil
    exact ⟨p, hlen, Or.inr ⟨hlen.ge, s, by rwa [List.take_of_length_le hlen.le]⟩⟩

/-- There is a computable stage test for membership in the a priori sublevel trees. -/
theorem exists_sublevelCheck :
    ∃ chk : ℕ → BitString → ℕ → Bool, IsSublevelCheck chk ∧
      Computable fun w : (ℕ × BitString) × ℕ => chk w.1.1 w.1.2 w.2 := by
  obtain ⟨chk0, hcomp, hmono, hspec⟩ := IsRE.exists_stageApprox kaSublevel_isRE
  refine ⟨fun k x s => chk0 (x, k) s, ⟨fun k x s t hst hs => hmono (x, k) s t hst hs,
    fun k x => hspec (x, k)⟩, ?_⟩
  exact hcomp.comp (Computable.pair (Computable.snd.comp Computable.fst)
    (Computable.fst.comp Computable.fst)) Computable.snd

/-- The a priori sublevel trees admit a uniformly enumerable family of address relations:
for every `k` the relation `Rel k` is a stream lower graph, and every element of `kaSublevel k`
has an address of length exactly `k`. -/
theorem exists_kaSublevel_addressRelation :
    ∃ Rel : ℕ → BitString → BitString → Prop,
      (∀ k, IsStreamLowerGraph (Rel k)) ∧
      IsRE (fun q : ℕ × (BitString × BitString) => Rel q.1 q.2.1 q.2.2) ∧
      ∀ k x, x ∈ kaSublevel k → ∃ p, p.length = k ∧ Rel k p x := by
  obtain ⟨chk, h, hcomp⟩ := exists_sublevelCheck
  exact ⟨greedyRel chk, greedyRel_isStreamLowerGraph h, greedyRel_isRE hcomp,
    greedyRel_covers h⟩

end Kolmogorov
