import KolmogorovMathlib.MonotoneComplexity.GacsDayGame

/-!
# Passing to a subtree of the Gacs-Day game

The Gacs-Day construction repeatedly restricts attention to the game played
below a fixed son `i` of the current node.  This file provides the corresponding
syntactic operation on the association lists that encode moves,
`restrictSubtreeAssoc i`, together with its two instances:

* `extractSubtreeServerMove i sm`, whose allocation at a node `x` is the
  allocation of `sm` at `i :: x`;
* `restrictSubtreeClientMove i req`, whose request at a node `x` is the request
  of `req` at `i :: x`.

The main results are that these operations preserve legality of a server play
(`serverPlayLegal_extractSubtree`) and coherence of a client request
(`requestCoherent_restrictSubtreeClientMove`).
-/

namespace Kolmogorov

/-! ### The generic restriction of an association list -/

/-- Restrict an association list indexed by game nodes to the subtree below the
son `i`: keep exactly the entries whose node lies below `i`, and strip the
leading `i`. -/
def restrictSubtreeAssoc {β : Type} (i : ℕ) (l : List (GacsDayNode × β)) :
    List (GacsDayNode × β) :=
  l.filterMap fun p =>
    match p.1 with
    | [] => none
    | j :: rest => if j = i then some (rest, p.2) else none

/-- Restricting the empty association list to a subtree leaves it empty. -/
@[simp] lemma restrictSubtreeAssoc_nil {β : Type} (i : ℕ) :
    restrictSubtreeAssoc i ([] : List (GacsDayNode × β)) = [] := rfl

/-- Looking a node up in the subtree of `i` is looking `i :: x` up in the original list. -/
lemma lookup_restrictSubtreeAssoc {β : Type} (i : ℕ) (l : List (GacsDayNode × β))
    (x : GacsDayNode) :
    (restrictSubtreeAssoc i l).lookup x = l.lookup (i :: x) := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨n, a⟩ := p
    match n with
    | [] => simpa [restrictSubtreeAssoc, List.lookup] using ih
    | j :: rest =>
      by_cases hj : j = i
      · subst hj
        by_cases hx : x = rest
        · subst hx; simp [restrictSubtreeAssoc, List.lookup]
        · have h1 : (x == rest) = false := by simpa using hx
          have h2 : ((j :: x) == (j :: rest)) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq, List.cons.injEq, not_and]
            exact fun _ => hx
          simpa [restrictSubtreeAssoc, List.lookup, h1, h2] using ih
      · have h2 : ((i :: x) == (j :: rest)) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq, List.cons.injEq, not_and]
          intro h
          exact absurd h.symm hj
        simpa [restrictSubtreeAssoc, List.lookup, hj, h2] using ih

/-! ### Server moves -/

/-- The server move seen from the son `i`. -/
def extractSubtreeServerMove (i : ℕ) (sm : ServerMove) : ServerMove :=
  restrictSubtreeAssoc i sm

/-- The subtree of the empty server move is empty. -/
@[simp] lemma extractSubtreeServerMove_nil (i : ℕ) :
    extractSubtreeServerMove i [] = [] := rfl

/-- Allocations of the extracted subtree move are the allocations of the original
move one level down. -/
@[simp] lemma getAlloc_extractSubtreeServerMove (i : ℕ) (sm : ServerMove) (x : GacsDayNode) :
    getAlloc (extractSubtreeServerMove i sm) x = getAlloc sm (i :: x) := by
  simp [getAlloc, extractSubtreeServerMove, lookup_restrictSubtreeAssoc]

/-- Extracting a subtree preserves coherence of a single server move. -/
theorem serverMoveCoherent_extractSubtreeServerMove {b i : ℕ} {sm : ServerMove}
    (h : serverMoveCoherent b sm) :
    serverMoveCoherent b (extractSubtreeServerMove i sm) := by
  refine ⟨?_, ?_⟩
  · intro x c
    have := h.1 (i :: x) c
    simpa using this
  · intro x c1 c2 hne
    have := h.2 (i :: x) c1 c2 hne
    simpa using this

/-- Extracting a subtree preserves legality of a server play. -/
theorem serverPlayLegal_extractSubtree {b i : ℕ} {sms : ℕ → ServerMove}
    (h : serverPlayLegal b sms) :
    serverPlayLegal b (fun t => extractSubtreeServerMove i (sms t)) := by
  refine ⟨fun t => serverMoveCoherent_extractSubtreeServerMove (h.1 t), ?_⟩
  intro t x
  have := h.2 t (i :: x)
  simpa using this

/-! ### Client moves -/

/-- The client move seen from the son `i`. -/
def restrictSubtreeClientMove (i : ℕ) (req : ClientMove) : ClientMove :=
  restrictSubtreeAssoc i req

/-- The subtree of the empty client move is empty. -/
@[simp] lemma restrictSubtreeClientMove_nil (i : ℕ) :
    restrictSubtreeClientMove i [] = [] := rfl

/-- The restricted client move requests at `x` what the original requests at `i :: x`. -/
@[simp] lemma getReq_restrictSubtreeClientMove (i : ℕ) (req : ClientMove) (x : GacsDayNode) :
    getReq (restrictSubtreeClientMove i req) x = getReq req (i :: x) := by
  simp [getReq, restrictSubtreeClientMove, lookup_restrictSubtreeAssoc]

/-- A son's request never exceeds the request at the root. -/
lemma getReq_son_le_root {b d i : ℕ} {req : ClientMove} (hi : i < b)
    (h : requestCoherent b d req) :
    getReq req [i] ≤ getReq req [] := by
  refine le_trans ?_ (h.2.2 [])
  have hmem : (⟨i, hi⟩ : Fin b) ∈ (Finset.univ : Finset (Fin b)) := Finset.mem_univ _
  refine Finset.single_le_sum (f := fun c : Fin b => getReq req ([] ++ [c.val]))
    (fun c _ => h.1 _) hmem

/-- Restricting a coherent client request to the subtree below a son `i < b`
again yields a coherent client request, with the same branching bound and the
same root cap. -/
theorem requestCoherent_restrictSubtreeClientMove {b d i : ℕ} {req : ClientMove}
    (hi : i < b) (h : requestCoherent b d req) :
    requestCoherent b d (restrictSubtreeClientMove i req) := by
  refine ⟨fun x => by simpa using h.1 (i :: x), ?_, ?_⟩
  · simp only [getReq_restrictSubtreeClientMove]
    exact le_trans (getReq_son_le_root hi h) h.2.1
  · intro x
    have := h.2.2 (i :: x)
    simpa using this

/-- Restricting a legal client play to the subtree below a son `i < b` again
yields a legal client play. -/
theorem clientPlayLegal_restrictSubtree {b d i : ℕ} {cms : ℕ → ClientMove}
    (hi : i < b) (h : clientPlayLegal b d cms) :
    clientPlayLegal b d (fun t => restrictSubtreeClientMove i (cms t)) := by
  refine ⟨fun t => requestCoherent_restrictSubtreeClientMove hi (h.1 t), ?_⟩
  intro t x
  have := h.2 t (i :: x)
  simpa using this

/-! ### Grafting subtrees together

The inverse operation: given a root value and one move per son, assemble the
move on the whole tree. -/

/-- Place an association list one level deeper, below the son `i`. -/
def liftSubtreeAssoc {β : Type} (i : ℕ) (l : List (GacsDayNode × β)) :
    List (GacsDayNode × β) :=
  l.map fun p => (i :: p.1, p.2)

/-- Lifting a list into the subtree of `i` and looking up `i :: x` recovers the original entry. -/
lemma lookup_liftSubtreeAssoc_self {β : Type} (i : ℕ) (l : List (GacsDayNode × β))
    (x : GacsDayNode) :
    (liftSubtreeAssoc i l).lookup (i :: x) = l.lookup x := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨n, a⟩ := p
    by_cases hx : x = n
    · subst hx; simp [liftSubtreeAssoc, List.lookup]
    · have h1 : (x == n) = false := by simpa using hx
      have h2 : ((i :: x) == (i :: n)) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq, List.cons.injEq, not_and]
        exact fun _ => hx
      simpa [liftSubtreeAssoc, List.lookup, h1, h2] using ih

/-- A list lifted into the subtree of `i` has no entry below any other child. -/
lemma lookup_liftSubtreeAssoc_of_ne {β : Type} {i j : ℕ} (hj : j ≠ i)
    (l : List (GacsDayNode × β)) (x : GacsDayNode) :
    (liftSubtreeAssoc i l).lookup (j :: x) = none := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨n, a⟩ := p
    have h2 : ((j :: x) == (i :: n)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, List.cons.injEq, not_and]
      exact fun h => absurd h hj
    simpa [liftSubtreeAssoc, List.lookup, h2] using ih

/-- A list lifted into a subtree has no entry at the root. -/
lemma lookup_liftSubtreeAssoc_root {β : Type} (i : ℕ) (l : List (GacsDayNode × β)) :
    (liftSubtreeAssoc i l).lookup [] = none := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨n, a⟩ := p
    have h2 : (([] : GacsDayNode) == (i :: n)) = false := by simp
    simpa [liftSubtreeAssoc, List.lookup, h2] using ih

/-- Assemble the moves of the sons `0, …, n - 1` into a single move on the tree
(the root itself carries no entry). -/
def graftSubtreeAssoc {β : Type} :
    ℕ → (ℕ → List (GacsDayNode × β)) → List (GacsDayNode × β)
  | 0, _ => []
  | n + 1, f => liftSubtreeAssoc n (f n) ++ graftSubtreeAssoc n f

/-- A grafted list has no entry at the root. -/
lemma lookup_graftSubtreeAssoc_root {β : Type} (n : ℕ) (f : ℕ → List (GacsDayNode × β)) :
    (graftSubtreeAssoc n f).lookup [] = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [graftSubtreeAssoc, List.lookup_append, lookup_liftSubtreeAssoc_root, ih]
    rfl

/-- A graft over the first `n` children has no entry below a child of index `n` or more. -/
lemma lookup_graftSubtreeAssoc_of_ge {β : Type} {n i : ℕ} (h : n ≤ i)
    (f : ℕ → List (GacsDayNode × β)) (x : GacsDayNode) :
    (graftSubtreeAssoc n f).lookup (i :: x) = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [graftSubtreeAssoc, List.lookup_append,
      lookup_liftSubtreeAssoc_of_ne (by omega) (f n) x, ih (by omega)]
    rfl

/-- Below the child `i`, a graft reproduces the grafted list `f i`. -/
lemma lookup_graftSubtreeAssoc_of_lt {β : Type} {n i : ℕ} (h : i < n)
    (f : ℕ → List (GacsDayNode × β)) (x : GacsDayNode) :
    (graftSubtreeAssoc n f).lookup (i :: x) = (f i).lookup x := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · rw [graftSubtreeAssoc, List.lookup_append,
        lookup_liftSubtreeAssoc_of_ne (by omega) (f n) x, ih hlt]
      rfl
    · subst heq
      rw [graftSubtreeAssoc, List.lookup_append, lookup_liftSubtreeAssoc_self]
      cases hlook : (f i).lookup x with
      | some v => rfl
      | none => simpa using lookup_graftSubtreeAssoc_of_ge (le_refl i) f x

/-- The client move that requests `root` at the root and follows `f i` below the
son `i`, for every `i < b`. -/
def graftClientMove (root : ℚ) (b : ℕ) (f : ℕ → ClientMove) : ClientMove :=
  ([], root) :: graftSubtreeAssoc b f

/-- A grafted client move requests `root` at the root. -/
@[simp] lemma getReq_graftClientMove_root (root : ℚ) (b : ℕ) (f : ℕ → ClientMove) :
    getReq (graftClientMove root b f) [] = root := by
  simp [getReq, graftClientMove]

/-- Below a child inside the branching, a grafted client move reproduces the grafted move. -/
@[simp] lemma getReq_graftClientMove_of_lt {root : ℚ} {b i : ℕ} (h : i < b)
    (f : ℕ → ClientMove) (x : GacsDayNode) :
    getReq (graftClientMove root b f) (i :: x) = getReq (f i) x := by
  have hb : ((i :: x) == ([] : GacsDayNode)) = false := by simp
  simp only [getReq, graftClientMove, List.lookup, hb,
    lookup_graftSubtreeAssoc_of_lt h]

/-- Below a child outside the branching, a grafted client move requests nothing. -/
@[simp] lemma getReq_graftClientMove_of_ge {root : ℚ} {b i : ℕ} (h : b ≤ i)
    (f : ℕ → ClientMove) (x : GacsDayNode) :
    getReq (graftClientMove root b f) (i :: x) = 0 := by
  have hb : ((i :: x) == ([] : GacsDayNode)) = false := by simp
  simp only [getReq, graftClientMove, List.lookup, hb,
    lookup_graftSubtreeAssoc_of_ge h]

/-- Restricting a grafted move to one of its sons recovers that son's move. -/
lemma getReq_restrictSubtree_graftClientMove {root : ℚ} {b i : ℕ} (h : i < b)
    (f : ℕ → ClientMove) (x : GacsDayNode) :
    getReq (restrictSubtreeClientMove i (graftClientMove root b f)) x = getReq (f i) x := by
  rw [getReq_restrictSubtreeClientMove, getReq_graftClientMove_of_lt h]

/-- **Composition of subtree requests.**  If each son `i < b` carries a
nonnegative request obeying the branching inequality, and the root value is a
nonnegative number that caps both `1 / d` and the total demand of the sons, then
the grafted move is a coherent client request. -/
theorem requestCoherent_graftClientMove {b d : ℕ} {root : ℚ} {f : ℕ → ClientMove}
    (hroot0 : 0 ≤ root) (hcap : root ≤ 1 / (d : ℚ))
    (hsum : ∑ c : Fin b, getReq (f c.val) [] ≤ root)
    (hpos : ∀ i < b, ∀ x, 0 ≤ getReq (f i) x)
    (hchild : ∀ i < b, ∀ x, getReq (f i) x ≥ ∑ c : Fin b, getReq (f i) (x ++ [c.val])) :
    requestCoherent b d (graftClientMove root b f) := by
  refine ⟨?_, by simpa using hcap, ?_⟩
  · intro x
    match x with
    | [] => simpa using hroot0
    | i :: y =>
      rcases lt_or_ge i b with hi | hi
      · rw [getReq_graftClientMove_of_lt hi]
        exact hpos i hi y
      · rw [getReq_graftClientMove_of_ge hi]
  · intro x
    match x with
    | [] =>
      refine le_trans (le_of_eq ?_) (le_trans hsum (le_of_eq (by simp)))
      refine Finset.sum_congr rfl fun c _ => ?_
      simp
    | i :: y =>
      have hkey : ∀ c : ℕ, (i :: y) ++ [c] = i :: (y ++ [c]) := fun c => rfl
      rcases lt_or_ge i b with hi | hi
      · rw [getReq_graftClientMove_of_lt hi]
        refine le_trans (le_of_eq ?_) (hchild i hi y)
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hkey c.val, getReq_graftClientMove_of_lt hi]
      · rw [getReq_graftClientMove_of_ge hi]
        refine le_of_eq (Finset.sum_eq_zero fun c _ => ?_)
        rw [hkey c.val, getReq_graftClientMove_of_ge hi]

end Kolmogorov
