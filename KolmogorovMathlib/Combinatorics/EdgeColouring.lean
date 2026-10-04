/-
Copyright (c) 2025 The Kolmogorov Project Developers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Kolmogorov Project Developers
-/
import KolmogorovMathlib.Combinatorics.Bipartite

/-!
# Proper edge colouring of a bipartite graph (König)

A finite bipartite graph whose vertices all have degree at most `N` can be edge-coloured with
`N` colours so that edges sharing an endpoint get different colours.  This is the off-line
statement of SUV Problem 321; the on-line colouring used in the proof of Theorem 232 needs
`2^{k+1}` colours instead, because the graph there is revealed edge by edge.

The proof colours the edges one at a time.  When a new edge `(l, r)` arrives, some colour `a`
is missing at `l` and some colour `b` is missing at `r` (the degrees are below `N`).  If `a`
is also missing at `r` the edge gets `a`; otherwise the colours `a` and `b` are exchanged
along the Kempe chain of `r` — the alternating `a`/`b`-path starting at `r` — which cannot
pass through `l` because every left vertex on it is entered along an `a`-edge, and then `a` is
free at both ends.  The chain is handled as a reachability predicate rather than as a path, so
that no path combinatorics is needed.

SUV Problem 321, p. 378.
-/

namespace Kolmogorov

variable {L R : Type*} [DecidableEq L] [DecidableEq R]

/-- A colouring of the edges of `g` — a function on the edges themselves — is proper when two
distinct edges with a common endpoint get different colours.

SUV Problem 321, p. 378. -/
def IsProperEdgeColouring (g : Finset (L × R)) {κ : Type*} (col : g → κ) : Prop :=
  ∀ e e' : g, e ≠ e' → (e.1.1 = e'.1.1 ∨ e.1.2 = e'.1.2) → col e ≠ col e'

/-! ### Total colourings

The induction works with a colouring defined on all of `L × R`, with natural-number colours,
required to be proper (and below `N`) only on the edges of `g`. -/

/-- A total colouring `c` is proper on `g`: distinct edges of `g` with a common endpoint get
different colours. -/
private def ProperOn (g : Finset (L × R)) (c : L × R → ℕ) : Prop :=
  ∀ e ∈ g, ∀ e' ∈ g, e ≠ e' → (e.1 = e'.1 ∨ e.2 = e'.2) → c e ≠ c e'

/-- The colour `a` is used by no edge of `g` at the left vertex `l`. -/
private def LeftFree (g : Finset (L × R)) (c : L × R → ℕ) (l : L) (a : ℕ) : Prop :=
  ∀ r, (l, r) ∈ g → c (l, r) ≠ a

/-- The colour `b` is used by no edge of `g` at the right vertex `r`. -/
private def RightFree (g : Finset (L × R)) (c : L × R → ℕ) (r : R) (b : ℕ) : Prop :=
  ∀ l, (l, r) ∈ g → c (l, r) ≠ b

omit [DecidableEq L] [DecidableEq R] in
private lemma properOn_eq_of_share {g : Finset (L × R)} {c : L × R → ℕ} (hc : ProperOn g c)
    {e e' : L × R} (he : e ∈ g) (he' : e' ∈ g) (hsh : e.1 = e'.1 ∨ e.2 = e'.2)
    (hcol : c e = c e') : e = e' := by
  by_contra hne
  exact hc e he e' he' hne hsh hcol

private lemma mem_neighbors_iff (g : Finset (L × R)) (l : L) (r : R) :
    r ∈ neighbors g l ↔ (l, r) ∈ g := by
  unfold neighbors
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨he, he1⟩ := Finset.mem_filter.1 he
    rwa [show (l, e.2) = e from Prod.ext he1.symm rfl]
  · intro h
    exact Finset.mem_image.2 ⟨(l, r), Finset.mem_filter.2 ⟨h, rfl⟩, rfl⟩

private lemma mem_rightNeighbors_iff (g : Finset (L × R)) (l : L) (r : R) :
    l ∈ rightNeighbors g r ↔ (l, r) ∈ g := by
  unfold rightNeighbors
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨he, he2⟩ := Finset.mem_filter.1 he
    rwa [show (e.1, r) = e from Prod.ext rfl he2.symm]
  · intro h
    exact Finset.mem_image.2 ⟨(l, r), Finset.mem_filter.2 ⟨h, rfl⟩, rfl⟩

/-- A left vertex of degree below `N` misses one of the colours `0, …, N - 1`. -/
private lemma exists_leftFree (g : Finset (L × R)) (c : L × R → ℕ) (l : L) {N : ℕ}
    (hl : leftDegree g l < N) : ∃ a < N, LeftFree g c l a := by
  have hl' : (neighbors g l).card < N := hl
  obtain ⟨a, ha, hna⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := (neighbors g l).image fun r => c (l, r)) (t := Finset.range N)
    (by rw [Finset.card_range]; exact Finset.card_image_le.trans_lt hl')
  refine ⟨a, Finset.mem_range.1 ha, fun r hr hcr => hna ?_⟩
  exact Finset.mem_image.2 ⟨r, (mem_neighbors_iff g l r).2 hr, hcr⟩

/-- A right vertex of degree below `N` misses one of the colours `0, …, N - 1`. -/
private lemma exists_rightFree (g : Finset (L × R)) (c : L × R → ℕ) (r : R) {N : ℕ}
    (hr : rightDegree g r < N) : ∃ b < N, RightFree g c r b := by
  have hr' : (rightNeighbors g r).card < N := hr
  obtain ⟨b, hb, hnb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := (rightNeighbors g r).image fun l => c (l, r)) (t := Finset.range N)
    (by rw [Finset.card_range]; exact Finset.card_image_le.trans_lt hr')
  refine ⟨b, Finset.mem_range.1 hb, fun l hl hcl => hnb ?_⟩
  exact Finset.mem_image.2 ⟨l, (mem_rightNeighbors_iff g l r).2 hl, hcl⟩

private lemma leftDegree_le_insert (g : Finset (L × R)) (e : L × R) (l : L) :
    leftDegree g l ≤ leftDegree (insert e g) l :=
  Finset.card_le_card (Finset.image_subset_image
    (Finset.filter_subset_filter (p := _) (Finset.subset_insert _ _)))

private lemma rightDegree_le_insert (g : Finset (L × R)) (e : L × R) (r : R) :
    rightDegree g r ≤ rightDegree (insert e g) r :=
  Finset.card_le_card (Finset.image_subset_image
    (Finset.filter_subset_filter (p := _) (Finset.subset_insert _ _)))

private lemma leftDegree_lt_of_insert {g : Finset (L × R)} {l : L} {r : R} (h : (l, r) ∉ g)
    {N : ℕ} (hN : leftDegree (insert (l, r) g) l ≤ N) : leftDegree g l < N := by
  have hsub : insert r (neighbors g l) ⊆ neighbors (insert (l, r) g) l :=
    Finset.insert_subset_iff.2 ⟨(mem_neighbors_iff _ _ _).2 (Finset.mem_insert_self _ _),
      Finset.image_subset_image
        (Finset.filter_subset_filter (p := _) (Finset.subset_insert _ _))⟩
  have hr : r ∉ neighbors g l := fun hr => h ((mem_neighbors_iff _ _ _).1 hr)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hr] at hcard
  unfold leftDegree at *
  omega

private lemma rightDegree_lt_of_insert {g : Finset (L × R)} {l : L} {r : R} (h : (l, r) ∉ g)
    {N : ℕ} (hN : rightDegree (insert (l, r) g) r ≤ N) : rightDegree g r < N := by
  have hsub : insert l (rightNeighbors g r) ⊆ rightNeighbors (insert (l, r) g) r :=
    Finset.insert_subset_iff.2 ⟨(mem_rightNeighbors_iff _ _ _).2 (Finset.mem_insert_self _ _),
      Finset.image_subset_image
        (Finset.filter_subset_filter (p := _) (Finset.subset_insert _ _))⟩
  have hl : l ∉ rightNeighbors g r := fun hl => h ((mem_rightNeighbors_iff _ _ _).1 hl)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hl] at hcard
  unfold rightDegree at *
  omega

/-! ### Kempe chains

The chain of a right vertex `r` for the colours `a`, `b` is the set of vertices reachable
from `r` by steps that leave a right vertex along its `a`-edge and a left vertex along its
`b`-edge.  Exchanging `a` and `b` on the edges touching the chain keeps the colouring proper,
frees `a` at `r` when `b` was free there, and does not touch a left vertex at which `a` is
free (such a vertex is never entered). -/

/-- One step of a Kempe chain: from a right vertex along an `a`-edge, from a left vertex
along a `b`-edge. -/
private inductive KempeStep (g : Finset (L × R)) (c : L × R → ℕ) (a b : ℕ) :
    L ⊕ R → L ⊕ R → Prop
  | right (l : L) (r : R) (h : (l, r) ∈ g) (hc : c (l, r) = a) :
      KempeStep g c a b (Sum.inr r) (Sum.inl l)
  | left (l : L) (r : R) (h : (l, r) ∈ g) (hc : c (l, r) = b) :
      KempeStep g c a b (Sum.inl l) (Sum.inr r)

/-- The Kempe chain of `r`: the vertices reachable from `r` by alternating steps. -/
private def KempeReach (g : Finset (L × R)) (c : L × R → ℕ) (a b : ℕ) (r : R)
    (v : L ⊕ R) : Prop :=
  Relation.ReflTransGen (KempeStep g c a b) (Sum.inr r) v

omit [DecidableEq L] [DecidableEq R] in
/-- A left vertex at which `a` is free is never entered by the chain. -/
private lemma not_kempeReach_inl {g : Finset (L × R)} {c : L × R → ℕ} {a b : ℕ} {r : R}
    {l : L} (hl : LeftFree g c l a) : ¬ KempeReach g c a b r (Sum.inl l) := by
  intro h
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨v, _, hs⟩
  · exact Sum.inl_ne_inr h
  · cases hs with
    | right l r hg hc => exact hl r hg hc

omit [DecidableEq L] [DecidableEq R] in
/-- An `a`- or `b`-coloured edge has both endpoints in the chain or neither. -/
private lemma kempeReach_inl_iff {g : Finset (L × R)} {c : L × R → ℕ} {a b : ℕ} {r : R}
    (hc : ProperOn g c) (hr : RightFree g c r b) {e : L × R} (he : e ∈ g)
    (hab : c e = a ∨ c e = b) :
    KempeReach g c a b r (Sum.inl e.1) ↔ KempeReach g c a b r (Sum.inr e.2) := by
  constructor
  · intro h
    rcases hab with hab | hab
    · rcases Relation.ReflTransGen.cases_tail h with h | ⟨v, hv, hs⟩
      · exact absurd h Sum.inl_ne_inr
      · cases hs with
        | right l r'' hg hc' =>
          have h2 : r'' = e.2 :=
            congrArg Prod.snd (properOn_eq_of_share hc hg he (Or.inl rfl) (hc'.trans hab.symm))
          subst h2
          exact hv
    · exact h.tail (KempeStep.left e.1 e.2 he hab)
  · intro h
    rcases hab with hab | hab
    · exact h.tail (KempeStep.right e.1 e.2 he hab)
    · rcases Relation.ReflTransGen.cases_tail h with h | ⟨v, hv, hs⟩
      · have h2 : e.2 = r := Sum.inr.inj h
        exact (hr e.1 (by rw [← h2]; exact he) (by rw [← h2]; exact hab)).elim
      · cases hs with
        | left l'' r' hg hc' =>
          have h2 : l'' = e.1 :=
            congrArg Prod.fst (properOn_eq_of_share hc hg he (Or.inr rfl) (hc'.trans hab.symm))
          subst h2
          exact hv

/-- The exchange of the colours `a` and `b`. -/
private def kempeSwap (a b x : ℕ) : ℕ := if x = a then b else if x = b then a else x

private lemma kempeSwap_eq_left_iff (a b x : ℕ) : kempeSwap a b x = a ↔ x = b := by
  unfold kempeSwap
  split_ifs <;> omega

private lemma kempeSwap_inj (a b : ℕ) {x y : ℕ} (h : kempeSwap a b x = kempeSwap a b y) :
    x = y := by
  unfold kempeSwap at h
  split_ifs at h <;> omega

private lemma kempeSwap_of_ne {a b x : ℕ} (ha : x ≠ a) (hb : x ≠ b) : kempeSwap a b x = x := by
  unfold kempeSwap
  rw [ite_eq_right ha, ite_eq_right hb]

private lemma kempeSwap_cases (a b x : ℕ) :
    kempeSwap a b x = x ∨ kempeSwap a b x = a ∨ kempeSwap a b x = b := by
  unfold kempeSwap
  split_ifs <;> simp

open Classical in
/-- The colouring obtained by exchanging `a` and `b` on the edges touching the chain of
`r`. -/
private noncomputable def kempeColour (g : Finset (L × R)) (c : L × R → ℕ) (a b : ℕ) (r : R)
    (e : L × R) : ℕ :=
  if KempeReach g c a b r (Sum.inl e.1) ∨ KempeReach g c a b r (Sum.inr e.2) then
    kempeSwap a b (c e) else c e

omit [DecidableEq L] [DecidableEq R] in
private lemma kempeColour_of_reach {g : Finset (L × R)} {c : L × R → ℕ} {a b : ℕ} {r : R}
    {e : L × R} (h : KempeReach g c a b r (Sum.inl e.1) ∨ KempeReach g c a b r (Sum.inr e.2)) :
    kempeColour g c a b r e = kempeSwap a b (c e) := by
  unfold kempeColour
  exact ite_eq_left h

omit [DecidableEq L] [DecidableEq R] in
/-- An edge with an endpoint outside the chain keeps its colour. -/
private lemma kempeColour_of_not_reach {g : Finset (L × R)} {c : L × R → ℕ} {a b : ℕ}
    {r : R} (hc : ProperOn g c) (hr : RightFree g c r b) {e : L × R} (he : e ∈ g)
    (h : ¬ KempeReach g c a b r (Sum.inl e.1) ∨ ¬ KempeReach g c a b r (Sum.inr e.2)) :
    kempeColour g c a b r e = c e := by
  unfold kempeColour
  split_ifs with h'
  · have key : ¬ (c e = a ∨ c e = b) := fun hab =>
      have hiff := kempeReach_inl_iff hc hr he hab
      h.elim (fun h1 => h1 (hiff.2 (h'.resolve_left h1)))
        (fun h2 => h2 (hiff.1 (h'.resolve_right h2)))
    exact kempeSwap_of_ne (fun ha => key (Or.inl ha)) (fun hb => key (Or.inr hb))
  · rfl

omit [DecidableEq L] [DecidableEq R] in
/-- The Kempe exchange: if `a` is free at `l` and `b` is free at `r`, the colouring can be
changed (using only the colours `a`, `b` and the old ones) so that `a` is free at both `l`
and `r`. -/
private lemma exists_properOn_free {g : Finset (L × R)} {c : L × R → ℕ} (hc : ProperOn g c)
    (a b : ℕ) (l : L) (r : R) (hl : LeftFree g c l a) (hr : RightFree g c r b) :
    ∃ c' : L × R → ℕ, ProperOn g c' ∧ (∀ e, c' e = c e ∨ c' e = a ∨ c' e = b) ∧
      LeftFree g c' l a ∧ RightFree g c' r a := by
  refine ⟨kempeColour g c a b r, ?_, ?_, ?_, ?_⟩
  · intro e he e' he' hne hsh heq
    have key : ∀ v : L ⊕ R, (v = Sum.inl e.1 ∨ v = Sum.inr e.2) →
        (v = Sum.inl e'.1 ∨ v = Sum.inr e'.2) → False := by
      intro v hv hv'
      by_cases hreach : KempeReach g c a b r v
      · have h1 : kempeColour g c a b r e = kempeSwap a b (c e) :=
          kempeColour_of_reach (by rcases hv with rfl | rfl <;> simp [hreach])
        have h2 : kempeColour g c a b r e' = kempeSwap a b (c e') :=
          kempeColour_of_reach (by rcases hv' with rfl | rfl <;> simp [hreach])
        rw [h1, h2] at heq
        exact hc e he e' he' hne hsh (kempeSwap_inj a b heq)
      · have h1 : kempeColour g c a b r e = c e :=
          kempeColour_of_not_reach hc hr he (by rcases hv with rfl | rfl <;> simp [hreach])
        have h2 : kempeColour g c a b r e' = c e' :=
          kempeColour_of_not_reach hc hr he' (by rcases hv' with rfl | rfl <;> simp [hreach])
        rw [h1, h2] at heq
        exact hc e he e' he' hne hsh heq
    rcases hsh with hsh | hsh
    · exact key (Sum.inl e.1) (Or.inl rfl) (Or.inl (by rw [hsh]))
    · exact key (Sum.inr e.2) (Or.inr rfl) (Or.inr (by rw [hsh]))
  · intro e
    unfold kempeColour
    split_ifs
    · exact kempeSwap_cases a b (c e)
    · exact Or.inl rfl
  · intro r' hr'
    rw [kempeColour_of_not_reach hc hr hr' (Or.inl (not_kempeReach_inl hl))]
    exact hl r' hr'
  · intro l' hl' heq
    rw [kempeColour_of_reach (e := (l', r)) (Or.inr Relation.ReflTransGen.refl)] at heq
    exact hr l' hl' ((kempeSwap_eq_left_iff a b _).1 heq)

/-- Adding an edge `(l, r)` with a colour free at both `l` and `r` keeps the colouring
proper. -/
private lemma properOn_insert {g : Finset (L × R)} {c : L × R → ℕ} (hc : ProperOn g c)
    {l : L} {r : R} (hg : (l, r) ∉ g) {a : ℕ} (hl : LeftFree g c l a)
    (hr : RightFree g c r a) :
    ProperOn (insert (l, r) g) (fun e => if e = (l, r) then a else c e) := by
  intro e he e' he' hne hsh
  rw [Finset.mem_insert] at he he'
  dsimp only
  rcases he with rfl | he <;> rcases he' with rfl | he'
  · exact absurd rfl hne
  · rw [ite_eq_left rfl, ite_eq_right (fun h : e' = (l, r) => hg (h ▸ he'))]
    obtain ⟨l', r'⟩ := e'
    dsimp only at hsh
    rcases hsh with hsh | hsh
    · subst hsh
      exact (hl r' he').symm
    · subst hsh
      exact (hr l' he').symm
  · rw [ite_eq_right (fun h : e = (l, r) => hg (h ▸ he)), ite_eq_left rfl]
    obtain ⟨l', r'⟩ := e
    dsimp only at hsh
    rcases hsh with hsh | hsh
    · subst hsh
      exact hl r' he
    · subst hsh
      exact hr l' he
  · rw [ite_eq_right (fun h : e = (l, r) => hg (h ▸ he)),
      ite_eq_right (fun h : e' = (l, r) => hg (h ▸ he'))]
    exact hc e he e' he' hne hsh

/-- The total-colouring form of König's theorem, by induction on the edge set. -/
private lemma exists_properOn (N : ℕ) (g : Finset (L × R)) (hleft : ∀ l, leftDegree g l ≤ N)
    (hright : ∀ r, rightDegree g r ≤ N) :
    ∃ c : L × R → ℕ, ProperOn g c ∧ ∀ e ∈ g, c e < N := by
  revert hleft hright
  induction g using Finset.induction_on with
  | empty =>
    intro _ _
    exact ⟨fun _ => 0, fun e he => absurd he (Finset.notMem_empty _),
      fun e he => absurd he (Finset.notMem_empty _)⟩
  | @insert e g he ih =>
    intro hleft hright
    obtain ⟨l, r⟩ := e
    obtain ⟨c, hc, hcN⟩ := ih (fun l' => (leftDegree_le_insert g _ l').trans (hleft l'))
      (fun r' => (rightDegree_le_insert g _ r').trans (hright r'))
    obtain ⟨a, haN, ha⟩ := exists_leftFree g c l (leftDegree_lt_of_insert he (hleft l))
    obtain ⟨b, hbN, hb⟩ := exists_rightFree g c r (rightDegree_lt_of_insert he (hright r))
    obtain ⟨c', hc', hval, hl', hr'⟩ := exists_properOn_free hc a b l r ha hb
    refine ⟨fun e => if e = (l, r) then a else c' e, properOn_insert hc' he hl' hr', ?_⟩
    intro e he'
    dsimp only
    split_ifs with h
    · exact haN
    · rw [Finset.mem_insert] at he'
      rcases he' with h' | he'
      · exact absurd h' h
      · rcases hval e with h'' | h'' | h''
        · rw [h'']
          exact hcN e he'
        · rw [h'']
          exact haN
        · rw [h'']
          exact hbN

/-- König's edge-colouring theorem: a finite bipartite graph with all degrees at most `N`
(on both sides) has a proper edge colouring with `N` colours.  A colouring is a function on
the set of edges, so the case of a graph without edges (and `N = 0`) is included.

SUV Problem 321, p. 378. -/
theorem exists_properEdgeColouring (g : Finset (L × R)) (N : ℕ)
    (hleft : ∀ l, leftDegree g l ≤ N) (hright : ∀ r, rightDegree g r ≤ N) :
    ∃ col : g → Fin N, IsProperEdgeColouring g col := by
  obtain ⟨c, hc, hcN⟩ := exists_properOn N g hleft hright
  refine ⟨fun e => ⟨c e, hcN e e.2⟩, fun e e' hne hsh h => ?_⟩
  exact hc e e.2 e' e'.2 (fun h' => hne (Subtype.ext h')) hsh (Fin.mk.inj_iff.1 h)

end Kolmogorov
