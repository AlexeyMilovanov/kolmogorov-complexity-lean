import KolmogorovMathlib.MonotoneComplexity.GacsDayFamilyGame
import KolmogorovMathlib.MonotoneComplexity.GacsDaySubtree
import KolmogorovMathlib.MonotoneComplexity.GacsDayAccumulation
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayComposition
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayWitness

/-!
# Truncating server allocations and relocating client requests

Server moves may grant long cylinders; the ladder construction only ever needs their prefixes of
length at most `eps`. `truncFamilyServerMove` performs this truncation,
`familyServerMoveAt_truncFamilyServerMove` says it acts clientwise, and
`familyServerPlayLegal_truncFamily` shows a legal play stays legal after truncation, with
`allocationAvoidsUnavailable_truncAlloc_simple` for the avoidance side. The remaining lemmas
(`disjointAllocations_of_allocationSubset`, `allocationSubset_getAlloc_cons`) are the containment
and disjointness facts about coherent server moves that relocating a request between nodes of the
family needs.
-/

namespace Kolmogorov

open scoped ENNReal

variable {n b : ℕ}

/-- The family server move with every allocation truncated to length at most `eps`. -/
def truncFamilyServerMove (eps : ℕ) (sm : FamilyServerMove) : FamilyServerMove :=
  sm.map (truncServerMove eps)

/-- The truncated family move acts on each client as the truncation of that client's move. -/
@[simp] lemma familyServerMoveAt_truncFamilyServerMove (eps : ℕ) (sm : FamilyServerMove) (i : ℕ) :
    familyServerMoveAt (truncFamilyServerMove eps sm) i
      = truncServerMove eps (familyServerMoveAt sm i) := by
  unfold familyServerMoveAt truncFamilyServerMove
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : i < sm.length
  · rw [List.getElem?_eq_getElem (by simpa), List.getElem?_eq_getElem h]
    simp [List.getElem_map]
  · push Not at h
    rw [List.getElem?_eq_none (by simpa), List.getElem?_eq_none h]
    rfl

/-- Truncating an allocation preserves avoidance of the unavailable set. -/
lemma allocationAvoidsUnavailable_truncAlloc_simple {eps : ℕ} {A alloc : Allocation}
    (h : allocationAvoidsUnavailable A alloc) :
    allocationAvoidsUnavailable A (truncAlloc eps alloc) := by
  intro c hc a ha hcomp
  exact h c (mem_truncAlloc.mp hc).1 a ha hcomp

/-- Truncating every move of a legal server play keeps it legal. -/
theorem familyServerPlayLegal_truncFamily {A : Allocation} {eps : ℕ}
    {sm : ℕ → FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal n b A (fun t => truncFamilyServerMove eps (sm t)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hlegal := serverPlayLegal_truncServerMove (eps := eps) (hsm.1 i hi)
    simpa using hlegal
  · intro t i hi j hj hneq
    have hdisj := disjointAllocations_truncAlloc (eps := eps) (hsm.2.1 t i hi j hj hneq)
    simpa [getFamilyAlloc, getAlloc_truncServerMove] using hdisj
  · intro t i hi x
    have havoid := allocationAvoidsUnavailable_truncAlloc_simple (eps := eps) (hsm.2.2 t i hi x)
    simpa [getFamilyAlloc, getAlloc_truncServerMove] using havoid

/-- Allocations inside disjoint allocations are disjoint. -/
lemma disjointAllocations_of_allocationSubset {a1 a2 b1 b2 : Allocation}
    (h1 : allocationSubset a1 b1) (h2 : allocationSubset a2 b2)
    (hd : disjointAllocations b1 b2) : disjointAllocations a1 a2 := by
  intro c1 hc1 c2 hc2 hcomp
  obtain ⟨d1, hd1, hpref1⟩ := h1 c1 hc1
  obtain ⟨d2, hd2, hpref2⟩ := h2 c2 hc2
  have hcomp2 : d1 <+: d2 ∨ d2 <+: d1 := by
    rcases hcomp with h | h
    · exact List.prefix_or_prefix_of_prefix (hpref1.trans h) hpref2
    · exact (List.prefix_or_prefix_of_prefix (hpref2.trans h) hpref1).symm
  exact hd d1 hd1 d2 hd2 hcomp2

/-- For a coherent server move, the allocation at a child is contained in the allocation at the
root. -/
lemma allocationSubset_getAlloc_cons {sm : ServerMove} {b : ℕ} (hcoh : serverMoveCoherent b sm)
    {x : ℕ} (hx : x < b) : allocationSubset (getAlloc sm [x]) (getAlloc sm []) := by
  have := hcoh.1 [] ⟨x, hx⟩
  simpa using this

/-- For a coherent server move, the allocation at a grandchild is contained in the allocation at
the root. -/
lemma allocationSubset_getAlloc_cons_cons {sm : ServerMove} {b : ℕ} (hcoh : serverMoveCoherent b sm)
    {x y : ℕ} (hx : x < b) (hy : y < b) : allocationSubset (getAlloc sm [x,
      y]) (getAlloc sm []) := by
  have h1 := allocationSubset_getAlloc_cons hcoh hx
  have h2 : allocationSubset (getAlloc sm [x, y]) (getAlloc sm [x]) := by
    have := hcoh.1 [x] ⟨y, hy⟩
    simpa using this
  exact allocationSubset_trans h2 h1

/-- The family server move seen by the slots, each slot receiving the subtree of the server move
below its grandchild. -/
def extractGrandchildFamilyMove (slots : List (Fin n × Fin b × Fin b))
    (sm : FamilyServerMove) : FamilyServerMove :=
  slots.map (fun slot => extractSubtreeServerMove slot.2.2.val
    (extractSubtreeServerMove slot.2.1.val (familyServerMoveAt sm slot.1.val)))

/-- The extracted move of slot `i` is the doubly restricted subtree move at that slot's
grandchild. -/
@[simp] lemma familyServerMoveAt_extractGrandchildFamilyMove (slots : List (Fin n × Fin b × Fin b))
    (sm : FamilyServerMove) (i : ℕ) (hi : i < slots.length) :
    familyServerMoveAt (extractGrandchildFamilyMove slots sm) i =
      extractSubtreeServerMove (slots.get ⟨i, hi⟩).2.2.val
        (extractSubtreeServerMove (slots.get ⟨i, hi⟩).2.1.val
          (familyServerMoveAt sm (slots.get ⟨i, hi⟩).1.val)) := by
  unfold extractGrandchildFamilyMove familyServerMoveAt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.get_eq_getElem]
  rw [List.getElem?_eq_getElem hi]
  simp

/-- Extracting the grandchild subtrees of distinct slots from a legal play again gives a legal
play. -/
theorem serverPlayLegal_extractGrandchild {A : Allocation}
    (slots : List (Fin n × Fin b × Fin b)) (hslots : slots.Nodup)
    {sm : ℕ → FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal slots.length b A (fun t => extractGrandchildFamilyMove slots (sm t)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simp only [familyServerMoveAt_extractGrandchildFamilyMove slots _ i hi]
    exact serverPlayLegal_extractSubtree (serverPlayLegal_extractSubtree (hsm.1 _ (slots.get ⟨i,
      hi⟩).1.isLt))
  · intro t i hi j hj hneq
    unfold getFamilyAlloc
    simp only [familyServerMoveAt_extractGrandchildFamilyMove slots _ i hi,
      familyServerMoveAt_extractGrandchildFamilyMove slots _ j hj]
    simp only [getAlloc_extractSubtreeServerMove]
    set h1 := slots.get ⟨i, hi⟩
    set h2 := slots.get ⟨j, hj⟩
    by_cases h : h1.1.val = h2.1.val
    · by_cases heq : h1.2.1.val = h2.2.1.val
      · by_cases heq2 : h1.2.2.val = h2.2.2.val
        · have h_full : h1 = h2 := by
            apply Prod.ext (Fin.ext h) (Prod.ext (Fin.ext heq) (Fin.ext heq2))
          have : (⟨i, hi⟩ : Fin slots.length) = ⟨j, hj⟩ :=
            List.Nodup.get_inj_iff hslots |>.mp h_full
          have : i = j := Fin.ext_iff.mp this
          exact absurd this hneq
        · have hdisj :=
          (hsm.1 h1.1.val h1.1.isLt).1 t
          |>.2 [h1.2.1.val] h1.2.2 h2.2.2 (by intro hhh; exact heq2 (congrArg Fin.val hhh))
          have hsub1 :=
            allocationSubset_refl (getAlloc (familyServerMoveAt (sm t) h1.1.val) [h1.2.1.val,
            h1.2.2.val])
          have hsub2 :=
            allocationSubset_refl (getAlloc (familyServerMoveAt (sm t) h2.1.val) [h2.2.1.val,
            h2.2.2.val])
          have hh : h2.1.val = h1.1.val := h.symm
          have hh2 : h2.2.1.val = h1.2.1.val := heq.symm
          simpa [hh, hh2] using hdisj
      · have hdisj :=
        (hsm.1 h1.1.val h1.1.isLt).1 t
        |>.2 [] h1.2.1 h2.2.1 (by intro hhh; exact heq (congrArg Fin.val hhh))
        have hsub1 : allocationSubset (getAlloc (familyServerMoveAt (sm t) h1.1.val) [h1.2.1.val,
          h1.2.2.val]) (getAlloc (familyServerMoveAt (sm t) h1.1.val) [h1.2.1.val]) := by
          have := (hsm.1 h1.1.val h1.1.isLt).1 t |>.1 [h1.2.1.val] h1.2.2
          simpa using this
        have hsub2 : allocationSubset (getAlloc (familyServerMoveAt (sm t) h2.1.val) [h2.2.1.val,
          h2.2.2.val]) (getAlloc (familyServerMoveAt (sm t) h2.1.val) [h2.2.1.val]) := by
          have := (hsm.1 h2.1.val h2.1.isLt).1 t |>.1 [h2.2.1.val] h2.2.2
          simpa using this
        have hh : h2.1.val = h1.1.val := h.symm
        have hsub2' : allocationSubset (getAlloc (familyServerMoveAt (sm t) h2.1.val) [h2.2.1.val,
          h2.2.2.val]) (getAlloc (familyServerMoveAt (sm t) h1.1.val) [h2.2.1.val]) := by
          simpa [hh] using hsub2
        exact disjointAllocations_of_allocationSubset hsub1 hsub2' hdisj
    · have hdisj :=
      hsm.2.1 t h1.1.val h1.1.isLt h2.1.val h2.1.isLt (by intro heq; apply h; exact heq)
      have hsub1 :=
        allocationSubset_getAlloc_cons_cons ((hsm.1 h1.1.val h1.1.isLt).1 t) h1.2.1.isLt h1.2.2.isLt
      have hsub2 :=
        allocationSubset_getAlloc_cons_cons ((hsm.1 h2.1.val h2.1.isLt).1 t) h2.2.1.isLt h2.2.2.isLt
      exact disjointAllocations_of_allocationSubset hsub1 hsub2 hdisj
  · intro t i hi x
    unfold getFamilyAlloc
    simp only [familyServerMoveAt_extractGrandchildFamilyMove slots _ i hi]
    simp only [getAlloc_extractSubtreeServerMove]
    exact hsm.2.2 t (slots.get ⟨i, hi⟩).1.val (slots.get ⟨i, hi⟩).1.isLt _

/-- For requests of at least `2 ^ (-eps)`, truncation at `eps` does not change which requests are
served. -/
@[simp] lemma serves_truncFamilyServerMove_iff {eps : ℕ} {sm : FamilyServerMove} {req : ℚ} {i :
  ℕ} {x : GacsDayNode}
    (heps : (1 / 2 : ℚ) ^ eps ≤ req) :
    Serves (getFamilyAlloc (truncFamilyServerMove eps sm) i x) req ↔
    Serves (getFamilyAlloc sm i x) req := by
  unfold getFamilyAlloc
  rw [familyServerMoveAt_truncFamilyServerMove, getAlloc_truncServerMove]
  exact serves_truncAlloc_iff heps

/-- The family client move restricted to the slots, each slot keeping the subtree of its client's
move below its grandchild. -/
def restrictGrandchildClientMove (slots : List (Fin n × Fin b × Fin b))
    (cm : FamilyClientMove) : FamilyClientMove :=
  slots.map (fun slot => restrictSubtreeClientMove slot.2.2.val
    (restrictSubtreeClientMove slot.2.1.val (familyClientMoveAt cm slot.1.val)))

/-- The restricted move of slot `i` is the doubly restricted subtree move at that slot's
grandchild. -/
@[simp] lemma familyClientMoveAt_restrictGrandchildClientMove (slots : List (Fin n × Fin b × Fin b))
    (cm : FamilyClientMove) (i : ℕ) (hi : i < slots.length) :
    familyClientMoveAt (restrictGrandchildClientMove slots cm) i =
      restrictSubtreeClientMove (slots.get ⟨i, hi⟩).2.2.val
        (restrictSubtreeClientMove (slots.get ⟨i, hi⟩).2.1.val
          (familyClientMoveAt cm (slots.get ⟨i, hi⟩).1.val)) := by
  unfold restrictGrandchildClientMove familyClientMoveAt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.get_eq_getElem]
  rw [List.getElem?_eq_getElem hi]
  simp

/-- The restricted move of a slot requests at a node what the original client requests below that
slot's grandchild. -/
@[simp] lemma getFamilyReq_restrictGrandchildClientMove (slots : List (Fin n × Fin b × Fin b))
    (cm : FamilyClientMove) (i : ℕ) (hi : i < slots.length) (x : GacsDayNode) :
    getFamilyReq (restrictGrandchildClientMove slots cm) i x =
    getFamilyReq cm (slots.get ⟨i, hi⟩).1.val ([(slots.get ⟨i, hi⟩).2.1.val, (slots.get ⟨i,
      hi⟩).2.2.val] ++ x) := by
  unfold getFamilyReq
  rw [familyClientMoveAt_restrictGrandchildClientMove _ _ _ hi]
  simp

/-- A reserve incomparable with the whole allocation stays incomparable with every new gray cell
of that allocation. -/
lemma freshReserve_incomparable_earlierGray {epsDepth deltaDepth : ℕ} {alloc unavailable :
  Finset BitString}
    {R c : BitString}
    (halloc_len : ∀ y ∈ alloc, y.length ≤ epsDepth)
    (hR : ∀ y ∈ alloc, ¬ (y <+: R ∨ R <+: y))
    (hc : c ∈ newGrayCells epsDepth deltaDepth alloc unavailable) :
    ¬ (R <+: c ∨ c <+: R) := by
  have hc_mem := mem_newGrayCells_iff.mp hc
  have ht := mem_neighborhoodCells_iff_prefixComparable.mp hc_mem.2.1
  obtain ⟨y, hy, hyc⟩ := ht.2
  have hlen_y := halloc_len y hy
  have ht_len := ht.1
  have y_pref_c : y <+: c := by
    have h_take : c.take epsDepth <+: c := ⟨c.drop epsDepth, c.take_append_drop epsDepth⟩
    rcases hyc with h | h
    · have h1 : (c.take epsDepth).length = epsDepth := ht_len
      have h2 : y.length = epsDepth := le_antisymm hlen_y (by
        have := h.length_le
        omega
      )
      have eq1 : c.take epsDepth = y := List.IsPrefix.eq_of_length h (by omega)
      rw [←eq1]
      exact h_take
    · exact h.trans h_take
  intro h
  refine hR y hy ?_
  rcases h with h | h
  · rcases List.prefix_or_prefix_of_prefix h y_pref_c with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'
  · exact Or.inl (y_pref_c.trans h)

/-- The cells a chain of gray calls charges in turn, each call blocked by the allocations of its
predecessors. -/
def grayCallsNewGrayMass (deltaDepth : ℕ) : List (ℕ × Finset BitString) → Finset BitString → ℕ
| [], _ => 0
| ((eps, A) :: rest), U =>
  (newGrayCells eps deltaDepth A U).card + grayCallsNewGrayMass deltaDepth rest (U ∪ A)

/-- Along a chain of nonincreasing epsilon depths, the last depth is at most the first. -/
lemma chain_last_le_head : ∀ (l : List (ℕ × Finset BitString)) (_hchain : l.IsChain (fun p1 p2 =>
  p2.1 ≤ p1.1)),
    (l.getLast? |>.map Prod.fst |>.getD 0) ≤ (l.head? |>.map Prod.fst |>.getD 0)
| [], _ => by simp
| [x], _ => by rfl
| x :: y :: tail, hchain => by
  cases hchain
  rename_i rel chain2
  have h1 : y.1 ≤ x.1 := rel
  have h2 : ((y :: tail).getLast? |>.map Prod.fst |>.getD 0) ≤ y.1 :=
    chain_last_le_head (y :: tail) chain2
  exact le_trans h2 h1

/-- A chain of gray calls of nonincreasing epsilon depth charges at most as many cells as a
single call at the last depth with the union of the allocations. -/
lemma grayCalls_newGrayMass_add (calls : List (ℕ × Finset BitString)) (deltaDepth : ℕ) (U :
  Finset BitString)
    (hscale : calls.IsChain (fun p1 p2 => p2.1 ≤ p1.1))
    (hA : ∀ p ∈ calls, ∀ c ∈ p.2, c.length ≤ p.1) :
    grayCallsNewGrayMass deltaDepth calls U ≤
    (newGrayCells (calls.getLast? |>.map Prod.fst |>.getD 0) deltaDepth
      (calls.map Prod.snd |>.foldr (· ∪ ·) ∅) U).card := by
  revert U hscale hA
  induction calls with
  | nil =>
    intro U hscale hA
    simp [grayCallsNewGrayMass]
  | cons head tail ih =>
    intro U hscale hA
    cases tail with
    | nil =>
      simp [grayCallsNewGrayMass]
    | cons head2 tail2 =>
      have hchain_tail : (head2 :: tail2).IsChain (fun p1 p2 => p2.1 ≤ p1.1) := by
        cases hscale
        rename_i _ h
        exact h
      have hA_tail : ∀ p ∈ head2 :: tail2, ∀ c ∈ p.2, c.length ≤ p.1 :=
        fun p hp => hA p (List.Mem.tail head hp)
      have hIH := ih (U ∪ head.2) hchain_tail hA_tail
      have h_gray : grayCallsNewGrayMass deltaDepth (head :: head2 :: tail2) U =
        (newGrayCells head.1 deltaDepth head.2 U).card
          + grayCallsNewGrayMass deltaDepth (head2 :: tail2) (U ∪ head.2) := rfl
      rw [h_gray]
      have h_last : (head :: head2 :: tail2).getLast? = (head2 :: tail2).getLast? := rfl
      rw [h_last]
      have h_le := Nat.add_le_add_left hIH (newGrayCells head.1 deltaDepth head.2 U).card
      refine le_trans h_le ?_
      have hA_head : ∀ c ∈ head.2, c.length ≤ head.1 := hA head (List.Mem.head _)
      have h_eps : ((head2 :: tail2).getLast? |>.map Prod.fst |>.getD 0) ≤ head.1 := by
        have h_last_le := chain_last_le_head (head :: head2 :: tail2) hscale
        have h_head : ((head :: head2 :: tail2).head? |>.map Prod.fst |>.getD 0) = head.1 := rfl
        rw [h_head] at h_last_le
        rw [h_last] at h_last_le
        exact h_last_le
      have h_comp :=
        card_add_le_card_newGrayCells_compose (deltaDepth := deltaDepth) (A2 := (head2 :: tail2).map
        Prod.snd |>.foldr (· ∪ ·) ∅) (U := U) h_eps hA_head
      exact h_comp

end Kolmogorov
