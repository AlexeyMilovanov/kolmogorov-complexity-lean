import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay

/-!
# Legality of the recursive plays in Day's gray-ladder tail

The outer server play is shifted to the start of the current round and then
relocated to its globally fresh grandson slots.  These lemmas connect that
mathematical infinite play with the finite history stored by the controller.
-/

namespace Kolmogorov

/-- Restricting a family move to the tree acts on each client as the restriction of that client's
move. -/
@[simp] lemma familyServerMoveAt_inTreeFamilyServerMove
    (b : ℕ) (sm : FamilyServerMove) (i : ℕ) :
    familyServerMoveAt (inTreeFamilyServerMove b sm) i =
      inTreeServerMove b (familyServerMoveAt sm i) := by
  unfold inTreeFamilyServerMove familyServerMoveAt
  simp only [List.getD_eq_getElem?_getD]
  by_cases hi : i < sm.length
  · rw [List.getElem?_eq_getElem (by simpa),
      List.getElem?_eq_getElem hi]
    simp [List.getElem_map]
  · push Not at hi
    rw [List.getElem?_eq_none (by simpa),
      List.getElem?_eq_none hi]
    rfl

/-- Restricting every move of a legal server play to the tree keeps it legal. -/
theorem familyServerPlayLegal_inTreeFamily {n b : ℕ} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal n b A
      (fun t => inTreeFamilyServerMove b (sm t)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simpa using
      serverPlayLegal_inTreeServerMove (hsm.1 i hi)
  · intro t i hi j hj hij
    unfold getFamilyAlloc
    rw [familyServerMoveAt_inTreeFamilyServerMove,
      familyServerMoveAt_inTreeFamilyServerMove]
    rw [getAlloc_inTreeServerMove_of_mem _ (by simp),
      getAlloc_inTreeServerMove_of_mem _ (by simp)]
    exact hsm.2.1 t i hi j hj hij
  · intro t i hi x
    unfold getFamilyAlloc
    rw [familyServerMoveAt_inTreeFamilyServerMove]
    by_cases hx : ∀ c ∈ x, c < b
    · rw [getAlloc_inTreeServerMove_of_mem _ hx]
      exact hsm.2.2 t i hi x
    · rw [getAlloc_inTreeServerMove_of_not_mem _ hx]
      intro c hc
      simp at hc

/-- The localised server move gives a slot the truncation, at depth `eps`, of the subtree
allocation at that slot's grandchild. -/
lemma getFamilyAlloc_grayTailLocalServerMove {n b eps : ℕ}
    (slots : List (GrayTailSlot n b)) (sm : FamilyServerMove)
    (i : ℕ) (hi : i < slots.length) (x : GacsDayNode)
    (hx : ∀ c ∈ x, c < b) :
    getFamilyAlloc (grayTailLocalServerMove eps slots sm) i x =
      truncAlloc eps (getAlloc
        (extractSubtreeServerMove (slots.get ⟨i, hi⟩).2.2.val
          (extractSubtreeServerMove (slots.get ⟨i, hi⟩).2.1.val
            (familyServerMoveAt sm (slots.get ⟨i, hi⟩).1.val))) x) := by
  unfold grayTailLocalServerMove getFamilyAlloc
  rw [familyServerMoveAt_truncFamilyServerMove,
    getAlloc_truncServerMove,
    familyServerMoveAt_inTreeFamilyServerMove,
    getAlloc_inTreeServerMove_of_mem _ hx,
    familyServerMoveAt_extractGrandchildFamilyMove slots sm i hi]

/-- The localised server move allocates nothing at nodes outside the tree. -/
lemma getFamilyAlloc_grayTailLocalServerMove_of_not_mem
    {n b eps : ℕ} (slots : List (GrayTailSlot n b))
    (sm : FamilyServerMove) (i : ℕ) (_hi : i < slots.length)
    (x : GacsDayNode) (hx : ¬ ∀ c ∈ x, c < b) :
    getFamilyAlloc (grayTailLocalServerMove eps slots sm) i x = [] := by
  unfold grayTailLocalServerMove getFamilyAlloc
  rw [familyServerMoveAt_truncFamilyServerMove,
    getAlloc_truncServerMove,
    familyServerMoveAt_inTreeFamilyServerMove,
    getAlloc_inTreeServerMove_of_not_mem _ hx, truncAlloc_nil]

/-- Allocations living below two different outer grandson slots never meet,
even when they are observed at different outer times. -/
theorem not_prefixComparable_of_grandchild_slots
    {n b : ℕ} {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm)
    (s₁ s₂ : GrayTailSlot n b) (hne : s₁ ≠ s₂)
    {u v : ℕ} {x y : GacsDayNode}
    (hx : ∀ c ∈ x, c < b) (hy : ∀ c ∈ y, c < b)
    {p q : BitString}
    (hp : p ∈ getAlloc
      (extractSubtreeServerMove s₁.2.2.val
        (extractSubtreeServerMove s₁.2.1.val
          (familyServerMoveAt (sm u) s₁.1.val))) x)
    (hq : q ∈ getAlloc
      (extractSubtreeServerMove s₂.2.2.val
        (extractSubtreeServerMove s₂.2.1.val
          (familyServerMoveAt (sm v) s₂.1.val))) y) :
    ¬ (p <+: q ∨ q <+: p) := by
  let slots : List (GrayTailSlot n b) := [s₁, s₂]
  have hslots : slots.Nodup := by
    simp [slots, hne]
  have hleg :
      familyServerPlayLegal slots.length b A
        (fun t => extractGrandchildFamilyMove slots (sm t)) :=
    serverPlayLegal_extractGrandchild slots hslots hsm
  have hp' :
      p ∈ getFamilyAlloc
        (extractGrandchildFamilyMove slots (sm u)) 0 x := by
    simpa [slots, getFamilyAlloc] using hp
  have hq' :
      q ∈ getFamilyAlloc
        (extractGrandchildFamilyMove slots (sm v)) 1 y := by
    simpa [slots, getFamilyAlloc] using hq
  exact not_prefixComparable_of_family_regions hleg
    (i := 0) (j := 1) (by simp [slots]) (by simp [slots])
    (by omega) hx hy hp' hq'

/-- Legality of a family play at a branching passes to any smaller branching. -/
lemma familyServerPlayLegal_of_le_branch {n b B : ℕ}
    {A : Allocation} (hbB : b ≤ B)
    {sm : ℕ → FamilyServerMove}
    (hsm : familyServerPlayLegal n B A sm) :
    familyServerPlayLegal n b A sm := by
  refine ⟨?_, hsm.2.1, hsm.2.2⟩
  intro i hi
  exact serverPlayLegal_mono_branching hbB (hsm.1 i hi)

/-- The server play the recursive call of the current round sees: the outer play from the round
start on, localised to the open slots at the round's delta depth. -/
def grayTailFutureServer {n b : ℕ}
    (q L e : ℕ) (st : GrayTailState n b)
    (sm : ℕ → FamilyServerMove) : ℕ → FamilyServerMove :=
  fun t =>
    grayTailLocalServerMove
      (grayTailRoundDelta q L e st.frozen.length) st.slots
      (sm (st.roundStart + t))

/-- For a well-shaped state, the server play seen by the recursive call is legal against the
original unavailable allocation. -/
lemma grayTailFutureServer_legal_A {n b : ℕ}
    (q L e : ℕ) {A : Allocation}
    {st : GrayTailState n b} (hst : GrayTailShape st)
    {sm : ℕ → FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal st.slots.length b A
      (grayTailFutureServer q L e st sm) := by
  have hshift :
      familyServerPlayLegal n b A
        (fun t => sm (st.roundStart + t)) := by
    simpa [Nat.add_comm] using
      familyServerPlayLegal_shift hsm st.roundStart
  unfold grayTailFutureServer grayTailLocalServerMove
  exact familyServerPlayLegal_truncFamily
    (familyServerPlayLegal_inTreeFamily
      (serverPlayLegal_extractGrandchild st.slots hst.slots_nodup
        hshift))

/-- The future play of the active round avoids both the original unavailable
allocation and every root allocation frozen by an earlier round. -/
theorem grayTailFutureServer_legal {n b q L e t : ℕ}
    {A : Allocation} {st : GrayTailState n b}
    {sm : ℕ → FamilyServerMove}
    (hcert : GrayTailCertified q L e A sm t st)
    (hround : st.frozen.length < grayTailRoundCount q)
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal st.slots.length b st.unavailable
      (grayTailFutureServer q L e st sm) := by
  have hA :=
    grayTailFutureServer_legal_A q L e hcert.shape hsm
  refine ⟨hA.1, hA.2.1, ?_⟩
  intro u i hi x
  rw [hcert.unavailable_eq]
  intro c hc a ha
  rcases List.mem_append.mp ha with haA | haFrozen
  · exact hA.2.2 u i hi x c hc a haA
  · simp only [grayTailFrozenAllocated, List.mem_flatMap] at haFrozen
    obtain ⟨p, hpFrozen, haRound⟩ := haFrozen
    rcases hcert.round_valid p hpFrozen with
      ⟨hpIndex, hpDepth, -, hpAllocated, -, -, hpSlotsRound⟩
    rw [grayTailRoundUnavailable,
      mem_neighborhoodCellsList] at haRound
    obtain ⟨haLength, d, hdRound, hdaComp⟩ := haRound
    rw [hpAllocated] at hdRound
    simp only [grayTailLocalAllocatedList, List.mem_flatMap,
      List.mem_range] at hdRound
    obtain ⟨j, hj, hdLocal⟩ := hdRound
    have hjSlots : j < p.slots.length := by
      simpa [grayTailLocalServerMove, truncFamilyServerMove,
        inTreeFamilyServerMove,
        extractGrandchildFamilyMove] using hj
    let oldSlot : GrayTailSlot n b :=
      p.slots.get ⟨j, hjSlots⟩
    let newSlot : GrayTailSlot n b :=
      st.slots.get ⟨i, hi⟩
    have hdOld : d ∈ getAlloc
        (extractSubtreeServerMove oldSlot.2.2.val
          (extractSubtreeServerMove oldSlot.2.1.val
            (familyServerMoveAt (sm p.serverTime) oldSlot.1.val))) [] := by
      rw [getFamilyAlloc_grayTailLocalServerMove
        p.slots (sm p.serverTime) j hjSlots [] (by simp)] at hdLocal
      exact (mem_truncAlloc.mp (by
        simpa [oldSlot] using hdLocal)).1
    have hcLocal :
        c ∈ getFamilyAlloc
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length) st.slots
            (sm (st.roundStart + u))) i x := by
      simpa [grayTailFutureServer] using hc
    have hx : ∀ d ∈ x, d < b := by
      by_contra hbad
      have hz := getFamilyAlloc_grayTailLocalServerMove_of_not_mem
        (eps := grayTailRoundDelta q L e st.frozen.length)
        st.slots (sm (st.roundStart + u)) i hi x hbad
      rw [hz] at hcLocal
      simp at hcLocal
    have hcNew : c ∈ getAlloc
        (extractSubtreeServerMove newSlot.2.2.val
          (extractSubtreeServerMove newSlot.2.1.val
            (familyServerMoveAt (sm (st.roundStart + u))
              newSlot.1.val))) x := by
      rw [getFamilyAlloc_grayTailLocalServerMove
        st.slots (sm (st.roundStart + u)) i hi x hx] at hcLocal
      exact (mem_truncAlloc.mp (by
        simpa [newSlot] using hcLocal)).1
    have hcLength :
        c.length ≤ grayTailRoundDelta q L e st.frozen.length := by
      rw [getFamilyAlloc_grayTailLocalServerMove
        st.slots (sm (st.roundStart + u)) i hi x hx] at hcLocal
      exact (mem_truncAlloc.mp (by
        simpa [newSlot] using hcLocal)).2
    have holdMem : oldSlot ∈ p.slots := by
      exact List.get_mem p.slots ⟨j, hjSlots⟩
    have hnewMem : newSlot ∈ st.slots := by
      exact List.get_mem st.slots ⟨i, hi⟩
    have holdRound := hpSlotsRound oldSlot holdMem
    have hnewRound := hcert.shape.slots_round newSlot hnewMem
    have hne : newSlot ≠ oldSlot := by
      intro hEq
      have hval := congrArg
        (fun s : GrayTailSlot n b => s.2.2.val) hEq
      change newSlot.2.2.val = oldSlot.2.2.val at hval
      rw [hnewRound, holdRound] at hval
      omega
    have hcd := not_prefixComparable_of_grandchild_slots hsm
      newSlot oldSlot hne hx (by simp) hcNew hdOld
    have hcoeff :
        (grayTailRoundCount q - 1 - st.frozen.length) + 1 ≤
          grayTailRoundCount q - 1 - p.roundIndex := by
      omega
    have hscale :
        grayTailRoundDelta q L e st.frozen.length ≤ p.epsDepth := by
      rw [hpDepth]
      unfold grayTailRoundDelta grayTailRoundEps
      rw [Nat.add_assoc]
      apply Nat.add_le_add_left
      have hmul := Nat.mul_le_mul_right L hcoeff
      simpa [Nat.add_mul] using hmul
    intro hca
    have hca' : c <+: a := by
      rcases hca with hca | hac
      · exact hca
      · have hacLength := hac.length_le
        have hacEq : a = c :=
          List.IsPrefix.eq_of_length hac (by omega)
        simp [hacEq]
    apply hcd
    rcases hdaComp with had | hda
    · exact Or.inl (hca'.trans had)
    · exact List.prefix_or_prefix_of_prefix hca' hda

/-- Along a traced history, the recorded server moves are exactly the moves of the future server. -/
lemma grayTailTrace_server_before {n b : ℕ}
    (q L e : ℕ) {sm : ℕ → FamilyServerMove} {t : ℕ}
    {st : GrayTailState n b}
    (hst : GrayTailTrace q L e sm t st)
    {j : ℕ} (hj : j < st.history.2.length) :
    grayTailServerOfList st.history.2 j =
      grayTailFutureServer q L e st sm j := by
  have hget := congrArg
    (fun l : List FamilyServerMove => l.getD j [])
    hst.servers_eq
  unfold grayTailServerOfList grayTailFutureServer
  rw [List.getD_eq_getElem _ _ hj]
  rw [← List.getD_eq_getElem st.history.2 [] hj]
  simpa [List.getD_eq_getElem?_getD, hj, List.getElem_ofFn] using hget

/-- The current move of a round is the move of the recursive family play at the current history
length. -/
lemma grayTailCurrentMove_eq_futurePlay {n b : ℕ}
    (q L e : ℕ) (sigma : FamilyStrategyScheme)
    {sm : ℕ → FamilyServerMove} {t : ℕ}
    {st : GrayTailState n b}
    (hhist : GrayTailHistoryOK q L e sigma st)
    (htrace : GrayTailTrace q L e sm t st) :
    grayTailCurrentMove q L e sigma st =
      playClientFamily st.unavailable st.slots.length
        (grayTailRoundStrategy q L e sigma st)
        (grayTailFutureServer q L e st sm)
        st.history.2.length := by
  rw [grayTailCurrentMove_eq_play q L e sigma st hhist]
  apply playClientFamily_congr_before
  intro j hj
  exact grayTailTrace_server_before q L e htrace hj

end Kolmogorov
