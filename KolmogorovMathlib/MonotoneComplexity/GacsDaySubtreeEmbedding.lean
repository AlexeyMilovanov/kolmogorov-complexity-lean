import KolmogorovMathlib.MonotoneComplexity.GacsDayFamilyGame

/-!
# Planting a family game inside one tree

This file supports the final Gacs-Day controller. It collects three pieces of
bookkeeping around the parallel family game of `GacsDayFamilyGame`:

* the measure ceiling for the gray area of a family play, and the resulting
  exclusion of the gray branch of the family winning condition;
* the move-level dictionary for planting the `i`-th tree of a family game below
  the root child `i` of one big tree, culminating in
  `isUniformWinningStrategy_of_familyUnservedWin`;
* the rounding of the integer request cap `1 / d` to a dyadic scale.

Nothing here changes the frozen statements of the game lane; the transfer
theorem is stated with the unserved branch of the family win as an explicit
hypothesis, which is exactly the semantic content still missing from the
parallel construction.
-/

namespace Kolmogorov

/-!
## Total mass bounds for the gray area

The gray cells of a family play live at depth `deltaDepth`, so their total mass
never exceeds the mass of the whole space. This is the measure-theoretic ceiling
used to rule out the gray branch of the family winning condition.
-/

/-- The new gray area has at most `2 ^ deltaDepth` cells. -/
lemma card_newGrayCells_le_two_pow (epsDepth deltaDepth : ℕ) (S U : Finset BitString) :
    (newGrayCells epsDepth deltaDepth S U).card ≤ 2 ^ deltaDepth := by
  classical
  calc (newGrayCells epsDepth deltaDepth S U).card
      ≤ (stringsOfLength deltaDepth).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ deltaDepth := card_stringsOfLength deltaDepth

/-- The gray mass of a family play is nonnegative. -/
lemma familyGrayMass_nonneg (epsDepth deltaDepth n T : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) :
    0 ≤ familyGrayMass epsDepth deltaDepth n T A sm := by
  unfold familyGrayMass
  positivity

/-- The gray mass of a family play is at most the mass of the whole space. -/
lemma familyGrayMass_le_one (epsDepth deltaDepth n T : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) :
    familyGrayMass epsDepth deltaDepth n T A sm ≤ 1 := by
  unfold familyGrayMass
  have hcard := card_newGrayCells_le_two_pow epsDepth deltaDepth
    (familyAllocated n T sm) A.toFinset
  have hQ : ((newGrayCells epsDepth deltaDepth (familyAllocated n T sm) A.toFinset).card : ℚ)
      ≤ (2 : ℚ) ^ deltaDepth := by exact_mod_cast hcard
  have hpos : (0 : ℚ) < (1 / 2 : ℚ) ^ deltaDepth := by positivity
  calc ((newGrayCells epsDepth deltaDepth (familyAllocated n T sm) A.toFinset).card : ℚ)
        * (1 / 2 : ℚ) ^ deltaDepth
      ≤ (2 : ℚ) ^ deltaDepth * (1 / 2 : ℚ) ^ deltaDepth := by nlinarith
    _ = 1 := by rw [← mul_pow]; norm_num

/-- If the demanded average gray mass exceeds the whole space, the gray branch of
the family winning condition is unreachable. -/
lemma not_familyGrayGoal_of_one_lt_target {kappa beta : ℚ} {epsDepth deltaDepth n : ℕ}
    {A : Allocation} {cm : ℕ → FamilyClientMove} {sm : ℕ → FamilyServerMove}
    (h : 1 < (n : ℚ) * beta) :
    ¬ familyGrayGoal kappa beta epsDepth deltaDepth n A cm sm := by
  rintro ⟨T, hT, -, -⟩
  exact absurd (hT.trans (familyGrayMass_le_one epsDepth deltaDepth n T A sm)) (by linarith)

/-- If the amplified root request always exceeds the whole space, the gray branch of
the family winning condition is unreachable. -/
lemma not_familyGrayGoal_of_one_lt_amplified {kappa beta : ℚ} {epsDepth deltaDepth n : ℕ}
    {A : Allocation} {cm : ℕ → FamilyClientMove} {sm : ℕ → FamilyServerMove}
    (h : ∀ T, 1 < kappa * totalRootRequest n (cm T)) :
    ¬ familyGrayGoal kappa beta epsDepth deltaDepth n A cm sm := by
  rintro ⟨T, -, hT, -⟩
  refine absurd (hT.trans (familyGrayMass_le_one epsDepth deltaDepth n T A sm)) ?_
  have := h T
  linarith

/-- A winning family strategy played against a family that is too large for the
gray branch must leave a permanently unserved request. -/
lemma familyClientWinsUnserved_of_spec_of_one_lt_target
    {kappa alpha beta : ℚ} {epsDepth deltaDepth h b n : ℕ} {A : Allocation}
    {σ : ClientFamilyStrategy}
    (hspec : GrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth h b n A σ)
    (hbig : 1 < (n : ℚ) * beta)
    (sm : ℕ → FamilyServerMove) (hsm : familyServerPlayLegal n b A sm) :
    familyClientWinsUnserved n h b (playClientFamily A n σ sm) sm := by
  rcases hspec.wins sm hsm with hw | hw
  · exact hw
  · exact absurd hw (not_familyGrayGoal_of_one_lt_target hbig)

/-- A strategy meeting the gray game specification with target mass above `1` wins with positive
unserved mass against every legal play. -/
lemma familyClientWinsUnservedPositive_of_spec_of_one_lt_target
    {kappa alpha beta : ℚ} {epsDepth deltaDepth h b n : ℕ} {A : Allocation}
    {σ : ClientFamilyStrategy}
    (hspec : GrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth h b n A σ)
    (hbig : 1 < (n : ℚ) * beta)
    (sm : ℕ → FamilyServerMove) (hsm : familyServerPlayLegal n b A sm) :
    familyClientWinsUnservedPositive n h b (playClientFamily A n σ sm) sm := by
  rcases hspec.wins_positively sm hsm with hw | hw
  · exact hw
  · exact absurd hw (not_familyGrayGoal_of_one_lt_target hbig)

/-!
## Embedding a family game into a single tree

The final controller plants the `i`-th tree of a family game below the root child
`i` of one big tree. This section provides the move-level dictionary for that
embedding: restriction of a single-tree server move to a root subtree, the lift of
a family client move to a single-tree client move, and the transfer of legality
and of the unserved win.
-/

/-- The part of a server move living below the root child `i`. -/
def serverMoveBelow (i : ℕ) (m : ServerMove) : ServerMove :=
  m.filterMap (fun p =>
    match p.1 with
    | [] => none
    | j :: z => if j = i then some (z, p.2) else none)

/-- The server move below `i` allocates at `x` what the original allocates at `i :: x`. -/
lemma getAlloc_serverMoveBelow (i : ℕ) (m : ServerMove) (x : GacsDayNode) :
    getAlloc (serverMoveBelow i m) x = getAlloc m (i :: x) := by
  induction m with
  | nil => simp [serverMoveBelow, getAlloc]
  | cons p rest ih =>
    obtain ⟨y, a⟩ := p
    cases y with
    | nil =>
      simp only [serverMoveBelow, List.filterMap_cons] at *
      simp only [getAlloc, List.lookup_cons] at *
      simpa using ih
    | cons j z =>
      by_cases hj : j = i
      · subst hj
        simp only [serverMoveBelow, List.filterMap_cons] at *
        simp only [getAlloc, List.lookup_cons] at *
        by_cases hx : x = z
        · subst hx; simp
        · have h1 : (x == z) = false := by simpa using hx
          simpa [List.lookup_cons, h1, hx] using ih
      · simp only [serverMoveBelow, List.filterMap_cons, if_neg hj] at *
        simp only [getAlloc, List.lookup_cons] at *
        have h2 : ((i :: x) == (j :: z)) = false := by simp [Ne.symm hj]
        simpa [h2] using ih

/-- The `n` root subtrees of a single-tree server play, read as a family server play. -/
def familyServerMovesBelow (n : ℕ) (sm : ℕ → ServerMove) : ℕ → FamilyServerMove :=
  fun t => List.ofFn (fun i : Fin n => serverMoveBelow i.val (sm t))

/-- Client `i` of the split family move receives the server move below the child `i`. -/
lemma familyServerMoveAt_below (n : ℕ) (sm : ℕ → ServerMove) (t : ℕ) {i : ℕ} (hi : i < n) :
    familyServerMoveAt (familyServerMovesBelow n sm t) i = serverMoveBelow i (sm t) := by
  unfold familyServerMoveAt familyServerMovesBelow
  rw [List.getD_eq_getElem?_getD]
  simp [hi]

/-- Client `i` of the split family move receives at `x` the allocation of `i :: x`. -/
lemma getFamilyAlloc_below (n : ℕ) (sm : ℕ → ServerMove) (t : ℕ) {i : ℕ} (hi : i < n)
    (x : GacsDayNode) :
    getFamilyAlloc (familyServerMovesBelow n sm t) i x = getAlloc (sm t) (i :: x) := by
  unfold getFamilyAlloc
  rw [familyServerMoveAt_below n sm t hi, getAlloc_serverMoveBelow]

/-- Restricting a legal play to the subtree below a child keeps it legal. -/
lemma serverPlayLegal_serverMoveBelow (b i : ℕ) (sm : ℕ → ServerMove)
    (hsm : serverPlayLegal b sm) :
    serverPlayLegal b (fun t => serverMoveBelow i (sm t)) := by
  constructor
  · intro t
    refine ⟨?_, ?_⟩
    · intro x c
      simp only [getAlloc_serverMoveBelow, ← List.cons_append]
      exact (hsm.1 t).1 (i :: x) c
    · intro x c1 c2 hc
      simp only [getAlloc_serverMoveBelow, ← List.cons_append]
      exact (hsm.1 t).2 (i :: x) c1 c2 hc
  · intro t x
    simp only [getAlloc_serverMoveBelow]
    exact hsm.2 t (i :: x)

/-- Any legal single-tree server play restricts to a legal family server play on the
first `n` root subtrees, with an empty unavailable set. Disjointness across the
family is exactly sibling disjointness at the root of the big tree. -/
lemma familyServerPlayLegal_below (n b : ℕ) (hnb : n ≤ b) (sm : ℕ → ServerMove)
    (hsm : serverPlayLegal b sm) :
    familyServerPlayLegal n b [] (familyServerMovesBelow n sm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hfun : (fun t => familyServerMoveAt (familyServerMovesBelow n sm t) i)
        = fun t => serverMoveBelow i (sm t) := by
      funext t; exact familyServerMoveAt_below n sm t hi
    rw [hfun]
    exact serverPlayLegal_serverMoveBelow b i sm hsm
  · intro t i hi j hj hij
    have hi' : i < b := lt_of_lt_of_le hi hnb
    have hj' : j < b := lt_of_lt_of_le hj hnb
    have h := (hsm.1 t).2 [] ⟨i, hi'⟩ ⟨j, hj'⟩ (by simpa using hij)
    simpa [getFamilyAlloc_below n sm t hi, getFamilyAlloc_below n sm t hj] using h
  · intro t i _ x c _ a ha
    simp at ha

/-- Transfer of the family win: a permanently unserved request in the `i`-th tree of
the restricted family play is a permanently unserved request at the node `i :: x`
of the big tree. -/
lemma clientWinsUnserved_of_familyClientWinsUnserved
    (n h b B : ℕ) (hnB : n ≤ B) (hbB : b ≤ B)
    (cm : ℕ → ClientMove) (fcm : ℕ → FamilyClientMove) (sm : ℕ → ServerMove)
    (hreq : ∀ t i, i < n → ∀ x, getReq (cm t) (i :: x) = getFamilyReq (fcm t) i x)
    (hwin : familyClientWinsUnserved n h b fcm (familyServerMovesBelow n sm)) :
    clientWinsUnserved (h + 1) B cm sm := by
  obtain ⟨i, hi, T, x, hlen, hdig, hfail⟩ := hwin
  refine ⟨T, i :: x, by simpa using Nat.succ_le_succ hlen, ?_, ?_⟩
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact lt_of_lt_of_le hi hnB
    · exact lt_of_lt_of_le (hdig a ha) hbB
  · intro t hserves
    refine hfail t ?_
    simp only [familyServerMoveAt_below n sm t hi, getAlloc_serverMoveBelow]
    rw [show getReq (familyClientMoveAt (fcm T) i) x = getReq (cm T) (i :: x) from
      (hreq T i hi x).symm]
    exact hserves

/-- The part of a client move living below the root child `i`. -/
def clientMoveBelow (i : ℕ) (m : ClientMove) : ClientMove :=
  m.filterMap (fun p =>
    match p.1 with
    | [] => none
    | j :: z => if j = i then some (z, p.2) else none)

/-- The client move below `i` requests at `x` what the original requests at `i :: x`. -/
lemma getReq_clientMoveBelow (i : ℕ) (m : ClientMove) (x : GacsDayNode) :
    getReq (clientMoveBelow i m) x = getReq m (i :: x) := by
  induction m with
  | nil => simp [clientMoveBelow, getReq]
  | cons p rest ih =>
    obtain ⟨y, q⟩ := p
    cases y with
    | nil =>
      simp only [clientMoveBelow, List.filterMap_cons] at *
      simp only [getReq, List.lookup_cons] at *
      simpa using ih
    | cons j z =>
      by_cases hj : j = i
      · subst hj
        simp only [clientMoveBelow, List.filterMap_cons] at *
        simp only [getReq, List.lookup_cons] at *
        by_cases hx : x = z
        · subst hx; simp
        · have h1 : (x == z) = false := by simpa using hx
          simpa [List.lookup_cons, h1, hx] using ih
      · simp only [clientMoveBelow, List.filterMap_cons, if_neg hj] at *
        simp only [getReq, List.lookup_cons] at *
        have h2 : ((i :: x) == (j :: z)) = false := by simp [Ne.symm hj]
        simpa [h2] using ih

/-- Looking up `i :: x` in a block prefixed by `j` succeeds only when `j = i`. -/
lemma lookup_map_cons (j : ℕ) (L : ClientMove) (i : ℕ) (x : GacsDayNode) :
    List.lookup (i :: x) (L.map (fun p => (j :: p.1, p.2))) =
      if j = i then List.lookup x L else none := by
  induction L with
  | nil => simp
  | cons p rest ih =>
    obtain ⟨y, q⟩ := p
    by_cases hj : j = i
    · subst hj
      by_cases hx : x = y
      · subst hx; simp
      · have h1 : (x == y) = false := by simpa using hx
        simp [List.lookup_cons, h1, ih]
    · have h2 : (i == j) = false := by simpa using Ne.symm hj
      simp [List.lookup_cons, hj, ih, h2]

/-- A node below a child outside the block list has no entry. -/
lemma lookup_flatMap_blocks_of_not_mem (l : List ℕ) (f : ℕ → ClientMove)
    (i : ℕ) (x : GacsDayNode) (hi : i ∉ l) :
    List.lookup (i :: x) (l.flatMap (fun j => (f j).map (fun p => (j :: p.1, p.2)))) = none := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hj : j ≠ i := by intro h; exact hi (by simp [h])
    have hi' : i ∉ l := fun h => hi (List.mem_cons_of_mem _ h)
    rw [List.flatMap_cons, List.lookup_append, lookup_map_cons, if_neg hj, ih hi']
    rfl

/-- Below a child of the block list, the assembled move reproduces that block. -/
lemma lookup_flatMap_blocks (l : List ℕ) (f : ℕ → ClientMove)
    (i : ℕ) (x : GacsDayNode) (hi : i ∈ l) (hnd : l.Nodup) :
    List.lookup (i :: x) (l.flatMap (fun j => (f j).map (fun p => (j :: p.1, p.2))))
      = List.lookup x (f i) := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rw [List.flatMap_cons, List.lookup_append, lookup_map_cons]
    rcases eq_or_ne j i with rfl | hj
    · rw [if_pos rfl]
      cases hx : List.lookup x (f j) with
      | some q => rfl
      | none =>
        rw [lookup_flatMap_blocks_of_not_mem l f j x (List.nodup_cons.mp hnd).1]
        rfl
    · rw [if_neg hj]
      have hi' : i ∈ l := by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h.symm hj
        · exact h
      rw [ih hi' (List.nodup_cons.mp hnd).2]
      rfl

/-- Lift a family client move into a single tree: the `i`-th tree is planted below
the root child `i`, and the root itself requests `r`. -/
def clientMoveLift (n : ℕ) (r : ℚ) (fcm : FamilyClientMove) : ClientMove :=
  (([] : GacsDayNode), r) ::
    (List.range n).flatMap (fun i => (familyClientMoveAt fcm i).map (fun p => (i :: p.1, p.2)))

/-- The lifted family move requests `r` at the root. -/
lemma getReq_clientMoveLift_root (n : ℕ) (r : ℚ) (fcm : FamilyClientMove) :
    getReq (clientMoveLift n r fcm) [] = r := by
  simp [clientMoveLift, getReq]

/-- Below the child `i` the lifted family move reproduces the move of client `i`. -/
lemma getReq_clientMoveLift_cons (n : ℕ) (r : ℚ) (fcm : FamilyClientMove)
    {i : ℕ} (hi : i < n) (x : GacsDayNode) :
    getReq (clientMoveLift n r fcm) (i :: x) = getFamilyReq fcm i x := by
  have hmem : i ∈ List.range n := List.mem_range.mpr hi
  simp only [clientMoveLift, getReq, getFamilyReq, List.lookup_cons]
  rw [show ((i :: x) == ([] : List ℕ)) = false by simp]
  rw [lookup_flatMap_blocks (List.range n) (fun j => familyClientMoveAt fcm j) i x hmem
    List.nodup_range]

/-- Below a child outside the family the lifted move requests nothing. -/
lemma getReq_clientMoveLift_cons_of_ge (n : ℕ) (r : ℚ) (fcm : FamilyClientMove)
    {i : ℕ} (hi : n ≤ i) (x : GacsDayNode) :
    getReq (clientMoveLift n r fcm) (i :: x) = 0 := by
  have hmem : i ∉ List.range n := by simp only [List.mem_range]; omega
  simp only [clientMoveLift, getReq, List.lookup_cons]
  rw [show ((i :: x) == ([] : List ℕ)) = false by simp]
  rw [lookup_flatMap_blocks_of_not_mem (List.range n) (fun j => familyClientMoveAt fcm j) i x hmem]

/-- The lift is monotone in the root request and in the family move. -/
lemma getReq_clientMoveLift_mono (n : ℕ) (r r' : ℚ) (fcm fcm' : FamilyClientMove)
    (hr : r ≤ r') (hfam : ∀ i, i < n → ∀ x, getFamilyReq fcm i x ≤ getFamilyReq fcm' i x)
    (y : GacsDayNode) :
    getReq (clientMoveLift n r fcm) y ≤ getReq (clientMoveLift n r' fcm') y := by
  cases y with
  | nil => rw [getReq_clientMoveLift_root, getReq_clientMoveLift_root]; exact hr
  | cons i x =>
    by_cases hi : i < n
    · rw [getReq_clientMoveLift_cons n r fcm hi x, getReq_clientMoveLift_cons n r' fcm' hi x]
      exact hfam i hi x
    · rw [getReq_clientMoveLift_cons_of_ge n r fcm (Nat.le_of_not_lt hi) x,
        getReq_clientMoveLift_cons_of_ge n r' fcm' (Nat.le_of_not_lt hi) x]

/-- A sum over `Fin B` collapses to a sum over `Fin m` when the summand vanishes above `m`. -/
lemma sum_fin_eq_sum_fin_of_vanishing (m B : ℕ) (hmB : m ≤ B) (g : ℕ → ℚ)
    (hg : ∀ c, m ≤ c → g c = 0) :
    ∑ c : Fin B, g c.val = ∑ c : Fin m, g c.val := by
  rw [Fin.sum_univ_eq_sum_range (fun c => g c) B, Fin.sum_univ_eq_sum_range (fun c => g c) m]
  refine (Finset.sum_subset (s₁ := Finset.range m) (s₂ := Finset.range B)
    (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hmB)) ?_).symm
  intro c _ hc
  exact hg c (by simpa [Finset.mem_range] using hc)

/-- A sum of `m` terms each at most `alpha` is at most `m * alpha`. -/
lemma sum_fin_le_card_mul (m : ℕ) (g : ℕ → ℚ) (alpha : ℚ) (hg : ∀ c, c < m → g c ≤ alpha) :
    ∑ c : Fin m, g c.val ≤ (m : ℚ) * alpha := by
  calc ∑ c : Fin m, g c.val ≤ ∑ _c : Fin m, alpha :=
        Finset.sum_le_sum (fun c _ => hg c.val c.isLt)
    _ = (m : ℚ) * alpha := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Coherence of a lifted family move in the big tree: the root pays for the `n`
planted roots, and every deeper node inherits the coherence of its own tree. The
branching factor `B` of the big tree may exceed both the family size `n` and the
branching factor `b` of the family game. -/
lemma requestCoherent_clientMoveLift (n b B d : ℕ) (hnB : n ≤ B) (hbB : b ≤ B)
    (alpha r : ℚ) (hr0 : 0 ≤ r) (hcap : r ≤ 1 / (d : ℚ)) (hsum : (n : ℚ) * alpha ≤ r)
    (fcm : FamilyClientMove)
    (hcoh : ∀ i, i < n → requestCoherentCap b alpha (familyClientMoveAt fcm i))
    (hrange : ∀ i, i < n → ∀ (x : GacsDayNode) (c : ℕ), b ≤ c →
      getReq (familyClientMoveAt fcm i) (x ++ [c]) = 0) :
    requestCoherent B d (clientMoveLift n r fcm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    cases y with
    | nil => rw [getReq_clientMoveLift_root]; exact hr0
    | cons i x =>
      by_cases hi : i < n
      · rw [getReq_clientMoveLift_cons n r fcm hi x]; exact (hcoh i hi).1 x
      · rw [getReq_clientMoveLift_cons_of_ge n r fcm (Nat.le_of_not_lt hi) x]
  · rw [getReq_clientMoveLift_root]; exact hcap
  · intro y
    cases y with
    | nil =>
      rw [getReq_clientMoveLift_root, ge_iff_le]
      have hzero : ∀ c, n ≤ c → getReq (clientMoveLift n r fcm) (([] : GacsDayNode) ++ [c]) = 0 :=
        fun c hc => getReq_clientMoveLift_cons_of_ge n r fcm hc []
      rw [sum_fin_eq_sum_fin_of_vanishing n B hnB
        (fun c => getReq (clientMoveLift n r fcm) (([] : GacsDayNode) ++ [c])) hzero]
      refine le_trans (sum_fin_le_card_mul n
        (fun c => getReq (clientMoveLift n r fcm) (([] : GacsDayNode) ++ [c])) alpha ?_) hsum
      intro c hc
      have hc' : getReq (clientMoveLift n r fcm) (([] : GacsDayNode) ++ [c])
          = getFamilyReq fcm c [] := getReq_clientMoveLift_cons n r fcm hc []
      simp only []
      rw [hc']
      exact (hcoh c hc).2.1
    | cons i x =>
      by_cases hi : i < n
      · rw [getReq_clientMoveLift_cons n r fcm hi x, ge_iff_le]
        have hzero : ∀ c, b ≤ c → getReq (clientMoveLift n r fcm) ((i :: x) ++ [c]) = 0 := by
          intro c hc
          change getReq (clientMoveLift n r fcm) (i :: (x ++ [c])) = 0
          rw [getReq_clientMoveLift_cons n r fcm hi (x ++ [c])]
          exact hrange i hi x c hc
        rw [sum_fin_eq_sum_fin_of_vanishing b B hbB
          (fun c => getReq (clientMoveLift n r fcm) ((i :: x) ++ [c])) hzero]
        have hcongr : ∀ c : Fin b, getReq (clientMoveLift n r fcm) ((i :: x) ++ [c.val])
            = getReq (familyClientMoveAt fcm i) (x ++ [c.val]) := by
          intro c
          change getReq (clientMoveLift n r fcm) (i :: (x ++ [c.val])) = _
          rw [getReq_clientMoveLift_cons n r fcm hi (x ++ [c.val])]
          rfl
        rw [Finset.sum_congr rfl (fun c _ => hcongr c)]
        exact (hcoh i hi).2.2 x
      · rw [getReq_clientMoveLift_cons_of_ge n r fcm (Nat.le_of_not_lt hi) x, ge_iff_le]
        have hzero : ∀ c : Fin B, getReq (clientMoveLift n r fcm) ((i :: x) ++ [c.val]) = 0 := by
          intro c
          change getReq (clientMoveLift n r fcm) (i :: (x ++ [c.val])) = 0
          exact getReq_clientMoveLift_cons_of_ge n r fcm (Nat.le_of_not_lt hi) (x ++ [c.val])
        rw [Finset.sum_congr rfl (fun c _ => hzero c)]
        simp

/-- Coherence at a branching passes to any smaller branching. -/
lemma serverMoveCoherent_mono_branching {b B : ℕ} (hbB : b ≤ B) {m : ServerMove}
    (hm : serverMoveCoherent B m) : serverMoveCoherent b m := by
  refine ⟨?_, ?_⟩
  · intro x c
    exact hm.1 x ⟨c.val, lt_of_lt_of_le c.isLt hbB⟩
  · intro x c1 c2 hc
    exact hm.2 x ⟨c1.val, lt_of_lt_of_le c1.isLt hbB⟩ ⟨c2.val, lt_of_lt_of_le c2.isLt hbB⟩
      (by simpa [Fin.ext_iff] using fun hEq => hc (Fin.ext hEq))

/-- Legality at a branching passes to any smaller branching. -/
lemma serverPlayLegal_mono_branching {b B : ℕ} (hbB : b ≤ B) {sm : ℕ → ServerMove}
    (hsm : serverPlayLegal B sm) : serverPlayLegal b sm :=
  ⟨fun t => serverMoveCoherent_mono_branching hbB (hsm.1 t), hsm.2⟩

/-- The root subtrees of a legal single-tree play form a legal family play, even when
the family game uses a smaller branching factor than the big tree. -/
lemma familyServerPlayLegal_below_of_le (n b B : ℕ) (hnB : n ≤ B) (hbB : b ≤ B)
    (sm : ℕ → ServerMove) (hsm : serverPlayLegal B sm) :
    familyServerPlayLegal n b [] (familyServerMovesBelow n sm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hfun : (fun t => familyServerMoveAt (familyServerMovesBelow n sm t) i)
        = fun t => serverMoveBelow i (sm t) := by
      funext t; exact familyServerMoveAt_below n sm t hi
    rw [hfun]
    exact serverPlayLegal_mono_branching hbB (serverPlayLegal_serverMoveBelow B i sm hsm)
  · intro t i hi j hj hij
    have hi' : i < B := lt_of_lt_of_le hi hnB
    have hj' : j < B := lt_of_lt_of_le hj hnB
    have h := (hsm.1 t).2 [] ⟨i, hi'⟩ ⟨j, hj'⟩ (by simpa using hij)
    simpa [getFamilyAlloc_below n sm t hi, getFamilyAlloc_below n sm t hj] using h
  · intro t i _ x c _ a ha
    simp at ha

/-- A family play at time `t` depends only on the server moves before `t`. -/
lemma playClientFamily_congr (A : Allocation) (n : ℕ) (σ : ClientFamilyStrategy)
    {sm sm' : ℕ → FamilyServerMove} :
    ∀ t, (∀ s, s < t → sm s = sm' s) →
      playClientFamily A n σ sm t = playClientFamily A n σ sm' t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    cases t with
    | zero => intro _; simp only [playClientFamily]
    | succ t =>
      intro h
      have hc : (fun i : Fin (t + 1) => playClientFamily A n σ sm i.val)
          = fun i : Fin (t + 1) => playClientFamily A n σ sm' i.val :=
        funext fun i => ih i.val (by omega) (fun s hs => h s (by omega))
      have hs : (fun i : Fin (t + 1) => sm i.val) = fun i : Fin (t + 1) => sm' i.val :=
        funext fun i => h i.val i.isLt
      simp only [playClientFamily, hc, hs]

/-- Every move of a family play is the strategy applied to some history. -/
lemma playClientFamily_eq_strategy_apply (A : Allocation) (n : ℕ) (σ : ClientFamilyStrategy)
    (sm : ℕ → FamilyServerMove) (t : ℕ) :
    ∃ hist : FamilyGameHistory, playClientFamily A n σ sm t = σ A n hist := by
  cases t with
  | zero => exact ⟨([], []), by simp only [playClientFamily]⟩
  | succ t =>
    exact ⟨(List.ofFn (fun i : Fin (t + 1) => playClientFamily A n σ sm i.val),
      List.ofFn (fun i : Fin (t + 1) => sm i.val)), by simp only [playClientFamily]⟩

/-- The single-tree strategy that plants the `n` trees of a family strategy below the
root children `0, …, n-1` and requests `r` at the root itself. The family play is
recomputed from the server part of the history, so the lift never has to be inverted. -/
def liftFamilyStrategy (n : ℕ) (r : ℚ) (σf : ClientFamilyStrategy) : ClientStrategy :=
  fun hist => clientMoveLift n r
    (playClientFamily [] n σf (familyServerMovesBelow n (fun s => hist.2.getD s []))
      hist.2.length)

/-- The lifted family strategy plays the lift of the family play against the split server moves. -/
lemma playClient_liftFamilyStrategy (n : ℕ) (r : ℚ) (σf : ClientFamilyStrategy)
    (sm : ℕ → ServerMove) (t : ℕ) :
    playClient (liftFamilyStrategy n r σf) sm t
      = clientMoveLift n r (playClientFamily [] n σf (familyServerMovesBelow n sm) t) := by
  cases t with
  | zero =>
    simp only [playClient, liftFamilyStrategy]
    congr 1
    exact playClientFamily_congr [] n σf 0 (by intro s hs; omega)
  | succ t =>
    simp only [playClient, liftFamilyStrategy]
    have hlen : (List.ofFn (fun i : Fin (t + 1) => sm i.val)).length = t + 1 := by simp
    have hagree : ∀ s, s < t + 1 →
        familyServerMovesBelow n
          (fun s => (List.ofFn (fun i : Fin (t + 1) => sm i.val)).getD s []) s
          = familyServerMovesBelow n sm s := by
      intro s hs
      have hs' : s < (List.ofFn (fun i : Fin (t + 1) => sm i.val)).length := by simpa using hs
      have hget : (List.ofFn (fun i : Fin (t + 1) => sm i.val)).getD s [] = sm s := by
        rw [List.getD_eq_getElem _ _ hs', List.getElem_ofFn]
      simp only [familyServerMovesBelow, hget]
    rw [hlen]
    congr 1
    exact playClientFamily_congr [] n σf (t + 1) hagree

/-- **Transfer of a family game into the single-tree game.** If a family strategy is
legal, range supported and always forces a permanently unserved request, then planting
its `n` trees below the root children of one big tree yields a uniform winning strategy
for the single-tree game of height `h + 1`, branching `B` and request cap `1 / d`.

Only the unserved branch of the family winning condition is used; the gray branch,
which is the remaining semantic content of the parallel construction, enters through
the hypothesis `hunserved`. -/
theorem isUniformWinningStrategy_of_familyUnservedWin
    {kappa alpha beta : ℚ} {epsDepth deltaDepth h b n B d : ℕ} {r : ℚ}
    {σf : ClientFamilyStrategy}
    (hnB : n ≤ B) (hbB : b ≤ B)
    (hr0 : 0 ≤ r) (hcap : r ≤ 1 / (d : ℚ)) (hsum : (n : ℚ) * alpha ≤ r)
    (hspec : GrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth h b n [] σf)
    (hunserved : ∀ sm : ℕ → FamilyServerMove, familyServerPlayLegal n b [] sm →
      familyClientWinsUnserved n h b (playClientFamily [] n σf sm) sm) :
    IsUniformWinningStrategy (h + 1) B d (liftFamilyStrategy n r σf) := by
  constructor
  · intro sm hsm
    have hfam := familyServerPlayLegal_below_of_le n b B hnB hbB sm hsm
    have hplay := hspec.legal _ hfam
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro t
      rw [playClient_liftFamilyStrategy]
      refine requestCoherent_clientMoveLift n b B d hnB hbB alpha r hr0 hcap hsum _
        (fun i hi => hplay.1 t i hi) ?_
      intro i hi x c hc
      obtain ⟨hist, hhist⟩ :=
        playClientFamily_eq_strategy_apply [] n σf (familyServerMovesBelow n sm) t
      rw [hhist]
      exact hspec.range_supported hist x c hc i hi
    · intro t x
      rw [playClient_liftFamilyStrategy, playClient_liftFamilyStrategy]
      exact getReq_clientMoveLift_mono n r r _ _ le_rfl (fun i hi y => hplay.2 t i hi y) x
    · refine clientWinsUnserved_of_familyClientWinsUnserved n h b B hnB hbB _ _ sm ?_
        (hunserved _ hfam)
      intro t i hi x
      rw [playClient_liftFamilyStrategy, getReq_clientMoveLift_cons n r _ hi x]
  · intro hist x i hBi
    unfold liftFamilyStrategy
    cases x with
    | nil => exact getReq_clientMoveLift_cons_of_ge n r _ (le_trans hnB hBi) []
    | cons j y =>
      by_cases hj : j < n
      · change getReq (clientMoveLift n r _) (j :: (y ++ [i])) = 0
        rw [getReq_clientMoveLift_cons n r _ hj]
        obtain ⟨hist', hhist⟩ :=
          playClientFamily_eq_strategy_apply [] n σf
            (familyServerMovesBelow n (fun s => hist.2.getD s [])) hist.2.length
        rw [show getFamilyReq _ j (y ++ [i]) = getReq (familyClientMoveAt _ j) (y ++ [i]) from rfl,
          hhist]
        exact hspec.range_supported hist' y i (le_trans hbB hBi) j hj
      · change getReq (clientMoveLift n r _) (j :: (y ++ [i])) = 0
        exact getReq_clientMoveLift_cons_of_ge n r _ (Nat.le_of_not_lt hj) _

/-!
## Dyadic scale bookkeeping

The single-tree game caps the root request by `1 / d` for a natural number `d`,
while the family game caps it by the dyadic number `dyadicScale a`. These lemmas
round `d` to a dyadic scale.
-/

/-- The dyadic scale is positive. -/
lemma dyadicScale_pos (a : ℕ) : 0 < dyadicScale a := by
  unfold dyadicScale; positivity

/-- The dyadic scale decreases as the depth grows. -/
lemma dyadicScale_antitone {a a' : ℕ} (h : a ≤ a') : dyadicScale a' ≤ dyadicScale a := by
  unfold dyadicScale
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- A positive number has binary size at least `1`. -/
lemma one_le_size_of_one_le {d : ℕ} (hd : 1 ≤ d) : 1 ≤ Nat.size d := by
  by_contra hlt
  have h0 : Nat.size d = 0 := by omega
  have : d = 0 := Nat.size_eq_zero.mp h0
  omega

/-- `Nat.size d` is a dyadic scale fine enough for the cap `1 / d`. -/
lemma dyadicScale_size_le_inv (d : ℕ) (hd : 1 ≤ d) : dyadicScale (Nat.size d) ≤ 1 / (d : ℚ) := by
  have hlt : d < 2 ^ Nat.size d := Nat.lt_size_self d
  have hdQ : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hpow : (d : ℚ) ≤ (2 : ℚ) ^ Nat.size d := by
    have : (d : ℚ) < (2 : ℚ) ^ Nat.size d := by exact_mod_cast hlt
    exact this.le
  have hpowpos : (0 : ℚ) < (2 : ℚ) ^ Nat.size d := by positivity
  unfold dyadicScale
  rw [div_pow, one_pow]
  exact one_div_le_one_div_of_le hdQ hpow

end Kolmogorov
