import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayWitness

/-!
# The first amplification stage above the base case

The base case `grayFamilyGameSpec_base` of the Gacs-Day induction wins with
amplification `kappa = 1`: the client asks `alpha = 2 ^ (-a)` at the root of
every tree of the family, and a server that serves all of them must allocate
`n * alpha` of pairwise incompatible mass, which is exactly the total request.

This file proves the next stage of the ladder, `kappa = 3 / 2`, unconditionally
and with an explicit static strategy. The mechanism is the rounding-up built
into `Serves`: a request is served by a *single* cylinder of at least the
requested mass, so a request of `alpha / 2 + 2 ^ (-D)` costs the server a whole
cylinder of mass `alpha`. The client therefore splits its root budget over the
two root children as

  `alpha / 2 + 2 ^ (-D)`  and  `alpha / 2 - 2 ^ (-D)`,

which is legal (the two add up to exactly `alpha`) and forces two incompatible
cylinders of masses `alpha` and `alpha / 2`, i.e. gray mass `(3 / 2) * alpha`
per tree. Source: SUV pp. 143-144.
-/

namespace Kolmogorov

/-- The static client move of the first amplification stage: `2 ^ (-a)` at the
root, and the two unequal halves `2 ^ (-a-1) ± 2 ^ (-D)` at the two root
children. -/
def halfStepMove (a D : ℕ) : ClientMove :=
  [(([] : GacsDayNode), (1 / 2 : ℚ) ^ a),
   (([0] : GacsDayNode), (1 / 2 : ℚ) ^ (a + 1) + (1 / 2 : ℚ) ^ D),
   (([1] : GacsDayNode), (1 / 2 : ℚ) ^ (a + 1) - (1 / 2 : ℚ) ^ D)]

/-- Every tree of the family plays `halfStepMove` at every stage. -/
def halfStepFamilyStrategy (a D : ℕ) : ClientFamilyStrategy :=
  fun _A n _hist => List.replicate n (halfStepMove a D)

/-- The half-step move requests `2 ^ (-a)` at the root. -/
@[simp] lemma getReq_halfStepMove_nil (a D : ℕ) :
    getReq (halfStepMove a D) [] = (1 / 2 : ℚ) ^ a := rfl

/-- The half-step move requests `2 ^ (-(a+1)) + 2 ^ (-D)` at the child `0`. -/
@[simp] lemma getReq_halfStepMove_zero (a D : ℕ) :
    getReq (halfStepMove a D) [0] = (1 / 2 : ℚ) ^ (a + 1) + (1 / 2 : ℚ) ^ D := rfl

/-- The half-step move requests `2 ^ (-(a+1)) - 2 ^ (-D)` at the child `1`. -/
@[simp] lemma getReq_halfStepMove_one (a D : ℕ) :
    getReq (halfStepMove a D) [1] = (1 / 2 : ℚ) ^ (a + 1) - (1 / 2 : ℚ) ^ D := rfl

/-- Away from the root and its two children the half-step move requests nothing. -/
lemma getReq_halfStepMove_eq_zero {a D : ℕ} {x : GacsDayNode}
    (h0 : x ≠ []) (h1 : x ≠ [0]) (h2 : x ≠ [1]) :
    getReq (halfStepMove a D) x = 0 := by
  have e0 : (x == ([] : GacsDayNode)) = false := by simpa using h0
  have e1 : (x == ([0] : GacsDayNode)) = false := by simpa using h1
  have e2 : (x == ([1] : GacsDayNode)) = false := by simpa using h2
  simp [getReq, halfStepMove, List.lookup, e0, e1, e2]

/-- Outside the root and its first two children nothing is requested; in
particular nothing is requested below depth `1`. -/
lemma getReq_halfStepMove_of_two_le_length {a D : ℕ} {x : GacsDayNode}
    (hx : 2 ≤ x.length) : getReq (halfStepMove a D) x = 0 := by
  refine getReq_halfStepMove_eq_zero ?_ ?_ ?_ <;>
    · intro h; rw [h] at hx; simp at hx

/-- Every client of the half-step family strategy plays the same half-step move. -/
lemma familyClientMoveAt_halfStepFamilyStrategy (a D : ℕ) (A : Allocation) (n : ℕ)
    (hist : FamilyGameHistory) {i : ℕ} (hi : i < n) :
    familyClientMoveAt (halfStepFamilyStrategy a D A n hist) i = halfStepMove a D := by
  unfold familyClientMoveAt halfStepFamilyStrategy
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp [hi]

/-- The half-step family strategy plays, at every time, `n` copies of the half-step move. -/
lemma playClientFamily_halfStep (a D : ℕ) (A : Allocation) (n : ℕ)
    (sm : ℕ → FamilyServerMove) (t : ℕ) :
    playClientFamily A n (halfStepFamilyStrategy a D) sm t =
      List.replicate n (halfStepMove a D) := by
  cases t <;> simp [playClientFamily, halfStepFamilyStrategy]

/-- Each client of a half-step play requests, at every node, what the half-step move requests
there. -/
lemma halfStep_getReq (a D : ℕ) (A : Allocation) (n : ℕ) (sm : ℕ → FamilyServerMove)
    (t : ℕ) {i : ℕ} (hi : i < n) (x : GacsDayNode) :
    getReq (familyClientMoveAt (playClientFamily A n (halfStepFamilyStrategy a D) sm t) i) x =
      getReq (halfStepMove a D) x := by
  rw [playClientFamily_halfStep]
  have hrep : List.replicate n (halfStepMove a D) = halfStepFamilyStrategy a D A n ([], []) := rfl
  rw [hrep, familyClientMoveAt_halfStepFamilyStrategy a D A n ([], []) hi]

/-- A request strictly larger than `2 ^ (-(m+1))` can only be served by a
cylinder of length at most `m`. This is the rounding-up that creates the waste
counted by the gray area. -/
lemma length_le_of_serves {alloc : Allocation} {q : ℚ} {m : ℕ}
    (hq : (1 / 2 : ℚ) ^ (m + 1) < q) (h : Serves alloc q) :
    ∃ c ∈ alloc, c.length ≤ m := by
  obtain ⟨c, hc, hle⟩ := h
  refine ⟨c, hc, ?_⟩
  by_contra hlen
  push Not at hlen
  have h1 : (1 / 2 : ℝ) ^ c.length ≤ (1 / 2 : ℝ) ^ (m + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hlen
  have h2 : (((1 / 2 : ℚ) ^ (m + 1) : ℚ) : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h3 : (((1 / 2 : ℚ) ^ (m + 1) : ℚ) : ℝ) = (1 / 2 : ℝ) ^ (m + 1) := by push_cast; ring
  rw [h3] at h2
  linarith

/-- All requests of the half-step move are nonnegative. -/
lemma getReq_halfStepMove_nonneg {a D : ℕ} (hD : a + 1 ≤ D) (x : GacsDayNode) :
    0 ≤ getReq (halfStepMove a D) x := by
  have hle : (1 / 2 : ℚ) ^ D ≤ (1 / 2 : ℚ) ^ (a + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hD
  by_cases h0 : x = []
  · rw [h0, getReq_halfStepMove_nil]; positivity
  by_cases h1 : x = [0]
  · rw [h1, getReq_halfStepMove_zero]; positivity
  by_cases h2 : x = [1]
  · rw [h2, getReq_halfStepMove_one]; linarith
  · rw [getReq_halfStepMove_eq_zero h0 h1 h2]

/-- The half-step move is coherent: the two children of the root ask for exactly
the root request, and every other node asks for nothing below itself. -/
lemma sum_getReq_halfStepMove_children {a D : ℕ} (hD : a + 1 ≤ D) (x : GacsDayNode) :
    ∑ c : Fin 2, getReq (halfStepMove a D) (x ++ [c.val]) ≤ getReq (halfStepMove a D) x := by
  rw [Fin.sum_univ_two]
  by_cases h0 : x = []
  · subst h0
    have hz : getReq (halfStepMove a D) ([] ++ [((0 : Fin 2) : ℕ)])
        = (1 / 2 : ℚ) ^ (a + 1) + (1 / 2 : ℚ) ^ D := by simp
    have ho : getReq (halfStepMove a D) ([] ++ [((1 : Fin 2) : ℕ)])
        = (1 / 2 : ℚ) ^ (a + 1) - (1 / 2 : ℚ) ^ D := by simp
    rw [hz, ho, getReq_halfStepMove_nil, pow_add]
    ring_nf
    norm_num
  · have hxlen : 1 ≤ x.length := List.length_pos_iff.mpr h0
    have hz : ∀ c : Fin 2, getReq (halfStepMove a D) (x ++ [(c : ℕ)]) = 0 := by
      intro c
      refine getReq_halfStepMove_of_two_le_length ?_
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hz 0, hz 1, add_zero]
    exact getReq_halfStepMove_nonneg hD x

/-- The half-step family strategy is a legal client strategy for any server play. -/
private lemma halfStepFamilyStrategy_legal (a D : ℕ) (hDa : a + 1 ≤ D) (n : ℕ)
    (A : Allocation) (sm : ℕ → FamilyServerMove) :
    familyClientPlayLegal n 2 (dyadicScale a)
      (playClientFamily A n (halfStepFamilyStrategy a D) sm) := by
  constructor
  · intro t i hi
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [halfStep_getReq a D A n sm t hi x]
      exact getReq_halfStepMove_nonneg hDa x
    · rw [halfStep_getReq a D A n sm t hi [], getReq_halfStepMove_nil]
      simp [dyadicScale]
    · intro x
      rw [halfStep_getReq a D A n sm t hi x]
      have hchild : ∀ c : Fin 2,
          getReq (familyClientMoveAt
            (playClientFamily A n (halfStepFamilyStrategy a D) sm t) i) (x ++ [c.val])
            = getReq (halfStepMove a D) (x ++ [c.val]) :=
        fun c => halfStep_getReq a D A n sm t hi (x ++ [c.val])
      rw [Finset.sum_congr rfl (fun c _ => hchild c)]
      exact sum_getReq_halfStepMove_children hDa x
  · intro t i hi x
    simp only [getFamilyReq]
    rw [halfStep_getReq a D A n sm t hi x, halfStep_getReq a D A n sm (t + 1) hi x]

/-- The half-step family strategy requests either nothing or at least `2 ^ (-D)` at every node. -/
private lemma halfStepFamilyStrategy_minimum_request (a D : ℕ)
    (ht8 : (1 / 2 : ℚ) ^ D ≤ (1 / 2 : ℚ) ^ a / 8) (n : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (t : ℕ) :
    familyRequestAvoidsSmall n ((1 / 2 : ℚ) ^ D)
      (playClientFamily A n (halfStepFamilyStrategy a D) sm t) := by
  have htpos : (0 : ℚ) < (1 / 2 : ℚ) ^ D := by positivity
  have hhalf : (1 / 2 : ℚ) ^ (a + 1) = (1 / 2 : ℚ) ^ a / 2 := by rw [pow_add]; ring
  intro i hi x
  rw [halfStep_getReq a D A n sm t hi x]
  by_cases h0 : x = []
  · refine Or.inr ?_
    rw [h0, getReq_halfStepMove_nil]
    linarith
  by_cases h1 : x = [0]
  · refine Or.inr ?_
    rw [h1, getReq_halfStepMove_zero]
    linarith
  by_cases h2 : x = [1]
  · refine Or.inr ?_
    rw [h2, getReq_halfStepMove_one]
    linarith
  · exact Or.inl (getReq_halfStepMove_eq_zero h0 h1 h2)

/-- If the client does not win unserved, all root child requests are eventually served. -/
private lemma halfStep_serves_of_not_wins_unserved (a D : ℕ) (n : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove)
    (hwin : ¬ familyClientWinsUnserved n 2 2
      (playClientFamily A n (halfStepFamilyStrategy a D) sm) sm) :
    ∀ p : Fin n × Fin 2, ∃ s : ℕ,
      Serves (getFamilyAlloc (sm s) p.1.val [p.2.val])
        (getReq (halfStepMove a D) [p.2.val]) := by
  rintro ⟨i, j⟩
  by_contra hcon
  push Not at hcon
  refine hwin ⟨i.val, i.isLt, 0, [j.val], by simp, ?_, ?_⟩
  · intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact j.isLt
  · intro s
    rw [halfStep_getReq a D A n sm 0 i.isLt]
    exact hcon s

/-- If the client does not win unserved with positive requests, all root child requests are
eventually served. -/
private lemma halfStep_serves_of_not_wins_unserved_positive (a e : ℕ) (hae : a ≤ e) (n : ℕ)
    (A : Allocation) (sm : ℕ → FamilyServerMove)
    (hwin : ¬ familyClientWinsUnservedPositive n 2 2
      (playClientFamily A n (halfStepFamilyStrategy a (e + 3)) sm) sm) :
    ∀ p : Fin n × Fin 2, ∃ s : ℕ,
      Serves (getFamilyAlloc (sm s) p.1.val [p.2.val])
        (getReq (halfStepMove a (e + 3)) [p.2.val]) := by
  set D := e + 3 with hD
  rintro ⟨i, j⟩
  by_contra hcon
  push Not at hcon
  refine hwin ⟨i.val, i.isLt, 0, [j.val], by simp, ?_, ?_, ?_⟩
  · intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact j.isLt
  · intro s
    rw [halfStep_getReq a D A n sm 0 i.isLt]
    exact hcon s
  · rw [halfStep_getReq a D A n sm 0 i.isLt]
    by_cases hj : j.val = 0
    · rw [hj, getReq_halfStepMove_zero]
      positivity
    · have hj1 : j.val = 1 := by have hjlt := j.isLt; omega
      rw [hj1, getReq_halfStepMove_one]
      have hDstrict : a + 1 < D := by omega
      have hstrict : (1 / 2 : ℚ) ^ D < (1 / 2 : ℚ) ^ (a + 1) :=
        pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hDstrict
      linarith

/-- If all root child requests are eventually served, the half-step strategy achieves the
gray mass goal. -/
private lemma halfStep_familyGrayGoal_of_serves (a e : ℕ) (hae : a ≤ e) (n : ℕ) (hn : 1 ≤ n)
    (A : Allocation) (sm : ℕ → FamilyServerMove) (hsm : familyServerPlayLegal n 2 A sm)
    (hserve : ∀ p : Fin n × Fin 2, ∃ s : ℕ,
      Serves (getFamilyAlloc (sm s) p.1.val [p.2.val])
        (getReq (halfStepMove a (e + 3)) [p.2.val])) :
    familyGrayGoal (halfAmplification 1) ((3 / 4 : ℚ) * dyadicScale a) e (e + 3) n A
      (playClientFamily A n (halfStepFamilyStrategy a (e + 3)) sm) sm := by
  set D := e + 3 with hD
  have halpha : (0 : ℚ) < (1 / 2 : ℚ) ^ a := by positivity
  have htpos : (0 : ℚ) < (1 / 2 : ℚ) ^ D := by positivity
  have ht8 : (1 / 2 : ℚ) ^ D ≤ (1 / 2 : ℚ) ^ a / 8 := by
    have h1 : (1 / 2 : ℚ) ^ D ≤ (1 / 2 : ℚ) ^ (a + 3) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (1 / 2 : ℚ) ^ (a + 3) = (1 / 2 : ℚ) ^ a / 8 := by
      rw [pow_add]; ring
    linarith [h1, h2.le, h2.ge]
  have hhalf : (1 / 2 : ℚ) ^ (a + 1) = (1 / 2 : ℚ) ^ a / 2 := by rw [pow_add]; ring
  have hquart : (1 / 2 : ℚ) ^ (a + 2) = (1 / 2 : ℚ) ^ a / 4 := by rw [pow_add]; ring
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
  choose tt htt using hserve
  set T := Finset.univ.sup tt with hT
  have hservesT : ∀ p : Fin n × Fin 2,
      Serves (getFamilyAlloc (sm T) p.1.val [p.2.val])
        (getReq (halfStepMove a D) [p.2.val]) := by
    intro p
    exact serves_mono_time (hsm.1 p.1.val p.1.isLt) (Finset.le_sup (Finset.mem_univ p)) (htt p)
  -- each of them forces a short cylinder
  have hcell : ∀ p : Fin n × Fin 2, ∃ c ∈ getFamilyAlloc (sm T) p.1.val [p.2.val],
      c.length ≤ a + p.2.val := by
    rintro ⟨i, j⟩
    have h := hservesT (i, j)
    match j with
    | ⟨0, _⟩ =>
      refine length_le_of_serves ?_ h
      simp only [getReq_halfStepMove_zero]
      linarith
    | ⟨1, _⟩ =>
      refine length_le_of_serves ?_ h
      simp only [getReq_halfStepMove_one]
      rw [show a + 1 + 1 = a + 2 from rfl, hquart]
      linarith
  choose c hc_mem hc_len using hcell
  -- the cylinders are pairwise incompatible, sit below the root allocations and avoid `A`
  have hroot_sub : ∀ (i : Fin n) (j : Fin 2), ∀ z ∈ getFamilyAlloc (sm T) i.val [j.val],
      ∃ y ∈ getFamilyAlloc (sm T) i.val [], y <+: z := by
    intro i j z hz
    have hco := (hsm.1 i.val i.isLt).1 T
    have h1 := hco.1 [] j z hz
    exact h1
  have hanc : ∀ p : Fin n × Fin 2, ∃ y ∈ familyAllocated n T sm, y <+: c p := by
    rintro ⟨i, j⟩
    obtain ⟨y, hy, hyc⟩ := hroot_sub i j (c (i, j)) (hc_mem (i, j))
    exact ⟨y, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, List.mem_toFinset.mpr hy⟩, hyc⟩
  have hdisj : ∀ p q : Fin n × Fin 2, p ≠ q →
      ¬ ((c p) <+: (c q) ∨ (c q) <+: (c p)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    by_cases hii : i = i'
    · subst hii
      have hjj : j ≠ j' := by
        intro h; exact hne (by simp [h])
      have hco := (hsm.1 i.val i.isLt).1 T
      have hd := hco.2 [] j j' hjj
      exact hd (c (i, j)) (hc_mem (i, j))
        (c (i, j')) (hc_mem (i, j'))
    · -- different trees: use disjointness of the root allocations
      obtain ⟨y, hy, hyc⟩ := hroot_sub i j (c (i, j)) (hc_mem (i, j))
      obtain ⟨y', hy', hyc'⟩ := hroot_sub i' j' (c (i', j')) (hc_mem (i', j'))
      have hroot := hsm.2.1 T i.val i.isLt i'.val i'.isLt (fun h => hii (Fin.ext h))
      intro hcomp
      refine hroot y hy y' hy' ?_
      rcases hcomp with hcomp | hcomp
      · exact List.prefix_or_prefix_of_prefix (hyc.trans hcomp) hyc'
      · exact (List.prefix_or_prefix_of_prefix (hyc'.trans hcomp) hyc).symm
  have havoid : ∀ p : Fin n × Fin 2, ∀ u ∈ A, ¬ ((c p) <+: u ∨ u <+: (c p)) := by
    rintro ⟨i, j⟩ u hu
    exact hsm.2.2 T i.val i.isLt [j.val] (c (i, j)) (hc_mem (i, j)) u hu
  have hlenD : ∀ p : Fin n × Fin 2, (c p).length ≤ D := by
    rintro ⟨i, j⟩
    have := hc_len (i, j)
    have hj : j.val ≤ 1 := by omega
    omega
  have hmass := familyGrayMass_ge_of_incomparable_witnesses (epsDepth := e) (deltaDepth := D)
    (n := n) (T := T) (A := A) (sm := sm) (by omega) c hlenD hanc hdisj havoid
  -- the witnesses weigh at least `(3/2) * n * alpha`
  have hterm : ∀ p : Fin n × Fin 2,
      (1 / 2 : ℚ) ^ (a + p.2.val) ≤ (1 / 2 : ℚ) ^ (c p).length := by
    intro p
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hc_len p)
  have hsum : (3 / 2 : ℚ) * ((n : ℚ) * (1 / 2 : ℚ) ^ a)
      ≤ ∑ p : Fin n × Fin 2, (1 / 2 : ℚ) ^ (c p).length := by
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum (fun p _ => hterm p))
    rw [Fintype.sum_prod_type]
    have hinner : ∀ i : Fin n,
        ∑ j : Fin 2, (1 / 2 : ℚ) ^ (a + j.val) = (3 / 2 : ℚ) * (1 / 2 : ℚ) ^ a := by
      intro i
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one, pow_add]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hinner i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hgray : (3 / 2 : ℚ) * ((n : ℚ) * (1 / 2 : ℚ) ^ a)
      ≤ familyGrayMass e D n T A sm := le_trans hsum hmass
  have hroot : totalRootRequest n (playClientFamily A n (halfStepFamilyStrategy a D) sm T)
      = (n : ℚ) * (1 / 2 : ℚ) ^ a := by
    unfold totalRootRequest getFamilyReq
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
      halfStep_getReq a D A n sm T i.isLt [])]
    simp
  refine ⟨T, ?_, ?_, ?_⟩
  · refine le_trans ?_ hgray
    simp only [dyadicScale]
    nlinarith
  · rw [hroot]
    simp only [halfAmplification]
    norm_num
    linarith [hgray]
  · rw [hroot]
    simp only [halfAmplification, dyadicScale]
    norm_num
    have hpa : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ a := by positivity
    nlinarith

/-- The half-step family strategy range is supported within branching 2. -/
private lemma halfStepFamilyStrategy_range_supported (a D n : ℕ) (A : Allocation) :
    FamilyRangeSupported n 2 A (halfStepFamilyStrategy a D) := by
  intro hist x i hi j hj
  rw [familyClientMoveAt_halfStepFamilyStrategy a D A n hist hj]
  by_cases hx : x = []
  · subst hx
    refine getReq_halfStepMove_eq_zero (by simp) ?_ ?_
    · intro h
      simp only [List.nil_append, List.cons.injEq] at h
      omega
    · intro h
      simp only [List.nil_append, List.cons.injEq] at h
      omega
  · refine getReq_halfStepMove_of_two_le_length ?_
    have hxlen : 1 ≤ x.length := List.length_pos_iff.mpr hx
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- The half-step family strategy tree is supported within height 2. -/
private lemma halfStepFamilyStrategy_tree_supported (a D n : ℕ) (A : Allocation) :
    FamilyTreeSupported n 2 A (halfStepFamilyStrategy a D) := by
  intro hist x hx j hj
  rw [familyClientMoveAt_halfStepFamilyStrategy a D A n hist hj]
  exact getReq_halfStepMove_of_two_le_length (Nat.le_of_lt hx)

/-- **First amplification stage.** For every dyadic request scale `2 ^ (-a)`,
every coarse scale `e ≥ a`, every nonempty family and every unavailable set, the
static two-child split wins the family game with amplification `3 / 2`, at
height `2`, branching `2` and fine scale `e + 3`. -/
theorem grayFamilyGameSpec_halfStep (a e : ℕ) (hae : a ≤ e) (n : ℕ) (hn : 1 ≤ n)
    (A : Allocation) :
    GrayFamilyGameSpec (halfAmplification 1) (dyadicScale a) ((3 / 4 : ℚ) * dyadicScale a)
      e (e + 3) 2 2 n A (halfStepFamilyStrategy a (e + 3)) := by
  classical
  set D := e + 3 with hD
  have halpha : (0 : ℚ) < (1 / 2 : ℚ) ^ a := by positivity
  have ht8 : (1 / 2 : ℚ) ^ D ≤ (1 / 2 : ℚ) ^ a / 8 := by
    have h1 : (1 / 2 : ℚ) ^ D ≤ (1 / 2 : ℚ) ^ (a + 3) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (1 / 2 : ℚ) ^ (a + 3) = (1 / 2 : ℚ) ^ a / 8 := by
      rw [pow_add]; ring
    linarith [h1, h2.le, h2.ge]
  have hDa : a + 1 ≤ D := by omega
  refine ⟨hn, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [halfAmplification]
  · simpa only [dyadicScale] using halpha
  · have : (0 : ℚ) ≤ dyadicScale a := by simp only [dyadicScale]; positivity
    linarith
  · intro sm _hsm
    exact halfStepFamilyStrategy_legal a D hDa n A sm
  · intro sm _hsm t
    exact halfStepFamilyStrategy_minimum_request a D ht8 n A sm t
  · intro sm hsm
    by_cases hwin : familyClientWinsUnserved n 2 2
        (playClientFamily A n (halfStepFamilyStrategy a D) sm) sm
    · exact Or.inl hwin
    · right
      have hserve := halfStep_serves_of_not_wins_unserved a D n A sm hwin
      exact halfStep_familyGrayGoal_of_serves a e hae n hn A sm hsm hserve
  · intro sm hsm
    by_cases hwin : familyClientWinsUnservedPositive n 2 2
        (playClientFamily A n (halfStepFamilyStrategy a D) sm) sm
    · exact Or.inl hwin
    · right
      have hserve := halfStep_serves_of_not_wins_unserved_positive a e hae n A sm hwin
      exact halfStep_familyGrayGoal_of_serves a e hae n hn A sm hsm hserve
  · exact halfStepFamilyStrategy_range_supported a D n A
  · exact halfStepFamilyStrategy_tree_supported a D n A

/-- The stage-`1` invariant of the family induction, proved outright: depth loss
`e + 3`, branching `2`, and the static two-child split as the strategy. -/
theorem grayFamilyStageSpec_one :
    GrayFamilyStageSpec 1 (fun _a e => e + 3) (fun _a _e => 2)
      (fun a e => halfStepFamilyStrategy a (e + 3)) := by
  intro alphaDepth epsDepth _ha hae
  refine ⟨by dsimp only; omega, fun n A hn => ?_⟩
  simpa using grayFamilyGameSpec_halfStep alphaDepth epsDepth hae n hn A


/-- The half-step scheme, shifted by three levels, is a computable family strategy scheme. -/
theorem computable_halfStepFamilyScheme :
    FamilyStrategySchemeComputable (fun a e => halfStepFamilyStrategy a (e + 3)) := by
  unfold FamilyStrategySchemeComputable halfStepFamilyStrategy halfStepMove
  have ha : Computable (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) => p.1.1) :=
    Computable.fst.comp Computable.fst
  have ha1 : Computable (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) => p.1.1 + 1) :=
    Computable.succ.comp ha
  have he : Computable (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hD : Computable
      (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) => p.1.2 + 3) :=
    Computable.succ.comp (Computable.succ.comp (Computable.succ.comp he))
  have q1 : Computable
      (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) => (1 / 2 : ℚ) ^ p.1.1) :=
    computable_half_pow.comp ha
  have q2 : Computable
      (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) => (1 / 2 : ℚ) ^ (p.1.1 + 1)) :=
    computable_half_pow.comp ha1
  have q3 : Computable
      (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) => (1 / 2 : ℚ) ^ (p.1.2 + 3)) :=
    computable_half_pow.comp hD
  have qadd : Computable (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) =>
      (1 / 2 : ℚ) ^ (p.1.1 + 1) + (1 / 2 : ℚ) ^ (p.1.2 + 3)) :=
    Computable₂.comp computable₂_ratAdd q2 q3
  have qsub : Computable (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) =>
      (1 / 2 : ℚ) ^ (p.1.1 + 1) - (1 / 2 : ℚ) ^ (p.1.2 + 3)) :=
    Computable₂.comp computable₂_ratSub q2 q3
  have p1 : Computable (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) =>
      ((([] : GacsDayNode)), (1 / 2 : ℚ) ^ p.1.1)) :=
    (Computable.const ([] : GacsDayNode)).pair q1
  have p2 : Computable (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) =>
      ((([0] : GacsDayNode)), (1 / 2 : ℚ) ^ (p.1.1 + 1) + (1 / 2 : ℚ) ^ (p.1.2 + 3))) :=
    (Computable.const ([0] : GacsDayNode)).pair qadd
  have p3 : Computable (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) =>
      ((([1] : GacsDayNode)), (1 / 2 : ℚ) ^ (p.1.1 + 1) - (1 / 2 : ℚ) ^ (p.1.2 + 3))) :=
    (Computable.const ([1] : GacsDayNode)).pair qsub
  have l3 : Computable (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) =>
      [((([1] : GacsDayNode)), (1 / 2 : ℚ) ^ (p.1.1 + 1) - (1 / 2 : ℚ) ^ (p.1.2 + 3))]) :=
    Computable₂.comp Primrec.list_cons.to_comp p3 (Computable.const [])
  have l2 := Computable₂.comp Primrec.list_cons.to_comp p2 l3
  have l1 := Computable₂.comp Primrec.list_cons.to_comp p1 l2
  have hn : Computable (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) =>
      p.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  exact Computable₂.comp Primrec.list_replicate.to_comp hn l1

/-- The first amplification stage in the packaged form of the game lane. -/
theorem grayFamilyInductionStatement_one : GrayFamilyInductionStatement 1 := by
  refine ⟨fun _a e => e + 3, fun _a _e => 2, fun a e => halfStepFamilyStrategy a (e + 3),
    ?_, ?_, fun _a _e => le_rfl, computable_halfStepFamilyScheme, grayFamilyStageSpec_one⟩
  · exact Computable.succ.comp (Computable.succ.comp (Computable.succ.comp Computable.snd))
  · exact Computable.const 2


end Kolmogorov
