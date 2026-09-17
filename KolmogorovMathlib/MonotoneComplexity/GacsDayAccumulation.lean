import KolmogorovMathlib.MonotoneComplexity.GacsDaySubtreeEmbedding

/-!
# Accumulating the gray area over a chain of family games

One application of the parallel-family construction can never finish the
Gacs-Day controller, and this file records why, together with the bookkeeping
that the real endgame needs.

Planting one family game below the root children of the big tree (see
`isUniformWinningStrategy_of_familyUnservedWin`) needs the gray branch of
`GrayFamilyGameSpec` to be unreachable.  The two available exclusions are
`not_familyGrayGoal_of_one_lt_target` (`1 < n * beta`) and
`not_familyGrayGoal_of_one_lt_amplified` (`1 < kappa * totalRootRequest`).  The
first one is *provably unusable* inside that lemma: its own hypotheses
`(n : ℚ) * alpha ≤ r` and `r ≤ 1 / d` force `n * beta = (3/4) * n * alpha ≤ 3/4`;
this is `not_one_lt_familyTarget_of_capped` below.  The second one needs a lower
bound on the root requests, which a single game does not provide.

The source (SUV pp. 138, 142, 144) resolves this by *composing* games: the games
are played one after another below fresh root children, and the gray cells of the
finished rounds are added to the unavailable set of the later ones.  Since the
grayed areas of different rounds are then disjoint, their masses add up, and the
whole space has mass one.  So a chain of rounds must stop, either because some
round leaves a permanently unserved request (Client wins the single-tree game) or
because the accumulated root request reaches the dangerous level `3 / (4 * d)`,
where the amplification `kappa = 2 * d` makes the gray branch impossible.

This file proves the two quantitative halves of that endgame:

* `sum_newGrayMass_le_one` and `sum_familyGrayMass_le_one`: the newly grayed
  masses of a chain of rounds sum to at most one;
* `grayScaleLadder`: the ladder of scales along which the rounds are run, with
  the additive depth bound that the envelope of
  `GrayFamilyUniformInductionStatement` supplies.

What is left for the construction itself is the round-robin strategy and the
legality of the simulated per-round server plays.
-/

namespace Kolmogorov

/-! ## One capped family game can never exhaust the space -/

/-- Under the request cap of the single-tree game the family target `n * beta`
stays below `3/4`, so `not_familyGrayGoal_of_one_lt_target` cannot fire. -/
lemma familyTarget_le_of_capped {alpha r : ℚ} {n d : ℕ} (hd : 1 ≤ d)
    (hsum : (n : ℚ) * alpha ≤ r) (hcap : r ≤ 1 / (d : ℚ)) :
    (n : ℚ) * ((3 / 4 : ℚ) * alpha) ≤ 3 / 4 := by
  have hd1 : (1 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
  have hdpos : (0 : ℚ) < (d : ℚ) := by linarith
  have hinv : 1 / (d : ℚ) ≤ 1 := by
    rw [div_le_one hdpos]; linarith
  have hna : (n : ℚ) * alpha ≤ 1 := le_trans hsum (le_trans hcap hinv)
  calc (n : ℚ) * ((3 / 4 : ℚ) * alpha) = (3 / 4 : ℚ) * ((n : ℚ) * alpha) := by ring
    _ ≤ (3 / 4 : ℚ) * 1 := by
        exact mul_le_mul_of_nonneg_left hna (by norm_num)
    _ = 3 / 4 := by norm_num

/-- The no-go itself: the cheap exclusion of the gray branch is unavailable to a
single planted family game. -/
lemma not_one_lt_familyTarget_of_capped {alpha r : ℚ} {n d : ℕ} (hd : 1 ≤ d)
    (hsum : (n : ℚ) * alpha ≤ r) (hcap : r ≤ 1 / (d : ℚ)) :
    ¬ 1 < (n : ℚ) * ((3 / 4 : ℚ) * alpha) := by
  have h := familyTarget_le_of_capped hd hsum hcap
  intro hlt
  linarith

/-! ## Rounds gray disjoint areas -/

/-- A cell grayed in a later round is prefix-incomparable with every cell grayed
in an earlier round, provided the earlier gray cells were added to the later
unavailable set.  This is the composition device of SUV p. 138. -/
lemma not_prefixComparable_of_newGrayCells_subset
    {epsEarly deltaEarly epsLate deltaLate : ℕ}
    {allocEarly allocLate unavailEarly unavailLate : Finset BitString}
    (hsub : newGrayCells epsEarly deltaEarly allocEarly unavailEarly ⊆ unavailLate)
    {q p : BitString}
    (hq : q ∈ newGrayCells epsEarly deltaEarly allocEarly unavailEarly)
    (hp : p ∈ newGrayCells epsLate deltaLate allocLate unavailLate) :
    ¬ (p <+: q ∨ q <+: p) := by
  intro hcomp
  obtain ⟨hlen, -, hnot⟩ := mem_newGrayCells_iff.mp hp
  exact hnot (mem_neighborhoodCells_iff_prefixComparable.mpr ⟨hlen, q, hsub hq, hcomp⟩)

/-! ## Why a later round cannot reuse the gray area of an earlier one -/

/-- **Blocking lemma** (SUV p. 137). A cylinder that meets the gray area of an
earlier round, while staying disjoint from everything that round allocated, is
strictly finer than the earlier round's `epsilon` scale.  This is the exact sense
in which the gray area is lost for the server: it is not that she may not touch
it, it is that whatever she puts there is too small to serve anything. -/
lemma epsDepth_lt_length_of_meets_newGrayCells
    {eps delta : ℕ} {S U : Finset BitString} {q c : BitString}
    (heps : eps ≤ delta)
    (hq : q ∈ newGrayCells eps delta S U)
    (hdisj : ∀ s ∈ S, ¬ (c <+: s ∨ s <+: c))
    (hmeet : c <+: q ∨ q <+: c) :
    eps < c.length := by
  obtain ⟨hqlen, hqgray, -⟩ := mem_newGrayCells_iff.mp hq
  obtain ⟨-, s, hs, hscomp⟩ := mem_neighborhoodCells_iff_prefixComparable.mp hqgray
  have htake : q.take eps <+: q := List.take_prefix _ _
  by_contra hle
  push Not at hle
  have hcq : c <+: q := by
    rcases hmeet with h | h
    · exact h
    · have hlen : q.length ≤ c.length := List.IsPrefix.length_le h
      have : c.length = q.length := by omega
      exact (h.eq_of_length this.symm) ▸ List.prefix_refl c
  have hctake : c <+: q.take eps := List.prefix_take_iff.mpr ⟨hcq, hle⟩
  refine hdisj s hs ?_
  rcases hscomp with h | h
  · exact Or.inl (hctake.trans h)
  · exact List.prefix_or_prefix_of_prefix hctake h

/-- Consequently a later round, whose requests are all at least the earlier round's
`epsilon`, is never served inside that gray area. -/
lemma not_serves_of_all_meet_newGrayCells
    {eps delta : ℕ} {S U : Finset BitString} {alloc : Allocation} {req : ℚ}
    (heps : eps ≤ delta)
    (hmeet : ∀ c ∈ alloc, ∃ q ∈ newGrayCells eps delta S U, c <+: q ∨ q <+: c)
    (hdisj : ∀ c ∈ alloc, ∀ s ∈ S, ¬ (c <+: s ∨ s <+: c))
    (hreq : (1 / 2 : ℚ) ^ eps ≤ req) :
    ¬ Serves alloc req := by
  rintro ⟨c, hc, hserve⟩
  obtain ⟨q, hq, hmeetc⟩ := hmeet c hc
  have hlt : eps < c.length :=
    epsDepth_lt_length_of_meets_newGrayCells heps hq (hdisj c hc) hmeetc
  have hstrict : (1 / 2 : ℝ) ^ c.length < (1 / 2 : ℝ) ^ eps :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hlt
  have h1 : (((1 / 2 : ℚ) ^ eps : ℚ) : ℝ) ≤ (req : ℝ) := (Rat.cast_le (K := ℝ)).mpr hreq
  have hcast : (((1 / 2 : ℚ) ^ eps : ℚ) : ℝ) = (1 / 2 : ℝ) ^ eps := by push_cast; ring
  have hreqR : (1 / 2 : ℝ) ^ eps ≤ (req : ℝ) := by rw [← hcast]; exact h1
  linarith

/-! ## Truncating a server play to the scale of the current round

The single-tree server of the composed game does not literally obey the
unavailable set of a later round: nothing stops her from allocating a cylinder
strictly inside a cell that an earlier round has grayed.  The blocking lemma says
that every such cylinder is finer than the earlier round's `epsilon`, so deleting
all cylinders finer than `epsilon` repairs legality without changing which
requests of the round are served. -/

/-- Delete from an allocation every cylinder too small to serve a request of size
`(1/2) ^ eps`. -/
def truncAlloc (eps : ℕ) (alloc : Allocation) : Allocation :=
  alloc.filter (fun c => decide (c.length ≤ eps))

/-- A codeword lies in the truncation `truncAlloc eps alloc` exactly when it lies in `alloc`
and has length at most `eps`. -/
@[simp] lemma mem_truncAlloc {eps : ℕ} {alloc : Allocation} {c : BitString} :
    c ∈ truncAlloc eps alloc ↔ c ∈ alloc ∧ c.length ≤ eps := by
  simp [truncAlloc]

/-- Truncating the empty allocation leaves it empty. -/
@[simp] lemma truncAlloc_nil (eps : ℕ) : truncAlloc eps [] = [] := rfl

/-- Truncation preserves the nesting condition of a legal server play. -/
lemma allocationSubset_truncAlloc {eps : ℕ} {a1 a2 : Allocation}
    (h : allocationSubset a1 a2) :
    allocationSubset (truncAlloc eps a1) (truncAlloc eps a2) := by
  intro c hc
  obtain ⟨hc1, hclen⟩ := mem_truncAlloc.mp hc
  obtain ⟨y, hy, hyc⟩ := h c hc1
  exact ⟨y, mem_truncAlloc.mpr ⟨hy, le_trans (List.IsPrefix.length_le hyc) hclen⟩, hyc⟩

/-- Truncation preserves disjointness of two allocations. -/
lemma disjointAllocations_truncAlloc {eps : ℕ} {a1 a2 : Allocation}
    (h : disjointAllocations a1 a2) :
    disjointAllocations (truncAlloc eps a1) (truncAlloc eps a2) := by
  intro x hx y hy
  exact h x (mem_truncAlloc.mp hx).1 y (mem_truncAlloc.mp hy).1

/-- Truncation does not change service of requests at the round's own scale. -/
lemma serves_truncAlloc_iff {eps : ℕ} {alloc : Allocation} {req : ℚ}
    (hreq : (1 / 2 : ℚ) ^ eps ≤ req) :
    Serves (truncAlloc eps alloc) req ↔ Serves alloc req := by
  constructor
  · rintro ⟨c, hc, hserve⟩
    exact ⟨c, (mem_truncAlloc.mp hc).1, hserve⟩
  · rintro ⟨c, hc, hserve⟩
    refine ⟨c, mem_truncAlloc.mpr ⟨hc, ?_⟩, hserve⟩
    by_contra hlen
    push Not at hlen
    have hstrict : (1 / 2 : ℝ) ^ c.length < (1 / 2 : ℝ) ^ eps :=
      pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hlen
    have h1 : (((1 / 2 : ℚ) ^ eps : ℚ) : ℝ) ≤ (req : ℝ) := (Rat.cast_le (K := ℝ)).mpr hreq
    have hcast : (((1 / 2 : ℚ) ^ eps : ℚ) : ℝ) = (1 / 2 : ℝ) ^ eps := by push_cast; ring
    rw [hcast] at h1
    linarith

/-- Truncating every allocation of a server move. -/
def truncServerMove (eps : ℕ) (m : ServerMove) : ServerMove :=
  m.map (fun p => (p.1, truncAlloc eps p.2))

/-- Truncating a server move at length `eps` truncates, node by node, the allocation it gives. -/
lemma getAlloc_truncServerMove (eps : ℕ) (m : ServerMove) (x : GacsDayNode) :
    getAlloc (truncServerMove eps m) x = truncAlloc eps (getAlloc m x) := by
  induction m with
  | nil => simp [truncServerMove, getAlloc]
  | cons p rest ih =>
    obtain ⟨y, a⟩ := p
    simp only [truncServerMove, List.map_cons] at *
    simp only [getAlloc, List.lookup_cons] at *
    by_cases hxy : x = y
    · subst hxy; simp
    · have hb : (x == y) = false := by simpa using hxy
      simpa [hb] using ih

/-- A truncated legal server play is a legal server play. -/
lemma serverPlayLegal_truncServerMove {b eps : ℕ} {sm : ℕ → ServerMove}
    (h : serverPlayLegal b sm) :
    serverPlayLegal b (fun t => truncServerMove eps (sm t)) := by
  refine ⟨fun t => ⟨?_, ?_⟩, ?_⟩
  · intro x c
    simp only [getAlloc_truncServerMove]
    exact allocationSubset_truncAlloc ((h.1 t).1 x c)
  · intro x c1 c2 hc
    simp only [getAlloc_truncServerMove]
    exact disjointAllocations_truncAlloc ((h.1 t).2 x c1 c2 hc)
  · intro t x
    simp only [getAlloc_truncServerMove]
    exact allocationSubset_truncAlloc (h.2 t x)

/-- **Repairing legality against the accumulated unavailable set.** If the
unavailable set of the current round consists of cells grayed by an earlier round
whose allocations the current cylinders avoid, then the truncated allocation
avoids the unavailable set outright. -/
lemma allocationAvoidsUnavailable_truncAlloc
    {eps delta : ℕ} {S U : Finset BitString} {alloc A : Allocation}
    (heps : eps ≤ delta)
    (hA : ∀ a ∈ A, a ∈ newGrayCells eps delta S U)
    (hdisj : ∀ c ∈ alloc, ∀ s ∈ S, ¬ (c <+: s ∨ s <+: c)) :
    allocationAvoidsUnavailable A (truncAlloc eps alloc) := by
  intro c hc a ha hcomp
  obtain ⟨hc1, hclen⟩ := mem_truncAlloc.mp hc
  have hlt : eps < c.length :=
    epsDepth_lt_length_of_meets_newGrayCells heps (hA a ha) (hdisj c hc1) hcomp
  omega

/-! ## The accumulated gray mass is at most one -/

/-- Pairwise prefix-incomparable families of cells, one family per round, cover at
most the whole space.  The cells of one round all have the same length, the
lengths of different rounds are arbitrary. -/
theorem sum_card_mul_dyadic_le_one
    (N : ℕ) (depth : ℕ → ℕ) (gray : ℕ → Finset BitString)
    (hlen : ∀ j, j < N → ∀ p ∈ gray j, p.length = depth j)
    (hincomp : ∀ i, i < N → ∀ j, j < N → i ≠ j →
      ∀ p ∈ gray i, ∀ q ∈ gray j, ¬ p <+: q) :
    ∑ j ∈ Finset.range N, ((gray j).card : ℚ) * (1 / 2 : ℚ) ^ depth j ≤ 1 := by
  classical
  set D := (Finset.range N).sup depth with hD
  have hjD : ∀ j, j < N → depth j ≤ D := by
    intro j hj
    exact Finset.le_sup (f := depth) (Finset.mem_range.mpr hj)
  -- the cells of all rounds, refined to the common depth `D`
  set T : Finset ((_ : ℕ) × (BitString × BitString)) :=
    (Finset.range N).sigma (fun j => (gray j) ×ˢ stringsOfLength (D - depth j)) with hT
  have hmem : ∀ x ∈ T, x.1 < N ∧ x.2.1 ∈ gray x.1 ∧ x.2.2.length = D - depth x.1 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hp, hw⟩ := Finset.mem_product.mp hx2
    exact ⟨Finset.mem_range.mp hx1, hp, (mem_stringsOfLength _ _).mp hw⟩
  have hmaps : ∀ x ∈ T, x.2.1 ++ x.2.2 ∈ stringsOfLength D := by
    intro x hx
    obtain ⟨hj, hp, hw⟩ := hmem x hx
    have hplen : (x.2.1).length = depth x.1 := hlen x.1 hj _ hp
    refine (mem_stringsOfLength _ _).mpr ?_
    have := hjD x.1 hj
    simp [hplen, hw]
    omega
  have hinj : ∀ x ∈ T, ∀ y ∈ T, x.2.1 ++ x.2.2 = y.2.1 ++ y.2.2 → x = y := by
    intro x hx y hy hEq
    obtain ⟨hjx, hpx, hwx⟩ := hmem x hx
    obtain ⟨hjy, hpy, hwy⟩ := hmem y hy
    have hlx : (x.2.1).length = depth x.1 := hlen x.1 hjx _ hpx
    have hly : (y.2.1).length = depth y.1 := hlen y.1 hjy _ hpy
    have hprefx : x.2.1 <+: x.2.1 ++ x.2.2 := List.prefix_append _ _
    have hprefy : y.2.1 <+: x.2.1 ++ x.2.2 := by rw [hEq]; exact List.prefix_append _ _
    have hsame : x.1 = y.1 := by
      by_contra hne
      rcases le_total (x.2.1).length (y.2.1).length with hle | hle
      · exact hincomp x.1 hjx y.1 hjy hne _ hpx _ hpy
          (List.prefix_of_prefix_length_le hprefx hprefy hle)
      · exact hincomp y.1 hjy x.1 hjx (Ne.symm hne) _ hpy _ hpx
          (List.prefix_of_prefix_length_le hprefy hprefx hle)
    have hlen_eq : (x.2.1).length = (y.2.1).length := by rw [hlx, hly, hsame]
    obtain ⟨hp_eq, hw_eq⟩ := List.append_inj hEq hlen_eq
    obtain ⟨i, p, w⟩ := x
    obtain ⟨i', p', w'⟩ := y
    simp only at hsame hp_eq hw_eq
    subst hsame; subst hp_eq; subst hw_eq
    rfl
  have hcardT : T.card ≤ 2 ^ D := by
    have hle : T.card ≤ (stringsOfLength D).card := by
      refine Finset.card_le_card_of_injOn (fun x => x.2.1 ++ x.2.2) ?_ ?_
      · intro x hx
        exact hmaps x hx
      · intro x hx y hy hEq
        exact hinj x hx y hy hEq
    rwa [card_stringsOfLength] at hle
  have hTsum : T.card = ∑ j ∈ Finset.range N, (gray j).card * 2 ^ (D - depth j) := by
    rw [hT, Finset.card_sigma]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.card_product, card_stringsOfLength]
  -- rewrite every summand at the common depth
  have hstep : ∀ j ∈ Finset.range N,
      ((gray j).card : ℚ) * (1 / 2 : ℚ) ^ depth j
        = (((gray j).card * 2 ^ (D - depth j) : ℕ) : ℚ) * (1 / 2 : ℚ) ^ D := by
    intro j hj
    have hle := hjD j (Finset.mem_range.mp hj)
    obtain ⟨m, hm⟩ : ∃ m, D = depth j + m := ⟨D - depth j, by omega⟩
    have hDm : D - depth j = m := by omega
    have h2 : (2 : ℚ) ^ m * (1 / 2 : ℚ) ^ m = 1 := by
      rw [← mul_pow]; norm_num
    rw [hDm, hm, Nat.cast_mul, Nat.cast_pow]
    push_cast
    rw [pow_add]
    calc ((gray j).card : ℚ) * (1 / 2 : ℚ) ^ depth j
        = ((gray j).card : ℚ) * (1 / 2 : ℚ) ^ depth j * ((2 : ℚ) ^ m * (1 / 2 : ℚ) ^ m) := by
          rw [h2]; ring
      _ = ((gray j).card : ℚ) * (2 : ℚ) ^ m * ((1 / 2 : ℚ) ^ depth j * (1 / 2 : ℚ) ^ m) := by
          ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]
  have hsumQ : (∑ j ∈ Finset.range N, (((gray j).card * 2 ^ (D - depth j) : ℕ) : ℚ))
      ≤ ((2 ^ D : ℕ) : ℚ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast le_trans (le_of_eq hTsum.symm) hcardT
  have hpow : (0 : ℚ) < (1 / 2 : ℚ) ^ D := by positivity
  calc (∑ j ∈ Finset.range N, (((gray j).card * 2 ^ (D - depth j) : ℕ) : ℚ)) * (1 / 2 : ℚ) ^ D
      ≤ ((2 ^ D : ℕ) : ℚ) * (1 / 2 : ℚ) ^ D := by
        exact mul_le_mul_of_nonneg_right hsumQ (le_of_lt hpow)
    _ = 1 := by
        push_cast
        rw [← mul_pow]
        norm_num

/-- The newly grayed masses of a chain of family rounds sum to at most one, as soon
as every round adds its gray cells to the unavailable sets of all later rounds. -/
theorem sum_familyGrayMass_le_one
    (N : ℕ) (epsDepth deltaDepth size time : ℕ → ℕ) (A : ℕ → Allocation)
    (sm : ℕ → ℕ → FamilyServerMove)
    (hchain : ∀ i, i < N → ∀ j, j < N → i < j →
      newGrayCells (epsDepth i) (deltaDepth i)
          (familyAllocated (size i) (time i) (sm i)) (A i).toFinset ⊆ (A j).toFinset) :
    ∑ j ∈ Finset.range N,
        familyGrayMass (epsDepth j) (deltaDepth j) (size j) (time j) (A j) (sm j) ≤ 1 := by
  classical
  set gray : ℕ → Finset BitString := fun j =>
    newGrayCells (epsDepth j) (deltaDepth j)
      (familyAllocated (size j) (time j) (sm j)) (A j).toFinset with hgray
  have hmass : ∀ j, familyGrayMass (epsDepth j) (deltaDepth j) (size j) (time j) (A j) (sm j)
      = ((gray j).card : ℚ) * (1 / 2 : ℚ) ^ deltaDepth j := by
    intro j; rfl
  simp only [hmass]
  refine sum_card_mul_dyadic_le_one N deltaDepth gray ?_ ?_
  · intro j _ p hp
    exact (mem_newGrayCells_iff.mp hp).1
  · intro i hi j hj hne p hp q hq
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · -- `i` is the earlier round: `q` is grayed later
      have := not_prefixComparable_of_newGrayCells_subset (hchain i hi j hj hlt) hp hq
      exact fun hpq => this (Or.inr hpq)
    · -- `j` is the earlier round: `p` is grayed later
      have := not_prefixComparable_of_newGrayCells_subset (hchain j hj i hi hlt) hq hp
      exact fun hpq => this (Or.inl hpq)

/-- A chain of rounds each of which grays at least `g` can only be so long. -/
theorem rounds_le_of_grayMass_lower_bound
    (N : ℕ) (epsDepth deltaDepth size time : ℕ → ℕ) (A : ℕ → Allocation)
    (sm : ℕ → ℕ → FamilyServerMove) (g : ℚ)
    (hchain : ∀ i, i < N → ∀ j, j < N → i < j →
      newGrayCells (epsDepth i) (deltaDepth i)
          (familyAllocated (size i) (time i) (sm i)) (A i).toFinset ⊆ (A j).toFinset)
    (hg : ∀ j, j < N →
      g ≤ familyGrayMass (epsDepth j) (deltaDepth j) (size j) (time j) (A j) (sm j)) :
    (N : ℚ) * g ≤ 1 := by
  classical
  have hsum := sum_familyGrayMass_le_one N epsDepth deltaDepth size time A sm hchain
  have hlow : (N : ℚ) * g
      ≤ ∑ j ∈ Finset.range N,
          familyGrayMass (epsDepth j) (deltaDepth j) (size j) (time j) (A j) (sm j) := by
    have : ∑ _j ∈ Finset.range N, g ≤
        ∑ j ∈ Finset.range N,
          familyGrayMass (epsDepth j) (deltaDepth j) (size j) (time j) (A j) (sm j) :=
      Finset.sum_le_sum (fun j hj => hg j (Finset.mem_range.mp hj))
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  linarith

/-! ## The ladder of scales along which the rounds are run -/

/-- The scales of a chain of rounds: the `delta` of each round is the `epsilon` of
the previous one (SUV p. 137).  Round `j` is played at depth
`grayScaleLadder deltaDepth k a e j`, the coarsest round being `j = 0`. -/
def grayScaleLadder (deltaDepth : ℕ → ℕ → ℕ → ℕ) (k a e : ℕ) : ℕ → ℕ
  | 0 => e
  | j + 1 => deltaDepth k a (grayScaleLadder deltaDepth k a e j)

/-- The gray scale ladder starts at its seed depth `e`. -/
@[simp] lemma grayScaleLadder_zero (deltaDepth : ℕ → ℕ → ℕ → ℕ) (k a e : ℕ) :
    grayScaleLadder deltaDepth k a e 0 = e := rfl

/-- Each rung of the gray scale ladder applies the depth increment `deltaDepth k a` to the
previous rung. -/
@[simp] lemma grayScaleLadder_succ (deltaDepth : ℕ → ℕ → ℕ → ℕ) (k a e j : ℕ) :
    grayScaleLadder deltaDepth k a e (j + 1)
      = deltaDepth k a (grayScaleLadder deltaDepth k a e j) := rfl

/-- Each rung is at least as fine as the previous one. -/
lemma grayScaleLadder_mono_step (deltaDepth : ℕ → ℕ → ℕ → ℕ) (k a e : ℕ)
    (hge : ∀ x, x ≤ deltaDepth k a x) (j : ℕ) :
    grayScaleLadder deltaDepth k a e j ≤ grayScaleLadder deltaDepth k a e (j + 1) := by
  simpa using hge (grayScaleLadder deltaDepth k a e j)

/-- If the depth increment never decreases its argument, the gray scale ladder is monotone in
the number of rungs climbed. -/
lemma grayScaleLadder_monotone (deltaDepth : ℕ → ℕ → ℕ → ℕ) (k a e : ℕ)
    (hge : ∀ x, x ≤ deltaDepth k a x) :
    Monotone (grayScaleLadder deltaDepth k a e) := by
  refine monotone_nat_of_le_succ ?_
  intro j
  exact grayScaleLadder_mono_step deltaDepth k a e hge j

/-- If the depth increment never decreases its argument, every rung of the gray scale ladder is
at least the seed depth `e`. -/
lemma le_grayScaleLadder (deltaDepth : ℕ → ℕ → ℕ → ℕ) (k a e : ℕ)
    (hge : ∀ x, x ≤ deltaDepth k a x) (j : ℕ) :
    e ≤ grayScaleLadder deltaDepth k a e j :=
  grayScaleLadder_monotone deltaDepth k a e hge (Nat.zero_le j)

/-- The additive envelope of `GrayFamilyUniformInductionStatement` bounds the whole
ladder: `N` rounds cost at most `N * E` extra depth.  This is what keeps the
branching factor of the composed tree below `2 ^ ((C * d) ^ (C * d))`. -/
lemma grayScaleLadder_le_add_mul (deltaDepth : ℕ → ℕ → ℕ → ℕ) (k a e E : ℕ)
    (hE : ∀ x, deltaDepth k a x ≤ x + E) (j : ℕ) :
    grayScaleLadder deltaDepth k a e j ≤ e + j * E := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep := hE (grayScaleLadder deltaDepth k a e j)
      have : grayScaleLadder deltaDepth k a e (j + 1)
          ≤ grayScaleLadder deltaDepth k a e j + E := by simpa using hstep
      have hmul : (j + 1) * E = j * E + E := by ring
      omega

/-! ## The endgame arithmetic of SUV p. 144 -/

/-- A coarse integral choice of the source endgame parameters.  Stage `4 * d`
has amplification at least `2 * d`, its planted-tree height is at most `9 * d`,
and `Nat.size (4 * d)` gives a dyadic request cap at most `1 / (4 * d)`.
These are exactly the three elementary parameter inequalities needed before the
sequential round composition. -/
lemma grayEndgame_parameters (d : ℕ) (hd : 1 ≤ d) :
    (2 * d : ℚ) ≤ halfAmplification (4 * d) ∧
    2 * (4 * d) + 1 ≤ 9 * d ∧
    dyadicScale (Nat.size (4 * d)) ≤ 1 / (4 * (d : ℚ)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold halfAmplification
    push_cast
    linarith
  · omega
  · have h4d : 1 ≤ 4 * d := by omega
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      dyadicScale_size_le_inv (4 * d) h4d

/-- At the dangerous level `3 / (4 * d)` the amplification `2 * d` already asks for
more than the whole space, so the gray branch of the composed game is impossible. -/
lemma one_lt_amplified_of_dangerous_level {d : ℕ} (hd : 1 ≤ d) {kappa total : ℚ}
    (hk : (2 * d : ℚ) ≤ kappa) (htotal : 3 / (4 * (d : ℚ)) ≤ total) :
    1 < kappa * total := by
  have hd1 : (1 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
  have hdpos : (0 : ℚ) < (d : ℚ) := by linarith
  have hlevel : (0 : ℚ) < 3 / (4 * (d : ℚ)) := by positivity
  have hprod : (2 * (d : ℚ)) * (3 / (4 * (d : ℚ))) = 3 / 2 := by
    field_simp
    ring
  have hmul : (2 * (d : ℚ)) * (3 / (4 * (d : ℚ))) ≤ kappa * total := by
    refine mul_le_mul hk htotal (le_of_lt hlevel) ?_
    linarith
  rw [hprod] at hmul
  linarith

/-- Stopping the chain as soon as the accumulated root request passes the dangerous
level keeps the total request under the cap `1 / d` of the single-tree game, as
long as each round asks for at most `1 / (4 * d)`. -/
lemma accumulated_request_le_cap {d : ℕ} (hd : 1 ≤ d) {alpha prev : ℚ}
    (halpha : alpha ≤ 1 / (4 * (d : ℚ))) (hprev : prev ≤ 3 / (4 * (d : ℚ))) :
    prev + alpha ≤ 1 / (d : ℚ) := by
  have hd1 : (1 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
  have hdpos : (0 : ℚ) < (d : ℚ) := by linarith
  have hsplit : 3 / (4 * (d : ℚ)) + 1 / (4 * (d : ℚ)) = 1 / (d : ℚ) := by
    field_simp
    ring
  linarith

end Kolmogorov
