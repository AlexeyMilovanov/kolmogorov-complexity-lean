import KolmogorovMathlib.MonotoneComplexity.GacsDayAccumulation
import KolmogorovMathlib.MonotoneComplexity.GacsDayReserveMass
import KolmogorovMathlib.MonotoneComplexity.GacsDayMass
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwo.ServerProbes
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwo

/-!
# Bookkeeping for the sequential rounds of the Gacs-Day endgame

The endgame of SUV p. 144 runs a *sequence* of family games. Round `j` is
planted in its own tree of the family, is handed the gray cells of all earlier
rounds as its unavailable allocation, and is started only after round `j - 1`
has produced its gray outcome. This file proves the four
bookkeeping facts that composition needs and that are independent of the
controller itself.

* *Regions never interfere.* Allocations that live in two different trees of a
  family are prefix-incomparable, **at all pairs of times** and at all nodes of
  the two trees (`not_prefixComparable_of_family_regions`). This is what feeds
  the hypothesis `hdisj` of `allocationAvoidsUnavailable_truncAlloc_chain`, so
  that a later round can safely be given the gray cells of an earlier one as
  its unavailable set.

* *Rounds may start late.* Legality of a server play is invariant under a time
  shift (`serverPlayLegal_shift`, `familyServerPlayLegal_shift`), and an
  unserved request of the shifted play is still unserved in the original play
  (`clientWinsUnserved_of_shift`, `familyClientWinsUnserved_of_shift`). A round
  that starts at time `s` can therefore be analysed as a game in its own right.

* *Gray mass only grows.* Allocations grow with time only in the coarsening
  sense of `allocationSubset`, but that already makes the neighborhood, the new
  gray cells and hence the gray mass monotone in time
  (`familyGrayMass_mono_time`). A controller may therefore test the gray goal
  at every step and fire at the first time it holds.

* *A chain of gray rounds is short.* Amplified root requests of the rounds add
  up to at most one (`sum_kappa_totalRootRequest_le_one`), so at the dangerous
  level `3 / (4 * d)` of SUV p. 144 not every round can be gray
  (`not_forall_gray_of_dangerous_level`), and a chain in which every round
  grays at least `g` has at most `1 / g` rounds
  (`not_forall_gray_of_count`).
-/

namespace Kolmogorov

/-! ### Different trees of a family never interfere -/

/-- Every cell allocated at a node of tree `i` is covered by a root cell of
tree `i` at any later time. -/
theorem exists_root_prefix_of_family_alloc {n b : ℕ} {A : Allocation}
    {sm : ℕ → FamilyServerMove} (hleg : familyServerPlayLegal n b A sm)
    {i : ℕ} (hi : i < n) {t T : ℕ} (htT : t ≤ T) {x : GacsDayNode}
    (hx : ∀ c ∈ x, c < b) {p : BitString} (hp : p ∈ getFamilyAlloc (sm t) i x) :
    ∃ q ∈ getFamilyAlloc (sm T) i [], q <+: p := by
  have hplay := hleg.1 i hi
  obtain ⟨q₁, hq₁, hq₁p⟩ :=
    allocationSubset_getAlloc_root (hplay.1 t) x hx p hp
  obtain ⟨q, hq, hqq₁⟩ :=
    allocationSubset_mono_time hplay htT [] q₁ hq₁
  exact ⟨q, hq, hqq₁.trans hq₁p⟩

/-- **Regions never interfere.** A cell allocated anywhere in tree `i` and a
cell allocated anywhere in tree `j` of the same family, at arbitrary times, are
prefix-incomparable as soon as `i ≠ j`. -/
theorem not_prefixComparable_of_family_regions {n b : ℕ} {A : Allocation}
    {sm : ℕ → FamilyServerMove} (hleg : familyServerPlayLegal n b A sm)
    {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j)
    {s t : ℕ} {x y : GacsDayNode} (hx : ∀ c ∈ x, c < b) (hy : ∀ c ∈ y, c < b)
    {p q : BitString} (hp : p ∈ getFamilyAlloc (sm s) i x)
    (hq : q ∈ getFamilyAlloc (sm t) j y) :
    ¬ (p <+: q ∨ q <+: p) := by
  obtain ⟨p₀, hp₀, hp₀p⟩ :=
    exists_root_prefix_of_family_alloc hleg hi (le_max_left s t) hx hp
  obtain ⟨q₀, hq₀, hq₀q⟩ :=
    exists_root_prefix_of_family_alloc hleg hj (le_max_right s t) hy hq
  have hdisj := hleg.2.1 (max s t) i hi j hj hij p₀ hp₀ q₀ hq₀
  intro hcomp
  refine hdisj ?_
  rcases hcomp with h | h
  · exact isPrefix_or_isPrefix_of_isPrefix (hp₀p.trans h) hq₀q
  · exact isPrefix_or_isPrefix_of_isPrefix hp₀p (hq₀q.trans h)

/-! ### A round may start late -/

/-- Shifting a legal server play in time keeps it legal. -/
theorem serverPlayLegal_shift {b : ℕ} {sm : ℕ → ServerMove}
    (hleg : serverPlayLegal b sm) (s : ℕ) :
    serverPlayLegal b (fun t => sm (t + s)) := by
  refine ⟨fun t => hleg.1 (t + s), fun t x => ?_⟩
  have := hleg.2 (t + s) x
  simpa [Nat.succ_add, Nat.add_right_comm] using this

/-- Shifting a legal family server play in time keeps it legal. -/
theorem familyServerPlayLegal_shift {n b : ℕ} {A : Allocation}
    {sm : ℕ → FamilyServerMove} (hleg : familyServerPlayLegal n b A sm) (s : ℕ) :
    familyServerPlayLegal n b A (fun t => sm (t + s)) :=
  ⟨fun i hi => serverPlayLegal_shift (hleg.1 i hi) s,
   fun t i hi j hj hij => hleg.2.1 (t + s) i hi j hj hij,
   fun t i hi x => hleg.2.2 (t + s) i hi x⟩

/-- An unserved request of a play that starts at time `s` is unserved in the
whole play: earlier allocations are only smaller. -/
theorem clientWinsUnserved_of_shift {h b s : ℕ} {cm : ℕ → ClientMove}
    {sm : ℕ → ServerMove} (hleg : serverPlayLegal b sm)
    (hwin : clientWinsUnserved h b cm (fun t => sm (t + s))) :
    clientWinsUnserved h b cm sm := by
  obtain ⟨T, x, hlen, hin, hfail⟩ := hwin
  refine ⟨T, x, hlen, hin, fun t hserves => hfail t ?_⟩
  exact serves_mono_time hleg (Nat.le_add_right t s) hserves

/-- Winning against a shifted legal play is winning against the original play. -/
theorem familyClientWinsUnserved_of_shift {n h b s : ℕ} {A : Allocation}
    {cm : ℕ → FamilyClientMove} {sm : ℕ → FamilyServerMove}
    (hleg : familyServerPlayLegal n b A sm)
    (hwin : familyClientWinsUnserved n h b cm (fun t => sm (t + s))) :
    familyClientWinsUnserved n h b cm sm := by
  obtain ⟨i, hi, hwin⟩ := hwin
  exact ⟨i, hi, clientWinsUnserved_of_shift (hleg.1 i hi) hwin⟩

/-! ### Gray mass only grows -/

/-- If every cell of `S₁` is covered by a cell of `S₂`, then the neighborhood of
`S₁` is contained in that of `S₂`. Note that `S₁ ⊆ S₂` is *not* assumed: the
allocations of the game grow by coarsening. -/
theorem neighborhoodCells_mono_of_covers {depth : ℕ} {S₁ S₂ : Finset BitString}
    (hcov : ∀ p ∈ S₁, ∃ q ∈ S₂, q <+: p) :
    neighborhoodCells depth S₁ ⊆ neighborhoodCells depth S₂ := by
  intro p hp
  obtain ⟨hlen, c, hc, hcomp⟩ := mem_neighborhoodCells_iff_prefixComparable.mp hp
  obtain ⟨q, hq, hqc⟩ := hcov c hc
  refine mem_neighborhoodCells_iff_prefixComparable.mpr ⟨hlen, q, hq, ?_⟩
  rcases hcomp with h | h
  · exact isPrefix_or_isPrefix_of_isPrefix h hqc
  · exact Or.inr (hqc.trans h)

/-- Replacing the allocated set by one whose members are prefixes of it only enlarges the new
gray area. -/
theorem newGrayCells_mono_of_covers {epsDepth deltaDepth : ℕ}
    {S₁ S₂ U : Finset BitString} (hcov : ∀ p ∈ S₁, ∃ q ∈ S₂, q <+: p) :
    newGrayCells epsDepth deltaDepth S₁ U ⊆ newGrayCells epsDepth deltaDepth S₂ U := by
  intro p hp
  obtain ⟨hlen, hnear, hnot⟩ := mem_newGrayCells_iff.mp hp
  exact mem_newGrayCells_iff.mpr
    ⟨hlen, neighborhoodCells_mono_of_covers hcov hnear, hnot⟩

/-- The root allocations of a family are covered by the root allocations at any
later time. -/
theorem familyAllocated_covers_of_le {n b : ℕ} {A : Allocation}
    {sm : ℕ → FamilyServerMove} (hleg : familyServerPlayLegal n b A sm)
    {t T : ℕ} (htT : t ≤ T) :
    ∀ p ∈ familyAllocated n t sm, ∃ q ∈ familyAllocated n T sm, q <+: p := by
  intro p hp
  simp only [familyAllocated, Finset.mem_biUnion, List.mem_toFinset,
    Finset.mem_univ, true_and] at hp
  obtain ⟨i, hp⟩ := hp
  obtain ⟨q, hq, hqp⟩ :=
    exists_root_prefix_of_family_alloc hleg i.isLt htT (by simp) hp
  refine ⟨q, ?_, hqp⟩
  simp only [familyAllocated, Finset.mem_biUnion, List.mem_toFinset,
    Finset.mem_univ, true_and]
  exact ⟨i, hq⟩

/-- **Gray mass only grows.** The mass newly grayed by a family play is
monotone in time. -/
theorem familyGrayMass_mono_time {epsDepth deltaDepth n b : ℕ} {A U : Allocation}
    {sm : ℕ → FamilyServerMove} (hleg : familyServerPlayLegal n b A sm)
    {t T : ℕ} (htT : t ≤ T) :
    familyGrayMass epsDepth deltaDepth n t U sm
      ≤ familyGrayMass epsDepth deltaDepth n T U sm := by
  have hsub := newGrayCells_mono_of_covers (epsDepth := epsDepth)
    (deltaDepth := deltaDepth) (U := U.toFinset) (familyAllocated_covers_of_le hleg htT)
  have hcard := Finset.card_le_card hsub
  have hpow : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ deltaDepth := by positivity
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hpow

/-! ### A chain of gray rounds is short -/

/-- **The amplified requests of a chain of rounds add up to at most one.**
Each round's amplified total root request is paid for by its own new gray
cells, and those are pairwise disjoint along the chain. -/
theorem sum_kappa_totalRootRequest_le_one
    (N : ℕ) {kappa : ℚ} (epsDepth deltaDepth size time : ℕ → ℕ) (A : ℕ → Allocation)
    (cm : ℕ → ℕ → FamilyClientMove) (sm : ℕ → ℕ → FamilyServerMove)
    (hchain : ∀ i, i < N → ∀ j, j < N → i < j →
      newGrayCells (epsDepth i) (deltaDepth i)
          (familyAllocated (size i) (time i) (sm i)) (A i).toFinset ⊆ (A j).toFinset)
    (hgray : ∀ j, j < N →
      kappa * totalRootRequest (size j) (cm j (time j))
        ≤ familyGrayMass (epsDepth j) (deltaDepth j) (size j) (time j) (A j) (sm j)) :
    kappa * (∑ j ∈ Finset.range N, totalRootRequest (size j) (cm j (time j))) ≤ 1 := by
  have hsum := sum_familyGrayMass_le_one N epsDepth deltaDepth size time A sm hchain
  have hle : ∑ j ∈ Finset.range N, kappa * totalRootRequest (size j) (cm j (time j))
      ≤ ∑ j ∈ Finset.range N,
          familyGrayMass (epsDepth j) (deltaDepth j) (size j) (time j) (A j) (sm j) :=
    Finset.sum_le_sum fun j hj => hgray j (Finset.mem_range.mp hj)
  rw [Finset.mul_sum]
  linarith

/-- **The dangerous level of SUV p. 144.** Once the root requests accumulated
over the rounds reach `3 / (4 * d)`, amplification `2 * d` asks for more gray
mass than the whole space: not every round can have had a gray outcome. -/
theorem not_forall_gray_of_dangerous_level
    {d N : ℕ} (hd : 1 ≤ d) {kappa : ℚ} (hk : (2 * d : ℚ) ≤ kappa)
    (epsDepth deltaDepth size time : ℕ → ℕ) (A : ℕ → Allocation)
    (cm : ℕ → ℕ → FamilyClientMove) (sm : ℕ → ℕ → FamilyServerMove)
    (hchain : ∀ i, i < N → ∀ j, j < N → i < j →
      newGrayCells (epsDepth i) (deltaDepth i)
          (familyAllocated (size i) (time i) (sm i)) (A i).toFinset ⊆ (A j).toFinset)
    (hlevel : 3 / (4 * (d : ℚ))
      ≤ ∑ j ∈ Finset.range N, totalRootRequest (size j) (cm j (time j))) :
    ¬ ∀ j, j < N →
      kappa * totalRootRequest (size j) (cm j (time j))
        ≤ familyGrayMass (epsDepth j) (deltaDepth j) (size j) (time j) (A j) (sm j) := by
  intro hgray
  have hle := sum_kappa_totalRootRequest_le_one N epsDepth deltaDepth size time A cm sm
    hchain hgray
  have hlt := one_lt_amplified_of_dangerous_level hd hk hlevel
  linarith

/-- **A chain of gray rounds is short.** If every one of `N` rounds grays at
least `g`, then `N * g ≤ 1`; so with `1 < N * g` some round has no gray
outcome. -/
theorem not_forall_gray_of_count
    (N : ℕ) {g : ℚ} (epsDepth deltaDepth size time : ℕ → ℕ) (A : ℕ → Allocation)
    (sm : ℕ → ℕ → FamilyServerMove)
    (hchain : ∀ i, i < N → ∀ j, j < N → i < j →
      newGrayCells (epsDepth i) (deltaDepth i)
          (familyAllocated (size i) (time i) (sm i)) (A i).toFinset ⊆ (A j).toFinset)
    (hbig : 1 < (N : ℚ) * g) :
    ¬ ∀ j, j < N →
      g ≤ familyGrayMass (epsDepth j) (deltaDepth j) (size j) (time j) (A j) (sm j) := by
  intro hg
  have := rounds_le_of_grayMass_lower_bound N epsDepth deltaDepth size time A sm g hchain hg
  linarith

/-! ### The play seen by one round -/

/-- Delete from a server move every node outside the `b`-ary tree. Legality
constrains the allocations of the game only inside the tree, so the allocations
outside it have to be dropped before a sub-play can be certified to avoid an
unavailable set. -/
def inTreeServerMove (b : ℕ) (m : ServerMove) : ServerMove :=
  m.filter (fun p => decide (∀ c ∈ p.1, c < b))

/-- Inside the tree, the restricted server move allocates what the original move allocates. -/
lemma getAlloc_inTreeServerMove_of_mem {b : ℕ} (m : ServerMove) {x : GacsDayNode}
    (hx : ∀ c ∈ x, c < b) :
    getAlloc (inTreeServerMove b m) x = getAlloc m x := by
  induction m with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, a⟩ := p
    by_cases hxy : x = y
    · subst hxy
      have hkeep : (decide (∀ c ∈ x, c < b)) = true := by simpa using hx
      simp [inTreeServerMove, hkeep, getAlloc]
    · have hb : (x == y) = false := by simpa using hxy
      by_cases hy : ∀ c ∈ y, c < b
      · have hkeep : (decide (∀ c ∈ y, c < b)) = true := by simpa using hy
        simp only [inTreeServerMove, List.filter_cons, hkeep, if_true, getAlloc,
          List.lookup_cons, hb]
        simpa [inTreeServerMove, getAlloc] using ih
      · have hdrop : (decide (∀ c ∈ y, c < b)) = false := by simpa using hy
        simp only [inTreeServerMove, List.filter_cons, hdrop, getAlloc,
          List.lookup_cons, hb]
        simpa [inTreeServerMove, getAlloc] using ih

/-- Outside the tree, the restricted server move allocates nothing. -/
lemma getAlloc_inTreeServerMove_of_not_mem {b : ℕ} (m : ServerMove) {x : GacsDayNode}
    (hx : ¬ ∀ c ∈ x, c < b) :
    getAlloc (inTreeServerMove b m) x = [] := by
  induction m with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, a⟩ := p
    by_cases hy : ∀ c ∈ y, c < b
    · have hkeep : (decide (∀ c ∈ y, c < b)) = true := by simpa using hy
      have hb : (x == y) = false := by
        by_contra hcon
        have : x = y := by simpa using hcon
        exact hx (this ▸ hy)
      simp only [inTreeServerMove, List.filter_cons, hkeep, if_true, getAlloc,
        List.lookup_cons, hb]
      simpa [inTreeServerMove, getAlloc] using ih
    · have hdrop : (decide (∀ c ∈ y, c < b)) = false := by simpa using hy
      simp only [inTreeServerMove, List.filter_cons, hdrop]
      simpa [inTreeServerMove, getAlloc] using ih

/-- Restricting every move of a legal play to the tree keeps it legal. -/
lemma serverPlayLegal_inTreeServerMove {b : ℕ} {sm : ℕ → ServerMove}
    (hleg : serverPlayLegal b sm) :
    serverPlayLegal b (fun t => inTreeServerMove b (sm t)) := by
  refine ⟨fun t => ⟨?_, ?_⟩, ?_⟩
  · intro x c
    by_cases hx : ∀ e ∈ x, e < b
    · have hxc : ∀ e ∈ x ++ [c.val], e < b := by
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hx e he
        · simp [List.mem_singleton.mp he]
      rw [getAlloc_inTreeServerMove_of_mem _ hxc, getAlloc_inTreeServerMove_of_mem _ hx]
      exact (hleg.1 t).1 x c
    · have hxc : ¬ ∀ e ∈ x ++ [c.val], e < b := by
        intro hall
        exact hx fun e he => hall e (List.mem_append.mpr (Or.inl he))
      rw [getAlloc_inTreeServerMove_of_not_mem _ hxc]
      intro y hy
      simp at hy
  · intro x c1 c2 hc
    by_cases hx : ∀ e ∈ x, e < b
    · have hxc : ∀ (c : ℕ), c < b → ∀ e ∈ x ++ [c], e < b := by
        intro c hcb e he
        rcases List.mem_append.mp he with he | he
        · exact hx e he
        · simpa [List.mem_singleton.mp he] using hcb
      rw [getAlloc_inTreeServerMove_of_mem _ (hxc c1.val c1.isLt),
        getAlloc_inTreeServerMove_of_mem _ (hxc c2.val c2.isLt)]
      exact (hleg.1 t).2 x c1 c2 hc
    · have hxc : ¬ ∀ e ∈ x ++ [c1.val], e < b := by
        intro hall
        exact hx fun e he => hall e (List.mem_append.mpr (Or.inl he))
      rw [getAlloc_inTreeServerMove_of_not_mem _ hxc]
      intro y hy
      simp at hy
  · intro t x
    by_cases hx : ∀ e ∈ x, e < b
    · rw [getAlloc_inTreeServerMove_of_mem _ hx, getAlloc_inTreeServerMove_of_mem _ hx]
      exact hleg.2 t x
    · rw [getAlloc_inTreeServerMove_of_not_mem _ hx]
      intro y hy
      simp at hy

/-- The play one round is fed: the moves of the tree `j` that the round owns, shifted to the round
start `s`, restricted to the `b`-ary tree and truncated at the scale `eps` at which the earlier
rounds have grayed. -/
def roundServerPlay (b eps j s : ℕ) (sm : ℕ → FamilyServerMove) : ℕ → FamilyServerMove :=
  fun t => [truncServerMove eps (inTreeServerMove b (familyServerMoveAt (sm (t + s)) j))]

/-- The round server play hands the single client the truncation, at depth `eps`, of what client
`j` receives at time `t + s`. -/
lemma getFamilyAlloc_roundServerPlay {b eps j s : ℕ} {sm : ℕ → FamilyServerMove}
    (t : ℕ) {x : GacsDayNode} (hx : ∀ c ∈ x, c < b) :
    getFamilyAlloc (roundServerPlay b eps j s sm t) 0 x
      = truncAlloc eps (getFamilyAlloc (sm (t + s)) j x) := by
  change getAlloc (truncServerMove eps (inTreeServerMove b (familyServerMoveAt (sm (t + s)) j))) x
      = truncAlloc eps (getAlloc (familyServerMoveAt (sm (t + s)) j) x)
  rw [getAlloc_truncServerMove, getAlloc_inTreeServerMove_of_mem _ hx]

/-- **Avoiding the accumulated gray area.** A cylinder truncated at a scale at
least as coarse as every earlier round's `epsilon` cannot meet the gray cells of
any of those rounds, as soon as it is prefix-incomparable with everything they
allocated. This is `allocationAvoidsUnavailable_truncAlloc_chain` with one
`epsilon` per round instead of a common one. -/
theorem allocationAvoidsUnavailable_truncAlloc_chain_of_le
    {N eps : ℕ} {epsD deltaD : ℕ → ℕ} {S U : ℕ → Finset BitString}
    {alloc : Allocation} {A : ℕ → Allocation}
    (heps : ∀ i, i < N → eps ≤ epsD i) (hle : ∀ i, i < N → epsD i ≤ deltaD i)
    (hA : ∀ i, i < N → ∀ a ∈ A i, a ∈ newGrayCells (epsD i) (deltaD i) (S i) (U i))
    (hdisj : ∀ i, i < N → ∀ c ∈ alloc, ∀ s ∈ S i, ¬ (c <+: s ∨ s <+: c)) :
    allocationAvoidsUnavailable ((List.range N).flatMap A) (truncAlloc eps alloc) := by
  intro c hc a ha hcomp
  obtain ⟨hc1, hclen⟩ := mem_truncAlloc.mp hc
  simp only [List.mem_flatMap, List.mem_range] at ha
  obtain ⟨i, hi, ha⟩ := ha
  have hlt : epsD i < c.length :=
    epsDepth_lt_length_of_meets_newGrayCells (hle i hi) (hA i hi a ha) (hdisj i hi c hc1) hcomp
  have := heps i hi
  omega

/-- **The round is a legal game of its own.** The play of the tree that a round
owns, shifted, restricted and truncated, is a legal one-tree family play against
the gray cells accumulated by the rounds that came before it. -/
theorem familyServerPlayLegal_roundServerPlay
    {n b N eps j s : ℕ} {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hleg : familyServerPlayLegal n b A sm) (hj : j < n)
    {epsD deltaD : ℕ → ℕ} {S U : ℕ → Finset BitString} {G : ℕ → Allocation} {region : ℕ → ℕ}
    (heps : ∀ i, i < N → eps ≤ epsD i) (hle : ∀ i, i < N → epsD i ≤ deltaD i)
    (hregion : ∀ i, i < N → region i < n) (hne : ∀ i, i < N → region i ≠ j)
    (hS : ∀ i, i < N → ∀ p ∈ S i, ∃ t, p ∈ getFamilyAlloc (sm t) (region i) [])
    (hG : ∀ i, i < N → ∀ a ∈ G i, a ∈ newGrayCells (epsD i) (deltaD i) (S i) (U i)) :
    familyServerPlayLegal 1 b ((List.range N).flatMap G) (roundServerPlay b eps j s sm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    have hshift : serverPlayLegal b (fun t => familyServerMoveAt (sm (t + s)) j) :=
      serverPlayLegal_shift (hleg.1 j hj) s
    exact serverPlayLegal_truncServerMove (serverPlayLegal_inTreeServerMove hshift)
  · intro t i hi i' hi' hne'
    omega
  · intro t i hi x
    have hi0 : i = 0 := by omega
    subst hi0
    by_cases hx : ∀ c ∈ x, c < b
    · rw [getFamilyAlloc_roundServerPlay t hx]
      refine allocationAvoidsUnavailable_truncAlloc_chain_of_le heps hle hG ?_
      intro i hi c hc p hp
      obtain ⟨t', hp⟩ := hS i hi p hp
      exact fun hcomp =>
        not_prefixComparable_of_family_regions hleg hj (hregion i hi) (Ne.symm (hne i hi))
          hx (by simp) hc hp hcomp
    · have : getFamilyAlloc (roundServerPlay b eps j s sm t) 0 x = [] := by
        change getAlloc (truncServerMove eps
          (inTreeServerMove b (familyServerMoveAt (sm (t + s)) j))) x = []
        rw [getAlloc_truncServerMove, getAlloc_inTreeServerMove_of_not_mem _ hx]
        rfl
      rw [this]
      intro c hc
      simp at hc

/-- **A round's unserved request is unserved in the whole game.** The request
has to be at least the truncation scale of the round: a request finer than that
could be served by a cylinder that the round never gets to see. -/
theorem familyClientWinsUnserved_of_round
    {n b h eps j s : ℕ} {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hleg : familyServerPlayLegal n b A sm) (hj : j < n)
    {cm : ℕ → FamilyClientMove} {T : ℕ} {x : GacsDayNode}
    (hlen : x.length ≤ h) (hin : ∀ a ∈ x, a < b)
    (hbig : (1 / 2 : ℚ) ^ eps ≤ getFamilyReq (cm T) j x)
    (hfail : ∀ t, ¬ Serves (getFamilyAlloc (roundServerPlay b eps j s sm t) 0 x)
      (getFamilyReq (cm T) j x)) :
    familyClientWinsUnserved n h b cm sm := by
  refine ⟨j, hj, T, x, hlen, hin, fun t hserves => ?_⟩
  have hmax : Serves (getFamilyAlloc (sm (max t s)) j x) (getFamilyReq (cm T) j x) :=
    serves_mono_time (hleg.1 j hj) (le_max_left t s) hserves
  have hsplit : max t s = (max t s - s) + s := by omega
  rw [hsplit] at hmax
  refine hfail (max t s - s) ?_
  rw [getFamilyAlloc_roundServerPlay _ hin]
  exact (serves_truncAlloc_iff hbig).mpr hmax

/-! ### Assembling the trees of the family -/

/-- The family move that plays `f i` in tree `i`. The controller builds its move
this way: the tree of the round that is currently running plays the move of that
round, and every other tree plays whatever it last asked for. -/
def familyMoveOfTrees (n : ℕ) (f : ℕ → ClientMove) : FamilyClientMove :=
  (List.range n).map f

/-- Client `i` of a family assembled from single-client moves plays `f i`. -/
lemma familyClientMoveAt_familyMoveOfTrees {n i : ℕ} (f : ℕ → ClientMove) (hi : i < n) :
    familyClientMoveAt (familyMoveOfTrees n f) i = f i := by
  unfold familyClientMoveAt familyMoveOfTrees
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- The request of client `i` in an assembled family move is the request of `f i`. -/
lemma getFamilyReq_familyMoveOfTrees {n i : ℕ} (f : ℕ → ClientMove) (hi : i < n)
    (x : GacsDayNode) :
    getFamilyReq (familyMoveOfTrees n f) i x = getReq (f i) x := by
  rw [getFamilyReq, familyClientMoveAt_familyMoveOfTrees f hi]

/-- The total root request of an assembled family move is the sum of the root requests of its
parts. -/
lemma totalRootRequest_familyMoveOfTrees (n : ℕ) (f : ℕ → ClientMove) :
    totalRootRequest n (familyMoveOfTrees n f) = ∑ i : Fin n, getReq (f i.val) [] :=
  Finset.sum_congr rfl fun i _ => getFamilyReq_familyMoveOfTrees f i.isLt []

/-- Legality of a family play assembled tree by tree. -/
theorem familyClientPlayLegal_of_trees {n b : ℕ} {alpha : ℚ} {cf : ℕ → ℕ → ClientMove}
    (hcoh : ∀ t i, i < n → requestCoherentCap b alpha (cf t i))
    (hmono : ∀ t i, i < n → ∀ x, getReq (cf t i) x ≤ getReq (cf (t + 1) i) x) :
    familyClientPlayLegal n b alpha (fun t => familyMoveOfTrees n (cf t)) := by
  refine ⟨fun t i hi => ?_, fun t i hi x => ?_⟩
  · rw [familyClientMoveAt_familyMoveOfTrees _ hi]
    exact hcoh t i hi
  · rw [getFamilyReq_familyMoveOfTrees _ hi, getFamilyReq_familyMoveOfTrees _ hi]
    exact hmono t i hi x

/-- **The endgame contradiction of SUV p. 144, ready for use.** A chain of
rounds in which every round grays at least its amplified root request and makes
at least the progress `g` cannot be all gray once `N * g` reaches the dangerous
level `3 / (4 * d)`: the amplification `2 * d` would ask for more gray mass than
the whole space. -/
theorem not_forall_gray_of_progress
    {d N : ℕ} (hd : 1 ≤ d) {kappa g : ℚ} (hk : (2 * d : ℚ) ≤ kappa)
    (hNg : 3 / (4 * (d : ℚ)) ≤ (N : ℚ) * g)
    (epsDepth deltaDepth size time : ℕ → ℕ) (A : ℕ → Allocation)
    (cm : ℕ → ℕ → FamilyClientMove) (sm : ℕ → ℕ → FamilyServerMove)
    (hchain : ∀ i, i < N → ∀ j, j < N → i < j →
      newGrayCells (epsDepth i) (deltaDepth i)
          (familyAllocated (size i) (time i) (sm i)) (A i).toFinset ⊆ (A j).toFinset)
    (hprog : ∀ j, j < N → g ≤ totalRootRequest (size j) (cm j (time j)))
    (hgray : ∀ j, j < N →
      kappa * totalRootRequest (size j) (cm j (time j))
        ≤ familyGrayMass (epsDepth j) (deltaDepth j) (size j) (time j) (A j) (sm j)) :
    False := by
  refine not_forall_gray_of_dangerous_level hd hk epsDepth deltaDepth size time A cm sm hchain
    ?_ hgray
  refine le_trans hNg ?_
  have hle : ∑ _j ∈ Finset.range N, g
      ≤ ∑ j ∈ Finset.range N, totalRootRequest (size j) (cm j (time j)) :=
    Finset.sum_le_sum fun j hj => hprog j (Finset.mem_range.mp hj)
  simpa [Finset.sum_const, nsmul_eq_mul] using hle

/-- **The endgame dichotomy of SUV p. 144, packaged.** Run `N` rounds. Each
round either already leaves an unserved request -- which the controller has to
be able to transfer back to the whole game, the hypothesis `htransfer` -- or it
grays at least its amplified root request.  The second alternative cannot hold
for every round once the accumulated progress `N * g` reaches the dangerous
level `3 / (4 * d)`, so the client wins.

This is the shape in which the endgame consumes the round machinery: it isolates
the two obligations that are about the *construction* of the controller (the
chain of accumulated gray areas, and the transfer of a round's win) from the
counting argument, which is discharged here. -/
theorem familyClientWinsUnserved_of_rounds
    {n h b N d : ℕ} (hd : 1 ≤ d) {kappa g : ℚ} (hk : (2 * d : ℚ) ≤ kappa)
    (hNg : 3 / (4 * (d : ℚ)) ≤ (N : ℚ) * g)
    {cm : ℕ → FamilyClientMove} {sm : ℕ → FamilyServerMove}
    (epsDepth deltaDepth size time : ℕ → ℕ) (Ar : ℕ → Allocation)
    (rcm : ℕ → ℕ → FamilyClientMove) (rsm : ℕ → ℕ → FamilyServerMove)
    (hchain : ∀ i, i < N → ∀ j, j < N → i < j →
      newGrayCells (epsDepth i) (deltaDepth i)
          (familyAllocated (size i) (time i) (rsm i)) (Ar i).toFinset ⊆ (Ar j).toFinset)
    (hprog : ∀ j, j < N → g ≤ totalRootRequest (size j) (rcm j (time j)))
    (hdich : ∀ j, j < N →
      familyClientWinsUnserved (size j) h b (rcm j) (rsm j) ∨
        kappa * totalRootRequest (size j) (rcm j (time j))
          ≤ familyGrayMass (epsDepth j) (deltaDepth j) (size j) (time j) (Ar j) (rsm j))
    (htransfer : ∀ j, j < N → familyClientWinsUnserved (size j) h b (rcm j) (rsm j) →
      familyClientWinsUnserved n h b cm sm) :
    familyClientWinsUnserved n h b cm sm := by
  by_cases hwin : ∃ j, j < N ∧ familyClientWinsUnserved (size j) h b (rcm j) (rsm j)
  · obtain ⟨j, hj, hjwin⟩ := hwin
    exact htransfer j hj hjwin
  · push Not at hwin
    exact absurd
      (not_forall_gray_of_progress hd hk hNg epsDepth deltaDepth size time Ar rcm rsm hchain hprog
        (fun j hj => (hdich j hj).resolve_left (hwin j hj))) not_false

end Kolmogorov
