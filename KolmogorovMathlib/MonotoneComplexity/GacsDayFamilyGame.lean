import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayGame
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayBridge
import KolmogorovMathlib.MonotoneComplexity.GacsDayReplay

/-!
# The parallel family game in the Gacs-Day induction

This file isolates the game used on pp. 142-144 of SUV. A family move is a
finite list, so histories are encodable. The unavailable set is fixed before
play and is an explicit input to the strategy. A win requires either a
permanently unserved request or enough genuinely new gray mass, both in total
and relative to the sum of the root requests.

The source induction uses amplification `1 + k / 2`, height `2 * k`, every
nonempty family, and every unavailable set. `GrayFamilyInductionStatement`
records that uniform assertion. In particular, an empty family cannot witness
the base case or the half-step.
-/

namespace Kolmogorov

/-- One client move for each tree in a finite family. -/
abbrev FamilyClientMove := List ClientMove

/-- One server move for each tree in a finite family. -/
abbrev FamilyServerMove := List ServerMove

/-- The record of all family client and server moves played so far. -/
abbrev FamilyGameHistory := List FamilyClientMove × List FamilyServerMove

/-- The client move made in the `i`-th tree of the family, empty beyond the family. -/
def familyClientMoveAt (m : FamilyClientMove) (i : ℕ) : ClientMove :=
  m.getD i []

/-- The server move made in the `i`-th tree of the family, empty beyond the family. -/
def familyServerMoveAt (m : FamilyServerMove) (i : ℕ) : ServerMove :=
  m.getD i []

/-- The mass requested at node `x` of the `i`-th tree. -/
def getFamilyReq (m : FamilyClientMove) (i : ℕ) (x : GacsDayNode) : ℚ :=
  getReq (familyClientMoveAt m i) x

/-- The allocation granted at node `x` of the `i`-th tree. -/
def getFamilyAlloc (m : FamilyServerMove) (i : ℕ) (x : GacsDayNode) : Allocation :=
  getAlloc (familyServerMoveAt m i) x

/-- The sum of the root requests over the `n` trees of the family. -/
def totalRootRequest (n : ℕ) (m : FamilyClientMove) : ℚ :=
  ∑ i : Fin n, getFamilyReq m i.val []

/-- The strategy sees the unavailable set, the family size, and the finite history. -/
def ClientFamilyStrategy :=
  Allocation → ℕ → FamilyGameHistory → FamilyClientMove

/-- The sequence of family client moves obtained by running the strategy `σ` against a fixed family
server play, with unavailable set `A` and family size `n`. -/
def playClientFamily (A : Allocation) (n : ℕ) (σ : ClientFamilyStrategy)
    (sm : ℕ → FamilyServerMove) : ℕ → FamilyClientMove
  | 0 => σ A n ([], [])
  | t + 1 =>
      σ A n
        (List.ofFn (fun i : Fin (t + 1) => playClientFamily A n σ sm i.val),
          List.ofFn (fun i : Fin (t + 1) => sm i.val))

/-- Coherence with a direct cap `alpha` on the root request. -/
def requestCoherentCap (b : ℕ) (alpha : ℚ) (req : ClientMove) : Prop :=
  (∀ x : GacsDayNode, 0 ≤ getReq req x) ∧
  getReq req [] ≤ alpha ∧
  ∀ x : GacsDayNode,
    getReq req x ≥ ∑ c : Fin b, getReq req (x ++ [c.val])

/-- Every tree of the family plays coherently under the cap `alpha` and its requests only grow. -/
def familyClientPlayLegal (n b : ℕ) (alpha : ℚ)
    (cm : ℕ → FamilyClientMove) : Prop :=
  (∀ t i, i < n → requestCoherentCap b alpha (familyClientMoveAt (cm t) i)) ∧
  ∀ t i, i < n → ∀ x,
    getFamilyReq (cm t) i x ≤ getFamilyReq (cm (t + 1)) i x

/-- Every positive request is either zero or at least `delta`. -/
def requestAvoidsSmall (delta : ℚ) (req : ClientMove) : Prop :=
  ∀ x : GacsDayNode, getReq req x = 0 ∨ delta ≤ getReq req x

/-- In every tree of the family each request is either zero or at least `delta`. -/
def familyRequestAvoidsSmall (n : ℕ) (delta : ℚ) (cm : FamilyClientMove) : Prop :=
  ∀ i, i < n → requestAvoidsSmall delta (familyClientMoveAt cm i)

/-- No allocated cylinder meets the unavailable union of cylinders. -/
def allocationAvoidsUnavailable (A : Allocation) (alloc : Allocation) : Prop :=
  ∀ c ∈ alloc, ∀ a ∈ A, ¬ (c <+: a ∨ a <+: c)

/-- Legal play in every tree, disjoint root allocations across trees, and no use of `A`. -/
def familyServerPlayLegal (n b : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) : Prop :=
  (∀ i, i < n → serverPlayLegal b (fun t => familyServerMoveAt (sm t) i)) ∧
  (∀ t i, i < n → ∀ j, j < n → i ≠ j →
    disjointAllocations (getFamilyAlloc (sm t) i []) (getFamilyAlloc (sm t) j [])) ∧
  ∀ t i, i < n → ∀ x,
    allocationAvoidsUnavailable A (getFamilyAlloc (sm t) i x)

/-- Some tree of the family has a permanently unserved request. -/
def familyClientWinsUnserved (n h b : ℕ) (cm : ℕ → FamilyClientMove)
    (sm : ℕ → FamilyServerMove) : Prop :=
  ∃ i, i < n ∧
    clientWinsUnserved h b
      (fun t => familyClientMoveAt (cm t) i)
      (fun t => familyServerMoveAt (sm t) i)

/-- Some tree of the family has a permanently unserved request that is in addition strictly
positive. -/
def familyClientWinsUnservedPositive (n h b : ℕ) (cm : ℕ → FamilyClientMove)
    (sm : ℕ → FamilyServerMove) : Prop :=
  ∃ i, i < n ∧
    ∃ T, ∃ x, x.length ≤ h ∧ (∀ a ∈ x, a < b) ∧
      (∀ t,
        ¬ Serves (getAlloc (familyServerMoveAt (sm t) i) x) (getReq (familyClientMoveAt
        (cm T) i) x)) ∧
      0 < getReq (familyClientMoveAt (cm T) i) x

/-- A positive unserved request is in particular an unserved request. -/
lemma familyClientWinsUnserved_of_positive (n h b : ℕ) (cm : ℕ → FamilyClientMove)
    (sm : ℕ → FamilyServerMove) (hwin : familyClientWinsUnservedPositive n h b cm sm) :
    familyClientWinsUnserved n h b cm sm := by
  rcases hwin with ⟨i, hi, T, x, hlen, hin, hfail, _⟩
  exact ⟨i, hi, T, x, hlen, hin, hfail⟩

/-- The union of the root allocations of the `n` trees at time `T`. -/
def familyAllocated (n T : ℕ) (sm : ℕ → FamilyServerMove) : Finset BitString :=
  (Finset.univ : Finset (Fin n)).biUnion
    (fun i => (getFamilyAlloc (sm T) i.val []).toFinset)

/-- The measure of the gray cells at resolution `deltaDepth` that the family's root allocations
newly create outside the unavailable set. -/
def familyGrayMass (epsDepth deltaDepth n T : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) : ℚ :=
  ((newGrayCells epsDepth deltaDepth (familyAllocated n T sm) A.toFinset).card : ℚ) *
    (1 / 2 : ℚ) ^ deltaDepth

/-- The source winning condition after the final root adjustment of SUV p. 143.
The gray mass is at least the target average, it is at least `kappa` times the
actual total root request, and that request is large enough to account for the
target average. Thus the actual request is not pinned to `n * alpha`; instead
it lies in the source-faithful interval
`n * beta <= kappa * totalRootRequest <= gray mass`. -/
def familyGrayGoal (kappa beta : ℚ) (epsDepth deltaDepth n : ℕ)
    (A : Allocation) (cm : ℕ → FamilyClientMove)
    (sm : ℕ → FamilyServerMove) : Prop :=
  ∃ T,
    (n : ℚ) * beta ≤ familyGrayMass epsDepth deltaDepth n T A sm ∧
    kappa * totalRootRequest n (cm T) ≤ familyGrayMass epsDepth deltaDepth n T A sm ∧
    (n : ℚ) * beta ≤ kappa * totalRootRequest n (cm T)

/-- The strategy only requests inside the `b`-ary tree, in every tree of the family. -/
def FamilyRangeSupported (n b : ℕ) (A : Allocation)
    (σ : ClientFamilyStrategy) : Prop :=
  ∀ hist x i, b ≤ i → ∀ j, j < n →
    getReq (familyClientMoveAt (σ A n hist) j) (x ++ [i]) = 0

/-- The strategy requests nothing below depth `h`, in every tree of the family. -/
def FamilyTreeSupported (n h : ℕ) (A : Allocation)
    (σ : ClientFamilyStrategy) : Prop :=
  ∀ hist x, h < x.length → ∀ j, j < n →
    getReq (familyClientMoveAt (σ A n hist) j) x = 0

/-- A source-faithful winning strategy for one fixed nonempty family game. -/
structure GrayFamilyGameSpec (kappa alpha beta : ℚ) (epsDepth deltaDepth h b n : ℕ)
    (A : Allocation) (σ : ClientFamilyStrategy) : Prop where
  nonempty : 1 ≤ n
  kappa_ge_one : 1 ≤ kappa
  alpha_pos : 0 < alpha
  beta_nonneg : 0 ≤ beta
  scales : epsDepth ≤ deltaDepth
  legal : ∀ sm, familyServerPlayLegal n b A sm →
    familyClientPlayLegal n b alpha (playClientFamily A n σ sm)
  minimum_request : ∀ sm, familyServerPlayLegal n b A sm → ∀ t,
    familyRequestAvoidsSmall n ((1 / 2 : ℚ) ^ deltaDepth)
      (playClientFamily A n σ sm t)
  wins : ∀ sm, familyServerPlayLegal n b A sm →
    familyClientWinsUnserved n h b (playClientFamily A n σ sm) sm ∨
      familyGrayGoal kappa beta epsDepth deltaDepth n A
        (playClientFamily A n σ sm) sm
  wins_positively : ∀ sm, familyServerPlayLegal n b A sm →
    familyClientWinsUnservedPositive n h b (playClientFamily A n σ sm) sm ∨
      familyGrayGoal kappa beta epsDepth deltaDepth n A
        (playClientFamily A n σ sm) sm
  range_supported : FamilyRangeSupported n b A σ
  tree_supported : FamilyTreeSupported n h A σ

/-- The dyadic scale `2 ^ (-depth)`. -/
def dyadicScale (depth : ℕ) : ℚ := (1 / 2 : ℚ) ^ depth

/-- The amplification factor `1 + k/2` reached after `k` steps of the induction. -/
def halfAmplification (k : ℕ) : ℚ := 1 + (k : ℚ) / 2

/-- A strategy scheme uniform in the dyadic scales. Its returned strategy is
still uniform in the nonempty family size and unavailable set. -/
abbrev FamilyStrategyScheme := ℕ → ℕ → ClientFamilyStrategy

/-- The strategy scheme is computable jointly in both dyadic depths, the unavailable set, the family
size and the history. -/
def FamilyStrategySchemeComputable (σ : FamilyStrategyScheme) : Prop :=
  Computable
    (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) =>
      σ p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)

/-- The semantic induction invariant from the parallel construction.
At stage `k`, amplification is `1 + k/2`, height is `2*k`, `epsilon <= alpha`,
and one computable scheme wins for every nonempty family and unavailable set. -/
def GrayFamilyStageSpec (k : ℕ) (deltaDepth branching : ℕ → ℕ → ℕ)
    (σ : FamilyStrategyScheme) : Prop :=
  ∀ alphaDepth epsDepth, 1 ≤ alphaDepth → alphaDepth ≤ epsDepth →
    epsDepth ≤ deltaDepth alphaDepth epsDepth ∧
      ∀ n A, 1 ≤ n →
        GrayFamilyGameSpec (halfAmplification k)
          (dyadicScale alphaDepth) ((3 / 4 : ℚ) * dyadicScale alphaDepth)
          epsDepth (deltaDepth alphaDepth epsDepth) (2 * k)
          (branching alphaDepth epsDepth) n A (σ alphaDepth epsDepth)

/-- Stage `k` of the parallel-family induction: there are computable depth-loss and
branching functions, with branching at least `2`, and a computable family strategy
scheme satisfying `GrayFamilyStageSpec k` for them. -/
def GrayFamilyInductionStatement (k : ℕ) : Prop :=
  ∃ deltaDepth branching : ℕ → ℕ → ℕ, ∃ σ : FamilyStrategyScheme,
    Computable₂ deltaDepth ∧ Computable₂ branching ∧
      (∀ a e, 2 ≤ branching a e) ∧ FamilyStrategySchemeComputable σ ∧
    GrayFamilyStageSpec k deltaDepth branching σ


/-- A family strategy scheme which is also uniform in the amplification stage. -/
abbrev UniformFamilyStrategyScheme := ℕ → FamilyStrategyScheme

/-- Joint computability in the amplification stage, the two dyadic depths, the
unavailable allocation, the nonempty family size, and the finite history. -/
def UniformFamilyStrategySchemeComputable (σ : UniformFamilyStrategyScheme) : Prop :=
  Computable
    (fun p : (ℕ × ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) =>
      σ p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2)

/-- Joint computability for a numerical parameter indexed by the amplification
stage and the two dyadic depths. -/
def GrayNat3Computable (f : ℕ → ℕ → ℕ → ℕ) : Prop :=
  Computable (fun p : ℕ × ℕ × ℕ => f p.1 p.2.1 p.2.2)

/-- A coarse envelope for the source recurrences on pp. 143-144. -/
def grayFamilyEnvelope (C k : ℕ) : ℕ :=
  (C * (k + 1)) ^ (C * (k + 1))

/-- The uniform form of the parallel-family induction needed by the final
Gacs-Day controller. It supplies one jointly computable construction for every
stage and records the source-shaped depth-loss and branching bounds. -/
def GrayFamilyUniformInductionStatement : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧
    ∃ deltaDepth branching : ℕ → ℕ → ℕ → ℕ,
      ∃ σ : UniformFamilyStrategyScheme,
        GrayNat3Computable deltaDepth ∧
        GrayNat3Computable branching ∧
        (∀ k a e, 2 ≤ branching k a e) ∧
        UniformFamilyStrategySchemeComputable σ ∧
        ∀ k alphaDepth epsDepth, 1 ≤ alphaDepth → alphaDepth ≤ epsDepth →
          epsDepth ≤ deltaDepth k alphaDepth epsDepth ∧
          deltaDepth k alphaDepth epsDepth ≤ epsDepth + grayFamilyEnvelope C k ∧
          branching k alphaDepth epsDepth ≤
            max (2 * 2 ^ (epsDepth - alphaDepth))
              (2 ^ grayFamilyEnvelope C k) ∧
          ∀ n A, 1 ≤ n →
            GrayFamilyGameSpec (halfAmplification k)
              (dyadicScale alphaDepth) ((3 / 4 : ℚ) * dyadicScale alphaDepth)
              epsDepth (deltaDepth k alphaDepth epsDepth) (2 * k)
              (branching k alphaDepth epsDepth) n A (σ k alphaDepth epsDepth)
/-- The base-case family strategy: every tree always requests mass `2^{-a}` at the root. -/
def baseFamilyStrategy (a : ℕ) : ClientFamilyStrategy :=
  fun _A n _hist => List.replicate n [(([] : GacsDayNode), (1 / 2 : ℚ) ^ a)]

/-- In the base strategy every tree of the family requests mass `2 ^ (-a)` at its root. -/
lemma familyClientMoveAt_baseFamilyStrategy (a : ℕ) (A : Allocation) (n : ℕ)
    (hist : FamilyGameHistory) {i : ℕ} (hi : i < n) :
    familyClientMoveAt (baseFamilyStrategy a A n hist) i =
      [(([] : GacsDayNode), (1 / 2 : ℚ) ^ a)] := by
  unfold familyClientMoveAt baseFamilyStrategy
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp [hi]

/-- A move requesting only at the root returns that request at the root. -/
lemma getReq_root_singleton (q : ℚ) :
    getReq [(([] : GacsDayNode), q)] [] = q := by
  simp [getReq]

/-- A move requesting only at the root requests nothing elsewhere. -/
lemma getReq_singleton_of_ne (q : ℚ) (x : GacsDayNode) (hx : x ≠ []) :
    getReq [(([] : GacsDayNode), q)] x = 0 := by
  cases x with
  | nil => exact absurd rfl hx
  | cons b y => simp [getReq, List.lookup]


/-- If `n` pairwise incompatible allocated cylinders of length at most `a` avoid the
unavailable set, then at depth `e ≥ a` they contribute at least `n * 2^(e-a)` new gray cells. -/
lemma card_newGrayCells_ge_of_disjoint_witnesses
    (a e : ℕ) (hae : a ≤ e) (S U : Finset BitString) (n : ℕ)
    (c : Fin n → BitString)
    (hc_len : ∀ i, (c i).length ≤ a)
    (hc_mem : ∀ i, c i ∈ S)
    (hc_disj : ∀ i j, i ≠ j → ¬ ((c i) <+: (c j) ∨ (c j) <+: (c i)))
    (hc_avoid : ∀ i, ∀ u ∈ U, ¬ ((c i) <+: u ∨ u <+: (c i))) :
    n * 2 ^ (e - a) ≤ (newGrayCells e e S U).card := by
  classical
  set pad : Fin n → BitString := fun i => c i ++ List.replicate (a - (c i).length) false with hpad
  have hpad_len : ∀ i, (pad i).length = a := by
    intro i
    have := hc_len i
    simp [hpad]
    omega
  have hpad_pref : ∀ i, c i <+: pad i := fun i => List.prefix_append _ _
  set f : Fin n × BitString → BitString := fun p => pad p.1 ++ p.2 with hf
  have hcard : ((Finset.univ : Finset (Fin n)) ×ˢ (stringsOfLength (e - a))).card
      = n * 2 ^ (e - a) := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, card_stringsOfLength]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · rintro ⟨i, w⟩ hp
    have hw : w.length = e - a := by
      have := (Finset.mem_product.mp hp).2
      exact (mem_stringsOfLength _ _).mp this
    have hlen : (f (i, w)).length = e := by
      simp [hf, hpad_len i, hw]
      omega
    have htake : (f (i, w)).take e = f (i, w) := by rw [← hlen, List.take_length]
    refine mem_newGrayCells_iff.mpr ⟨hlen, ?_, ?_⟩
    · rw [htake]
      refine mem_neighborhoodCells_iff_prefixComparable.mpr ⟨hlen, c i, hc_mem i, Or.inr ?_⟩
      exact (hpad_pref i).trans (List.prefix_append _ _)
    · intro hmem
      obtain ⟨-, u, hu, hcomp⟩ := mem_neighborhoodCells_iff_prefixComparable.mp hmem
      have hci : c i <+: f (i, w) := (hpad_pref i).trans (List.prefix_append _ _)
      refine hc_avoid i u hu ?_
      rcases hcomp with hcomp | hcomp
      · exact Or.inl (hci.trans hcomp)
      · exact List.prefix_or_prefix_of_prefix hci hcomp
  · rintro ⟨i, w⟩ hp ⟨j, v⟩ hq hEq
    have hEq' : pad i ++ w = pad j ++ v := hEq
    have hlen : (pad i).length = (pad j).length := by rw [hpad_len, hpad_len]
    obtain ⟨hpadeq, hwv⟩ := List.append_inj hEq' hlen
    have hij : i = j := by
      by_contra hne
      refine hc_disj i j hne ?_
      have h1 : c i <+: pad i := hpad_pref i
      have h2 : c j <+: pad i := by rw [hpadeq]; exact hpad_pref j
      exact List.prefix_or_prefix_of_prefix h1 h2
    simp [hij, hwv]


/-- The map `a ↦ 2 ^ (-a)` into the rationals is computable. -/
lemma computable_half_pow : Computable (fun a : ℕ => (1 / 2 : ℚ) ^ a) := by
  refine computable_of_num_den (N := fun _ : ℕ => (1 : ℤ)) (D := fun a : ℕ => 2 ^ a)
    (Computable.const 1)
    ((nat_pow_primrec₂.comp (Primrec.const 2) Primrec.id).to_comp)
    (fun a => by positivity) (fun a => ?_)
  push_cast
  rw [div_pow, one_pow]

/-- The base strategy scheme is computable. -/
lemma computable_baseFamilyScheme :
    FamilyStrategySchemeComputable (fun a (_e : ℕ) => baseFamilyStrategy a) := by
  unfold FamilyStrategySchemeComputable baseFamilyStrategy
  have hq : Computable (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) =>
      (1 / 2 : ℚ) ^ p.1.1) :=
    computable_half_pow.comp (Computable.fst.comp Computable.fst)
  have hpair : Computable (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) =>
      ((([] : GacsDayNode)), (1 / 2 : ℚ) ^ p.1.1) ) :=
    (Computable.const ([] : GacsDayNode)).pair hq
  have hmove : Computable (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) =>
      [((([] : GacsDayNode)), (1 / 2 : ℚ) ^ p.1.1)]) :=
    Computable₂.comp Primrec.list_cons.to_comp hpair (Computable.const [])
  have hn : Computable (fun p : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) =>
      p.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  exact Computable₂.comp Primrec.list_replicate.to_comp hn hmove


/-- The base strategy plays the same move at every time: mass `2 ^ (-a)` at the root of each tree.
-/
lemma playClientFamily_base (a : ℕ) (A : Allocation) (n : ℕ) (sm : ℕ → FamilyServerMove) (t : ℕ) :
    playClientFamily A n (baseFamilyStrategy a) sm t =
      List.replicate n [(([] : GacsDayNode), (1 / 2 : ℚ) ^ a)] := by
  cases t <;> simp [playClientFamily, baseFamilyStrategy]

/-- Under the base strategy the request is `2 ^ (-a)` at the root of every tree and zero elsewhere.
-/
lemma baseFamily_getReq (a : ℕ) (A : Allocation) (n : ℕ) (sm : ℕ → FamilyServerMove)
    (t : ℕ) {i : ℕ} (hi : i < n) (x : GacsDayNode) :
    getReq (familyClientMoveAt (playClientFamily A n (baseFamilyStrategy a) sm t) i) x =
      if x = [] then (1 / 2 : ℚ) ^ a else 0 := by
  rw [playClientFamily_base]
  have : List.replicate n [(([] : GacsDayNode), (1 / 2 : ℚ) ^ a)] =
      baseFamilyStrategy a A n ([], []) := rfl
  rw [this, familyClientMoveAt_baseFamilyStrategy a A n ([], []) hi]
  by_cases hx : x = []
  · simp [hx, getReq_root_singleton]
  · simp [hx, getReq_singleton_of_ne _ _ hx]

/-- Client play is legal under the base family strategy. -/
private lemma baseFamily_familyClientPlayLegal (a : ℕ) (n : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) :
    familyClientPlayLegal n 2 (dyadicScale a)
      (playClientFamily A n (baseFamilyStrategy a) sm) := by
  constructor
  · intro t i hi
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [baseFamily_getReq a A n sm t hi x]
      split <;> positivity
    · rw [baseFamily_getReq a A n sm t hi []]
      simp [dyadicScale]
    · intro x
      have hzero : ∀ c : Fin 2,
          getReq (familyClientMoveAt (playClientFamily A n (baseFamilyStrategy a) sm t) i)
            (x ++ [c.val]) = 0 := by
        intro c
        rw [baseFamily_getReq a A n sm t hi]
        simp
      rw [Finset.sum_congr rfl (fun c _ => hzero c)]
      simp only [Finset.sum_const_zero]
      rw [baseFamily_getReq a A n sm t hi x]
      split <;> positivity
  · intro t i hi x
    simp only [getFamilyReq]
    rw [baseFamily_getReq a A n sm t hi x, baseFamily_getReq a A n sm (t + 1) hi x]

/-- Each request in the base family play avoids small values below `2^(-e)`. -/
private lemma baseFamily_familyRequestAvoidsSmall (a e : ℕ) (hae : a ≤ e) (n : ℕ)
    (A : Allocation) (sm : ℕ → FamilyServerMove) (t : ℕ) :
    familyRequestAvoidsSmall n ((1 / 2 : ℚ) ^ e)
      (playClientFamily A n (baseFamilyStrategy a) sm t) := by
  have hpow_le : ((1 : ℚ) / 2) ^ e ≤ ((1 : ℚ) / 2) ^ a :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hae
  intro i hi x
  rw [baseFamily_getReq a A n sm t hi x]
  by_cases hx : x = []
  · exact Or.inr (by simpa [hx] using hpow_le)
  · exact Or.inl (by simp [hx])

/-- Under the base family strategy the total root request equals `n * 2^(-a)`. -/
private lemma baseFamily_totalRootRequest (a : ℕ) (A : Allocation) (n T : ℕ)
    (sm : ℕ → FamilyServerMove) :
    totalRootRequest n (playClientFamily A n (baseFamilyStrategy a) sm T) =
      (n : ℚ) * (1 / 2 : ℚ) ^ a := by
  unfold totalRootRequest getFamilyReq
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    baseFamily_getReq a A n sm T i.isLt [])]
  simp

/-- If every root request of the base family strategy is eventually served at level `2 ^ (-a)`,
the base strategy meets the family gray-mass goal. -/
private lemma baseFamily_familyGrayGoal_of_served (a e : ℕ) (hae : a ≤ e) (n : ℕ)
    (A : Allocation) (sm : ℕ → FamilyServerMove)
    (hsm : familyServerPlayLegal n 2 A sm)
    (hserved : ∀ i : Fin n, ∃ t, Serves (getFamilyAlloc (sm t) i.val []) ((1 / 2 : ℚ) ^ a)) :
    familyGrayGoal (halfAmplification 0) ((3 / 4 : ℚ) * dyadicScale a) e e n A
      (playClientFamily A n (baseFamilyStrategy a) sm) sm := by
  choose tt htt using hserved
  set T := Finset.univ.sup tt with hT
  have hserveT : ∀ i : Fin n, ∃ y, y ∈ getFamilyAlloc (sm T) i.val [] ∧
      (((1 / 2 : ℚ) ^ a : ℚ) : ℝ) ≤ (1 / 2 : ℝ) ^ y.length := by
    intro i
    have hlegal_i : serverPlayLegal 2 (fun t => familyServerMoveAt (sm t) i.val) :=
      hsm.1 i.val i.isLt
    exact serves_mono_time hlegal_i (Finset.le_sup (Finset.mem_univ i)) (htt i)
  choose c hc_mem hc_le using hserveT
  have hc_len : ∀ i, (c i).length ≤ a := by
    intro i
    by_contra hlt
    push Not at hlt
    have h := hc_le i
    have hcast : (((1 / 2 : ℚ) ^ a : ℚ) : ℝ) = (1 / 2 : ℝ) ^ a := by push_cast; ring
    rw [hcast] at h
    have hstrict : (1 / 2 : ℝ) ^ (c i).length < (1 / 2 : ℝ) ^ a :=
      pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hlt
    linarith
  have hcard : n * 2 ^ (e - a) ≤
      (newGrayCells e e (familyAllocated n T sm) A.toFinset).card := by
    refine card_newGrayCells_ge_of_disjoint_witnesses a e hae _ _ n c hc_len ?_ ?_ ?_
    · intro i
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, List.mem_toFinset.mpr (hc_mem i)⟩
    · intro i j hij
      exact hsm.2.1 T i.val i.isLt j.val j.isLt
        (fun h => hij (Fin.ext h)) (c i) (hc_mem i) (c j) (hc_mem j)
    · intro i u hu
      exact hsm.2.2 T i.val i.isLt [] (c i) (hc_mem i) u (List.mem_toFinset.mp hu)
  have hpow : ((2 : ℚ) ^ (e - a)) * (1 / 2 : ℚ) ^ e = (1 / 2 : ℚ) ^ a := by
    obtain ⟨k, rfl⟩ : ∃ k, e = a + k := ⟨e - a, by omega⟩
    have hk : a + k - a = k := by omega
    rw [hk, pow_add, div_pow, div_pow, one_pow, one_pow]
    field_simp
  have hmass : (n : ℚ) * (1 / 2 : ℚ) ^ a ≤ familyGrayMass e e n T A sm := by
    unfold familyGrayMass
    have hcQ : ((n * 2 ^ (e - a) : ℕ) : ℚ) ≤
        ((newGrayCells e e (familyAllocated n T sm) A.toFinset).card : ℚ) := by
      exact_mod_cast hcard
    have hstep : (n : ℚ) * (1 / 2 : ℚ) ^ a
        = ((n * 2 ^ (e - a) : ℕ) : ℚ) * (1 / 2 : ℚ) ^ e := by
      push_cast
      rw [mul_assoc, hpow]
    rw [hstep]
    gcongr
  have hroot : totalRootRequest n (playClientFamily A n (baseFamilyStrategy a) sm T)
      = (n : ℚ) * (1 / 2 : ℚ) ^ a :=
    baseFamily_totalRootRequest a A n T sm
  refine ⟨T, ?_, ?_, ?_⟩
  · refine le_trans ?_ hmass
    have hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
    have hpa : (0 : ℚ) < (1 / 2 : ℚ) ^ a := by positivity
    simp only [dyadicScale]
    nlinarith
  · rw [hroot]
    simp only [halfAmplification]
    norm_num
    exact hmass
  · rw [hroot]
    simp only [halfAmplification, dyadicScale]
    norm_num
    have hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
    have hpa : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ a := by positivity
    nlinarith

/-- The base strategy meets the family game specification at amplification `1`, establishing the
base case of the induction. -/
lemma grayFamilyGameSpec_base (a e : ℕ) (hae : a ≤ e) (n : ℕ) (hn : 1 ≤ n)
    (A : Allocation) :
    GrayFamilyGameSpec (halfAmplification 0) (dyadicScale a)
      ((3 / 4 : ℚ) * dyadicScale a) e e 0 2 n A (baseFamilyStrategy a) := by
  refine ⟨hn, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [halfAmplification]
  · simp only [dyadicScale]; positivity
  · simp only [dyadicScale]; positivity
  · intro sm _hsm
    exact baseFamily_familyClientPlayLegal a n A sm
  · intro sm _hsm t
    exact baseFamily_familyRequestAvoidsSmall a e hae n A sm t
  · intro sm hsm
    by_cases hserved : ∀ i : Fin n, ∃ t, Serves (getFamilyAlloc (sm t) i.val []) ((1 / 2 : ℚ) ^ a)
    · exact Or.inr (baseFamily_familyGrayGoal_of_served a e hae n A sm hsm hserved)
    · left
      push Not at hserved
      obtain ⟨i, hi⟩ := hserved
      refine ⟨i.val, i.isLt, ⟨0, [], by simp, by simp, ?_⟩⟩
      intro t
      rw [baseFamily_getReq a A n sm 0 i.isLt []]
      simpa [getFamilyAlloc] using hi t
  · intro sm hsm
    by_cases hserved : ∀ i : Fin n, ∃ t, Serves (getFamilyAlloc (sm t) i.val []) ((1 / 2 : ℚ) ^ a)
    · exact Or.inr (baseFamily_familyGrayGoal_of_served a e hae n A sm hsm hserved)
    · left
      push Not at hserved
      obtain ⟨i, hi⟩ := hserved
      refine ⟨i.val, i.isLt, 0, [], by simp, by simp, ?_, ?_⟩
      · intro t
        rw [baseFamily_getReq a A n sm 0 i.isLt []]
        simpa [getFamilyAlloc] using hi t
      · rw [baseFamily_getReq a A n sm 0 i.isLt []]
        simp
  · intro hist x i hi j hj
    have : familyClientMoveAt (baseFamilyStrategy a A n hist) j =
        [(([] : GacsDayNode), (1 / 2 : ℚ) ^ a)] :=
      familyClientMoveAt_baseFamilyStrategy a A n hist hj
    rw [this, getReq_singleton_of_ne _ _ (by simp)]
  · intro hist x hx j hj
    have : familyClientMoveAt (baseFamilyStrategy a A n hist) j =
        [(([] : GacsDayNode), (1 / 2 : ℚ) ^ a)] :=
      familyClientMoveAt_baseFamilyStrategy a A n hist hj
    rw [this, getReq_singleton_of_ne _ _ (by intro h; rw [h] at hx; simp at hx)]

/-- Base of the source induction (`kappa = 1`). -/
theorem dayGray_base : GrayFamilyInductionStatement 0 := by
  refine ⟨fun _a e => e, fun _a _e => 2, fun a _e => baseFamilyStrategy a,
    Computable.snd, Computable.const 2, fun a e => le_rfl, computable_baseFamilyScheme, ?_⟩
  intro alphaDepth epsDepth _ha hae
  exact ⟨le_rfl, fun n A hn => grayFamilyGameSpec_base alphaDepth epsDepth hae n hn A⟩


/-- The single-tree client strategy obtained by running the family scheme on a family of size one
with empty unavailable set. -/
def clientStrategyFromFamily (σ : UniformFamilyStrategyScheme) (k a e : ℕ) : ClientStrategy :=
  fun hist => familyClientMoveAt (playClientFamily [] 1 (σ k a e) (fun i =>
    [hist.2.getD i []]) hist.2.length) 0

/-- The first family client move does not depend on the server play. -/
lemma playClientFamily_zero (A : Allocation) (n : ℕ) (σ : ClientFamilyStrategy) (sm1 sm2 : ℕ
  → FamilyServerMove) :
    playClientFamily A n σ sm1 0 = playClientFamily A n σ sm2 0 := by
  unfold playClientFamily
  rfl

/-- The family client move at time `t` depends only on the server moves before `t`. -/
lemma playClientFamily_eq_of_sm_eq (A : Allocation) (n : ℕ) (σ : ClientFamilyStrategy) :
    ∀ t (sm1 sm2 : ℕ → FamilyServerMove), (∀ i < t, sm1 i = sm2 i) →
    playClientFamily A n σ sm1 t = playClientFamily A n σ sm2 t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero =>
      intro sm1 sm2 h
      exact playClientFamily_zero A n σ sm1 sm2
    | succ t =>
      intro sm1 sm2 h
      unfold playClientFamily
      congr 2
      · congr 1
        funext i
        apply ih i.val (by omega)
        intro j hj
        apply h
        omega
      · congr 1
        funext i
        apply h
        omega



/-- The first `k` client moves the strategy produces against the recorded list of server moves,
computed by replaying the history from the start. -/
def familySelfPlayAux (A : Allocation) (n : ℕ) (σ : ClientFamilyStrategy) (ss : List
  FamilyServerMove) : ℕ → List FamilyClientMove
  | 0 => []
  | k + 1 =>
    let prev := familySelfPlayAux A n σ ss k
    prev ++ [σ A n (prev, ss.take k)]

/-- All client moves the strategy produces against the recorded list of server moves. -/
def familySelfPlay (A : Allocation) (n : ℕ) (σ : ClientFamilyStrategy) (ss : List
  FamilyServerMove) : List FamilyClientMove :=
  familySelfPlayAux A n σ ss ss.length

/-- The replay agrees with the primitive recursion appending one move per step, the form used to
establish computability. -/
lemma familySelfPlayAux_eq_rec (A : Allocation) (n : ℕ) (σ : ClientFamilyStrategy) (ss : List
  FamilyServerMove) (k : ℕ) :
    familySelfPlayAux A n σ ss k =
      Nat.rec ([] : List FamilyClientMove) (fun y IH => IH ++ [σ A n (IH, ss.take y)]) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [familySelfPlayAux, ih]

/-- For a computable family of strategies the replay is computable in the strategy index and the
recorded server moves. -/
lemma computable₂_familySelfPlay (A : Allocation) (n : ℕ) {σ' : ℕ → ClientFamilyStrategy}
    (h : Computable₂ (fun (d : ℕ) p => σ' d A n p)) :
    Computable₂ (fun d ss => familySelfPlay A n (σ' d) ss) := by
  have hstep : Computable₂ (fun (a : ℕ × List FamilyServerMove) (p : ℕ × List FamilyClientMove) =>
      p.2 ++ [σ' a.1 A n (p.2, a.2.take p.1)]) := by
    have hσ : Computable (fun q : (ℕ × List FamilyServerMove) × (ℕ × List FamilyClientMove) =>
        σ' q.1.1 A n (q.2.2, q.1.2.take q.2.1)) :=
      h.comp (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.snd.comp Computable.snd)
          (Primrec.list_take.to_comp.comp (Computable.fst.comp Computable.snd)
          (Computable.snd.comp Computable.fst)))
    exact Computable.list_concat.comp (Computable.snd.comp Computable.snd) hσ
  have hrec := Computable.nat_rec (f := fun a : ℕ × List FamilyServerMove => a.2.length)
    (g := fun _ : ℕ × List FamilyServerMove => ([] : List FamilyClientMove))
    (Computable.list_length.comp Computable.snd) (Computable.const _) hstep
  refine hrec.of_eq ?_
  rintro ⟨d, ss⟩
  exact (familySelfPlayAux_eq_rec _ _ _ _ _).symm

/-- Replaying the first `k` moves against a truncated server play reproduces the actual client
moves. -/
lemma familySelfPlayAux_ofFn (A : Allocation) (n : ℕ) (σ : ClientFamilyStrategy) (sms : ℕ
  → FamilyServerMove) (t k : ℕ) (h : k ≤ t) :
    familySelfPlayAux A n σ (List.ofFn fun i : Fin t => sms i) k =
    List.ofFn fun i : Fin k => playClientFamily A n σ sms i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : k ≤ t := Nat.le_trans (Nat.le_succ k) h
    rw [familySelfPlayAux]
    rw [ih hk]
    rw [list_take_ofFn _ _ hk]
    have h1 : (List.ofFn fun i : Fin (k + 1) => playClientFamily A n σ sms ↑i) =
      (List.ofFn fun i : Fin k =>
        playClientFamily A n σ sms ↑i) ++ [playClientFamily A n σ sms k] := by
      exact List.ofFn_succ_last
    rw [h1]
    cases k with
    | zero =>
      rw [playClientFamily]
      rfl
    | succ m =>
      rw [playClientFamily]

/-- Replaying against the first `t` server moves reproduces the actual first `t` client moves. -/
lemma familySelfPlay_ofFn (A : Allocation) (n : ℕ) (σ : ClientFamilyStrategy) (sms : ℕ
  → FamilyServerMove) (t : ℕ) :
    familySelfPlay A n σ (List.ofFn fun i : Fin t => sms i) =
    List.ofFn fun i : Fin t => playClientFamily A n σ sms i := by
  rw [familySelfPlay]
  have h_len : (List.ofFn fun i : Fin t => sms i).length = t := by simp
  rw [h_len]
  exact familySelfPlayAux_ofFn A n σ sms t t (le_refl t)

/-- The client move at time `t` is the strategy applied to the replayed history, which is the form
used for its computability. -/
lemma playClientFamily_eq_selfPlay (A : Allocation) (n : ℕ) (σ : ClientFamilyStrategy) (sms : ℕ
  → FamilyServerMove) (t : ℕ) :
    playClientFamily A n σ sms t =
    σ A n (familySelfPlay A n σ (List.ofFn fun i : Fin t => sms i),
      List.ofFn fun i : Fin t => sms i) := by
  cases t with
  | zero =>
    simp [playClientFamily, familySelfPlay, familySelfPlayAux]
  | succ t =>
    rw [playClientFamily]
    congr
    rw [familySelfPlay_ofFn]

/-- Wrapping each entry of a list of server moves into a singleton family move can be written as a
`List.map`. -/
lemma ofFn_getD_eq_map (l : List ServerMove) :
    (List.ofFn fun i : Fin l.length => [l.getD i []]) = l.map (fun m => [m]) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD]

/-- The single-tree strategy is the family scheme applied to the replayed one-element family
history. -/
lemma clientStrategyFromFamily_eq (σ : UniformFamilyStrategyScheme) (k a e : ℕ) (hist :
  GameHistory) :
    clientStrategyFromFamily σ k a e hist =
    familyClientMoveAt
      (σ k a e [] 1
        (familySelfPlay [] 1 (σ k a e) (hist.2.map fun m => [m]), hist.2.map fun m => [m]))
      0 := by
  unfold clientStrategyFromFamily
  congr 1
  rw [playClientFamily_eq_selfPlay]
  congr
  · rw [ofFn_getD_eq_map]
  · rw [ofFn_getD_eq_map]

/-- One halving step of the binary-length computation: halve the running value and
increment the counter, unless the value has already reached `0`. -/
def natSizeStep (p : ℕ × ℕ) : ℕ × ℕ := if p.1 = 0 then p else (p.1 / 2, p.2 + 1)

/-- Halving a nonzero natural number decreases its binary size by exactly one. -/
lemma nat_size_div_two (x : ℕ) (hx : x ≠ 0) : Nat.size x = Nat.size (x / 2) + 1 := by
  apply le_antisymm
  · refine Nat.size_le.mpr ?_
    have h := Nat.lt_size_self (x / 2)
    have hx2 : x ≤ 2 * (x / 2) + 1 := by omega
    calc x ≤ 2 * (x / 2) + 1 := hx2
      _ < 2 ^ (Nat.size (x / 2) + 1) := by rw [pow_succ]; omega
  · rcases Nat.eq_zero_or_pos (x / 2) with h | h
    · simp only [h, Nat.size_zero, Nat.zero_add]
      exact Nat.size_pos.mpr (Nat.pos_of_ne_zero hx)
    · have hs : 0 < Nat.size (x / 2) := Nat.size_pos.mpr h
      have h1 : 2 ^ (Nat.size (x / 2) - 1) ≤ x / 2 := Nat.lt_size.mp (by omega)
      have h2 : 2 ^ Nat.size (x / 2) ≤ x := by
        have he : 2 ^ Nat.size (x / 2) = 2 * 2 ^ (Nat.size (x / 2) - 1) := by
          rw [← pow_succ']; congr 1; omega
        omega
      exact Nat.lt_size.mpr h2

/-- Iterating the halving step `k` times on a number below `2 ^ k` reduces it to zero and
accumulates
its binary size. -/
lemma natSizeStep_iterate (k : ℕ) : ∀ x acc : ℕ, x < 2 ^ k →
    natSizeStep^[k] (x, acc) = (0, acc + Nat.size x) := by
  induction k with
  | zero =>
    intro x acc hx
    simp only [pow_zero, Nat.lt_one_iff] at hx
    subst hx
    simp
  | succ k ih =>
    intro x acc hx
    rw [Function.iterate_succ_apply]
    by_cases h : x = 0
    · subst h
      have h0 : natSizeStep ((0 : ℕ), acc) = (0, acc) := by simp [natSizeStep]
      rw [h0, ih 0 acc (by positivity)]
    · have h1 : natSizeStep (x, acc) = (x / 2, acc + 1) := by simp [natSizeStep, h]
      have h2 : x / 2 < 2 ^ k := Nat.div_lt_of_lt_mul (by rw [pow_succ] at hx; omega)
      rw [h1, ih (x / 2) (acc + 1) h2, nat_size_div_two x h]
      congr 1
      omega

/-- The halving step used to compute the binary size is primitive recursive. -/
lemma primrec_natSizeStep : Primrec natSizeStep := by
  unfold natSizeStep
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) Primrec.id
    (Primrec.pair (Primrec.nat_div.comp Primrec.fst (Primrec.const 2))
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)))

/-- The binary size of a natural number is computable. -/
lemma computable_nat_size : Computable (fun d : ℕ => Nat.size d) := by
  have hstep : Computable₂ (fun (_ : ℕ) (p : ℕ × ℕ × ℕ) => natSizeStep p.2) :=
    primrec_natSizeStep.to_comp.comp (Computable.snd.comp Computable.snd)
  have hrec := Computable.nat_rec (σ := ℕ × ℕ) (f := fun n : ℕ => n)
      (g := fun n : ℕ => (n, 0)) (h := fun _ p => natSizeStep p.2)
      Computable.id (Computable.pair Computable.id (Computable.const 0)) hstep
  refine (Computable.snd.comp hrec).of_eq fun n => ?_
  have hiter : ∀ m : ℕ, natSizeStep^[m] (n, 0) =
      Nat.rec (motive := fun _ => ℕ × ℕ) (n, 0) (fun _ p => natSizeStep p) m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih]
  rw [← hiter n, natSizeStep_iterate n n 0 Nat.lt_two_pow_self]
  simp

/-- For a computable uniform family scheme the derived single-tree strategies are computable in the
parameter `d`, with stage `8 d` and both depths the binary size of `d`. -/
lemma clientStrategyFromFamily_computable (σ : UniformFamilyStrategyScheme)
    (hcomp : UniformFamilyStrategySchemeComputable σ) :
    Computable₂ (fun (d : ℕ) => clientStrategyFromFamily σ (8 * d) (Nat.size d) (Nat.size d)) := by
  have hsize : Computable (fun d : ℕ => Nat.size d) := computable_nat_size
  have hσ' : Computable₂ (fun (d : ℕ) (p : FamilyGameHistory) =>
      σ (8 * d) (Nat.size d) (Nat.size d) [] 1 p) := by
    have harg : Computable (fun q : ℕ × FamilyGameHistory =>
        (((8 * q.1, Nat.size q.1, Nat.size q.1) : ℕ × ℕ × ℕ),
          ((([] : Allocation), (((1 : ℕ), q.2) : ℕ × FamilyGameHistory)) :
            Allocation × (ℕ × FamilyGameHistory)))) := by
      refine Computable.pair (Computable.pair
        (Primrec.nat_mul.to_comp.comp (Computable.const 8) Computable.fst)
        (Computable.pair (hsize.comp Computable.fst) (hsize.comp Computable.fst)))
        (Computable.pair (Computable.const [])
          (Computable.pair (Computable.const 1) Computable.snd))
    exact hcomp.comp harg
  have hself := computable₂_familySelfPlay ([] : Allocation) 1
    (σ' := fun d => σ (8 * d) (Nat.size d) (Nat.size d)) hσ'
  have hmap : Computable (fun hist : GameHistory => hist.2.map (fun m => [m])) :=
    (Primrec.list_map Primrec.snd
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to₂).to_comp
  have hmain : Computable (fun q : ℕ × GameHistory =>
      σ (8 * q.1) (Nat.size q.1) (Nat.size q.1) [] 1
        (familySelfPlay [] 1 (fun p => σ (8 * q.1) (Nat.size q.1) (Nat.size q.1) p)
            (q.2.2.map fun m => [m]),
          q.2.2.map fun m => [m])) :=
    hσ'.comp Computable.fst
      (Computable.pair (hself.comp Computable.fst (hmap.comp Computable.snd))
        (hmap.comp Computable.snd))
  refine ((Primrec.list_getD ([] : ClientMove)).to_comp.comp hmain
    (Computable.const 0)).of_eq ?_
  rintro ⟨d, hist⟩
  exact (clientStrategyFromFamily_eq σ (8 * d) (Nat.size d) (Nat.size d) hist).symm

/-- Playing the derived single-tree strategy reproduces the first tree of the family play. -/
lemma playClient_eq_family (σ : UniformFamilyStrategyScheme) (k a e : ℕ) (sm : ℕ → ServerMove) :
    ∀ t, playClient (clientStrategyFromFamily σ k a e) sm t =
    familyClientMoveAt (playClientFamily [] 1 (σ k a e) (fun i => [sm i]) t) 0 := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero =>
      unfold playClient clientStrategyFromFamily
      congr 1
      exact playClientFamily_zero [] 1 (σ k a e) _ _
    | succ t =>
      unfold playClient clientStrategyFromFamily
      dsimp
      have hlen: (List.ofFn fun i : Fin (t+1) => sm ↑i).length = t + 1 := by simp
      rw [hlen]
      congr 1
      apply playClientFamily_eq_of_sm_eq
      intro i hi
      have : i < t + 1 := by omega
      simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_succ,
        List.getD_eq_getElem?_getD, List.cons.injEq, and_true]
      rw [List.getElem?_eq_getElem (by simpa)]
      cases i with
      | zero => simp
      | succ i => simp [List.getElem_ofFn]
end Kolmogorov
