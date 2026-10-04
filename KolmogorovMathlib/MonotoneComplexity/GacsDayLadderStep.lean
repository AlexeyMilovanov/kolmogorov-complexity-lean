import KolmogorovMathlib.MonotoneComplexity.GacsDayFamilyGame

/-!
# The ladder of SUV pp. 142-144, split into base, half-step and bookkeeping

`GrayStageLadder` (in `GacsDayParallelStep`) bundles everything the uniform
induction needs. Proving it in one go mixes three unrelated jobs: the base
game, Day's half-step `kappa -> kappa + 1/2`, and the arithmetic that keeps the
depth loss and the branching factor inside `grayFamilyEnvelope`. This file
separates them, so that `grayStageLadder_nonempty` becomes a *proved*
assembly of a kernel-checked base theorem and one remaining half-step leaf.

The organising observation is the one the source makes on p. 143: the fine
scale of stage `k` is `delta = epsilon / c_k`, with `c_k` depending on `k`
*alone* and not on `alpha` and `epsilon`. In depth units that says the loss
`deltaDepth k a e - e` is a function of `k` only, and the branching factor is
`max {alpha / epsilon, B_k}` (p. 144). `GrayRung` records exactly that shape,
which is what makes the recurrences of `GrayStageLadder` provable by a plain
recursion on the stage.

The split:

* `grayFamilyGameSpec_base_branching` -- the kernel-checked base game at every
  branching factor;
* `exists_grayLadderStep` -- Day's half-step as one uniformly computable
  transformer of strategy schemes (leaf 2, the remaining mathematics);
* the assembly and the arithmetic, proved here and in `GacsDayParallelStep`;
* three self-contained facts the half-step consumes, proved here:
  `halfStep_accounting`, `ladderRound_count_le`,
  `incomparable_of_alloc_anchor`.
-/

namespace Kolmogorov

/-! ### The rung predicate -/

/-- The branching factor of the charged stage-`k` tree.  The first
`alpha / epsilon` sons are the source population and a disjoint block of the
same size is reserved for spend calls; `B` controls the deeper recursive
branching.  The factor two is absorbed by the final existential envelope. -/
def ladderBranching (B a e : ℕ) : ℕ := max (2 * 2 ^ (e - a)) B

/-- The ladder branching is always at least `2`. -/
lemma two_le_ladderBranching {B : ℕ} (hB : 2 ≤ B) (a e : ℕ) :
    2 ≤ ladderBranching B a e := le_trans hB (le_max_right _ _)

/-- One rung of the induction of SUV p. 142: at stage `k` the scheme `sigma`
wins the family game at amplification `1 + k / 2`, on trees of height `2 * k`
and branching `ladderBranching B`, with fine scale `2 ^ (-(e + L))`.

Neither the depth loss `L` nor the deep branching `B` depends on the scales
`a`, `e`; that is the content of `delta = epsilon / c_k` on p. 143. -/
def GrayRung (k L B : ℕ) (sigma : FamilyStrategyScheme) : Prop :=
  ∀ a e, 1 ≤ a → a ≤ e → ∀ n A, 1 ≤ n →
    GrayFamilyGameSpec (halfAmplification k) (dyadicScale a)
      ((3 / 4 : ℚ) * dyadicScale a) e (e + L) (2 * k)
      (ladderBranching B a e) n A (sigma a e)

/-! ### Leaf 1: the base rung at an arbitrary branching factor -/

/-- The base family strategy produces legal client moves for any legal server play. -/
private lemma baseFamily_clientPlayLegal (b a : ℕ) (n : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (_hsm : familyServerPlayLegal n b A sm) :
    familyClientPlayLegal n b (dyadicScale a)
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
      have hzero : ∀ c : Fin b,
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

/-- The base family strategy achieves the gray goal when all roots are served. -/
private lemma baseFamily_familyGrayGoal (b a e : ℕ) (hae : a ≤ e) (n : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (hsm : familyServerPlayLegal n b A sm)
    (hserved : ∀ i : Fin n, ∃ t, Serves (getFamilyAlloc (sm t) i.val []) ((1 / 2 : ℚ) ^ a)) :
    familyGrayGoal (halfAmplification 0) ((3 / 4 : ℚ) * dyadicScale a) e e n A
      (playClientFamily A n (baseFamilyStrategy a) sm) sm := by
  choose tt htt using hserved
  set T := Finset.univ.sup tt with _hT
  have hserveT : ∀ i : Fin n, ∃ y, y ∈ getFamilyAlloc (sm T) i.val [] ∧
      (((1 / 2 : ℚ) ^ a : ℚ) : ℝ) ≤ (1 / 2 : ℝ) ^ y.length := by
    intro i
    have hlegal_i : serverPlayLegal b (fun t => familyServerMoveAt (sm t) i.val) :=
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
    have _hcQ : ((n * 2 ^ (e - a) : ℕ) : ℚ) ≤
        ((newGrayCells e e (familyAllocated n T sm) A.toFinset).card : ℚ) := by
      exact_mod_cast hcard
    have hstep : (n : ℚ) * (1 / 2 : ℚ) ^ a
        = ((n * 2 ^ (e - a) : ℕ) : ℚ) * (1 / 2 : ℚ) ^ e := by
      push_cast
      rw [mul_assoc, hpow]
    rw [hstep]
    gcongr
  have hroot : totalRootRequest n (playClientFamily A n (baseFamilyStrategy a) sm T)
      = (n : ℚ) * (1 / 2 : ℚ) ^ a := by
    unfold totalRootRequest getFamilyReq
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
      baseFamily_getReq a A n sm T i.isLt [])]
    simp
  refine ⟨T, ?_, ?_, ?_⟩
  · refine le_trans ?_ hmass
    have _hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
    have _hpa : (0 : ℚ) < (1 / 2 : ℚ) ^ a := by positivity
    simp only [dyadicScale]
    nlinarith
  · rw [hroot]
    simp only [halfAmplification]
    norm_num
    exact hmass
  · rw [hroot]
    simp only [halfAmplification, dyadicScale]
    norm_num
    have _hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
    have _hpa : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ a := by positivity
    nlinarith

/-- **Leaf 1.** The base family strategy wins the stage-`0` game on a tree of
any branching factor, not only on the binary tree of `grayFamilyGameSpec_base`.

Plan of closure: copy the proof of `grayFamilyGameSpec_base`. The strategy
`baseFamilyStrategy a` requests `2 ^ (-a)` at the root and `0` at every other
node (`familyClientMoveAt_baseFamilyStrategy`, `getReq_singleton_of_ne`), so of
the eleven fields only `legal` mentions the branching factor at all, through
the coherence inequality `getReq req x >= sum over Fin b of getReq req (x ++
[i])`, whose right-hand side is `0` for every `b`. No other field of that proof
inspects `b`. -/
theorem grayFamilyGameSpec_base_branching (b a e : ℕ) (_hb : 2 ≤ b) (hae : a ≤ e)
    (n : ℕ) (hn : 1 ≤ n) (A : Allocation) :
    GrayFamilyGameSpec (halfAmplification 0) (dyadicScale a)
      ((3 / 4 : ℚ) * dyadicScale a) e e (2 * 0) b n A (baseFamilyStrategy a) := by
  have hpow_le : ((1 : ℚ) / 2) ^ e ≤ ((1 : ℚ) / 2) ^ a :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hae
  refine ⟨hn, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [halfAmplification]
  · simp only [dyadicScale]; positivity
  · simp only [dyadicScale]; positivity
  · intro sm hsm; exact baseFamily_clientPlayLegal b a n A sm hsm
  · -- minimum_request
    intro sm hsm t i hi x
    rw [baseFamily_getReq a A n sm t hi x]
    by_cases hx : x = []
    · exact Or.inr (by simpa [hx] using hpow_le)
    · exact Or.inl (by simp [hx])
  · -- wins
    intro sm hsm
    by_cases hserved : ∀ i : Fin n, ∃ t, Serves (getFamilyAlloc (sm t) i.val []) ((1 / 2 : ℚ) ^ a)
    · right; exact baseFamily_familyGrayGoal b a e hae n A sm hsm hserved
    · left
      push Not at hserved
      obtain ⟨i, hi⟩ := hserved
      refine ⟨i.val, i.isLt, ⟨0, [], by simp, by simp, ?_⟩⟩
      intro t
      rw [baseFamily_getReq a A n sm 0 i.isLt []]
      simpa [getFamilyAlloc] using hi t
  · -- wins_positively
    intro sm hsm
    by_cases hserved : ∀ i : Fin n, ∃ t, Serves (getFamilyAlloc (sm t) i.val []) ((1 / 2 : ℚ) ^ a)
    · right; exact baseFamily_familyGrayGoal b a e hae n A sm hsm hserved
    · left
      push Not at hserved
      obtain ⟨i, hi⟩ := hserved
      refine ⟨i.val, i.isLt, 0, [], by simp, by simp, ?_, ?_⟩
      · intro t
        rw [baseFamily_getReq a A n sm 0 i.isLt []]
        simpa [getFamilyAlloc] using hi t
      · rw [baseFamily_getReq a A n sm 0 i.isLt []]
        simp
  · -- range_supported
    intro hist x i hi j hj
    have : familyClientMoveAt (baseFamilyStrategy a A n hist) j =
        [(([] : GacsDayNode), (1 / 2 : ℚ) ^ a)] :=
      familyClientMoveAt_baseFamilyStrategy a A n hist hj
    rw [this, getReq_singleton_of_ne _ _ (by simp)]
  · -- tree_supported
    intro hist x hx j hj
    have : familyClientMoveAt (baseFamilyStrategy a A n hist) j =
        [(([] : GacsDayNode), (1 / 2 : ℚ) ^ a)] :=
      familyClientMoveAt_baseFamilyStrategy a A n hist hj
    rw [this, getReq_singleton_of_ne _ _ (by intro h; rw [h] at hx; simp at hx)]

/-! ### Leaf 2: Day's half-step -/

/-- The strategy scheme of the ladder: stage `0` is the base game, stage
`k + 1` is the half-step transformer applied to stage `k`. -/
def ladderScheme (F : ℕ → FamilyStrategyScheme → FamilyStrategyScheme) :
    UniformFamilyStrategyScheme :=
  fun k => Nat.rec (motive := fun _ => FamilyStrategyScheme)
    (fun a _e => baseFamilyStrategy a) (fun k' ih => F k' ih) k



/-- The base rung: the stage-zero ladder scheme wins with amplification `1`, no depth loss and
branching `2`. -/
theorem grayRung_zero (F : ℕ → FamilyStrategyScheme → FamilyStrategyScheme) :
    GrayRung 0 0 2 (ladderScheme F 0) := by
  intro a e _ha hae n A hn
  have h := grayFamilyGameSpec_base_branching (ladderBranching 2 a e) a e
    (two_le_ladderBranching le_rfl a e) hae n hn A
  simpa [ladderScheme] using h

/-! ### Three self-contained facts the half-step consumes -/

/-- **The accounting inequality of SUV pp. 140 and 143.** With `gamma` the sum
of the non-final request increases and `M` the reserved mass `m * epsilon`,
amplification `kappa` on the recursive calls plus the fresh `(3/4) * M` gives
amplification `kappa + 1/2` overall. Tight at `kappa = 1`, `gamma = M`. -/
theorem halfStep_accounting {kappa gamma M : ℚ} (hk : 1 ≤ kappa) (_hg : 0 ≤ gamma)
    (hM : 0 ≤ M) (hcap : gamma ≤ M) :
    (kappa + 1 / 2) * (gamma + M / (6 * kappa)) ≤ kappa * gamma + (3 / 4) * M := by
  have hkpos : (0 : ℚ) < kappa := lt_of_lt_of_le one_pos hk
  rw [← sub_nonneg]
  have key : kappa * gamma + (3 / 4) * M - (kappa + 1 / 2) * (gamma + M / (6 * kappa))
      = (7 * kappa * M - 6 * kappa * gamma - M) / (12 * kappa) := by
    field_simp
    ring
  rw [key]
  refine div_nonneg ?_ (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr hk) hM,
    mul_le_mul_of_nonneg_left hcap (le_of_lt hkpos)]

/-- **The iteration bound of SUV p. 143.** A quantity that starts nonnegative,
never exceeds `M` and grows by at least `c` at each of the first `J` steps
bounds `J` by `M / c`. Applied to the sum of the requests of all sons of all
roots, with `c = (3/4) * m * epsilon / (12 * kappa ^ 2)` and `M = m * epsilon`,
this is the `O(k ^ 2)` bound on the number of recursive calls. -/
theorem ladderRound_count_le {c M : ℚ} (S : ℕ → ℚ)
    (h0 : 0 ≤ S 0) (hcap : ∀ j, S j ≤ M) (J : ℕ)
    (hstep : ∀ j, j < J → S j + c ≤ S (j + 1)) :
    (J : ℚ) * c ≤ M := by
  have key : ∀ j, j ≤ J → S 0 + (j : ℚ) * c ≤ S j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hjJ : j ≤ J := le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self j) hj)
      have h1 := ih hjJ
      have h2 := hstep j (lt_of_lt_of_le (Nat.lt_succ_self j) hj)
      push_cast
      linarith
  have h1 := key J le_rfl
  have h2 := hcap J
  linarith

/-- **Freshly reserved space is new gray space.** A cylinder `R` incomparable
to every cylinder of an allocation is incomparable to every cell anchored in
that allocation. This is why the reserved intervals of p. 140 do not overlap
the gray mass of the earlier recursive calls: the witness cells of
`FamilyWitnessForcing` are anchored in `familyAllocated`. -/
theorem incomparable_of_alloc_anchor {R c : BitString} {alloc : Allocation}
    (hR : ∀ y ∈ alloc, ¬ (y <+: R ∨ R <+: y))
    (hc : ∃ y ∈ alloc, y <+: c) :
    ¬ (R <+: c ∨ c <+: R) := by
  obtain ⟨y, hy, hyc⟩ := hc
  intro h
  refine hR y hy ?_
  rcases h with h | h
  · rcases List.prefix_or_prefix_of_prefix h hyc with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'
  · exact Or.inl (hyc.trans h)

/-! ### The ladder data -/

/-- Depth loss of stage `k`: the source `log2 c_k` of p. 143. -/
def ladderLoss (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => c * (k + 1) ^ 2 * ladderLoss c k + c * (k + 1)

/-- Deep branching factor of stage `k`: the `6 * k * c_k` of p. 144. Here
`2 ^ ladderLoss c k` is the current scale ratio `c_k`; charging the previous
ratio would state a strictly stronger recurrence than the source proves. At
`k = 0` the product vanishes, so the value is `2`. -/
def ladderBound (c k : ℕ) : ℕ := max 2 (c * k * 2 ^ ladderLoss c k)

/-- The ladder loses no depth at stage `0`. -/
lemma ladderLoss_zero (c : ℕ) : ladderLoss c 0 = 0 := rfl

/-- The ladder branching bound at stage `0` is `2`. -/
lemma ladderBound_zero (c : ℕ) : ladderBound c 0 = 2 := by simp [ladderBound]

/-- The ladder branching bound at stage `k+1` is `max 2 (c * (k+1) * 2 ^ ladderLoss c (k+1))`. -/
lemma ladderBound_succ (c k : ℕ) :
    ladderBound c (k + 1) = max 2 (c * (k + 1) * 2 ^ ladderLoss c (k + 1)) := by
  rfl

/-- The ladder branching bound is always at least `2`. -/
lemma two_le_ladderBound (c k : ℕ) : 2 ≤ ladderBound c k := le_max_left _ _

/-- For `c ≥ 1` the ladder depth loss is monotone in the stage. -/
lemma ladderLoss_mono (c : ℕ) (hc : 1 ≤ c) : Monotone (ladderLoss c) := by
  refine monotone_nat_of_le_succ fun k => ?_
  have h1 : 1 ≤ c * (k + 1) ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity))
  calc ladderLoss c k = 1 * ladderLoss c k := (one_mul _).symm
    _ ≤ c * (k + 1) ^ 2 * ladderLoss c k := Nat.mul_le_mul_right _ h1
    _ ≤ c * (k + 1) ^ 2 * ladderLoss c k + c * (k + 1) := Nat.le_add_right _ _

/-- The ladder branching bound at stage `k` is below the bound formed with the stage-`k` depth
loss and the stage `k + 1` factor. -/
lemma ladderBound_le_step (c k : ℕ) (_hc : 1 ≤ c) :
    ladderBound c k ≤ max 2 (c * (k + 1) * 2 ^ ladderLoss c k) := by
  unfold ladderBound
  refine max_le_max le_rfl ?_
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left c (Nat.le_succ k))


/-- The ladder depth loss written as an explicit recursion. -/
lemma ladderLoss_eq_rec (c a : ℕ) :
    ladderLoss c a
      = Nat.rec (motive := fun _ => ℕ) 0
          (fun n ih => c * (n + 1) ^ 2 * ih + c * (n + 1)) a := by
  induction a with
  | zero => rfl
  | succ n ih => simp [ladderLoss, ih]

/-- The ladder depth loss is primitive recursive in the stage. -/
lemma primrec_ladderLoss (c : ℕ) : Primrec (ladderLoss c) := by
  have hstep : Primrec₂ (fun n ih : ℕ => c * (n + 1) ^ 2 * ih + c * (n + 1)) := by
    have hn : Primrec (fun p : ℕ × ℕ => p.1 + 1) := Primrec.succ.comp Primrec.fst
    have hsq : Primrec (fun p : ℕ × ℕ => c * (p.1 + 1) ^ 2) := by
      have : Primrec (fun p : ℕ × ℕ => (p.1 + 1) * (p.1 + 1)) :=
        Primrec.nat_mul.comp hn hn
      simpa [pow_two, mul_assoc] using
        (Primrec.nat_mul.comp (Primrec.const c) this)
    have hlin : Primrec (fun p : ℕ × ℕ => c * (p.1 + 1)) :=
      Primrec.nat_mul.comp (Primrec.const c) hn
    exact Primrec.nat_add.comp (Primrec.nat_mul.comp hsq Primrec.snd) hlin
  exact (Primrec.nat_rec₁ (0 : ℕ) hstep).of_eq fun a => (ladderLoss_eq_rec c a).symm

/-- The branching factor `2 ^ ladderLoss c k` is primitive recursive in the stage. -/
lemma primrec_two_pow_ladderLoss (c : ℕ) :
    Primrec (fun k => 2 ^ ladderLoss c k) :=
  primrec_two_pow_aux.comp (primrec_ladderLoss c)

/-- The ladder branching bound is primitive recursive in the stage. -/
lemma primrec_ladderBound (c : ℕ) : Primrec (ladderBound c) :=
  Primrec.nat_max.comp (Primrec.const 2)
    (Primrec.nat_mul.comp
      (Primrec.nat_mul.comp (Primrec.const c) Primrec.id)
      (primrec_two_pow_ladderLoss c))


/-! ### The reserve predicate -/

/-- A reserved interval for son `x` at scale `e`: a cylinder `R` of length `e`
that covers some allocated space of `x`, and does not overlap `A` or the
allocation of any vertex incomparable to `x` (i.e. not in the subtree and not an ancestor). -/
def hasReserve (e : ℕ) (A : Allocation) (m : ServerMove) (x : GacsDayNode) : Prop :=
  ∃ R : BitString, R.length = e ∧
    (∃ v ∈ getAlloc m x, R <+: v) ∧
    (∀ y, ¬ (x <+: y ∨ y <+: x) → ∀ c ∈ getAlloc m y, ¬ (R <+: c ∨ c <+: R)) ∧
    (∀ a ∈ A, ¬ (R <+: a ∨ a <+: R))

/-- Computable implementation of the reserve predicate.

The scan over the other vertices runs over the *keys* of `m` and reads their
allocation back through `getAlloc`, rather than reading the payload of each
entry directly: `getAlloc` resolves a repeated key to its first occurrence, so
reading the payloads would reject a reserve that `hasReserve` accepts whenever
`m` lists a node twice. -/
def getReserve (e : ℕ) (A : Allocation) (m : ServerMove) (x : GacsDayNode) : Option BitString :=
  (getAlloc m x).find? fun v =>
    if e ≤ v.length then
      let R := v.take e
      let avoidsA := A.all fun a => decide ¬ (R <+: a ∨ a <+: R)
      let avoidsOthers := m.all fun p =>
        if x <+: p.1 || p.1 <+: x then true
        else (getAlloc m p.1).all fun c => decide ¬ (R <+: c ∨ c <+: R)
      avoidsA && avoidsOthers
    else false

/-- A vertex with a nonempty allocation occurs as a key of the server move. -/
lemma exists_key_of_getAlloc_ne_nil {m : ServerMove} {y : GacsDayNode}
    (h : getAlloc m y ≠ []) : ∃ p ∈ m, p.1 = y := by
  cases hl : m.lookup y with
  | none => simp [getAlloc, hl] at h
  | some a =>
    obtain ⟨l₁, l₂, hm, -⟩ := List.lookup_eq_some_iff.mp hl
    exact ⟨(y, a), by rw [hm]; simp, rfl⟩

/-- A reserve is returned exactly when one exists. -/
lemma getReserve_isSome_iff {e : ℕ} {A : Allocation} {m : ServerMove} {x : GacsDayNode} :
    (getReserve e A m x).isSome ↔ hasReserve e A m x := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    have hmem : v ∈ getAlloc m x := List.mem_of_find?_eq_some hv
    have hpred := List.find?_some hv
    by_cases hlen : e ≤ v.length
    · simp only [hlen, ite_true, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq] at hpred
      obtain ⟨hA, hoth⟩ := hpred
      refine ⟨v.take e, by simp [hlen], ⟨v, hmem, List.take_prefix _ _⟩, ?_, hA⟩
      intro y hy c hc
      obtain ⟨p, hp, hpy⟩ := exists_key_of_getAlloc_ne_nil (y := y) (m := m)
        (by intro hnil; rw [hnil] at hc; simp at hc)
      have hall := hoth p hp
      simp only [hpy] at hall
      rw [ite_eq_right (by simpa using hy)] at hall
      simpa using (List.all_eq_true.mp hall) c hc
    · simp [hlen] at hpred
  · rintro ⟨R, hRlen, ⟨v, hv, hRv⟩, hoth, hA⟩
    have hlen : e ≤ v.length := hRlen ▸ hRv.length_le
    have hRtake : v.take e = R := by
      have := List.prefix_iff_eq_take.mp hRv
      rw [hRlen] at this
      exact this.symm
    refine List.find?_isSome.mpr ⟨v, hv, ?_⟩
    simp only [hlen, ite_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, hRtake]
    refine ⟨hA, ?_⟩
    intro p hp
    by_cases hcond : x <+: p.1 ∨ p.1 <+: x
    · rw [ite_eq_left (by simpa using hcond)]
    · rw [ite_eq_right (by simpa using hcond)]
      exact List.all_eq_true.mpr fun c hc => by simpa using hoth p.1 hcond c hc

/-- The reserve predicate is decidable, via its computable implementation. -/
instance (e : ℕ) (A : Allocation) (m : ServerMove) (x : GacsDayNode) :
    Decidable (hasReserve e A m x) :=
  decidable_of_iff _ getReserve_isSome_iff

/-! ### The scale of the recursive calls (SUV p. 143) -/

/-- The half-step amplification factor is positive. -/
lemma halfAmplification_pos (k : ℕ) : (0 : ℚ) < halfAmplification k := by
  simp only [halfAmplification]; positivity

/-- The dyadic scale of `a + b` is the scale of `a` divided by `2 ^ b`. -/
lemma dyadicScale_add (a b : ℕ) : dyadicScale (a + b) = dyadicScale a / 2 ^ b := by
  simp [dyadicScale, pow_add, div_eq_mul_inv]

/-- The depth of the scale `alpha'` at which the half-step makes its recursive
calls.  We take two dyadic levels below the window used in the paper.  The
extra factor four pays for deleting the last component meeting each reserve;
it leaves the public asymptotic statement unchanged. -/
def grayCallDepth (k e : ℕ) : ℕ := e + (Nat.size (3 * k + 5) + 2)

/-- The power `2 ^ Nat.size (3 * k + 5)` is at least `3 * k + 6`. -/
lemma two_pow_size_lower (k : ℕ) : 3 * k + 6 ≤ 2 ^ Nat.size (3 * k + 5) :=
  Nat.lt_size_self _

/-- The power `2 ^ Nat.size (3 * k + 5)` is at most `6 * k + 10`. -/
lemma two_pow_size_upper (k : ℕ) : 2 ^ Nat.size (3 * k + 5) ≤ 6 * k + 10 := by
  have hpos : 0 < Nat.size (3 * k + 5) := Nat.size_pos.mpr (by omega)
  have h : 2 ^ (Nat.size (3 * k + 5) - 1) ≤ 3 * k + 5 := Nat.lt_size.mp (by omega)
  have hs : Nat.size (3 * k + 5) = (Nat.size (3 * k + 5) - 1) + 1 := by omega
  rw [hs, pow_succ]
  omega

/-- The recursive-call scale is a power of two in the half-open window
`(dyadicScale e / (48 * kappa_k), dyadicScale e / (24 * kappa_k)]`. -/
theorem grayCallDepth_scale_bounds (k e : ℕ) :
    dyadicScale e / (48 * halfAmplification k) <
        dyadicScale (grayCallDepth k e) ∧
    dyadicScale (grayCallDepth k e) ≤
        dyadicScale e / (24 * halfAmplification k) := by
  set s := Nat.size (3 * k + 5) with hs
  have hD : (0 : ℚ) < dyadicScale e := by simp only [dyadicScale]; positivity
  have hP : (0 : ℚ) < 2 ^ (s + 2) := by positivity
  have heq : dyadicScale (grayCallDepth k e) = dyadicScale e / 2 ^ (s + 2) := by
    rw [grayCallDepth, dyadicScale_add]
  have hlow0 : (6 : ℚ) * halfAmplification k ≤ 2 ^ s := by
    have hc : ((3 * k + 6 : ℕ) : ℚ) ≤ ((2 ^ s : ℕ) : ℚ) := by
      exact_mod_cast two_pow_size_lower k
    push_cast at hc
    simp only [halfAmplification]
    linarith
  have hup0 : (2 : ℚ) ^ s < 12 * halfAmplification k := by
    have hc : ((2 ^ s : ℕ) : ℚ) ≤ ((6 * k + 10 : ℕ) : ℚ) := by
      exact_mod_cast two_pow_size_upper k
    push_cast at hc
    simp only [halfAmplification]
    linarith
  have hlow : (24 : ℚ) * halfAmplification k ≤ 2 ^ (s + 2) := by
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ, pow_succ]
    nlinarith
  have hup : (2 : ℚ) ^ (s + 2) < 48 * halfAmplification k := by
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ, pow_succ]
    nlinarith
  rw [heq]
  refine ⟨div_lt_div_of_pos_left hD hP hup, ?_⟩
  gcongr
  exact mul_pos (by norm_num) (halfAmplification_pos k)

/-- The depth offset paid by one recursive call is linear in the stage. -/
lemma grayCallDepth_le (k e : ℕ) : grayCallDepth k e ≤ e + 3 * k + 7 := by
  have h : Nat.size (3 * k + 5) ≤ 3 * k + 5 := Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [grayCallDepth]
  omega

/-- The call depth of a stage is at least the scale it is called at. -/
lemma le_grayCallDepth (k e : ℕ) : e ≤ grayCallDepth k e := Nat.le_add_right _ _

/-- The call scale is computable jointly in the stage and the scale. -/
lemma computable_grayCallDepth : Computable₂ grayCallDepth := by
  have h : Computable (fun p : ℕ × ℕ => 3 * p.1 + 5) :=
    Primrec.to_comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 3) Primrec.fst) (Primrec.const 5))
  have hs : Computable (fun p : ℕ × ℕ => Nat.size (3 * p.1 + 5) + 2) :=
    Primrec.nat_add.to_comp.comp (computable_nat_size.comp h)
      (Primrec.const 2).to_comp
  exact Primrec.nat_add.to_comp.comp Computable.snd hs

/-- **The concrete `O(k ^ 2)` call bound of SUV p. 143.** With the son-request
total `S` capped by the reserved mass `M` and each recursive call raising it by
at least `M / (16 * kappa_k ^ 2)`, the number of calls is at most
`16 * (k + 1) ^ 2`, independently of the scale ratio. -/
theorem ladderRound_count_le_source
    {M : ℚ} (hM : 0 < M) (S : ℕ → ℚ) (k J : ℕ)
    (h0 : 0 ≤ S 0) (hcap : ∀ j, S j ≤ M)
    (hstep : ∀ j < J,
      S j + M / (16 * (halfAmplification k) ^ 2) ≤ S (j + 1)) :
    J ≤ 16 * (k + 1) ^ 2 := by
  have hkpos : (0 : ℚ) < halfAmplification k := halfAmplification_pos k
  have hden : (0 : ℚ) < 16 * (halfAmplification k) ^ 2 := by positivity
  have hkey := ladderRound_count_le (c := M / (16 * (halfAmplification k) ^ 2)) (M := M)
    S h0 hcap J hstep
  have h1 : (J : ℚ) * M / (16 * (halfAmplification k) ^ 2) ≤ M := by
    rw [mul_div_assoc]; exact hkey
  rw [div_le_iff₀ hden] at h1
  have hJ : (J : ℚ) ≤ 16 * (halfAmplification k) ^ 2 := by nlinarith
  have hb : 16 * (halfAmplification k) ^ 2 ≤ 16 * ((k : ℚ) + 1) ^ 2 := by
    simp only [halfAmplification]
    nlinarith [Nat.cast_nonneg (α := ℚ) k]
  have hfin : (J : ℚ) ≤ ((16 * (k + 1) ^ 2 : ℕ) : ℚ) := by push_cast; linarith
  exact_mod_cast hfin

end Kolmogorov
