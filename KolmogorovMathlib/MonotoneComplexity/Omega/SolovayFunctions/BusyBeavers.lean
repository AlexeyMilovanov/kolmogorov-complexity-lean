import KolmogorovMathlib.AlgorithmicRandomness.ProbabilityBounded
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.BusyBeaver
import KolmogorovMathlib.Complexity.NatComplexity
import KolmogorovMathlib.MonotoneComplexity.Omega.AntitoneSplit
import KolmogorovMathlib.MonotoneComplexity.Omega.BusyBeaverInfra
import KolmogorovMathlib.MonotoneComplexity.Omega.BusyBeaverSearch
import KolmogorovMathlib.MonotoneComplexity.Omega.CappedScaling
import KolmogorovMathlib.MonotoneComplexity.Omega.IntervalCover
import KolmogorovMathlib.MonotoneComplexity.Omega.ModulusRandom
import KolmogorovMathlib.MonotoneComplexity.Omega.NeighbourhoodCover
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealCantor
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealKraft
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaBitsFromApprox
import KolmogorovMathlib.MonotoneComplexity.Omega.Prediction
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctionComputable
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.Existence
import KolmogorovMathlib.Prefix.UpperSemicomputableBound

/-!
# Busy-beaver functions for prefix and plain complexity

`BP U n` is the largest integer of prefix complexity at most `n`, and `BPlain V n` its plain
counterpart; both are genuine maxima once the sublevel set is nonempty
(`kpNatSublevel_nonempty`, `plainKNatSublevel_nonempty`, `BP_mem_and_le`, `BPlain_mem_and_le`).

### Outline

* elementary properties of the two busy beavers and the dyadic weights their estimates need;
* Theorem 114 and Theorem 115, relating the busy beaver to Solovay functions and to the
  convergence modulus of a computable increasing sequence
  (`convergenceModulus_ge_BPprime_of_isMartinLofRandomReal`);
* the stage machinery for Theorem 116, including the monotone diagonal sums
  (`diagSum_diag_mono`).

Source: SUV §1.2 (p. 21) and §5.7.7 (pp. 169–170).
-/

namespace Kolmogorov
open MeasureTheory ENNReal

/-- **Nonemptiness of the sublevel set.** For an optimal prefix-free machine `K(0)` is
finite, so `0 ∈ kpNatSublevel U n` as soon as `n ≥ K(0)`; below that threshold the
book's `BP(n)` is undefined and `sSup` returns `0`, which is why every statement about
`BP` below is asymptotic in `n`. -/
theorem kpNatSublevel_nonempty {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (kpNatSublevel U n).Nonempty := by
  obtain ⟨c, hc⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨2 * (natToBitString 0).length + c, fun n hn => ⟨0, ?_⟩⟩
  simp only [kpNatSublevel, Set.mem_ofPred_eq]
  calc KPNat U 0 ≤ 2 * ((natToBitString 0).length : ENat) + (c : ENat) := hc _
    _ = ((2 * (natToBitString 0).length + c : ℕ) : ENat) := by push_cast; ring
    _ ≤ (n : ENat) := by exact_mod_cast hn

/-- The same threshold for plain complexity. -/
theorem plainKNatSublevel_nonempty {V : Map} (hV : isOptimalConditional V) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (plainKNatSublevel V n).Nonempty := by
  obtain ⟨c, hc⟩ := plainKNat_le_length V hV
  refine ⟨programLength (Nat.bits 0) + c, fun n hn => ⟨0, ?_⟩⟩
  simp only [plainKNatSublevel, Set.mem_ofPred_eq]
  calc plainKNat V 0 ≤ ((programLength (Nat.bits 0) : ℕ) : ENat) + (c : ENat) := hc 0
    _ = ((programLength (Nat.bits 0) + c : ℕ) : ENat) := by push_cast; ring
    _ ≤ (n : ENat) := by exact_mod_cast hn

/-- **SUV p. 169.** `BP U n` is the maximal integer whose prefix complexity does not
exceed `n`.  Well-behaved exactly on the domain isolated by `kpNatSublevel_finite` and
`kpNatSublevel_nonempty`; see `BP_mem_and_le`. -/
noncomputable def BP (U : Map) (n : ℕ) : ℕ := sSup (kpNatSublevel U n)

/-- **SUV Section 1.2 (p. 21), recalled on p. 169.** `BPlain V n` is the maximal
integer whose plain complexity does not exceed `n`; this is the `B(n)` of
Theorem 15. -/
noncomputable def BPlain (V : Map) (n : ℕ) : ℕ := sSup (plainKNatSublevel V n)

/-- **`BP` really is a maximum** whenever the sublevel set is nonempty: it belongs to
the set and dominates it.  This is the only property of `BP` used below, and it is
false for the junk value, so no statement can be satisfied vacuously. -/
theorem BP_mem_and_le {U : Map} {n : ℕ} (h : (kpNatSublevel U n).Nonempty) :
    BP U n ∈ kpNatSublevel U n ∧ ∀ k ∈ kpNatSublevel U n, k ≤ BP U n :=
  ⟨Nat.sSup_mem h (kpNatSublevel_finite U n).bddAbove,
    fun _ hk => le_csSup (kpNatSublevel_finite U n).bddAbove hk⟩

/-- The same for the plain busy beaver `B(n)`. -/
theorem BPlain_mem_and_le {V : Map} {n : ℕ} (h : (plainKNatSublevel V n).Nonempty) :
    BPlain V n ∈ plainKNatSublevel V n ∧ ∀ k ∈ plainKNatSublevel V n, k ≤ BPlain V n :=
  ⟨Nat.sSup_mem h (plainKNatSublevel_finite V n).bddAbove,
    fun _ hk => le_csSup (plainKNatSublevel_finite V n).bddAbove hk⟩

/-! #### Elementary properties of the busy beavers

All of the following are **proved**; they are the form in which Theorems 114–116 and
Problem 165 actually use `BP` and `BPlain`. -/

/-- The prefix sublevel sets grow with the complexity budget. -/
theorem kpNatSublevel_subset {U : Map} {a b : ℕ} (h : a ≤ b) :
    kpNatSublevel U a ⊆ kpNatSublevel U b := by
  intro k hk
  simp only [kpNatSublevel, Set.mem_ofPred_eq] at hk ⊢
  exact le_trans hk (by exact_mod_cast h)

/-- The plain sublevel sets grow with the complexity budget. -/
theorem plainKNatSublevel_subset {V : Map} {a b : ℕ} (h : a ≤ b) :
    plainKNatSublevel V a ⊆ plainKNatSublevel V b := by
  intro k hk
  simp only [plainKNatSublevel, Set.mem_ofPred_eq] at hk ⊢
  exact le_trans hk (by exact_mod_cast h)

/-- The prefix busy beaver is non-decreasing. -/
theorem BP_mono (U : Map) : Monotone (BP U) := by
  intro a b hab
  rcases Set.eq_empty_or_nonempty (kpNatSublevel U a) with he | hne
  · rw [BP, he, csSup_empty]
    exact Nat.zero_le _
  · exact csSup_le_csSup (kpNatSublevel_finite U b).bddAbove hne (kpNatSublevel_subset hab)

/-- The plain busy beaver `B` is non-decreasing. -/
theorem BPlain_mono (V : Map) : Monotone (BPlain V) := by
  intro a b hab
  rcases Set.eq_empty_or_nonempty (plainKNatSublevel V a) with he | hne
  · rw [BPlain, he, csSup_empty]
    exact Nat.zero_le _
  · exact csSup_le_csSup (plainKNatSublevel_finite V b).bddAbove hne
      (plainKNatSublevel_subset hab)

/-- Any number of prefix complexity at most `n` is at most `BP n`.  Unlike
`BP_mem_and_le` this needs no nonemptiness hypothesis: the witness supplies it. -/
theorem le_BP_of_KPNat_le {U : Map} {n k : ℕ} (h : KPNat U k ≤ (n : ENat)) : k ≤ BP U n :=
  le_csSup (kpNatSublevel_finite U n).bddAbove h

/-- The same for the plain busy beaver `B` of SUV Section 1.2. -/
theorem le_BPlain_of_plainKNat_le {V : Map} {n k : ℕ} (h : plainKNat V k ≤ (n : ENat)) :
    k ≤ BPlain V n :=
  le_csSup (plainKNatSublevel_finite V n).bddAbove h

/-- **Everything above `BP n` is complex** (SUV p. 169): the direction of the `BP`
characterisation used by Theorem 114 and Problem 165. -/
theorem lt_KPNat_of_BP_lt {U : Map} {n k : ℕ} (h : BP U n < k) : (n : ENat) < KPNat U k := by
  by_contra hle
  exact absurd (le_BP_of_KPNat_le (not_lt.1 hle)) (not_le.2 h)

/-- The same for the plain busy beaver. -/
theorem lt_plainKNat_of_BPlain_lt {V : Map} {n k : ℕ} (h : BPlain V n < k) :
    (n : ENat) < plainKNat V k := by
  by_contra hle
  exact absurd (le_BPlain_of_plainKNat_le (not_lt.1 hle)) (not_le.2 h)

/-- **`BP` is bounded by any upper bound of its sublevel set.**  The shape in which the
lower bounds `BP(k - c) ≤ …` of Theorems 114–115 are established. -/
theorem BP_le_of_forall {U : Map} {n b : ℕ} (h : ∀ k, KPNat U k ≤ (n : ENat) → k ≤ b) :
    BP U n ≤ b := by
  rcases Set.eq_empty_or_nonempty (kpNatSublevel U n) with he | hne
  · rw [BP, he, csSup_empty]
    exact Nat.zero_le _
  · exact csSup_le hne h

/-- **No natural number has prefix complexity `0`** with respect to an optimal
prefix-free machine, so `BP U 0 = 0`. -/
theorem kpNatSublevel_zero_eq_empty {U : Map} (hU : IsOptimalPrefixConditional U) :
    kpNatSublevel U 0 = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro i hi
  obtain ⟨p, hplen, hprod⟩ :=
    (condK_le_iff U (natToBitString i) [] 0).1 (by simpa [kpNatSublevel, KPNat, KP_eq_condK]
      using hi)
  have hp : p = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hplen)
  subst hp
  obtain ⟨c, hc⟩ := KPPlain_le_two_mul_length U hU
  have key : ∀ x : BitString, x = natToBitString i := by
    intro x
    have hxfin : KPPlain U x ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (hc x)
      have hcast : (2 * (x.length : ENat) + (c : ENat)) = ((2 * x.length + c : ℕ) : ENat) := by
        push_cast; ring
      rw [hcast]
      exact ENat.natCast_ne_top _
    obtain ⟨q, hq, -⟩ := exists_program_of_KP_ne_top (M := U) (x := x) (y := []) hxfin
    have hqe : ([] : BitString) = q :=
      hU.isPrefixMachine.eq_of_prefix hprod hq (List.nil_prefix)
    exact Part.mem_unique (hqe ▸ hq) hprod
  have h1 := key []
  have h2 := key [true]
  rw [← h1] at h2
  exact absurd h2 (by simp)

/-- `BP U 0 = 0` for an optimal prefix-free machine. -/
theorem BP_zero {U : Map} (hU : IsOptimalPrefixConditional U) : BP U 0 = 0 := by
  rw [BP, kpNatSublevel_zero_eq_empty hU, csSup_empty]
  rfl

/-- **SUV p. 171.** `C(x) ≤ K(x) + O(1)` makes the *plain* busy beaver at least as
large as the prefix one after an `O(1)` shift of the argument: `BP(n) ≤ B(n + c)`.

The two sublevel sets use different codings of `ℕ` (`natToBitString` for `KPNat`,
`Nat.bits` for `plainKNat`); the re-coding costs `O(1)` by
`exists_const_KPNat_natBits_equiv`.  The converse (`B(n) ≤ BP(n + O(log n))`, the
`O(log n)`-precision of Theorem 116) needs SUV Theorem 65 and is *not* claimed. -/
theorem exists_const_BP_le_BPlain {U V : Map} (hU : IsOptimalPrefixConditional U)
    (hV : isOptimalConditional V) : ∃ c : ℕ, ∀ n : ℕ, BP U n ≤ BPlain V (n + c) := by
  obtain ⟨c₁, h₁⟩ := plain_le_prefix V U hV hU.isPrefixDecompressor
  obtain ⟨c₂, h₂⟩ := exists_const_KPNat_natBits_equiv U hU
  refine ⟨c₁ + c₂, fun n => ?_⟩
  rcases Set.eq_empty_or_nonempty (kpNatSublevel U n) with he | hne
  · rw [BP, he, csSup_empty]
    exact Nat.zero_le _
  · have hmem : KPNat U (BP U n) ≤ (n : ENat) := (BP_mem_and_le hne).1
    refine le_BPlain_of_plainKNat_le (V := V) (n := n + (c₁ + c₂)) ?_
    calc plainKNat V (BP U n)
        ≤ KPPlain U (Nat.bits (BP U n)) + (c₁ : ENat) := h₁ _
      _ ≤ (KPNat U (BP U n) + (c₂ : ENat)) + (c₁ : ENat) := by gcongr; exact h₂.2 _
      _ ≤ ((n : ENat) + (c₂ : ENat)) + (c₁ : ENat) := by gcongr
      _ = ((n + (c₁ + c₂) : ℕ) : ENat) := by push_cast; ring

/-- **SUV p. 171, the `O(log n)` half of the plain/prefix comparison behind Theorem 116.**
`B(n) ≤ BP(n + O(log n))`.

Together with `exists_const_BP_le_BPlain` (`BP(n) ≤ B(n + O(1))`) this is the whole
"the difference between plain and prefix complexity (that could make `B(n)` greater than
`BP(n)`) can be compensated by an `O(log n)`-change in `n`" of the source — the plain/prefix
bookkeeping that both halves of Theorem 116 need. -/
theorem exists_const_BPlain_le_BP {U V : Map} (hU : IsOptimalPrefixConditional U)
    (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ n : ℕ, BPlain V n ≤ BP U (n + c * Nat.log 2 (n + 2) + c) := by
  obtain ⟨c₁, h₁⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨c₂, h₂, -⟩ := exists_const_KPNat_natBits_equiv U hU
  obtain ⟨c₃, h₃⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨max 2 (2 + c₁ + c₂ + c₃), fun n => ?_⟩
  rcases Set.eq_empty_or_nonempty (plainKNatSublevel V n) with he | hne
  · rw [BPlain, he, csSup_empty]
    exact Nat.zero_le _
  · have hmem : plainKNat V (BPlain V n) ≤ (n : ENat) := (BPlain_mem_and_le hne).1
    have hfin : plainKNat V (BPlain V n) ≠ ⊤ := by
      intro h
      rw [h] at hmem
      exact absurd hmem (by simp)
    obtain ⟨kC, hkC⟩ := ENat.ne_top_iff_exists.1 hfin
    have hkCn : kC ≤ n := by
      rw [← hkC] at hmem
      exact_mod_cast hmem
    have hT65 : KPPlain U (Nat.bits (BPlain V n))
        ≤ (kC : ENat) + KPPlain U (Nat.bits kC) + (c₁ : ENat) :=
      h₁ (Nat.bits (BPlain V n)) kC hkC.symm
    have hsize : (Nat.bits kC).length ≤ Nat.log 2 (n + 2) + 1 := by
      rw [Nat.size_eq_bits_len]
      refine Nat.size_le.2 ?_
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (n + 2)
      omega
    have hsmall : KPPlain U (Nat.bits kC)
        ≤ ((2 * (Nat.log 2 (n + 2) + 1) + c₃ : ℕ) : ENat) := by
      refine le_trans (h₃ (Nat.bits kC)) ?_
      have hstep : (2 : ENat) * (((Nat.bits kC).length : ℕ) : ENat) + (c₃ : ENat)
          ≤ (2 : ENat) * ((Nat.log 2 (n + 2) + 1 : ℕ) : ENat) + (c₃ : ENat) := by
        gcongr
      refine le_trans hstep ?_
      push_cast
      exact le_rfl
    refine le_BP_of_KPNat_le (U := U) ?_
    calc KPNat U (BPlain V n) ≤ KPPlain U (Nat.bits (BPlain V n)) + (c₂ : ENat) := h₂ _
      _ ≤ ((kC : ENat) + KPPlain U (Nat.bits kC) + (c₁ : ENat)) + (c₂ : ENat) := by gcongr
      _ ≤ ((n : ENat) + ((2 * (Nat.log 2 (n + 2) + 1) + c₃ : ℕ) : ENat) + (c₁ : ENat))
            + (c₂ : ENat) := by
          gcongr
      _ = ((n + (2 * (Nat.log 2 (n + 2) + 1) + c₃) + c₁ + c₂ : ℕ) : ENat) := by push_cast; ring
      _ ≤ ((n + max 2 (2 + c₁ + c₂ + c₃) * Nat.log 2 (n + 2)
            + max 2 (2 + c₁ + c₂ + c₃) : ℕ) : ENat) := by
          refine Nat.cast_le.2 ?_
          have hA : 2 ≤ max 2 (2 + c₁ + c₂ + c₃) := le_max_left _ _
          have hB : 2 + c₁ + c₂ + c₃ ≤ max 2 (2 + c₁ + c₂ + c₃) := le_max_right _ _
          have hmul : 2 * Nat.log 2 (n + 2)
              ≤ max 2 (2 + c₁ + c₂ + c₃) * Nat.log 2 (n + 2) :=
            Nat.mul_le_mul_right _ hA
          omega

/-! #### Dyadic weights: the elementary facts the `BP`/`BPapriori`
bridge needs, all proved. -/

/-- Dyadic weights are *strictly* decreasing in the exponent. -/
theorem inv_two_pow_succ_lt (k : ℕ) : (2 : ℝ≥0∞)⁻¹ ^ (k + 1) < (2 : ℝ≥0∞)⁻¹ ^ k := by
  have hne : (2 : ℝ≥0∞)⁻¹ ^ k ≠ 0 := pow_ne_zero _ (by simp)
  have htop : (2 : ℝ≥0∞)⁻¹ ^ k ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have hlt : (2 : ℝ≥0∞)⁻¹ < 1 := by simp
  calc (2 : ℝ≥0∞)⁻¹ ^ (k + 1) = (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ^ k := by ring
    _ < 1 * (2 : ℝ≥0∞)⁻¹ ^ k := ENNReal.mul_lt_mul_left hne htop hlt
    _ = (2 : ℝ≥0∞)⁻¹ ^ k := one_mul _

/-- A complexity of at most `k` gives a weight of at least `2^{-k}`. -/
theorem inv_two_pow_le_complexityWeight {x : ENat} {k : ℕ} (h : x ≤ (k : ENat)) :
    (2 : ℝ≥0∞)⁻¹ ^ k ≤ complexityWeight x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact absurd h (by simp)
  · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hx
    subst hv
    have hvk : v ≤ k := by exact_mod_cast h
    rw [complexityWeight_coe]
    exact inv_two_pow_antitone hvk

/-- A complexity strictly above `k` gives a weight of at most `2^{-(k+1)}`. -/
theorem complexityWeight_le_inv_two_pow_succ {x : ENat} {k : ℕ} (h : (k : ENat) < x) :
    complexityWeight x ≤ (2 : ℝ≥0∞)⁻¹ ^ (k + 1) := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hx
    subst hv
    have hkv : k + 1 ≤ v := by
      have : k < v := by exact_mod_cast h
      omega
    rw [complexityWeight_coe]
    exact inv_two_pow_antitone hkv

/-- **SUV p. 170.** Reformulation of `BP` in terms of the a priori probability: the
minimal `N` such that all `n > N` have a priori probability less than `2^{-k}`.
`⊤` when no such `N` exists. -/
noncomputable def BPapriori (m : ℕ → ℝ≥0∞) (k : ℕ) : ℕ∞ :=
  natSInfTop {N : ℕ | ∀ n, N < n → m n < (2 : ℝ≥0∞)⁻¹ ^ k}

/-- **SUV p. 170.** `BP' m k` is the minimal `N` such that the *total* a priori
probability of all `n > N` is less than `2^{-k}`; `⊤` when no such `N` exists. -/
noncomputable def BPprime (m : ℕ → ℝ≥0∞) (k : ℕ) : ℕ∞ :=
  natSInfTop {N : ℕ | (∑' n, if N < n then m n else 0) < (2 : ℝ≥0∞)⁻¹ ^ k}

/-- **SUV p. 170.** Both a priori cutoffs are defined (`≠ ⊤`) for a maximal lower
semicomputable semimeasure: its total mass is finite, so the tail sums tend to `0`.
This is the domain fact that the old `ℕ`-valued `sInf` silently assumed. -/
theorem BPprime_ne_top {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m) (k : ℕ) :
    BPprime m k ≠ ⊤ := by
  have hpos : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹ ^ k := by
    refine pos_iff_ne_zero.2 (pow_ne_zero _ ?_)
    simp
  have hfin : (∑' n, m n) ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hm.tsum_le_one
  obtain ⟨N, hN⟩ := exists_tsum_tail_lt hfin hpos
  rw [BPprime, Ne, natSInfTop_eq_top_iff]
  exact Set.nonempty_iff_ne_empty.1 ⟨N, hN⟩

/-- **SUV p. 170.** The two definitions of `BP` agree up to an `O(1)` shift of the
argument. -/
theorem BP_equiv_BPapriori {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ k : ℕ, BPapriori m k ≤ (BP U (k + c) : ℕ∞) ∧
      (BP U k : ℕ∞) ≤ BPapriori m (k + c) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h₁, h₂⟩ := exists_const_KPNat_aprioriNat_equiv hm hU
  obtain ⟨d₁, hd₁⟩ := ENNReal.exists_inv_two_pow_lt hc₁.ne'
  obtain ⟨d₂, hd₂⟩ := ENNReal.exists_inv_two_pow_lt hc₂.ne'
  refine ⟨max d₁ d₂, fun k => ⟨?_, ?_⟩⟩
  · -- `BP U (k + c)` is itself a cutoff for `BPapriori m k`.
    refine natSInfTop_le_coe (fun n hn => ?_)
    have hKn : ((k + max d₁ d₂ : ℕ) : ENat) < KPNat U n := lt_KPNat_of_BP_lt hn
    have hw : complexityWeight (KPNat U n) ≤ (2 : ℝ≥0∞)⁻¹ ^ (k + max d₁ d₂ + 1) :=
      complexityWeight_le_inv_two_pow_succ hKn
    have hstep : (2 : ℝ≥0∞)⁻¹ ^ d₁ * m n ≤ (2 : ℝ≥0∞)⁻¹ ^ (k + max d₁ d₂ + 1) :=
      le_trans (le_trans (by gcongr) (h₁ n)) hw
    have hsplit : (2 : ℝ≥0∞)⁻¹ ^ (k + max d₁ d₂ + 1)
        = (2 : ℝ≥0∞)⁻¹ ^ d₁ * (2 : ℝ≥0∞)⁻¹ ^ (k + max d₁ d₂ + 1 - d₁) := by
      rw [← pow_add]
      congr 1
      have : d₁ ≤ max d₁ d₂ := le_max_left _ _
      omega
    rw [hsplit] at hstep
    have hcancel : m n ≤ (2 : ℝ≥0∞)⁻¹ ^ (k + max d₁ d₂ + 1 - d₁) :=
      (ENNReal.mul_le_mul_iff_right (pow_ne_zero _ (by simp)) (ENNReal.pow_ne_top (by simp))).1
        hstep
    refine lt_of_le_of_lt (le_trans hcancel ?_) (inv_two_pow_succ_lt k)
    refine inv_two_pow_antitone ?_
    have : d₁ ≤ max d₁ d₂ := le_max_left _ _
    omega
  · -- every cutoff for `BPapriori m (k + c)` dominates `BP U k`.
    refine le_sInf ?_
    rintro _ ⟨N, hN, rfl⟩
    have hle : BP U k ≤ N := by
      refine BP_le_of_forall fun j hj => ?_
      by_contra hgt
      push Not at hgt
      have hmj : m j < (2 : ℝ≥0∞)⁻¹ ^ (k + max d₁ d₂) := hN j hgt
      have hw : (2 : ℝ≥0∞)⁻¹ ^ k ≤ complexityWeight (KPNat U j) :=
        inv_two_pow_le_complexityWeight hj
      have hlow : (2 : ℝ≥0∞)⁻¹ ^ (d₂ + k) ≤ m j := by
        calc (2 : ℝ≥0∞)⁻¹ ^ (d₂ + k) = (2 : ℝ≥0∞)⁻¹ ^ d₂ * (2 : ℝ≥0∞)⁻¹ ^ k := by rw [pow_add]
          _ ≤ c₂ * complexityWeight (KPNat U j) := by gcongr
          _ ≤ m j := h₂ j
      have hup : m j < (2 : ℝ≥0∞)⁻¹ ^ (d₂ + k) := by
        refine lt_of_lt_of_le hmj (inv_two_pow_antitone ?_)
        have : d₂ ≤ max d₁ d₂ := le_max_right _ _
        omega
      exact absurd hlow (not_le.2 hup)
    change ((BP U k : ℕ) : ℕ∞) ≤ ((N : ℕ) : ℕ∞)
    exact_mod_cast hle

/-- **SUV p. 170.** "Generally speaking, `BP'(m)` can be greater than `BP(m)`." -/
theorem BPapriori_le_BPprime {m : ℕ → ℝ≥0∞} (_hm : IsUniversalSemimeasureNat m) (k : ℕ) :
    BPapriori m k ≤ BPprime m k := by
  refine sInf_le_sInf ?_
  rintro _ ⟨N, hN, rfl⟩
  refine ⟨N, ?_, rfl⟩
  intro n hn
  refine lt_of_le_of_lt ?_ hN
  calc m n = (if N < n then m n else 0) := by simp [hn]
    _ ≤ ∑' n', (if N < n' then m n' else 0) :=
      ENNReal.le_tsum (f := fun n' => if N < n' then m n' else 0) n

/-- **SUV p. 169.** The *modulus of convergence* of `aₙ → α`: the minimal `N` such
that `|α - aₙ| < ε` for all `n > N` — the source's own quantifier (p. 169: "there
exists some `N` such that `|α - aₙ| < ε` for all `n > N`; the minimal `N` with this
property").  `⊤` when the sequence does not `ε`-approximate `α` eventually, so a
divergent sequence can no longer masquerade as one with modulus `0`. -/
noncomputable def convergenceModulus (a : ℕ → ℚ) (α : ℝ) (ε : ℝ) : ℕ∞ :=
  natSInfTop {N : ℕ | ∀ n, N < n → |α - (a n : ℝ)| < ε}

/-- A convergent sequence has a finite modulus at every positive precision; this is
the domain fact that Theorems 114–115 need and that the old totalization hid. -/
theorem convergenceModulus_ne_top {a : ℕ → ℚ} {α : ℝ}
    (h : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α)) {ε : ℝ} (hε : 0 < ε) :
    convergenceModulus a α ε ≠ ⊤ := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h ε hε
  rw [convergenceModulus, Ne, natSInfTop_eq_top_iff]
  refine Set.nonempty_iff_ne_empty.1 ⟨N, fun n hn => ?_⟩
  have := hN n (le_of_lt hn)
  rwa [Real.dist_eq, abs_sub_comm] at this

/-! ### Theorem 114 -/

/-- **SUV Theorem 114 (Section 5.7, pp. 169–170), the covering argument — new C11b
leaf.**  For a random `α`, every partial sum that `2^{-k}`-approximates `α` has index of
prefix complexity at least `k - O(1)`.  This is the whole content of the forward half of
Theorem 114; the rest is the bookkeeping done in
`convergenceModulus_ge_busyBeaverPrefix_of_isMartinLofRandomReal` below. -/
theorem exists_const_le_KPNat_add_of_partialSums_approx {U : Map}
    (hU : IsOptimalPrefixConditional U) {r : ℕ → ℚ} (hr : Computable r)
    {α : ℝ} (h : IsMartinLofRandomReal α) :
    ∃ c : ℕ, ∀ (k i : ℕ), |α - (partialSums r i : ℝ)| < (2 : ℝ)⁻¹ ^ k →
      (k : ENat) ≤ KPNat U i + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    exists_const_inv_two_pow_le_dist_of_KPNat_lt hU (computable_partialSums hr) h
  refine ⟨c, fun k i hki => ?_⟩
  have hfin := KPNat_ne_top hU i
  have hcoe : KPNat U i = (((KPNat U i).toNat : ℕ) : ℕ∞) := (ENat.natCast_toNat hfin).symm
  set κ := (KPNat U i).toNat with hκ
  have hlt : KPNat U i < ((κ + 1 : ℕ) : ℕ∞) := by
    rw [hcoe]
    exact_mod_cast Nat.lt_succ_self κ
  have hdist := hc i (κ + 1) hlt
  have hkle : k ≤ κ + c := by
    by_contra hcon
    push Not at hcon
    have hstep : ((2 : ℝ)⁻¹) ^ k ≤ ((2 : ℝ)⁻¹) ^ (κ + 1 + c) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  rw [hcoe]
  exact_mod_cast hkle

/-- If the series has a random sum, then `N(2^{-k}) ≥ BP(k - c)` for some `c` and all `k`.
*Proof (assembled from `exists_const_le_KPNat_add_of_partialSums_approx`).* Write `N` for
the modulus at precision `2^{-k}`; it is finite (`convergenceModulus_ne_top`) and, being a
minimum over a nonempty set of naturals, belongs to that set: every `j > N` satisfies `|α -
aⱼ| < 2^{-k}` and hence `k ≤ K(j) + c`. So any `j` with `K(j) ≤ k - (c+1)` must satisfy `j ≤
N`, and `BP(k - (c+1)) ≤ N` follows. The small-`k` case, where `k - (c+1)` truncates to `0`,
is covered by `kpNatSublevel_zero_eq_empty`.  SUV Theorem 114 (Section 5.7, p. 169), forward
direction. -/
theorem convergenceModulus_ge_busyBeaverPrefix_of_isMartinLofRandomReal {U : Map}
    (hU : IsOptimalPrefixConditional U) {r : ℕ → ℚ} (hr : Computable r) (_hr0 : ∀ i, 0 ≤ r i)
    {α : ℝ} (hsum : Filter.Tendsto (fun n => (partialSums r n : ℝ)) Filter.atTop (nhds α))
    (h : IsMartinLofRandomReal α) :
    ∃ c : ℕ, ∀ k : ℕ,
      (BP U (k - c) : ℕ∞) ≤ convergenceModulus (partialSums r) α ((2 : ℝ)⁻¹ ^ k) := by
  obtain ⟨c, hc⟩ := exists_const_le_KPNat_add_of_partialSums_approx hU hr h
  refine ⟨c + 1, fun k => ?_⟩
  have hεpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  have hne : convergenceModulus (partialSums r) α ((2 : ℝ)⁻¹ ^ k) ≠ ⊤ :=
    convergenceModulus_ne_top hsum hεpos
  have hSne :
      {N : ℕ | ∀ n, N < n → |α - ((partialSums r n : ℚ) : ℝ)| < (2 : ℝ)⁻¹ ^ k}.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    exact hne ((natSInfTop_eq_top_iff _).2 hemp)
  have hmem := Nat.sInf_mem hSne
  have hcoe : convergenceModulus (partialSums r) α ((2 : ℝ)⁻¹ ^ k)
      = ((sInf {N : ℕ | ∀ n, N < n → |α - ((partialSums r n : ℚ) : ℝ)| < (2 : ℝ)⁻¹ ^ k} :
          ℕ) : ℕ∞) :=
    natSInfTop_eq_coe_sInf hSne
  rw [hcoe]
  have hkey : BP U (k - (c + 1)) ≤
      sInf {N : ℕ | ∀ n, N < n → |α - ((partialSums r n : ℚ) : ℝ)| < (2 : ℝ)⁻¹ ^ k} := by
    refine BP_le_of_forall fun j hj => ?_
    by_contra hgt
    push Not at hgt
    have hkle := hc k j (hmem j hgt)
    rcases Nat.lt_or_ge k (c + 1) with hk | hk
    · have hz : k - (c + 1) = 0 := by omega
      rw [hz] at hj
      have hj0 : j ∈ kpNatSublevel U 0 := by simpa [kpNatSublevel] using hj
      rw [kpNatSublevel_zero_eq_empty hU] at hj0
      exact hj0
    · have hle : (k : ENat) ≤ ((k - (c + 1) : ℕ) : ENat) + (c : ENat) :=
        le_trans hkle (by gcongr)
      have hcast : k ≤ (k - (c + 1)) + c := by exact_mod_cast hle
      omega
  exact_mod_cast hkey

/-- **A fast-growing modulus makes every late index complex** (SUV p. 170, first
sentence of the reverse direction of Theorem 114).  If `BP(k - c)` is below
the modulus at precision `2^{-k}`, then every index strictly beyond that modulus has
prefix complexity at least `k - c`, hence `k ≤ K(i) + c`. -/
theorem exists_const_le_KPNat_of_modulus_ge {U : Map} {r : ℕ → ℚ} {α : ℝ}
    (h : ∃ c : ℕ, ∀ k : ℕ,
      (BP U (k - c) : ℕ∞) ≤ convergenceModulus (partialSums r) α ((2 : ℝ)⁻¹ ^ k)) :
    ∃ c : ℕ, ∀ (k i : ℕ),
      convergenceModulus (partialSums r) α ((2 : ℝ)⁻¹ ^ k) < (i : ℕ∞) →
        (k : ENat) ≤ KPNat U i + (c : ENat) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun k i hi => ?_⟩
  have hBPlt : (BP U (k - c) : ℕ∞) < (i : ℕ∞) := lt_of_le_of_lt (hc k) hi
  have hBP : BP U (k - c) < i := by exact_mod_cast hBPlt
  have hlt : ((k - c : ℕ) : ENat) < KPNat U i := lt_KPNat_of_BP_lt hBP
  rcases eq_or_ne (KPNat U i) ⊤ with htop | hfin
  · simp [htop]
  · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hfin
    rw [← hv] at hlt ⊢
    have hvlt : k - c < v := by exact_mod_cast hlt
    have : k ≤ v + c := by omega
    exact_mod_cast this

/-- **SUV Theorem 114 (Section 5.7, p. 170), the Levin–Schnorr step — new C11b leaf.**
If for some constant `c` every index beyond the modulus of convergence at precision
`2^{-k}` has `K(i) ≥ k - c`, then the sum is ML-random. -/
theorem isMartinLofRandomReal_of_modulus_complexity {U : Map}
    (hU : IsOptimalPrefixConditional U) {r : ℕ → ℚ} (hr : Computable r) (hr0 : ∀ i, 0 ≤ r i)
    {α : ℝ} (hsum : Filter.Tendsto (fun n => (partialSums r n : ℝ)) Filter.atTop (nhds α))
    (h : ∃ c : ℕ, ∀ (k i : ℕ),
      convergenceModulus (partialSums r) α ((2 : ℝ)⁻¹ ^ k) < (i : ℕ∞) →
        (k : ENat) ≤ KPNat U i + (c : ENat)) :
    IsMartinLofRandomReal α := by
  classical
  obtain ⟨c, hc⟩ := h
  -- shift `α` into `(0,1]` by a rational; randomness is invariant
  set q : ℚ := ((⌈α⌉ : ℤ) : ℚ) - 1 with hqdef
  have hqR : ((q : ℚ) : ℝ) = ((⌈α⌉ : ℤ) : ℝ) - 1 := by rw [hqdef]; push_cast; ring
  set β : ℝ := α - ((q : ℚ) : ℝ) with hβdef
  have h0 : 0 < β := by
    rw [hβdef, hqR]
    have := Int.ceil_lt_add_one α
    linarith
  have h1 : β ≤ 1 := by
    rw [hβdef, hqR]
    have := Int.le_ceil α
    linarith
  -- the shifted computable sequence
  set b : ℕ → ℚ := fun n => partialSums r n - q with hbdef
  have hbcomp : Computable b :=
    computable₂_ratSub.comp (computable_partialSums hr) (Computable.const q)
  have hpm : Monotone (partialSums r) := by
    refine monotone_nat_of_le_succ fun n => ?_
    have hstep : partialSums r (n + 1) = partialSums r n + r n := by
      rw [partialSums, partialSums, Finset.sum_range_succ]
    rw [hstep]
    linarith [hr0 n]
  have hbmono : Monotone b := fun m n hmn => by
    rw [hbdef]
    exact sub_le_sub_right (hpm hmn) q
  have hcastb : ∀ n : ℕ, ((b n : ℚ) : ℝ) = ((partialSums r n : ℚ) : ℝ) - ((q : ℚ) : ℝ) := by
    intro n
    rw [hbdef]
    push_cast
    ring
  have hblim : Filter.Tendsto (fun n => ((b n : ℚ) : ℝ)) Filter.atTop (nhds β) := by
    refine Filter.Tendsto.congr (fun n => (hcastb n).symm) ?_
    rw [hβdef]
    exact hsum.sub tendsto_const_nhds
  have hpmR : Monotone (fun n : ℕ => ((partialSums r n : ℚ) : ℝ)) := by
    intro m n hmn
    change ((partialSums r m : ℚ) : ℝ) ≤ ((partialSums r n : ℚ) : ℝ)
    exact_mod_cast hpm hmn
  have hble : ∀ n, ((b n : ℚ) : ℝ) ≤ β := by
    intro n
    rw [hcastb n, hβdef]
    have := hpmR.ge_of_tendsto hsum n
    linarith
  -- translate the modulus hypothesis
  have hmain : IsMartinLofRandomReal β := by
    refine isMartinLofRandomReal_of_modulus_bound hU hbcomp hbmono h0 h1 hble hblim ⟨c, ?_⟩
    rintro k i ⟨N, hNi, hN⟩
    refine hc k i (lt_of_le_of_lt ?_ (by exact_mod_cast hNi : (N : ℕ∞) < (i : ℕ∞)))
    refine natSInfTop_le_coe (S := {N : ℕ | ∀ n, N < n → |α - (partialSums r n : ℝ)| <
      (2 : ℝ)⁻¹ ^ k}) ?_
    intro j hj
    have hjj := hN j hj
    rw [hcastb j, hβdef] at hjj
    have heq : α - ((q : ℚ) : ℝ) - (((partialSums r j : ℚ) : ℝ) - ((q : ℚ) : ℝ))
        = α - ((partialSums r j : ℚ) : ℝ) := by ring
    rwa [heq] at hjj
  have hshift := (isMartinLofRandomReal_add_rat β q).2 hmain
  have heq : β + ((q : ℚ) : ℝ) = α := by rw [hβdef]; ring
  rwa [heq] at hshift

/-- If `N(2^{-k}) ≥ BP(k - c)` for some `c` and all `k`, then the sum is random. *Proof.*
`exists_const_le_KPNat_of_modulus_ge` turns the modulus hypothesis into the complexity
hypothesis of `isMartinLofRandomReal_of_modulus_complexity`.  SUV Theorem 114 (Section 5.7,
p. 169), reverse direction. -/
theorem isMartinLofRandomReal_of_convergenceModulus_ge_busyBeaverPrefix {U : Map}
    (hU : IsOptimalPrefixConditional U) {r : ℕ → ℚ} (hr : Computable r) (hr0 : ∀ i, 0 ≤ r i)
    {α : ℝ} (hsum : Filter.Tendsto (fun n => (partialSums r n : ℝ)) Filter.atTop (nhds α))
    (h : ∃ c : ℕ, ∀ k : ℕ,
      (BP U (k - c) : ℕ∞) ≤ convergenceModulus (partialSums r) α ((2 : ℝ)⁻¹ ^ k)) :
    IsMartinLofRandomReal α :=
  isMartinLofRandomReal_of_modulus_complexity hU hr hr0 hsum
    (exists_const_le_KPNat_of_modulus_ge h)

/-- The computable series `∑ rᵢ` of nonnegative rationals has the Solovay property
(equivalently, has a random sum) if and only if its modulus of convergence grows fast:
`N(2^{-k}) ≥ BP(k - c)` for some `c` and for all `k`.  SUV Theorem 114 (Section 5.7, p.
169). -/
theorem hasSolovayProperty_iff_convergenceModulus_ge_busyBeaverPrefix {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {U : Map} (hU : IsOptimalPrefixConditional U)
    {r : ℕ → ℚ} (hr : Computable r) (hr0 : ∀ i, 0 ≤ r i)
    {α : ℝ} (hsum : Filter.Tendsto (fun n => (partialSums r n : ℝ)) Filter.atTop (nhds α)) :
    HasSolovayProperty m r ↔
      ∃ c : ℕ, ∀ k : ℕ,
        (BP U (k - c) : ℕ∞) ≤ convergenceModulus (partialSums r) α ((2 : ℝ)⁻¹ ^ k) := by
  rw [← isMartinLofRandomReal_iff_hasSolovayProperty hm hr hr0 hsum]
  exact ⟨convergenceModulus_ge_busyBeaverPrefix_of_isMartinLofRandomReal hU hr hr0 hsum,
    isMartinLofRandomReal_of_convergenceModulus_ge_busyBeaverPrefix hU hr hr0 hsum⟩

/-! ### Theorem 115 -/

/-- **SUV p. 170.** `m(q)`, the a priori probability of a *rational* `q`, taken through
the shared canonical rational coding `ratBitCode` of `SharedCoding`
rather than through `Encodable.encode`, which in Mathlib denotes two different codes
for `ℚ` (the plain `Encodable ℚ` and the `Denumerable`-derived one behind
`Primcodable ℚ`) and is not tied to the repository's computable `ratCode`.

Invariance remark: `exists_const_KPPlain_ratBitCode_invariant` shows that any other
computable injective coding of `ℚ` changes `K` by `O(1)`, hence the a priori
probability by a `Θ(1)` factor — the precision at which the estimate below is
stated. -/
noncomputable def aprioriRat (m : ℕ → ℝ≥0∞) (q : ℚ) : ℝ≥0∞ :=
  m (bitStringToNat (ratBitCode q))

/-- `aprioriRat` is the a priori probability of the repository's canonical `ℕ`-code of
a rational. -/
@[simp] theorem aprioriRat_eq (m : ℕ → ℝ≥0∞) (q : ℚ) :
    aprioriRat m q = m (ratCode q) := by
  simp [aprioriRat, ratBitCode]

/-- **SUV p. 170, the measure estimate behind Theorem 115.** For a random `α` the
total a priori probability of the rationals in the `2^{-k}`-neighbourhood of `α` is
`O(2^{-k})`; the covering family of "bad" intervals has measure at most `4/c`. -/
theorem exists_const_apriori_neighbourhood_le {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {α : ℝ} (h : IsMartinLofRandomReal α) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ k : ℕ,
      (∑' q : ℚ, if |α - (q : ℝ)| < (2 : ℝ)⁻¹ ^ k then aprioriRat m q else 0)
        ≤ c * (2 : ℝ≥0∞)⁻¹ ^ k := by
  classical
  obtain ⟨c, hct, hc⟩ := exists_const_apriori_ratCode_neighbourhood_le hm h
  refine ⟨c, hct, fun k => ?_⟩
  refine le_trans (le_of_eq (tsum_congr fun q => ?_)) (hc k)
  by_cases hq : |α - (q : ℝ)| < (2 : ℝ)⁻¹ ^ k
  · simp [aprioriRat_eq]
  · simp

/-- Constant `c₀` bounding `c₀ * m n` by `aprioriRat m (a n)` for a computable sequence `a`. -/
private theorem exists_pos_c₀_mul_apriori_le {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    {a : ℕ → ℚ} (ha : Computable a) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ c₀ ≠ ⊤ ∧ ∀ n : ℕ, c₀ * m n ≤ aprioriRat m (a n) := by
  classical
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c₁, c₂, hc₁, hc₂, hA, hB⟩ := exists_const_KPNat_aprioriNat_equiv hm hU
  have hecomp : Computable (fun n : ℕ => natToBitString (ratCode (a n))) :=
    computable_natToBitString.comp (computable_ratCode.comp ha)
  obtain ⟨d, hd⟩ := exists_const_KPPlain_le_KPNat U hU hecomp
  set c₀ : ℝ≥0∞ := c₂ * (2 : ℝ≥0∞)⁻¹ ^ d * c₁ with hc₀def
  have hinvpos : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹ ^ d :=
    ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) d
  have hc₀pos : 0 < c₀ :=
    ENNReal.mul_pos (ENNReal.mul_pos (ne_of_gt hc₂) (ne_of_gt hinvpos)).ne' (ne_of_gt hc₁)
  have hdom : ∀ n : ℕ, c₀ * m n ≤ aprioriRat m (a n) := by
    intro n
    have h1 : KPNat U (ratCode (a n)) ≤ KPNat U n + (d : ENat) := hd n
    have h2 : complexityWeight (KPNat U n) * (2 : ℝ≥0∞)⁻¹ ^ d
        ≤ complexityWeight (KPNat U (ratCode (a n))) := by
      have hcw := complexityWeight_le_of_le h1
      rwa [complexityWeight_add_nat] at hcw
    calc c₀ * m n = c₂ * (2 : ℝ≥0∞)⁻¹ ^ d * (c₁ * m n) := by rw [hc₀def]; ring
      _ ≤ c₂ * (2 : ℝ≥0∞)⁻¹ ^ d * complexityWeight (KPNat U n) := by gcongr; exact hA n
      _ = c₂ * (complexityWeight (KPNat U n) * (2 : ℝ≥0∞)⁻¹ ^ d) := by ring
      _ ≤ c₂ * complexityWeight (KPNat U (ratCode (a n))) := by gcongr
      _ ≤ m (ratCode (a n)) := hB _
      _ = aprioriRat m (a n) := (aprioriRat_eq m (a n)).symm
  have hratle : ∀ q : ℚ, aprioriRat m q ≤ 1 := by
    intro q
    rw [aprioriRat_eq]
    exact le_trans (ENNReal.le_tsum _) hm.tsum_le_one
  have hc₀top : c₀ ≠ ⊤ := by
    intro htop
    have h0 := hdom 0
    rw [htop, ENNReal.top_mul (ne_of_gt (apriori_pos_of_universal hm 0))] at h0
    simpa using le_trans h0 (hratle (a 0))
  exact ⟨c₀, hc₀pos, hc₀top, hdom⟩

/-- Upper bound `C ≤ c₀ * 2^j` for a positive constant `c₀` and finite constant `C`. -/
private theorem exists_nat_pow_two_mul_ge {c₀ C : ℝ≥0∞} (hc₀pos : 0 < c₀) (hc₀top : c₀ ≠ ⊤)
    (hCtop : C ≠ ⊤) : ∃ j : ℕ, C ≤ c₀ * (2 : ℝ≥0∞) ^ j := by
  obtain ⟨j, hj0⟩ :=
    ENNReal.exists_nat_gt (ENNReal.mul_ne_top hCtop (ENNReal.inv_ne_top.2 (ne_of_gt hc₀pos)))
  have hjpow : ((j : ℕ) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ j := by
    have hnat : (j : ℕ) ≤ 2 ^ j := k_le_two_pow_k j
    calc ((j : ℕ) : ℝ≥0∞) ≤ (((2 ^ j : ℕ) : ℝ≥0∞)) := by exact_mod_cast hnat
      _ = (2 : ℝ≥0∞) ^ j := by push_cast; ring
  have hCle : C ≤ c₀ * (2 : ℝ≥0∞) ^ j := by
    have h1 : C * c₀⁻¹ ≤ (2 : ℝ≥0∞) ^ j := le_trans hj0.le hjpow
    calc C = C * c₀⁻¹ * c₀ := by
          rw [mul_assoc, ENNReal.inv_mul_cancel (ne_of_gt hc₀pos) hc₀top, mul_one]
      _ ≤ (2 : ℝ≥0∞) ^ j * c₀ := by gcongr
      _ = c₀ * (2 : ℝ≥0∞) ^ j := by ring
  exact ⟨j, hCle⟩

/-- Simplification of `2^s * (1/2)^t` when `s ≤ t`. -/
private theorem pow_two_mul_inv_two_pow (t s : ℕ) (hst : s ≤ t) :
    (2 : ℝ≥0∞) ^ s * (2 : ℝ≥0∞)⁻¹ ^ t = (2 : ℝ≥0∞)⁻¹ ^ (t - s) := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + s := ⟨t - s, by omega⟩
  have hcan : (2 : ℝ≥0∞) ^ s * (2 : ℝ≥0∞)⁻¹ ^ s = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  rw [Nat.add_sub_cancel]
  calc (2 : ℝ≥0∞) ^ s * (2 : ℝ≥0∞)⁻¹ ^ (u + s)
      = ((2 : ℝ≥0∞) ^ s * (2 : ℝ≥0∞)⁻¹ ^ s) * (2 : ℝ≥0∞)⁻¹ ^ u := by rw [pow_add]; ring
    _ = (2 : ℝ≥0∞)⁻¹ ^ u := by rw [hcan, one_mul]

/-- The tail sum of a universal semimeasure after index `N` is strictly less than 1. -/
private theorem tsum_tail_apriori_lt_one {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    (N : ℕ) : (∑' n, if N < n then m n else 0) < 1 := by
  have hTtop : (∑' n, if N < n then m n else 0) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans ?_ hm.tsum_le_one)
    exact ENNReal.tsum_le_tsum fun n => by by_cases hn : N < n <;> simp [hn]
  have hhead : 0 < ∑ n ∈ Finset.range (N + 1), m n :=
    lt_of_lt_of_le (apriori_pos_of_universal hm 0)
      (Finset.single_le_sum (f := m) (fun i _ => zero_le) (Finset.mem_range.2 (by omega)))
  have h1 : (∑ n ∈ Finset.range (N + 1), m n) + (∑' n, if N < n then m n else 0) ≤ 1 := by
    rw [← tsum_eq_sum_range_add_tsum_tail m N]
    exact hm.tsum_le_one
  have h2 := ENNReal.lt_add_right hTtop (ne_of_gt hhead)
  rw [add_comm] at h2
  exact lt_of_lt_of_le h2 h1

/-- Bounding the weighted tail sum by the sum over rationals in the neighbourhood of `α`. -/
private theorem tsum_tail_mul_le_tsum_apriori_neighbourhood {m : ℕ → ℝ≥0∞} {a : ℕ → ℚ}
    (hmono : StrictMono a) {α : ℝ} {k N : ℕ} {c₀ : ℝ≥0∞} (hdom : ∀ n, c₀ * m n ≤ aprioriRat m (a n))
    (hS : ∀ n, N < n → |α - (a n : ℝ)| < (2 : ℝ)⁻¹ ^ k) :
    c₀ * (∑' n, if N < n then m n else 0)
      ≤ ∑' q : ℚ, (if |α - (q : ℝ)| < (2 : ℝ)⁻¹ ^ k then aprioriRat m q else 0) := by
  classical
  set f : ℚ → ℝ≥0∞ := fun q => if ∃ n, N < n ∧ a n = q then aprioriRat m q else 0 with hfdef
  have hfval : ∀ q : ℚ, f q = if ∃ n, N < n ∧ a n = q then aprioriRat m q else 0 :=
    fun q => by rw [hfdef]
  have hsupp : Function.support f ⊆ Set.range a := by
    intro q hq
    rw [Function.mem_support] at hq
    by_cases hc : ∃ n, N < n ∧ a n = q
    · obtain ⟨n, _, hn⟩ := hc
      exact ⟨n, hn⟩
    · exact absurd (by rw [hfval, ite_eq_right hc]) hq
  have h1 : c₀ * (∑' n, if N < n then m n else 0)
      = ∑' n : ℕ, (if N < n then c₀ * m n else 0) := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun n => by by_cases hn : N < n <;> simp [hn]
  have h2 : ∀ n : ℕ, (if N < n then c₀ * m n else 0) ≤ f (a n) := by
    intro n
    by_cases hn : N < n
    · have hex : ∃ n' : ℕ, N < n' ∧ a n' = a n := ⟨n, hn, rfl⟩
      rw [ite_eq_left hn, hfval, ite_eq_left hex]
      exact hdom n
    · simp [hn]
  have h3 : ∀ q : ℚ,
      f q ≤ (if |α - (q : ℝ)| < (2 : ℝ)⁻¹ ^ k then aprioriRat m q else 0) := by
    intro q
    by_cases hc : ∃ n, N < n ∧ a n = q
    · obtain ⟨n, hn, hq⟩ := hc
      subst hq
      have hex : ∃ n' : ℕ, N < n' ∧ a n' = a n := ⟨n, hn, rfl⟩
      rw [hfval, ite_eq_left hex, ite_eq_left (hS n hn)]
    · rw [hfval, ite_eq_right hc]
      exact zero_le
  calc c₀ * (∑' n, if N < n then m n else 0)
      = ∑' n : ℕ, (if N < n then c₀ * m n else 0) := h1
    _ ≤ ∑' n : ℕ, f (a n) := ENNReal.tsum_le_tsum h2
    _ = ∑' q : ℚ, f q := hmono.injective.tsum_eq hsupp
    _ ≤ _ := ENNReal.tsum_le_tsum h3

/-- **SUV Theorem 115 (Section 5.7, p. 170), the transfer step — new C11b leaf.**
Beyond the modulus of convergence at precision `2^{-k}` the *total* a priori
probability of the indices is at most `2^{-(k-c)}`. -/
theorem exists_const_tsum_apriori_beyond_modulus_lt {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {a : ℕ → ℚ} (ha : Computable a) (hmono : StrictMono a)
    {α : ℝ} (_hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    (h : IsMartinLofRandomReal α) :
    ∃ c : ℕ, ∀ (k N : ℕ), convergenceModulus a α ((2 : ℝ)⁻¹ ^ k) = (N : ℕ∞) →
      (∑' n, if N < n then m n else 0) < (2 : ℝ≥0∞)⁻¹ ^ (k - c) := by
  classical
  obtain ⟨c₀, hc₀pos, hc₀top, hdom⟩ := exists_pos_c₀_mul_apriori_le hm ha
  obtain ⟨C, hCtop, hC⟩ := exists_const_apriori_neighbourhood_le hm h
  obtain ⟨j, hCle⟩ := exists_nat_pow_two_mul_ge hc₀pos hc₀top hCtop
  refine ⟨j + 1, fun k N hkN => ?_⟩
  have hSne : ({N' : ℕ | ∀ n, N' < n → |α - (a n : ℝ)| < (2 : ℝ)⁻¹ ^ k}).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have htop : convergenceModulus a α ((2 : ℝ)⁻¹ ^ k) = ⊤ := by
      rw [convergenceModulus, natSInfTop_eq_top_iff]
      exact hcon
    rw [hkN] at htop
    exact (ENat.natCast_ne_top N) htop
  have hS : ∀ n, N < n → |α - (a n : ℝ)| < (2 : ℝ)⁻¹ ^ k := by
    have hNeq : N = sInf {N' : ℕ | ∀ n, N' < n → |α - (a n : ℝ)| < (2 : ℝ)⁻¹ ^ k} := by
      have hval := hkN
      rw [convergenceModulus, natSInfTop_eq_coe_sInf hSne] at hval
      exact_mod_cast hval.symm
    rw [hNeq]
    exact Nat.sInf_mem hSne
  by_cases hk : k ≤ j
  · rw [show k - (j + 1) = 0 by omega, pow_zero]
    exact tsum_tail_apriori_lt_one hm N
  · push Not at hk
    have hchain := tsum_tail_mul_le_tsum_apriori_neighbourhood hmono hdom hS
    have hfinal : c₀ * (∑' n, if N < n then m n else 0)
        ≤ c₀ * ((2 : ℝ≥0∞) ^ j * (2 : ℝ≥0∞)⁻¹ ^ k) := by
      calc c₀ * (∑' n, if N < n then m n else 0)
          ≤ ∑' q : ℚ, (if |α - (q : ℝ)| < (2 : ℝ)⁻¹ ^ k then aprioriRat m q else 0) := hchain
        _ ≤ C * (2 : ℝ≥0∞)⁻¹ ^ k := hC k
        _ ≤ (c₀ * (2 : ℝ≥0∞) ^ j) * (2 : ℝ≥0∞)⁻¹ ^ k := by gcongr
        _ = c₀ * ((2 : ℝ≥0∞) ^ j * (2 : ℝ≥0∞)⁻¹ ^ k) := by ring
    have hTle : (∑' n, if N < n then m n else 0) ≤ (2 : ℝ≥0∞) ^ j * (2 : ℝ≥0∞)⁻¹ ^ k :=
      (ENNReal.mul_le_mul_iff_right (ne_of_gt hc₀pos) hc₀top).1 hfinal
    have hhalf : ∀ u : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (u + 1) < (2 : ℝ≥0∞)⁻¹ ^ u := by
      intro u
      have hx0 : (2 : ℝ≥0∞)⁻¹ ^ (u + 1) ≠ 0 :=
        ne_of_gt (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) (u + 1))
      have hxt : (2 : ℝ≥0∞)⁻¹ ^ (u + 1) ≠ ⊤ :=
        ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero)
      have hdouble : (2 : ℝ≥0∞)⁻¹ ^ (u + 1) + (2 : ℝ≥0∞)⁻¹ ^ (u + 1) = (2 : ℝ≥0∞)⁻¹ ^ u := by
        rw [← two_mul, pow_succ, ← mul_assoc, mul_comm (2 : ℝ≥0∞) ((2 : ℝ≥0∞)⁻¹ ^ u),
          mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
      calc (2 : ℝ≥0∞)⁻¹ ^ (u + 1)
          < (2 : ℝ≥0∞)⁻¹ ^ (u + 1) + (2 : ℝ≥0∞)⁻¹ ^ (u + 1) := ENNReal.lt_add_right hxt hx0
        _ = (2 : ℝ≥0∞)⁻¹ ^ u := hdouble
    calc (∑' n, if N < n then m n else 0) ≤ (2 : ℝ≥0∞) ^ j * (2 : ℝ≥0∞)⁻¹ ^ k := hTle
      _ = (2 : ℝ≥0∞)⁻¹ ^ (k - j) := pow_two_mul_inv_two_pow k j (by omega)
      _ = (2 : ℝ≥0∞)⁻¹ ^ ((k - (j + 1)) + 1) := by rw [show k - j = (k - (j + 1)) + 1 by omega]
      _ < (2 : ℝ≥0∞)⁻¹ ^ (k - (j + 1)) := hhalf _

/-- Let `aᵢ` be a computable increasing sequence of rational numbers that converges to a random
number `α`. Then `N(2^{-k}) ≥ BP'(k - c)` for some `c` and all `k`. *Proof.* The modulus is
finite (`convergenceModulus_ne_top`), say equal to `N`; by
`exists_const_tsum_apriori_beyond_modulus_lt` this very `N` belongs to the defining set of
`BP'(k - c)`, so the infimum `BP'(k - c)` is at most `N`.  SUV Theorem 115 (Section 5.7, p.
170). -/
theorem convergenceModulus_ge_BPprime_of_isMartinLofRandomReal {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m)
    {a : ℕ → ℚ} (ha : Computable a) (hmono : StrictMono a) {α : ℝ}
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    (h : IsMartinLofRandomReal α) :
    ∃ c : ℕ, ∀ k : ℕ, BPprime m (k - c) ≤ convergenceModulus a α ((2 : ℝ)⁻¹ ^ k) := by
  obtain ⟨c, hc⟩ := exists_const_tsum_apriori_beyond_modulus_lt hm ha hmono hlim h
  refine ⟨c, fun k => ?_⟩
  have hεpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 (convergenceModulus_ne_top hlim hεpos)
  rw [← hN]
  exact natSInfTop_le_coe (hc k N hN.symm)

/-! ### Theorem 116

The two forward statements `exists_computable_gt_BP_of_omegaPrefix` and
`busyBeaver_of_omegaPrefix` are false in their totally computable form (the refutations
`not_exists_computable_gt_BP` / `not_exists_computable_eq_BPlain` are below); they hold
with `Partrec` in place of `Computable`, and are stated in that form in the "corrected
leaves" section below, together with the `…_partrec` `alias`es.  Only the reverse
direction is stated here. -/

/-- The diagonal stage sums increase with the stage: a later stage has inspected more
indices and has assigned each of them at least as much mass. -/
theorem diagSum_diag_mono {A : ℕ → ℕ → ℕ}
    (hstep : ∀ s i, dyadicValue (A s i) s ≤ dyadicValue (A (s + 1) i) (s + 1)) :
    Monotone (fun s : ℕ => diagSum A s s) := by
  intro s t hst
  have hE : ENNReal.ofReal ((diagSum A s s : ℚ) : ℝ)
      ≤ ENNReal.ofReal ((diagSum A t t : ℚ) : ℝ) := by
    rw [ofReal_diagSum, ofReal_diagSum]
    refine le_trans (Finset.sum_le_sum fun k _ => dyadicValue_mono_stage hstep k hst) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => zero_le)
    exact fun x hx => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hst)
  have hnn : (0 : ℝ) ≤ ((diagSum A t t : ℚ) : ℝ) := by
    exact_mod_cast diagSum_nonneg A t t
  have hR := (ENNReal.ofReal_le_ofReal_iff hnn).1 hE
  exact_mod_cast hR

end Kolmogorov
