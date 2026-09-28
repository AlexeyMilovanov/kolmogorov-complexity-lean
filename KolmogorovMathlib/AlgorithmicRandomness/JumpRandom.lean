import KolmogorovMathlib.AlgorithmicRandomness.EffectiveOpenNormalForm
import KolmogorovMathlib.AlgorithmicRandomness.LevelStrings
import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.AlgorithmicRandomness.OracleSemidecision
import KolmogorovMathlib.MonotoneComplexity.Dimension.ImageMeasure

/-!
# A `0′`-computable Martin-Löf random sequence (SUV Theorem 37)

Let `U` be a universal Martin-Löf test for the uniform measure and let
`V = U 2`, so `μ V ≤ 1/4`.  A sequence avoiding `V` is Martin-Löf random, and
such a sequence is built greedily: keeping the invariant
`μ (Ω_x ∩ V) < 2^{-n} - 2^{-2n-1}`, one of the two one-bit extensions of `x`
again satisfies the invariant, and which one can be found by deciding a single
`Σ⁰₁` question about the measure of `V` inside a cylinder.  The halting oracle
`0′` decides such questions, so the whole construction is `0′`-computable.

Main definitions and results:

* `Kolmogorov.jumpApx`: the stage-`N` approximation of `Ω_x ∩ V` by cylinders
  of level `N`, with `Kolmogorov.uniformMeasure_jumpApx` computing its measure
  exactly as a dyadic rational;
* `Kolmogorov.jumpTest`: the computable Boolean stage test whose existential
  quantification expresses `μ (Ω_x ∩ V) > 2^{-n-1} - 2^{-2n-2}`
  (`Kolmogorov.jumpTest_spec`);
* `Kolmogorov.jumpSeq`: the sequence produced by the greedy construction;
* `Kolmogorov.exists_isMartinLofRandom_uniform_computableInJump`: SUV
  Theorem 37.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-! ## Sets decided by a fixed-length prefix -/

/-- A set decided by a Boolean test on the length-`L` prefix is the (finite)
union of the level-`L` cylinders that the test accepts. -/
lemma setOf_prefixPred_eq_biUnion (L : ℕ) (Q : BitString → Bool) :
    {z : CantorSeq | Q (cantorPrefix z L) = true}
      = ⋃ y ∈ levelFinset L, (if Q y then cantorCylinder y else (∅ : Set CantorSeq)) := by
  classical
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · intro hz
    refine ⟨cantorPrefix z L, mem_levelFinset.2 (by simp), ?_⟩
    rw [if_pos hz]
    change IsCantorPrefix (cantorPrefix z L) z
    rw [isCantorPrefix_iff_cantorPrefix_eq]
    simp
  · rintro ⟨y, hy, hz⟩
    by_cases hQ : Q y = true
    · rw [if_pos hQ] at hz
      have hlen : y.length = L := mem_levelFinset.1 hy
      have : cantorPrefix z y.length = y :=
        (isCantorPrefix_iff_cantorPrefix_eq y z).1 hz
      rw [hlen] at this
      rwa [this]
    · rw [if_neg hQ] at hz
      exact absurd hz (Set.notMem_empty z)

/-- A condition on the length-`L` prefix determines a measurable subset of Cantor space. -/
lemma measurableSet_setOf_prefixPred (L : ℕ) (Q : BitString → Bool) :
    MeasurableSet {z : CantorSeq | Q (cantorPrefix z L) = true} := by
  classical
  rw [setOf_prefixPred_eq_biUnion]
  refine Finset.measurableSet_biUnion _ fun y _ => ?_
  by_cases h : Q y <;> simp [h, measurableSet_cantorCylinder]

/-- The number of length-`L` bitstrings accepted by `Q`. -/
def levelCount (L : ℕ) (Q : BitString → Bool) : ℕ :=
  ((levelList L).map fun y => if Q y then 1 else 0).sum

/-- The uniform measure of a set decided by a Boolean test on the length-`L`
prefix is the accepted count divided by `2 ^ L`. -/
lemma uniformMeasure_setOf_prefixPred (L : ℕ) (Q : BitString → Bool) :
    uniformMeasure {z : CantorSeq | Q (cantorPrefix z L) = true}
      = (levelCount L Q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ L := by
  classical
  set S : Set CantorSeq := {z : CantorSeq | Q (cantorPrefix z L) = true} with hS
  set f : BitString → ℝ≥0∞ := fun y => if Q y then 1 else 0 with hf
  have hind : (fun z => f (cantorPrefix z L)) = S.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext z
    by_cases h : Q (cantorPrefix z L) = true
    · have hz : z ∈ S := h
      simp [hf, h, Set.indicator_of_mem hz]
    · have hz : z ∉ S := h
      simp [hf, h, Set.indicator_of_notMem hz]
  have key := lintegral_comp_cantorPrefix uniformMeasure L f
  rw [hind, lintegral_indicator_const (measurableSet_setOf_prefixPred L Q) (1 : ℝ≥0∞),
    one_mul] at key
  rw [key]
  have hmass : ∀ y ∈ levelFinset L, f y * cantorMass uniformMeasure y
      = f y * (2 : ℝ≥0∞)⁻¹ ^ L := by
    intro y hy
    rw [cantorMass_uniformMeasure, mem_levelFinset.1 hy]
  rw [Finset.sum_congr rfl hmass, ← Finset.sum_mul,
    sum_levelFinset_eq_sum_levelList]
  congr 1
  rw [levelCount, Nat.cast_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun y _ => ?_
  by_cases h : Q y <;> simp [hf, h]

/-- Belonging to a cylinder is a property of any sufficiently long prefix. -/
lemma mem_cantorCylinder_iff_prefix_cantorPrefix (s : BitString) (L : ℕ) (z : CantorSeq)
    (h : s.length ≤ L) : z ∈ cantorCylinder s ↔ s <+: cantorPrefix z L := by
  rw [List.prefix_iff_eq_take, cantorPrefix_take z s.length L h]
  exact (isCantorPrefix_iff_cantorPrefix_eq s z).trans eq_comm

/-! ## Finite approximations of `Ω_x ∩ U` -/

/-- Boolean test deciding, from a length-`N` string `y`, whether the cylinder
`Ω_y` is inside `Ω_x` and is already covered by the first `N` values emitted by
the enumeration `g`. -/
def jumpPred (g : ℕ → Option BitString) (x : BitString) (N : ℕ) (y : BitString) : Bool :=
  normalFormIsPrefixB x y && prefixSeen g y N

/-- Stage-`N` approximation of `Ω_x ∩ U`, where `U` is enumerated by `g`. -/
def jumpApx (g : ℕ → Option BitString) (x : BitString) (N : ℕ) : Set CantorSeq :=
  {z : CantorSeq | jumpPred g x N (cantorPrefix z N) = true}

/-- A point lies in the stage-`N` approximation exactly when its length-`N` prefix extends `x`
and is covered by one of the first `N` emissions of the enumeration. -/
lemma mem_jumpApx_iff (g : ℕ → Option BitString) (x : BitString) (N : ℕ) (z : CantorSeq) :
    z ∈ jumpApx g x N ↔
      x <+: cantorPrefix z N ∧ ∃ i < N, ∃ v, g i = some v ∧ v <+: cantorPrefix z N := by
  simp only [jumpApx, Set.mem_setOf_eq, jumpPred, Bool.and_eq_true,
    normalFormIsPrefixB_iff, prefixSeen_spec]

/-- The approximations increase with the stage. -/
lemma jumpApx_mono (g : ℕ → Option BitString) (x : BitString) {N M : ℕ} (h : N ≤ M) :
    jumpApx g x N ⊆ jumpApx g x M := by
  intro z hz
  rw [mem_jumpApx_iff] at hz ⊢
  obtain ⟨hx, i, hi, v, hv, hvz⟩ := hz
  have hpre : cantorPrefix z N <+: cantorPrefix z M := cantorPrefix_mono z h
  exact ⟨hx.trans hpre, i, lt_of_lt_of_le hi h, v, hv, hvz.trans hpre⟩

/-- The approximations exhaust the intersection of the cylinder of `x` with the open set
enumerated by `g`. -/
lemma iUnion_jumpApx (g : ℕ → Option BitString) (x : BitString) :
    (⋃ N, jumpApx g x N) = cantorCylinder x ∩ ⋃ i, (g i).elim ∅ cantorCylinder := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨N, hz⟩
    rw [mem_jumpApx_iff] at hz
    obtain ⟨hx, i, _, v, hv, hvz⟩ := hz
    have hxlen : x.length ≤ N := by
      have := hx.length_le
      simpa using this
    have hvlen : v.length ≤ N := by
      have := hvz.length_le
      simpa using this
    refine ⟨(mem_cantorCylinder_iff_prefix_cantorPrefix x N z hxlen).2 hx, ?_⟩
    refine ⟨i, ?_⟩
    rw [hv]
    exact (mem_cantorCylinder_iff_prefix_cantorPrefix v N z hvlen).2 hvz
  · rintro ⟨hx, i, hi⟩
    cases hgi : g i with
    | none => rw [hgi] at hi; exact absurd hi (Set.notMem_empty z)
    | some v =>
        rw [hgi] at hi
        refine ⟨max (max x.length v.length) (i + 1), ?_⟩
        rw [mem_jumpApx_iff]
        refine ⟨?_, i, by omega, v, hgi, ?_⟩
        · exact (mem_cantorCylinder_iff_prefix_cantorPrefix x _ z (by omega)).1 hx
        · exact (mem_cantorCylinder_iff_prefix_cantorPrefix v _ z (by omega)).1 hi

/-- The uniform measure of a stage approximation is the number of accepted length-`N` strings
divided by `2^N`. -/
lemma uniformMeasure_jumpApx (g : ℕ → Option BitString) (x : BitString) (N : ℕ) :
    uniformMeasure (jumpApx g x N)
      = (levelCount N (jumpPred g x N) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ N :=
  uniformMeasure_setOf_prefixPred N (jumpPred g x N)

/-- The uniform measure of the intersection is the supremum of the measures of the
approximations. -/
lemma uniformMeasure_inter_eq_iSup (g : ℕ → Option BitString) (x : BitString) :
    uniformMeasure (cantorCylinder x ∩ ⋃ i, (g i).elim ∅ cantorCylinder)
      = ⨆ N, uniformMeasure (jumpApx g x N) := by
  rw [← iUnion_jumpApx g x]
  exact Monotone.measure_iUnion fun _ _ h => jumpApx_mono g x h

/-! ## Comparing dyadic rationals -/

/-- Comparison of two dyadic numbers reduces to an inequality between naturals. -/
lemma dyadic_lt_dyadic_iff (A B p q : ℕ) :
    (A : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ p < (B : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ q
      ↔ A * 2 ^ q < B * 2 ^ p := by
  have hinv : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by simp) (by simp)
  have hpow : ∀ k : ℕ, (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ k = 1 := by
    intro k; rw [← mul_pow, hinv, one_pow]
  have hc0 : ((2 : ℝ≥0∞)⁻¹ ^ (p + q)) ≠ 0 := by
    exact pow_ne_zero _ (by simp)
  have hct : ((2 : ℝ≥0∞)⁻¹ ^ (p + q)) ≠ ⊤ := by
    exact ENNReal.pow_ne_top (by simp)
  have hA : (A : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ p
      = ((A : ℝ≥0∞) * 2 ^ q) * (2 : ℝ≥0∞)⁻¹ ^ (p + q) := by
    have h : ((A : ℝ≥0∞) * 2 ^ q) * (2 : ℝ≥0∞)⁻¹ ^ (p + q)
        = (A : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ p * ((2 : ℝ≥0∞) ^ q * (2 : ℝ≥0∞)⁻¹ ^ q) := by
      rw [pow_add]; ring
    rw [h, hpow, mul_one]
  have hB : (B : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ q
      = ((B : ℝ≥0∞) * 2 ^ p) * (2 : ℝ≥0∞)⁻¹ ^ (p + q) := by
    have h : ((B : ℝ≥0∞) * 2 ^ p) * (2 : ℝ≥0∞)⁻¹ ^ (p + q)
        = (B : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ q * ((2 : ℝ≥0∞) ^ p * (2 : ℝ≥0∞)⁻¹ ^ p) := by
      rw [pow_add]; ring
    rw [h, hpow, mul_one]
  rw [hA, hB, ENNReal.mul_lt_mul_iff_left hc0 hct]
  rw [show ((A : ℝ≥0∞) * 2 ^ q) = ((A * 2 ^ q : ℕ) : ℝ≥0∞) by push_cast; ring,
    show ((B : ℝ≥0∞) * 2 ^ p) = ((B * 2 ^ p : ℕ) : ℝ≥0∞) by push_cast; ring,
    Nat.cast_lt]

/-! ## The semidecidable test driving the construction -/

/-- The dyadic threshold `2^{-n-1} - 2^{-2n-2}` used at stage `n`. -/
noncomputable def jumpThreshold (n : ℕ) : ℝ≥0∞ :=
  ((2 ^ (n + 1) - 1 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (2 * n + 2)

/-- Stage-`N` Boolean test: "the stage-`N` approximation of `Ω_x ∩ U` already has
measure exceeding `jumpThreshold n`". -/
def jumpTest (g : ℕ → Option BitString) (p : BitString × ℕ) (N : ℕ) : Bool :=
  decide ((2 ^ (p.2 + 1) - 1) * 2 ^ N < levelCount N (jumpPred g p.1 N) * 2 ^ (2 * p.2 + 2))

/-- The halting-problem query used in the construction succeeds at some stage exactly when the
measure of the trace of the open set on the cylinder of `x` exceeds the threshold. -/
lemma jumpTest_spec (g : ℕ → Option BitString) (x : BitString) (n : ℕ) :
    (∃ N, jumpTest g (x, n) N = true)
      ↔ jumpThreshold n
          < uniformMeasure (cantorCylinder x ∩ ⋃ i, (g i).elim ∅ cantorCylinder) := by
  rw [uniformMeasure_inter_eq_iSup, lt_iSup_iff]
  refine exists_congr fun N => ?_
  rw [uniformMeasure_jumpApx, jumpThreshold, dyadic_lt_dyadic_iff, jumpTest,
    decide_eq_true_iff]

/-! ## Computability of the test -/

/-- An index-recursive presentation of `levelCount`, convenient for
computability arguments. -/
def countBelow (Q : BitString → Bool) (l : List BitString) : ℕ → ℕ
  | 0 => 0
  | k + 1 => countBelow Q l k + ((l[k]?).map fun y => if Q y then 1 else 0).getD 0

/-- The bounded count over a list is the sum of the indicator over its first `k` entries. -/
lemma countBelow_eq_take (Q : BitString → Bool) (l : List BitString) (k : ℕ) :
    countBelow Q l k = ((l.take k).map fun y => if Q y then 1 else 0).sum := by
  induction k with
  | zero => simp [countBelow]
  | succ k ih =>
      rw [countBelow, ih, List.take_add_one]
      cases l[k]? with
      | none => simp
      | some y => simp

/-- The number of length-`L` strings satisfying a predicate is the count over the list of all
of them. -/
lemma levelCount_eq_countBelow (L : ℕ) (Q : BitString → Bool) :
    levelCount L Q = countBelow Q (levelList L) (2 ^ L) := by
  rw [countBelow_eq_take, List.take_of_length_le (by rw [length_levelList]), levelCount]

/-- The bounded count of a computable predicate over a computable list is computable. -/
lemma computable_countBelow {α : Type*} [Primcodable α] {Q : α → BitString → Bool}
    {l : α → List BitString} {k : α → ℕ}
    (hQ : Computable₂ Q) (hl : Computable l) (hk : Computable k) :
    Computable fun a => countBelow (Q a) (l a) (k a) := by
  have hstep : Computable₂ (fun (a : α) (q : ℕ × ℕ) =>
      q.2 + ((l a)[q.1]?.map fun y => if Q a y then 1 else 0).getD 0) := by
    have hla : Computable (fun r : α × (ℕ × ℕ) => l r.1) := hl.comp Computable.fst
    have hidx : Computable (fun r : α × (ℕ × ℕ) => r.2.1) :=
      Computable.fst.comp Computable.snd
    have hget : Computable (fun r : α × (ℕ × ℕ) => (l r.1)[r.2.1]?) :=
      Primrec.list_getElem?.to_comp.comp hla hidx
    have hQr : Computable (fun s : (α × (ℕ × ℕ)) × BitString => Q s.1.1 s.2) :=
      hQ.comp (Computable.fst.comp Computable.fst) Computable.snd
    have hval : Computable₂ (fun (r : α × (ℕ × ℕ)) (y : BitString) =>
        if Q r.1 y then (1 : ℕ) else 0) := by
      refine (Computable.cond hQr (Computable.const 1) (Computable.const 0)).of_eq ?_
      rintro ⟨r, y⟩
      cases h : Q r.1 y <;> simp [h]
    have hmapped : Computable (fun r : α × (ℕ × ℕ) =>
        ((l r.1)[r.2.1]?.map fun y => if Q r.1 y then (1 : ℕ) else 0).getD 0) :=
      Computable.option_getD (Computable.option_map hget hval) (Computable.const 0)
    exact (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd) hmapped).to₂
  refine (Computable.nat_rec hk (Computable.const 0) hstep).of_eq fun a => ?_
  generalize k a = m
  induction m with
  | zero => rfl
  | succ m ih => simp [countBelow, ih]

/-- The halting-problem query used in the construction is computable in its arguments, so that
the sequence built from it is computable in the jump. -/
lemma computable_jumpTest {f : ℕ → ℕ → Option BitString} (hf : Computable₂ f) (m : ℕ) :
    Computable₂ (jumpTest (f m)) := by
  have hseen := computable_prefixSeen hf
  -- the predicate `jumpPred (f m) x N y`, computable in `((x, n), N)` and `y`
  have hQ : Computable₂ (fun (t : (BitString × ℕ) × ℕ) (y : BitString) =>
      jumpPred (f m) t.1.1 t.2 y) := by
    have hx : Computable (fun s : ((BitString × ℕ) × ℕ) × BitString => s.1.1.1) :=
      Computable.fst.comp (Computable.fst.comp Computable.fst)
    have hy : Computable (fun s : ((BitString × ℕ) × ℕ) × BitString => s.2) := Computable.snd
    have hN : Computable (fun s : ((BitString × ℕ) × ℕ) × BitString => s.1.2) :=
      Computable.snd.comp Computable.fst
    have h1 : Computable (fun s : ((BitString × ℕ) × ℕ) × BitString =>
        normalFormIsPrefixB s.1.1.1 s.2) :=
      primrec₂_normalFormIsPrefixB.to_comp.comp hx hy
    have harg : Computable (fun s : ((BitString × ℕ) × ℕ) × BitString =>
        (((m, s.2), s.1.2) : (ℕ × BitString) × ℕ)) :=
      ((Computable.const m).pair hy).pair hN
    have h2 : Computable (fun s : ((BitString × ℕ) × ℕ) × BitString =>
        prefixSeen (f m) s.2 s.1.2) := by
      have h := hseen.comp harg
      exact h
    exact (Primrec.and.to_comp.comp h1 h2).to₂
  have hcount : Computable (fun t : (BitString × ℕ) × ℕ =>
      levelCount t.2 (jumpPred (f m) t.1.1 t.2)) := by
    have hlist : Computable (fun t : (BitString × ℕ) × ℕ => levelList t.2) :=
      primrec_levelList.to_comp.comp Computable.snd
    have hk : Computable (fun t : (BitString × ℕ) × ℕ => 2 ^ t.2) :=
      Primrec.to_comp (primrec_two_pow_aux.comp Primrec.snd)
    refine (computable_countBelow hQ hlist hk).of_eq fun t => ?_
    rw [levelCount_eq_countBelow]
  have hleft : Computable (fun t : (BitString × ℕ) × ℕ =>
      (2 ^ (t.1.2 + 1) - 1) * 2 ^ t.2) := by
    refine Primrec.to_comp ?_
    exact Primrec.nat_mul.comp
      (Primrec.nat_sub.comp
        (primrec_two_pow_aux.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.const 1))
      (primrec_two_pow_aux.comp Primrec.snd)
  have hright : Computable (fun t : (BitString × ℕ) × ℕ =>
      levelCount t.2 (jumpPred (f m) t.1.1 t.2) * 2 ^ (2 * t.1.2 + 2)) := by
    have hpow : Computable (fun t : (BitString × ℕ) × ℕ => 2 ^ (2 * t.1.2 + 2)) :=
      Primrec.to_comp (primrec_two_pow_aux.comp
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.fst))
          (Primrec.const 2)))
    exact Primrec.nat_mul.to_comp.comp hcount hpow
  have hltc : Computable₂ (fun a b : ℕ => decide (a < b)) :=
    ((PrimrecRel.comp Primrec.nat_lt Primrec.fst Primrec.snd).decide).to_comp
  have h := hltc.comp hleft hright
  exact h

/-! ## Arithmetic of the two dyadic sequences -/

/-- The stage-`n` invariant bound `2^{-n} - 2^{-2n-1}`. -/
noncomputable def jumpBound (n : ℕ) : ℝ≥0∞ :=
  ((2 ^ (n + 1) - 1 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (2 * n + 1)

/-- The bound of level `n` is twice the threshold of level `n`. -/
lemma jumpBound_eq_two_mul (n : ℕ) : jumpBound n = 2 * jumpThreshold n := by
  rw [jumpBound, jumpThreshold]
  have h2 : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
  have hsplit : (2 : ℝ≥0∞)⁻¹ ^ (2 * n + 2)
      = (2 : ℝ≥0∞)⁻¹ ^ (2 * n + 1) * (2 : ℝ≥0∞)⁻¹ := pow_succ _ _
  have hpow : (2 : ℝ≥0∞)⁻¹ ^ (2 * n + 1) = 2 * (2 : ℝ≥0∞)⁻¹ ^ (2 * n + 2) := by
    rw [hsplit, show (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ (2 * n + 1) * (2 : ℝ≥0∞)⁻¹)
      = ((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) * (2 : ℝ≥0∞)⁻¹ ^ (2 * n + 1) from by ring,
      h2, one_mul]
  rw [hpow]; ring

/-- The bound at level zero is `1/2`. -/
lemma jumpBound_zero : jumpBound 0 = (2 : ℝ≥0∞)⁻¹ := by
  norm_num [jumpBound]

/-- Each threshold is strictly below the bound of the next level, which leaves room for the
extension step of the construction. -/
lemma jumpThreshold_lt_jumpBound_succ (n : ℕ) : jumpThreshold n < jumpBound (n + 1) := by
  rw [jumpThreshold, jumpBound, dyadic_lt_dyadic_iff]
  have hc : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  have hexp : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
  have hp : (2 : ℕ) ^ (2 * n + 3) = 2 * 2 ^ (2 * n + 2) := by ring
  have hq : (2 : ℕ) ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
  have hpos : 0 < (2 : ℕ) ^ (2 * n + 2) := Nat.two_pow_pos _
  rw [hexp, hp, hq]
  have hlt : (2 ^ (n + 1) - 1) * 2 < 2 * 2 ^ (n + 1) - 1 := by omega
  calc (2 ^ (n + 1) - 1) * (2 * 2 ^ (2 * n + 2))
      = ((2 ^ (n + 1) - 1) * 2) * 2 ^ (2 * n + 2) := by ring
    _ < (2 * 2 ^ (n + 1) - 1) * 2 ^ (2 * n + 2) :=
        (Nat.mul_lt_mul_right hpos).2 hlt

/-- The bounds decrease strictly faster than `2^{-n}`. -/
lemma jumpBound_lt_inv_two_pow (n : ℕ) : jumpBound n < (2 : ℝ≥0∞)⁻¹ ^ n := by
  have h1 : ((1 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n = (2 : ℝ≥0∞)⁻¹ ^ n := by simp
  rw [jumpBound, ← h1, dyadic_lt_dyadic_iff]
  have hp : (2 : ℕ) ^ (2 * n + 1) = 2 ^ (n + 1) * 2 ^ n := by
    rw [← pow_add]; ring_nf
  have hc : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  have hpos : 0 < (2 : ℕ) ^ n := Nat.two_pow_pos _
  rw [hp, one_mul]
  exact (Nat.mul_lt_mul_right hpos).2 (by omega)

/-! ## The greedy construction -/

/-- The prefix chosen after `n` stages of the greedy construction. -/
def jumpPrefix (h : BitString × ℕ → Bool) : ℕ → BitString
  | 0 => []
  | k + 1 => jumpPrefix h k ++ [h (jumpPrefix h k ++ [false], k)]

/-- The sequence produced by the greedy construction. -/
def jumpSeq (h : BitString × ℕ → Bool) : CantorSeq :=
  fun n => h (jumpPrefix h n ++ [false], n)

/-- The constructed prefix of length `k + 1` extends the one of length `k` by the next bit. -/
lemma jumpPrefix_succ_eq (h : BitString × ℕ → Bool) (k : ℕ) :
    jumpPrefix h (k + 1) = jumpPrefix h k ++ [jumpSeq h k] := rfl

/-- The constructed prefix of index `n` has length `n`. -/
lemma jumpPrefix_length (h : BitString × ℕ → Bool) : ∀ n, (jumpPrefix h n).length = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [jumpPrefix_succ_eq, ih]

/-- The constructed prefixes are the prefixes of the constructed sequence. -/
lemma jumpPrefix_eq_cantorPrefix (h : BitString × ℕ → Bool) :
    ∀ n, jumpPrefix h n = cantorPrefix (jumpSeq h) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [jumpPrefix_succ_eq, cantorPrefix_succ, ih]

/-- The trace of a measurable set on a cylinder splits into its traces on the two one-bit
extensions of that cylinder. -/
lemma uniformMeasure_cylinder_inter_split {A : Set CantorSeq} (hA : MeasurableSet A)
    (x : BitString) :
    uniformMeasure (cantorCylinder x ∩ A)
      = uniformMeasure (cantorCylinder (x ++ [false]) ∩ A)
        + uniformMeasure (cantorCylinder (x ++ [true]) ∩ A) := by
  have hunion : cantorCylinder x
      = cantorCylinder (x ++ [false]) ∪ cantorCylinder (x ++ [true]) := by
    rw [← union_extensions_one x]
    ext z
    simp only [Set.mem_iUnion, Set.mem_union]
    exact ⟨fun ⟨b, hb⟩ => by cases b with
        | false => exact Or.inl hb
        | true => exact Or.inr hb,
      fun hz => hz.elim (fun h => ⟨false, h⟩) fun h => ⟨true, h⟩⟩
  have hdisj : Disjoint (cantorCylinder (x ++ [false]) ∩ A)
      (cantorCylinder (x ++ [true]) ∩ A) := by
    rw [Set.disjoint_left]
    rintro w ⟨hw0, -⟩ ⟨hw1, -⟩
    have h0 := (isCantorPrefix_append_singleton x false w).1 hw0
    have h1 := (isCantorPrefix_append_singleton x true w).1 hw1
    rw [h0.2] at h1
    exact absurd h1.2 (by simp)
  rw [hunion, Set.union_inter_distrib_right,
    measure_union hdisj ((measurableSet_cantorCylinder _).inter hA)]

/-- The invariant: after `n` stages, the chosen cylinder still has small
intersection with the effective open set. -/
lemma jumpPrefix_measure_lt {V : Set CantorSeq} (hV : MeasurableSet V)
    {h : BitString × ℕ → Bool}
    (hspec : ∀ x n, h (x, n) = true ↔ jumpThreshold n < uniformMeasure (cantorCylinder x ∩ V))
    (h0 : uniformMeasure V < jumpBound 0) :
    ∀ n, uniformMeasure (cantorCylinder (jumpPrefix h n) ∩ V) < jumpBound n := by
  intro n
  induction n with
  | zero =>
      have : cantorCylinder (jumpPrefix h 0) ∩ V = V := by
        rw [show jumpPrefix h 0 = ([] : BitString) from rfl, cantorCylinder_nil,
          Set.univ_inter]
      rw [this]
      exact h0
  | succ n ih =>
      have hsplit := uniformMeasure_cylinder_inter_split hV (jumpPrefix h n)
      have hkey : uniformMeasure
          (cantorCylinder (jumpPrefix h n ++ [jumpSeq h n]) ∩ V) ≤ jumpThreshold n := by
        have hb : jumpSeq h n = h (jumpPrefix h n ++ [false], n) := rfl
        cases hcase : h (jumpPrefix h n ++ [false], n) with
        | false =>
            have hbf : jumpSeq h n = false := by rw [hb, hcase]
            rw [hbf]
            have hnot : ¬ jumpThreshold n
                < uniformMeasure (cantorCylinder (jumpPrefix h n ++ [false]) ∩ V) := by
              intro hcon
              rw [← hspec] at hcon
              rw [hcase] at hcon
              exact Bool.false_ne_true hcon
            exact not_lt.1 hnot
        | true =>
            have hbt : jumpSeq h n = true := by rw [hb, hcase]
            rw [hbt]
            have hgt : jumpThreshold n
                < uniformMeasure (cantorCylinder (jumpPrefix h n ++ [false]) ∩ V) :=
              (hspec _ n).1 hcase
            by_contra hcon
            push_neg at hcon
            have hadd : jumpThreshold n + jumpThreshold n
                < uniformMeasure (cantorCylinder (jumpPrefix h n ++ [false]) ∩ V)
                  + uniformMeasure (cantorCylinder (jumpPrefix h n ++ [true]) ∩ V) :=
              ENNReal.add_lt_add hgt hcon
            rw [← hsplit] at hadd
            have hfin : uniformMeasure (cantorCylinder (jumpPrefix h n) ∩ V)
                < jumpThreshold n + jumpThreshold n := by
              rw [← two_mul, ← jumpBound_eq_two_mul]
              exact ih
            exact absurd hadd (not_lt.2 hfin.le)
      calc uniformMeasure (cantorCylinder (jumpPrefix h (n + 1)) ∩ V)
          ≤ jumpThreshold n := by rw [jumpPrefix_succ_eq]; exact hkey
        _ < jumpBound (n + 1) := jumpThreshold_lt_jumpBound_succ n

/-- If every constructed prefix keeps the local measure of the open set below the level bound,
the constructed sequence escapes that open set. -/
lemma jumpSeq_notMem (g : ℕ → Option BitString) {h : BitString × ℕ → Bool}
    (hlt : ∀ n, uniformMeasure
      (cantorCylinder (jumpPrefix h n) ∩ ⋃ i, (g i).elim ∅ cantorCylinder) < jumpBound n) :
    jumpSeq h ∉ ⋃ i, (g i).elim ∅ cantorCylinder := by
  intro hmem
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmem
  cases hgi : g i with
  | none => rw [hgi] at hi; exact absurd hi (Set.notMem_empty _)
  | some v =>
      rw [hgi] at hi
      have hpre : cantorPrefix (jumpSeq h) v.length = v :=
        (isCantorPrefix_iff_cantorPrefix_eq v _).1 hi
      have hjp : jumpPrefix h v.length = v := by
        rw [jumpPrefix_eq_cantorPrefix, hpre]
      have hsub : cantorCylinder (jumpPrefix h v.length)
          ⊆ ⋃ j, (g j).elim ∅ cantorCylinder := by
        rw [hjp]
        intro z hz
        exact Set.mem_iUnion.2 ⟨i, by rw [hgi]; exact hz⟩
      have hmeas : uniformMeasure (cantorCylinder (jumpPrefix h v.length))
          = (2 : ℝ≥0∞)⁻¹ ^ v.length := by
        have hm := cantorMass_uniformMeasure (jumpPrefix h v.length)
        rw [cantorMass, jumpPrefix_length] at hm
        exact hm
      have hcontr := hlt v.length
      rw [Set.inter_eq_left.2 hsub, hmeas] at hcontr
      exact absurd hcontr (not_lt.2 (jumpBound_lt_inv_two_pow v.length).le)

/-! ## `0′`-computability of the construction -/

/-- The constructed prefixes are computable in the halting problem when the decision step is. -/
lemma computableInJump_jumpPrefix {h : BitString × ℕ → Bool} (hh : ComputableInJump h) :
    ComputableInJump (jumpPrefix h) := by
  have hcat : ComputableIn₂ ({haltingChi} : Set (ℕ →. ℕ))
      (fun (l : BitString) (b : Bool) => l ++ [b]) :=
    Computable₂.computableIn₂ Primrec.list_concat.to_comp
  have hstep : ComputableIn₂ ({haltingChi} : Set (ℕ →. ℕ))
      (fun (_ : ℕ) (q : ℕ × BitString) => q.2 ++ [h (q.2 ++ [false], q.1)]) := by
    have hprev : ComputableIn ({haltingChi} : Set (ℕ →. ℕ))
        (fun r : ℕ × (ℕ × BitString) => r.2.2) :=
      Primrec.computableIn (Primrec.snd.comp Primrec.snd)
    have hk : ComputableIn ({haltingChi} : Set (ℕ →. ℕ))
        (fun r : ℕ × (ℕ × BitString) => r.2.1) :=
      Primrec.computableIn (Primrec.fst.comp Primrec.snd)
    have hext : ComputableIn ({haltingChi} : Set (ℕ →. ℕ))
        (fun r : ℕ × (ℕ × BitString) => r.2.2 ++ [false]) :=
      Primrec.computableIn (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.const [false]))
    have hb : ComputableIn ({haltingChi} : Set (ℕ →. ℕ))
        (fun r : ℕ × (ℕ × BitString) => h (r.2.2 ++ [false], r.2.1)) := by
      have hpair := hext.pair hk
      have := hh.comp hpair
      exact this
    exact (hcat.comp hprev hb).to₂
  have hrec := ComputableIn.nat_rec (O := ({haltingChi} : Set (ℕ →. ℕ)))
    (f := fun n : ℕ => n) (g := fun _ : ℕ => ([] : BitString))
    ComputableIn.id (ComputableIn.const []) hstep
  have hrecEq : ∀ n : ℕ, (Nat.rec ([] : BitString)
      (fun y IH => IH ++ [h (IH ++ [false], y)]) n : BitString) = jumpPrefix h n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [jumpPrefix, ← ih]
  exact hrec.of_eq hrecEq

/-- The constructed sequence is computable in the halting problem when the decision step is. -/
lemma computableInJump_jumpSeq {h : BitString × ℕ → Bool} (hh : ComputableInJump h) :
    ComputableInJump (jumpSeq h) := by
  have hcat : ComputableIn₂ ({haltingChi} : Set (ℕ →. ℕ))
      (fun (l : BitString) (b : Bool) => l ++ [b]) :=
    Computable₂.computableIn₂ Primrec.list_concat.to_comp
  have hp := computableInJump_jumpPrefix hh
  have hext : ComputableIn ({haltingChi} : Set (ℕ →. ℕ))
      (fun n : ℕ => jumpPrefix h n ++ [false]) :=
    hcat.comp hp (ComputableIn.const false)
  have hpair := hext.pair (ComputableIn.id (α := ℕ))
  have := hh.comp hpair
  exact this

/-! ## SUV Theorem 37 -/

/-- **SUV Theorem 37.** There exists a sequence that is Martin-Löf random for
the uniform measure and computable with the halting oracle `0′`. -/
theorem exists_isMartinLofRandom_uniform_computableInJump :
    ∃ w : CantorSeq, IsMartinLofRandom uniformMeasure w ∧ ComputableInJump w := by
  obtain ⟨U, hU⟩ := exists_universal_martinLof_test isComputableMeasure_uniform
  obtain ⟨f, hf, hUeq⟩ := hU.1.1
  have hVmeas : MeasurableSet (⋃ i, ((f 2 i).elim ∅ cantorCylinder : Set CantorSeq)) := by
    refine MeasurableSet.iUnion fun i => ?_
    cases f 2 i with
    | none => exact MeasurableSet.empty
    | some v => exact measurableSet_cantorCylinder v
  obtain ⟨h, hhcomp, hhspec⟩ :=
    exists_computableInJump_semidecide (computable_jumpTest hf 2)
  have hspec : ∀ x n, h (x, n) = true ↔ jumpThreshold n
      < uniformMeasure (cantorCylinder x ∩ ⋃ i, (f 2 i).elim ∅ cantorCylinder) := by
    intro x n
    rw [hhspec (x, n)]
    exact jumpTest_spec (f 2) x n
  have h0 : uniformMeasure (⋃ i, ((f 2 i).elim ∅ cantorCylinder : Set CantorSeq))
      < jumpBound 0 := by
    have hb := hU.1.2 2
    rw [dyadicValue_one_eq_inv_two_pow', hUeq 2] at hb
    have hlt : (2 : ℝ≥0∞)⁻¹ ^ 2 < (2 : ℝ≥0∞)⁻¹ := by
      have := (dyadic_lt_dyadic_iff 1 1 2 1).2 (by norm_num)
      simpa using this
    rw [jumpBound_zero]
    exact lt_of_le_of_lt hb hlt
  refine ⟨jumpSeq h, ?_, computableInJump_jumpSeq hhcomp⟩
  have hnot := jumpSeq_notMem (f 2) (jumpPrefix_measure_lt hVmeas hspec h0)
  by_contra hnr
  rw [not_isMartinLofRandom_iff_mem_universal_test hU] at hnr
  have hmem := Set.mem_iInter.1 hnr 2
  rw [hUeq 2] at hmem
  exact hnot hmem

end Kolmogorov
