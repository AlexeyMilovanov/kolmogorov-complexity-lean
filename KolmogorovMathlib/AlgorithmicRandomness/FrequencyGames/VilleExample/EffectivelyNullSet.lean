/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.VilleExample.CountableFamilies
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.VilleExample.LogarithmicComplexity

/-!
# Effectively Null Set

Effectively null sets in Cantor space with respect to the uniform measure.  The module shows that
the set of infinite paths through a decidable tree of measure zero is effectively null
(`isEffectivelyNull_of_decidable_tree`), and proves that there is a Mises-Church random sequence
that is not Martin-Löf random (SUV Theorem 174), the Ville-type example of the book by Shen,
Uspensky and Vereshchagin.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-- Step 1 of the proof of `exists_isMisesChurchRandom_not_isMartinLofRandom`: a linear
function is eventually below `2 ^ k`. -/
private lemma exists_isMisesChurchRandom_not_isMartinLofRandom_asymp (a b : ℝ) :
    ∃ k : ℕ, a * k + b < 2 ^ k := by
  have h1 : Tendsto (fun k : ℕ => (k:ℝ) ^ 1 / (2:ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num)
  have h2 : Tendsto (fun k : ℕ => ((1:ℝ)/2) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h3 : Tendsto (fun k : ℕ => a * ((k:ℝ) ^ 1 / (2:ℝ) ^ k) + b * ((1:ℝ)/2) ^ k) atTop
      (𝓝 (a * 0 + b * 0)) :=
    (h1.const_mul a).add (h2.const_mul b)
  simp only [mul_zero, add_zero] at h3
  obtain ⟨k, hk⟩ := (h3.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))).exists
  refine ⟨k, ?_⟩
  have hp : (0:ℝ) < 2 ^ k := by positivity
  have : a * ((k:ℝ) ^ 1 / (2:ℝ) ^ k) + b * ((1:ℝ)/2) ^ k = (a * k + b) / 2 ^ k := by
    rw [one_div, inv_pow]; field_simp
  rw [this, div_lt_one hp] at hk
  exact hk

/-- **SUV Theorem 174, p. 270.**  There is a Mises-Church random sequence that is not Martin-Löf
random with respect to the uniform measure.  Corollary of Theorem 173 and the Levin-Schnorr
criterion `isMartinLofRandom_uniform_iff_KA_KMOf_eq_length`. -/
theorem exists_isMisesChurchRandom_not_isMartinLofRandom :
    ∃ w, IsMisesChurchRandom w ∧ ¬ IsMartinLofRandom uniformMeasure w := by
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨D, hD⟩ := exists_optimalMonotoneDecompressor
  obtain ⟨w, hw, c, hc⟩ := exists_isMisesChurchRandom_plainK_log V hV
  refine ⟨w, hw, fun hML => ?_⟩
  obtain ⟨c1, hc1⟩ := (isMartinLofRandom_uniform_iff_KA_KMOf_eq_length hD w).mp hML
  obtain ⟨c2, hc2⟩ := exists_const_KMOf_le_plainK_add_log V U hV hU hD
  obtain ⟨k, hk⟩ := exists_isMisesChurchRandom_not_isMartinLofRandom_asymp
    ((c : ℝ) + 2) ((c : ℝ) + 2 + c1 + c2)
  have h1 := (abs_le.mp (hc1 (2 ^ k)).2).1
  have h2 := hc2 (cantorPrefix w (2 ^ k))
  rw [cantorPrefix_length] at h2
  have h3 : ((plainK V (cantorPrefix w (2 ^ k))).toNat : ℝ) ≤ c * k + c := by
    have h := hc (2 ^ k)
    rw [Nat.log_pow (by norm_num)] at h
    have h' := ENat.toNat_le_of_le_natCast h
    exact_mod_cast h'
  have h4 : Real.logb 2 (((2 ^ k : ℕ) : ℝ) + 1) ≤ k + 1 := by
    have h5 : (((2 ^ k : ℕ) : ℝ) + 1) ≤ (2 : ℝ) ^ (k + 1) := by
      push_cast
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      rw [pow_succ]; linarith
    calc Real.logb 2 (((2 ^ k : ℕ) : ℝ) + 1) ≤ Real.logb 2 ((2 : ℝ) ^ (k + 1)) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) h5
      _ = ((k + 1 : ℕ) : ℝ) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
      _ = k + 1 := by push_cast; ring
  push_cast at h1 h2 h4 hk
  linarith

/-- **SUV Problem 261, p. 269**, in the generality the hint uses: a uniform null set of the form
"all prefixes in a decidable set of strings" is effectively null, since the measures of its finite
approximations decrease computably to `0`.  (The set of Problem 261 is an instance.) -/
private def isEffectivelyNull_of_decidable_tree_approxSet (T : Set BitString) (n : ℕ) :
    Set CantorSeq :=
  {w | ∀ k ≤ n, cantorPrefix w k ∈ T}

/-- Step 1 of the proof of isEffectivelyNull_of_decidable_tree: the approximations are
measurable. -/
private lemma isEffectivelyNull_of_decidable_tree_meas (T : Set BitString) (n : ℕ) : 
  MeasurableSet (isEffectivelyNull_of_decidable_tree_approxSet T n) := by
  have hk : ∀ k, MeasurableSet {w : CantorSeq | cantorPrefix w k ∈ T} := by
    intro k
    have : {w : CantorSeq | cantorPrefix w k ∈ T} =
        ⋃ x ∈ {x : BitString | x ∈ T ∧ x.length = k}, cantorCylinder x := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      constructor
      · intro h
        exact ⟨cantorPrefix w k, ⟨h, cantorPrefix_length w k⟩,
          (isCantorPrefix_iff_cantorPrefix_eq _ _).2 (by rw [cantorPrefix_length])⟩
      · rintro ⟨x, ⟨hx, hxk⟩, hw⟩
        have := (isCantorPrefix_iff_cantorPrefix_eq x w).1 hw
        rw [hxk] at this
        rw [this]; exact hx
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) fun x _ => measurableSet_cantorCylinder x
  have : isEffectivelyNull_of_decidable_tree_approxSet T n =
      ⋂ k ∈ Finset.range (n + 1), {w : CantorSeq | cantorPrefix w k ∈ T} := by
    ext w
    simp [isEffectivelyNull_of_decidable_tree_approxSet]
  rw [this]
  exact Finset.measurableSet_biInter _ fun k _ => hk k

/-- Step 2 of the proof of isEffectivelyNull_of_decidable_tree: the measures converge to
the intersection. -/
private lemma isEffectivelyNull_of_decidable_tree_limit (T : Set BitString) :
    Tendsto (fun n => uniformMeasure (isEffectivelyNull_of_decidable_tree_approxSet T n)) atTop
        (𝓝 (uniformMeasure {w | ∀ n, cantorPrefix w n ∈ T})) := by
  have h_mono : Antitone (isEffectivelyNull_of_decidable_tree_approxSet T) := by
    intro n m hnm w hw k hk
    exact hw k (le_trans hk hnm)
  have h_null : ∀ n, NullMeasurableSet (isEffectivelyNull_of_decidable_tree_approxSet T n)
      uniformMeasure := fun n => (isEffectivelyNull_of_decidable_tree_meas T
                                   n).nullMeasurableSet
  have := MeasureTheory.tendsto_measure_iInter_atTop h_null h_mono ⟨0, measure_ne_top _ _⟩
  have eq1 : (⋂ n, isEffectivelyNull_of_decidable_tree_approxSet T n) = {w | ∀ n, cantorPrefix w n ∈
      T} := by
    ext w
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, isEffectivelyNull_of_decidable_tree_approxSet]
    constructor
    · intro h n
      exact h n n (le_refl n)
    · intro h n k _
      exact h k
  rw [eq1] at this
  exact this

/-- Strings accepted by `g` at all prefix lengths `≤ n` (Boolean test). -/
private def isEffectivelyNull_of_decidable_tree_extract_good (g : BitString → Bool)
    (n : ℕ) (x : BitString) : Bool :=
  !((List.range (n + 1)).any (fun j => !(g (x.take j))))

private lemma isEffectivelyNull_of_decidable_tree_extract_good_iff (g : BitString → Bool)
    (n : ℕ) (x : BitString) :
    isEffectivelyNull_of_decidable_tree_extract_good g n x = true ↔
      ∀ j ≤ n, g (x.take j) = true := by
  unfold isEffectivelyNull_of_decidable_tree_extract_good
  simp

/-- The number of strings of length `n` all of whose prefixes of length `≤ n` are accepted. -/
private def isEffectivelyNull_of_decidable_tree_extract_cnt (g : BitString → Bool)
    (n : ℕ) : ℕ :=
  ((allStrings n).filter (isEffectivelyNull_of_decidable_tree_extract_good g n)).length

private lemma isEffectivelyNull_of_decidable_tree_extract_cnt_computable
    (g : BitString → Bool) (hg : Computable g) :
    Computable (isEffectivelyNull_of_decidable_tree_extract_cnt g) := by
  unfold isEffectivelyNull_of_decidable_tree_extract_cnt
  have hall : Computable (fun n : ℕ => allStrings n) :=
    CodedFiniteDistribution.allStrings_primrec.to_comp
  have h1 : Computable₂ (fun (a : ℕ × BitString) (j : ℕ) => !(g (a.2.take j))) := by
    have h2 : Computable (fun p : (ℕ × BitString) × ℕ => g (p.1.2.take p.2)) := by
      have hx : Computable (fun p : (ℕ × BitString) × ℕ => p.2) := Computable.snd
      have hy : Computable (fun p : (ℕ × BitString) × ℕ => p.1.2) :=
        Computable.snd.comp Computable.fst
      have ht : Computable (fun p : (ℕ × BitString) × ℕ => p.1.2.take p.2) :=
        Primrec.list_take.to_comp.comp hx hy
      have := hg.comp ht
      exact this
    exact (Primrec.not.to_comp.comp h2).to₂
  have h3 : Computable (fun a : ℕ × BitString => (List.range (a.1 + 1)).any
      (fun j => !(g (a.2.take j)))) :=
    computable_list_any (Primrec.list_range.to_comp.comp
      (Primrec.succ.to_comp.comp Computable.fst)) h1
  have h4 : Computable (fun a : ℕ × BitString =>
      isEffectivelyNull_of_decidable_tree_extract_good g a.1 a.2) := by
    have := Primrec.not.to_comp.comp h3
    exact this
  have hp : Computable₂ (fun (n : ℕ) (x : BitString) =>
      isEffectivelyNull_of_decidable_tree_extract_good g n x) := h4
  have := computable_list_filter hall hp
  have h5 := Primrec.list_length.to_comp.comp this
  exact h5

private lemma isEffectivelyNull_of_decidable_tree_extract_measure (T : Set BitString)
    (g : BitString → Bool) (hg : ∀ a, g a = true ↔ a ∈ T) (n : ℕ) :
    uniformMeasure (isEffectivelyNull_of_decidable_tree_approxSet T n) =
      (isEffectivelyNull_of_decidable_tree_extract_cnt g n : ENNReal) *
        (2 : ENNReal)⁻¹ ^ n := by
  classical
  have hnd : ((allStrings n).filter
      (isEffectivelyNull_of_decidable_tree_extract_good g n)).Nodup :=
    (allStrings_nodup n).filter _
  set S : Finset BitString := ((allStrings n).filter
      (isEffectivelyNull_of_decidable_tree_extract_good g n)).toFinset with hS
  have hmem : ∀ x, x ∈ S ↔ x.length = n ∧ ∀ j ≤ n, g (x.take j) = true := by
    intro x
    simp only [hS, List.mem_toFinset, List.mem_filter, mem_allStrings,
      isEffectivelyNull_of_decidable_tree_extract_good_iff]
  have hcard : S.card = isEffectivelyNull_of_decidable_tree_extract_cnt g n := by
    rw [hS, List.toFinset_card_of_nodup hnd]; rfl
  have hset : isEffectivelyNull_of_decidable_tree_approxSet T n = ⋃ x ∈ S, cantorCylinder x := by
    ext w
    simp only [isEffectivelyNull_of_decidable_tree_approxSet, Set.mem_ofPred_eq,
      Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      refine ⟨cantorPrefix w n, (hmem _).2 ⟨by simp, ?_⟩, ?_⟩
      · intro j hj
        rw [cantorPrefix_take w j n hj]
        exact (hg _).2 (h j hj)
      · change IsCantorPrefix (cantorPrefix w n) w
        rw [isCantorPrefix_iff_cantorPrefix_eq]
        simp
    · rintro ⟨x, hx, hw⟩ k hk
      obtain ⟨hlen, hall⟩ := (hmem x).1 hx
      have hw' : IsCantorPrefix x w := hw
      rw [isCantorPrefix_iff_cantorPrefix_eq, hlen] at hw'
      have := hall k hk
      rw [← hw', cantorPrefix_take w k n hk] at this
      exact (hg _).1 this
  have hdisj : Set.PairwiseDisjoint (↑S : Set BitString) cantorCylinder := by
    intro x hx y hy hxy
    have hlx := ((hmem x).1 hx).1
    have hly := ((hmem y).1 hy).1
    apply cantorCylinder_disjoint_of_incompatible
    · intro h; exact hxy (h.eq_of_length (hlx.trans hly.symm))
    · intro h; exact hxy ((h.eq_of_length (hly.trans hlx.symm)).symm)
  rw [hset, measure_biUnion_finset hdisj (fun x _ => measurableSet_cantorCylinder x)]
  have : ∀ x ∈ S, uniformMeasure (cantorCylinder x) = (2 : ENNReal)⁻¹ ^ n := by
    intro x hx
    have := cantorMass_uniformMeasure x
    rw [((hmem x).1 hx).1] at this
    exact this
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcard]

private lemma isEffectivelyNull_of_decidable_tree_extract_iff (c n k : ℕ) :
    (c : ENNReal) * (2 : ENNReal)⁻¹ ^ n ≤ dyadicValue 1 k ↔ c * 2 ^ k ≤ 2 ^ n := by
  unfold dyadicValue
  have h2 : (2 : ENNReal) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2' : (2 : ENNReal) ^ n ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have h3 : (2 : ENNReal) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3' : (2 : ENNReal) ^ k ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have key : ∀ c : ENNReal, c * ((2 : ENNReal) ^ n)⁻¹ ≤ 1 / (2 : ENNReal) ^ k ↔
      c * (2 : ENNReal) ^ k ≤ (2 : ENNReal) ^ n := by
    intro c
    rw [ENNReal.mul_inv_le_iff h2 h2', one_div, mul_comm, ← div_eq_mul_inv,
      ENNReal.le_div_iff_mul_le (Or.inl h3) (Or.inl h3')]
  have := key (c : ENNReal)
  rw [← ENNReal.inv_pow, Nat.cast_one]
  rw [this]
  exact_mod_cast Iff.rfl

/-- Step 3 of the proof of isEffectivelyNull_of_decidable_tree: extract a computable
sequence bounding measure by 2^-k. -/
private lemma isEffectivelyNull_of_decidable_tree_extract (T : Set BitString)
    (hT : IsDecidableSet T)
    (hlimit : Tendsto (fun n => uniformMeasure (isEffectivelyNull_of_decidable_tree_approxSet T n))
        atTop (𝓝 0)) :
    ∃ N : ℕ → ℕ, Computable N ∧ ∀ k, uniformMeasure (isEffectivelyNull_of_decidable_tree_approxSet T
        (N k)) ≤ dyadicValue 1 k := by
  obtain ⟨g, hgc, hg⟩ := hT
  have hcnt := isEffectivelyNull_of_decidable_tree_extract_cnt_computable g hgc
  have hmeas := isEffectivelyNull_of_decidable_tree_extract_measure T g hg
  have hiff := isEffectivelyNull_of_decidable_tree_extract_iff
  have hex : ∀ k : ℕ, ∃ n : ℕ,
      isEffectivelyNull_of_decidable_tree_extract_cnt g n * 2 ^ k ≤ 2 ^ n := by
    intro k
    have hpos : (0 : ENNReal) < dyadicValue 1 k := by
      unfold dyadicValue
      simp only [Nat.cast_one]
      exact ENNReal.div_pos (by norm_num) (ENNReal.pow_ne_top (by norm_num))
    obtain ⟨n, hn⟩ := (hlimit.eventually (gt_mem_nhds hpos)).exists
    refine ⟨n, ?_⟩
    rw [← hiff, ← hmeas]
    exact hn.le
  have hP : Computable (fun p : ℕ × ℕ => decide
      (isEffectivelyNull_of_decidable_tree_extract_cnt g p.2 * 2 ^ p.1 ≤ 2 ^ p.2)) := by
    have h1 : Computable (fun p : ℕ × ℕ =>
        isEffectivelyNull_of_decidable_tree_extract_cnt g p.2) :=
      hcnt.comp Computable.snd
    have h2 : Computable (fun p : ℕ × ℕ => 2 ^ p.1) :=
      (nat_pow_primrec₂.comp (Primrec.const 2) Primrec.fst).to_comp
    have h3 : Computable (fun p : ℕ × ℕ => 2 ^ p.2) :=
      (nat_pow_primrec₂.comp (Primrec.const 2) Primrec.snd).to_comp
    have h4 : Computable (fun p : ℕ × ℕ =>
        isEffectivelyNull_of_decidable_tree_extract_cnt g p.2 * 2 ^ p.1) :=
      (Primrec.nat_mul.to_comp.comp h1 h2)
    obtain ⟨dec, hp⟩ := (Primrec.nat_le : PrimrecRel (fun a b : ℕ => a ≤ b))
    refine (hp.to_comp.comp (Computable.pair h4 h3)).of_eq (fun a => ?_)
    exact Bool.eq_iff_iff.mpr (by simp)
  have hN := Computable.natFind
    (P := fun k n => isEffectivelyNull_of_decidable_tree_extract_cnt g n * 2 ^ k ≤ 2 ^ n)
    hP hex
  refine ⟨_, hN, fun k => ?_⟩
  rw [hmeas, hiff]
  exact Nat.find_spec (hex k)

private lemma isEffectivelyNull_of_decidable_tree_U_foldr (b : ℕ → Bool) (l : List ℕ) :
    l.foldr (fun j s => b j && s) true = true ↔ ∀ j ∈ l, b j = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Step 4 of the proof of isEffectivelyNull_of_decidable_tree: the extracted
approximations are uniformly effectively open. -/
private lemma isEffectivelyNull_of_decidable_tree_U (T : Set BitString) (hT : IsDecidableSet
    T) (N : ℕ → ℕ) (hN : Computable N) :
    IsUniformlyEffectiveOpen (fun k => isEffectivelyNull_of_decidable_tree_approxSet T (N k)) := by
  obtain ⟨g, hg, hgT⟩ := hT
  -- the (Boolean) test applied to the pair `((k, i), x)`
  let test : (ℕ × ℕ) × BitString → Bool := fun p =>
    decide (p.2.length = N p.1.1) &&
      (List.range (N p.1.1 + 1)).foldr (fun j s => g (p.2.take j) && s) true
  have htest : Computable test := by
    have hN1 : Computable fun p : (ℕ × ℕ) × BitString => N p.1.1 :=
      hN.comp (Computable.fst.comp Computable.fst)
    have hx : Computable fun p : (ℕ × ℕ) × BitString => p.2 := Computable.snd
    have heq : Computable₂ fun a b : ℕ => decide (a = b) :=
      (PrimrecRel.decide (Primrec.eq (α := ℕ))).to_comp
    have hlen : Computable fun p : (ℕ × ℕ) × BitString => decide (p.2.length = N p.1.1) :=
      heq.comp (Computable.list_length.comp hx) hN1
    have hlist : Computable fun p : (ℕ × ℕ) × BitString => List.range (N p.1.1 + 1) :=
      Primrec.list_range.to_comp.comp (Computable.succ.comp hN1)
    have hstep : Computable₂ fun (p : (ℕ × ℕ) × BitString) (u : ℕ × Bool) =>
        g (p.2.take u.1) && u.2 := by
      have h1 : Computable fun q : ((ℕ × ℕ) × BitString) × (ℕ × Bool) => q.2.1 :=
        Computable.fst.comp Computable.snd
      have h2 : Computable fun q : ((ℕ × ℕ) × BitString) × (ℕ × Bool) => q.1.2 :=
        Computable.snd.comp Computable.fst
      have h3 : Computable fun q : ((ℕ × ℕ) × BitString) × (ℕ × Bool) => q.2.2 :=
        Computable.snd.comp Computable.snd
      have htake : Computable fun p : ℕ × BitString => p.2.take p.1 :=
        Primrec.list_take.to_comp
      have htk0 := Computable.comp htake (h1.pair h2)
      have htk : Computable fun q : ((ℕ × ℕ) × BitString) × (ℕ × Bool) => q.1.2.take q.2.1 :=
        htk0
      have hgt0 := hg.comp htk
      have hgt : Computable fun q : ((ℕ × ℕ) × BitString) × (ℕ × Bool) => g (q.1.2.take q.2.1) :=
        hgt0
      have hand : Computable₂ (fun a b : Bool => a && b) := (Primrec.and).to_comp
      exact (hand.comp hgt h3).to₂
    have hfold := Computable.list_foldr hlist (Computable.const true) hstep
    have hand : Computable₂ (fun a b : Bool => a && b) := (Primrec.and).to_comp
    exact hand.comp hlen hfold
  let f : ℕ → ℕ → Option BitString := fun k i =>
    (Encodable.decode (α := BitString) i).bind fun x => bif test ((k, i), x) then some x else none
  refine ⟨f, ?_, ?_⟩
  · have hdec : Computable fun p : ℕ × ℕ => Encodable.decode (α := BitString) p.2 :=
      Computable.decode.comp Computable.snd
    have hbody : Computable₂ fun (p : ℕ × ℕ) (x : BitString) =>
        bif test (p, x) then some x else none :=
      Computable.cond (htest.comp (Computable.fst.pair Computable.snd))
        (Computable.option_some.comp Computable.snd) (Computable.const none)
    exact Computable.option_bind hdec hbody
  · intro k
    have htest_iff : ∀ i x, test ((k, i), x) = true ↔
        x.length = N k ∧ ∀ j ≤ N k, x.take j ∈ T := by
      intro i x
      simp only [test, Bool.and_eq_true, decide_eq_true_eq,
        isEffectivelyNull_of_decidable_tree_U_foldr, List.mem_range]
      refine and_congr Iff.rfl (forall_congr' fun j => ?_)
      rw [Nat.lt_succ_iff, hgT]
    ext w
    simp only [isEffectivelyNull_of_decidable_tree_approxSet, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hw
      refine ⟨Encodable.encode (cantorPrefix w (N k)), ?_⟩
      simp only [f, Encodable.encodek, Option.bind_some]
      have : test ((k, Encodable.encode (cantorPrefix w (N k))), cantorPrefix w (N k)) = true := by
        rw [htest_iff]
        refine ⟨cantorPrefix_length _ _, fun j hj => ?_⟩
        rw [cantorPrefix_take w j (N k) hj]
        exact hw j hj
      rw [this]
      exact mem_cantorCylinder_cantorPrefix w _
    · rintro ⟨i, hi⟩
      simp only [f] at hi
      cases hd : Encodable.decode (α := BitString) i with
      | none => simp [hd] at hi
      | some x =>
        rw [hd, Option.bind_some] at hi
        cases ht : test ((k, i), x) with
        | false => simp [ht] at hi
        | true =>
          rw [ht] at hi
          obtain ⟨hlen, hall⟩ := (htest_iff i x).1 ht
          have hw : IsCantorPrefix x w := hi
          have hpre : cantorPrefix w x.length = x := (isCantorPrefix_iff_cantorPrefix_eq x w).1 hw
          intro j hj
          have := hall j hj
          rw [← hpre, hlen, cantorPrefix_take w j (N k) hj] at this
          exact this

/-- The set of infinite paths through a decidable tree `T` is effectively null for the uniform
measure as soon as it has measure zero. -/
theorem isEffectivelyNull_of_decidable_tree {T : Set BitString} (hT : IsDecidableSet T)
    (hnull : uniformMeasure {w | ∀ n, cantorPrefix w n ∈ T} = 0) :
    IsEffectivelyNull uniformMeasure {w | ∀ n, cantorPrefix w n ∈ T} := by
  have hlimit := isEffectivelyNull_of_decidable_tree_limit T
  rw [hnull] at hlimit
  obtain ⟨N, hN, hN_meas⟩ := isEffectivelyNull_of_decidable_tree_extract T hT hlimit
  refine ⟨fun k => isEffectivelyNull_of_decidable_tree_approxSet T (N k), ?_, ?_, hN_meas⟩
  · exact isEffectivelyNull_of_decidable_tree_U T hT N hN
  · intro w hw
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, isEffectivelyNull_of_decidable_tree_approxSet]
    intro k i hi
    exact hw i

/-- Step 1 of the proof of `isEffectivelyNull_zerosDominate`: the set of strings where
zeroes dominate ones is decidable. -/
private lemma isEffectivelyNull_zerosDominate_decidableSet : IsDecidableSet
    {s : BitString | s.count true ≤ s.count false} := by
  have hc : ∀ b : Bool, Primrec (fun s : BitString => s.count b) := fun b => by
    have h := list_countP_primrec (f := fun s : BitString => s)
      (p := fun _ c => c == b) Primrec.id
      (Primrec.beq.comp Primrec.snd (Primrec.const b))
    exact h.of_eq (fun s => by simp [List.count_eq_countP])
  refine ⟨fun s => decide (s.count true ≤ s.count false), ?_, ?_⟩
  · exact (Primrec.nat_le.decide.comp (hc true) (hc false)).to_comp
  · intro s
    simp

/-- Put the bit `b` in front of `w`. -/
private def isEffectivelyNull_zerosDominate_uniformMeasure_null_cons (b : Bool)
    (w : CantorSeq) : CantorSeq :=
  fun i => match i with
    | 0 => b
    | j + 1 => w j

/-- The `±1` walk of the first `n` bits. -/
private def isEffectivelyNull_zerosDominate_uniformMeasure_null_walk (w : CantorSeq) (n : ℕ) :
    ℤ :=
  ∑ i ∈ Finset.range n, if w i then (1 : ℤ) else -1

/-- The level set `L_a`. -/
private def isEffectivelyNull_zerosDominate_uniformMeasure_null_L (a : ℤ) : Set CantorSeq :=
  {w | ∀ n, isEffectivelyNull_zerosDominate_uniformMeasure_null_walk w n ≤ a}

private lemma isEffectivelyNull_zerosDominate_uniformMeasure_null_cons_measurable (b : Bool) :
    Measurable (isEffectivelyNull_zerosDominate_uniformMeasure_null_cons b) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  cases i with
  | zero => exact measurable_const
  | succ j => exact measurable_pi_apply j

private lemma isEffectivelyNull_zerosDominate_uniformMeasure_null_cons_preimage_nil (b : Bool)
    :
    isEffectivelyNull_zerosDominate_uniformMeasure_null_cons b ⁻¹' cantorCylinder [] =
        Set.univ := by
  ext w
  simp [cantorCylinder, IsCantorPrefix]

private lemma isEffectivelyNull_zerosDominate_uniformMeasure_null_cons_preimage_cons
    (b c : Bool)
    (y : BitString) :
    isEffectivelyNull_zerosDominate_uniformMeasure_null_cons b ⁻¹' cantorCylinder (c :: y) =
      if b = c then cantorCylinder y else ∅ := by
  ext w
  by_cases hbc : b = c
  · subst hbc
    simp only [ite_true, Set.mem_preimage, cantorCylinder, Set.mem_ofPred_eq, IsCantorPrefix]
    constructor
    · intro h i hi
      have := h (i + 1) (by simp; omega)
      simpa [isEffectivelyNull_zerosDominate_uniformMeasure_null_cons] using this
    · intro h i hi
      cases i with
      | zero => simp [isEffectivelyNull_zerosDominate_uniformMeasure_null_cons]
      | succ j =>
        have := h j (by simpa using hi)
        simpa [isEffectivelyNull_zerosDominate_uniformMeasure_null_cons] using this
  · simp only [hbc, ite_false, Set.mem_preimage, cantorCylinder, Set.mem_ofPred_eq, IsCantorPrefix,
      Set.mem_empty_iff_false, iff_false]
    intro h
    have := h 0 (by simp)
    exact hbc (by simpa [isEffectivelyNull_zerosDominate_uniformMeasure_null_cons] using this)

private lemma isEffectivelyNull_zerosDominate_uniformMeasure_null_decomp :
    uniformMeasure = (2 : ENNReal)⁻¹ • Measure.map
        (isEffectivelyNull_zerosDominate_uniformMeasure_null_cons true) uniformMeasure +
      (2 : ENNReal)⁻¹ • Measure.map (isEffectivelyNull_zerosDominate_uniformMeasure_null_cons
          false) uniformMeasure := by
  have hm1 := isEffectivelyNull_zerosDominate_uniformMeasure_null_cons_measurable true
  have hm0 := isEffectivelyNull_zerosDominate_uniformMeasure_null_cons_measurable false
  have : IsProbabilityMeasure (Measure.map
      (isEffectivelyNull_zerosDominate_uniformMeasure_null_cons true) uniformMeasure) :=
    ⟨by rw [Measure.map_apply hm1 MeasurableSet.univ]; simp⟩
  have : IsProbabilityMeasure (Measure.map
      (isEffectivelyNull_zerosDominate_uniformMeasure_null_cons false) uniformMeasure) :=
    ⟨by rw [Measure.map_apply hm0 MeasurableSet.univ]; simp⟩
  have : IsProbabilityMeasure ((2 : ENNReal)⁻¹ • Measure.map
      (isEffectivelyNull_zerosDominate_uniformMeasure_null_cons true) uniformMeasure +
      (2 : ENNReal)⁻¹ • Measure.map (isEffectivelyNull_zerosDominate_uniformMeasure_null_cons
          false) uniformMeasure) := by
    constructor
    simp [ENNReal.inv_two_add_inv_two]
  apply cantorMeasure_unique
  intro x
  unfold cantorMass
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply hm1 (measurableSet_cantorCylinder x),
    Measure.map_apply hm0 (measurableSet_cantorCylinder x)]
  have h := cantorMass_uniformMeasure x
  unfold cantorMass at h
  cases x with
  | nil =>
    rw [isEffectivelyNull_zerosDominate_uniformMeasure_null_cons_preimage_nil,
      isEffectivelyNull_zerosDominate_uniformMeasure_null_cons_preimage_nil]
    simpa [ENNReal.inv_two_add_inv_two] using h
  | cons c y =>
    rw [isEffectivelyNull_zerosDominate_uniformMeasure_null_cons_preimage_cons,
      isEffectivelyNull_zerosDominate_uniformMeasure_null_cons_preimage_cons, h]
    have hy := cantorMass_uniformMeasure y
    unfold cantorMass at hy
    cases c <;> simp [hy, pow_succ, mul_comm]

private lemma isEffectivelyNull_zerosDominate_uniformMeasure_null_walk_zero (w : CantorSeq) :
    isEffectivelyNull_zerosDominate_uniformMeasure_null_walk w 0 = 0 := by
  simp [isEffectivelyNull_zerosDominate_uniformMeasure_null_walk]

private lemma isEffectivelyNull_zerosDominate_uniformMeasure_null_walk_cons (b : Bool)
    (w : CantorSeq) (n : ℕ) :
    isEffectivelyNull_zerosDominate_uniformMeasure_null_walk
      (isEffectivelyNull_zerosDominate_uniformMeasure_null_cons b w) (n + 1) =
      (if b then (1 : ℤ) else -1) +
        isEffectivelyNull_zerosDominate_uniformMeasure_null_walk w n := by
  unfold isEffectivelyNull_zerosDominate_uniformMeasure_null_walk
  rw [Finset.sum_range_succ']
  simp [isEffectivelyNull_zerosDominate_uniformMeasure_null_cons, add_comm]
  rfl

private lemma isEffectivelyNull_zerosDominate_uniformMeasure_null_L_measurable (a : ℤ) :
    MeasurableSet (isEffectivelyNull_zerosDominate_uniformMeasure_null_L a) := by
  have hw : ∀ n, Measurable (fun w : CantorSeq =>
      isEffectivelyNull_zerosDominate_uniformMeasure_null_walk w n) := by
    intro n
    unfold isEffectivelyNull_zerosDominate_uniformMeasure_null_walk
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact (Measurable.of_discrete (f := fun b : Bool => if b then (1 : ℤ) else -1)).comp
      (measurable_pi_apply i)
  have : isEffectivelyNull_zerosDominate_uniformMeasure_null_L a =
      ⋂ n, (fun w : CantorSeq => isEffectivelyNull_zerosDominate_uniformMeasure_null_walk w n)
          ⁻¹'
        {z : ℤ | z ≤ a} := by
    ext w; simp [isEffectivelyNull_zerosDominate_uniformMeasure_null_L]
  rw [this]
  exact MeasurableSet.iInter (fun n => (hw n) (MeasurableSet.of_discrete))

private lemma isEffectivelyNull_zerosDominate_uniformMeasure_null_preimage_true (a : ℤ)
    (ha : 0 ≤ a) :
    isEffectivelyNull_zerosDominate_uniformMeasure_null_cons true ⁻¹'
      isEffectivelyNull_zerosDominate_uniformMeasure_null_L a =
      isEffectivelyNull_zerosDominate_uniformMeasure_null_L (a - 1) := by
  ext w
  simp only [Set.mem_preimage, isEffectivelyNull_zerosDominate_uniformMeasure_null_L,
      Set.mem_ofPred_eq]
  constructor
  · intro h n
    have := h (n + 1)
    rw [isEffectivelyNull_zerosDominate_uniformMeasure_null_walk_cons] at this
    simp at this
    omega
  · intro h n
    cases n with
    | zero => simpa [isEffectivelyNull_zerosDominate_uniformMeasure_null_walk_zero] using ha
    | succ n =>
      rw [isEffectivelyNull_zerosDominate_uniformMeasure_null_walk_cons]
      have := h n
      simp
      omega

private lemma isEffectivelyNull_zerosDominate_uniformMeasure_null_preimage_false (a : ℤ)
    (ha : 0 ≤ a) :
    isEffectivelyNull_zerosDominate_uniformMeasure_null_cons false ⁻¹'
      isEffectivelyNull_zerosDominate_uniformMeasure_null_L a =
      isEffectivelyNull_zerosDominate_uniformMeasure_null_L (a + 1) := by
  ext w
  simp only [Set.mem_preimage, isEffectivelyNull_zerosDominate_uniformMeasure_null_L,
      Set.mem_ofPred_eq]
  constructor
  · intro h n
    have := h (n + 1)
    rw [isEffectivelyNull_zerosDominate_uniformMeasure_null_walk_cons] at this
    simp at this
    omega
  · intro h n
    cases n with
    | zero => simpa [isEffectivelyNull_zerosDominate_uniformMeasure_null_walk_zero] using ha
    | succ n =>
      rw [isEffectivelyNull_zerosDominate_uniformMeasure_null_walk_cons]
      have := h n
      simp
      omega

private lemma isEffectivelyNull_zerosDominate_uniformMeasure_null_rec (a : ℤ) (ha : 0 ≤ a) :
    (uniformMeasure (isEffectivelyNull_zerosDominate_uniformMeasure_null_L a)).toReal =
      (1 / 2) * (uniformMeasure (isEffectivelyNull_zerosDominate_uniformMeasure_null_L
          (a - 1))).toReal +
      (1 / 2) * (uniformMeasure (isEffectivelyNull_zerosDominate_uniformMeasure_null_L
          (a + 1))).toReal := by
  have hL := isEffectivelyNull_zerosDominate_uniformMeasure_null_L_measurable a
  have h : uniformMeasure (isEffectivelyNull_zerosDominate_uniformMeasure_null_L a) =
      2⁻¹ * uniformMeasure (isEffectivelyNull_zerosDominate_uniformMeasure_null_L (a - 1)) +
      2⁻¹ * uniformMeasure (isEffectivelyNull_zerosDominate_uniformMeasure_null_L (a + 1)) :=
          by
    conv_lhs => rw [isEffectivelyNull_zerosDominate_uniformMeasure_null_decomp]
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.map_apply (isEffectivelyNull_zerosDominate_uniformMeasure_null_cons_measurable true)
          hL,
      Measure.map_apply (isEffectivelyNull_zerosDominate_uniformMeasure_null_cons_measurable false)
          hL,
      isEffectivelyNull_zerosDominate_uniformMeasure_null_preimage_true a ha,
      isEffectivelyNull_zerosDominate_uniformMeasure_null_preimage_false a ha]
    rfl
  rw [h, ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _))
    (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)), ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp

private lemma isEffectivelyNull_zerosDominate_uniformMeasure_null_ZD_eq :
    {w : CantorSeq | ZerosDominate w} = isEffectivelyNull_zerosDominate_uniformMeasure_null_L
        0 := by
  have key : ∀ (w : CantorSeq) (n : ℕ), (onesCount w n : ℤ) - (zerosCount w n : ℤ) =
      isEffectivelyNull_zerosDominate_uniformMeasure_null_walk w n := by
    intro w n
    induction n with
    | zero => simp [onesCount, zerosCount, cantorPrefix,
                isEffectivelyNull_zerosDominate_uniformMeasure_null_walk]
    | succ n ih =>
      have e : isEffectivelyNull_zerosDominate_uniformMeasure_null_walk w (n + 1) =
          isEffectivelyNull_zerosDominate_uniformMeasure_null_walk w n +
              (if w n then 1 else -1) := by
        unfold isEffectivelyNull_zerosDominate_uniformMeasure_null_walk
        rw [Finset.sum_range_succ]
      rw [e, ← ih]
      unfold onesCount zerosCount
      rw [cantorPrefix_succ]
      cases h : w n <;> simp [List.count_append] <;> omega
  ext w
  simp only [ZerosDominate, Set.mem_ofPred_eq,
      isEffectivelyNull_zerosDominate_uniformMeasure_null_L]
  constructor
  · intro h n
    rw [← key]
    have := h n
    omega
  · intro h n
    have := h n
    rw [← key] at this
    omega

/-- Step 2 of the proof of `isEffectivelyNull_zerosDominate`: the measure of sequences
where zeros dominate ones is 0. -/
private lemma isEffectivelyNull_zerosDominate_uniformMeasure_null : uniformMeasure
    {w : CantorSeq | ZerosDominate w} = 0 := by
  rw [isEffectivelyNull_zerosDominate_uniformMeasure_null_ZD_eq]
  set m : ℤ → ℝ := fun a =>
    (uniformMeasure (isEffectivelyNull_zerosDominate_uniformMeasure_null_L a)).toReal with hm
  have hle : ∀ a, m a ≤ 1 := by
    intro a
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := uniformMeasure)
      (s := isEffectivelyNull_zerosDominate_uniformMeasure_null_L a))
    simpa [hm] using this
  have hrec : ∀ a : ℤ, 0 ≤ a → m a = 1 / 2 * m (a - 1) + 1 / 2 * m (a + 1) :=
    fun a ha => isEffectivelyNull_zerosDominate_uniformMeasure_null_rec a ha
  have hneg : m (-1) = 0 := by
    have : isEffectivelyNull_zerosDominate_uniformMeasure_null_L (-1) = ∅ := by
      ext w
      simp only [isEffectivelyNull_zerosDominate_uniformMeasure_null_L, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨0, by simp [isEffectivelyNull_zerosDominate_uniformMeasure_null_walk_zero]⟩
    simp [hm, this]
  have claim : ∀ k : ℕ, m ((k : ℤ) - 1) = k * m 0 ∧ m (k : ℤ) = (k + 1) * m 0 := by
    intro k
    induction k with
    | zero => simp [hneg]
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      have e1 : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by push_cast; ring
      have e2 := hrec (k : ℤ) (by positivity)
      refine ⟨?_, ?_⟩
      · rw [e1, h2]; push_cast; ring
      · have e3 : (((k + 1 : ℕ) : ℤ)) = (k : ℤ) + 1 := by push_cast; ring
        rw [e3]
        rw [h1, h2] at e2
        push_cast
        linarith
  have hc0 : 0 ≤ m 0 := ENNReal.toReal_nonneg
  have hc : m 0 = 0 := by
    by_contra hne
    have hpos : 0 < m 0 := lt_of_le_of_ne hc0 (Ne.symm hne)
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / m 0)
    have h1 : 1 < (k : ℝ) * m 0 := (div_lt_iff₀ hpos).mp hk
    have h2 := hle (k : ℤ)
    rw [(claim k).2] at h2
    nlinarith
  have : (uniformMeasure (isEffectivelyNull_zerosDominate_uniformMeasure_null_L 0)).toReal =
      0 := hc
  rcases (ENNReal.toReal_eq_zero_iff _).mp this with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

/-- **SUV Problem 262, p. 270.**  The sequences all of whose prefixes have at least as many zeros as
ones form an effectively null set, proved without the law of the iterated logarithm.  The book says
"more zeros than ones"; the set stated here contains that one, and is the set that Theorem 182(d)
needs.  (`IsEffectivelyNull` passes to subsets.) -/
theorem isEffectivelyNull_zerosDominate :
    IsEffectivelyNull uniformMeasure {w | ZerosDominate w} := by
  have hT := isEffectivelyNull_zerosDominate_decidableSet
  have hnull := isEffectivelyNull_zerosDominate_uniformMeasure_null
  have H : {w : CantorSeq | ZerosDominate w} = {w : CantorSeq | ∀ n, cantorPrefix w n ∈
      {s : BitString | s.count true ≤ s.count false}} := by
    ext w
    simp [ZerosDominate, zerosCount, onesCount]
  rw [H]
  rw [H] at hnull
  exact isEffectivelyNull_of_decidable_tree hT hnull

end Kolmogorov.FrequencyGames
