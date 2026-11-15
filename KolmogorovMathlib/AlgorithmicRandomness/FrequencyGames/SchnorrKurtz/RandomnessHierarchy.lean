/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz.SchnorrMartingaleGrowth
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz.KurtzMartingales

/-!
# Randomness Hierarchy

This module compares Martin-Löf, Schnorr and Kurtz randomness on Cantor space and relates them
to the Strong Law of Large Numbers.

* `isSchnorrRandom_of_isMartinLofRandom`: Martin-Löf random sequences are Schnorr random.
* `isKurtzRandom_of_isSchnorrRandom`: Schnorr random sequences are Kurtz random
  (SUV p. 284, after Problem 272).
* `isBalanced_of_isSchnorrRandom`: Schnorr random sequences satisfy the Strong Law of Large
  Numbers (SUV Problem 92 of Section 3.4, cited on p. 310).
* `exists_isKurtzRandom_not_isBalanced`: some Kurtz random sequence does not satisfy it, so the
  inclusion of Schnorr randomness in Kurtz randomness is strict.

It formalizes the hierarchy of randomness notions in the book by Shen, Uspensky and
Vereshchagin.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped ENNReal

/-- **SUV p. 284, after Problem 272.**  Schnorr random sequences are Kurtz random. -/
theorem isKurtzRandom_of_isSchnorrRandom {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) {w : CantorSeq}
    (hw : IsSchnorrRandom π w) : IsKurtzRandom π w := by
  intro h_not_kurtz
  have h_not : ¬IsKurtzRandom π w := by
    change ¬ ¬ IsKurtzNull π {w}
    intro h_not_not
    exact h_not_not h_not_kurtz
  have ⟨m, g, h_fair, h_comp, h_growth, h_forall⟩ := (not_isKurtzRandom_iff_exists_growth hπ hpos
      w).mp h_not
  have h_freq : ∃ᶠ n in atTop, (g n : ℝ) ≤ m (cantorPrefix w n) := by
    apply Filter.Eventually.frequently
    exact Filter.Eventually.of_forall h_forall
  have h_not_schnorr : ¬IsSchnorrRandom π w := by
    apply (not_isSchnorrRandom_iff_exists_growth hπ hpos w).mpr
    exact ⟨m, g, h_fair, h_comp, h_growth, h_freq⟩
  exact h_not_schnorr hw

/-- Step 1 of the proof of `exists_isKurtzRandom_not_isBalanced`: The set of computable
functions `f : ℕ → List BitString` is countable. -/
private lemma exists_isKurtzRandom_not_isBalanced_countable_computable :
    Set.Countable {f : ℕ → List BitString | Computable f} := by
  classical
  have hex : ∀ f : {f : ℕ → List BitString | Computable f},
      ∃ c : Nat.Partrec.Code, Nat.Partrec.Code.eval c =
        fun n => Part.bind (Encodable.decode (α := ℕ) n) fun a =>
          (((f.1 a : List BitString) : Part (List BitString))).map Encodable.encode :=
    fun f => Nat.Partrec.Code.exists_code.mp f.2.partrec
  choose g hg using hex
  have hinj : Function.Injective g := by
    intro f₁ f₂ h
    apply Subtype.ext
    funext a
    have h1 := congrFun (hg f₁) (Encodable.encode a)
    have h2 := congrFun (hg f₂) (Encodable.encode a)
    rw [h] at h1
    have h3 := h1.symm.trans h2
    simp only [Encodable.encodek, Part.coe_some, Part.bind_some, Part.map_some, Part.some_inj,
      Encodable.encode_inj] at h3
    exact h3
  have : Countable {f : ℕ → List BitString | Computable f} := hinj.countable
  exact Set.countable_coe_iff.mp this

/-- Step 2 of the proof of `exists_isKurtzRandom_not_isBalanced`: If a computable function
`f : ℕ → List BitString` satisfies the Kurtz budget bound `∀ n, ((f n).map (cantorMass
uniformMeasure)).sum ≤ dyadicValue 1 n`, then the complement of the intersection over n of the union
of cylinders for strings in `f n` is open and dense. -/
private lemma exists_isKurtzRandom_not_isBalanced_dense_compl (f : ℕ → List BitString)
    (hbound : ∀ n, ((f n).map (cantorMass uniformMeasure)).sum ≤ dyadicValue 1 n) :
    Dense (⋂ n, ⋃ x ∈ f n, {w | IsCantorPrefix x w})ᶜ := by
  rw [isTopologicalBasis_cantorCylinders.dense_iff]
  rintro o ⟨σ, rfl⟩ ⟨w₀, hw₀⟩
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hsub : cantorCylinder σ ⊆ ⋃ x ∈ f (σ.length + 1), {w | IsCantorPrefix x w} := by
    intro w hw
    by_contra hnot
    have : w ∈ cantorCylinder σ ∩ (⋂ n, ⋃ x ∈ f n, {w | IsCantorPrefix x w})ᶜ := by
      refine ⟨hw, fun hK => hnot ?_⟩
      exact Set.mem_iInter.mp hK (σ.length + 1)
    rw [hne] at this
    exact this
  have hunion : ∀ l : List BitString,
      uniformMeasure (⋃ x ∈ l, {w | IsCantorPrefix x w}) ≤
        (l.map (cantorMass uniformMeasure)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.sum_cons]
      simp only [List.mem_cons, Set.iUnion_iUnion_eq_or_left]
      refine (measure_union_le _ _).trans ?_
      exact add_le_add le_rfl ih
  have h1 : uniformMeasure (cantorCylinder σ) ≤ dyadicValue 1 (σ.length + 1) :=
    (measure_mono hsub).trans ((hunion _).trans (hbound _))
  have h2 : uniformMeasure (cantorCylinder σ) = (2 : ENNReal)⁻¹ ^ σ.length :=
    cantorMass_uniformMeasure σ
  rw [h2, dyadicValue_one_eq_inv_two_pow', pow_succ'] at h1
  have hpos : (0 : ENNReal) < (2 : ENNReal)⁻¹ ^ σ.length := by
    apply ENNReal.pow_pos
    simp
  have hfin : (2 : ENNReal)⁻¹ ^ σ.length ≠ ⊤ := by
    apply ENNReal.pow_ne_top
    simp
  have hlt : (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ ^ σ.length < (2 : ENNReal)⁻¹ ^ σ.length := by
    calc (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ ^ σ.length
        = (2 : ENNReal)⁻¹ ^ σ.length * (2 : ENNReal)⁻¹ := mul_comm _ _
      _ < (2 : ENNReal)⁻¹ ^ σ.length * 1 :=
          ENNReal.mul_lt_mul_right hpos.ne' hfin (by simp)
      _ = _ := mul_one _
  exact absurd h1 (not_le.mpr hlt)

/-- Step 3 of the proof of `exists_isKurtzRandom_not_isBalanced`: For every N, the set of
sequences `w` with some `n ≥ N` satisfying `(3 / 4 : ℝ) ≤ freqOne w n` is open and dense. -/
private lemma exists_isKurtzRandom_not_isBalanced_dense_freq (N : ℕ) :
    Dense {w : CantorSeq | ∃ n ≥ N, (3 / 4 : ℝ) ≤ (Kolmogorov.freqOne w n : ℝ)} ∧
    IsOpen {w : CantorSeq | ∃ n ≥ N, (3 / 4 : ℝ) ≤ (Kolmogorov.freqOne w n : ℝ)} := by
  constructor
  · rw [isTopologicalBasis_cantorCylinders.dense_iff]
    rintro o ⟨σ, rfl⟩ _
    set w' : CantorSeq := prependCantor σ (fun _ => true) with hw'
    have hmem : w' ∈ cantorCylinder σ := isCantorPrefix_prepend σ _
    refine ⟨w', hmem, 4 * (σ.length + N) + 4, by omega, ?_⟩
    set n := 4 * (σ.length + N) + 4 with hn
    have hnpos : (0 : ℝ) < n := by positivity
    rw [Kolmogorov.freqOne_eq, le_div_iff₀ hnpos]
    have hones : ∀ i ∈ Finset.Ico σ.length n, Kolmogorov.bitVal (w' i) = 1 := by
      intro i hi
      have hi' := (Finset.mem_Ico.1 hi).1
      have : w' i = true := by
        simp [hw', prependCantor, show ¬ i < σ.length by omega]
      simp [this, Kolmogorov.bitVal]
    have hsub : Finset.Ico σ.length n ⊆ Finset.range n := by
      intro i hi
      exact Finset.mem_range.2 (Finset.mem_Ico.1 hi).2
    have h1 : ∑ i ∈ Finset.Ico σ.length n, Kolmogorov.bitVal (w' i) ≤
        ∑ i ∈ Finset.range n, Kolmogorov.bitVal (w' i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by
        unfold Kolmogorov.bitVal; split_ifs <;> norm_num)
    rw [Finset.sum_congr rfl hones] at h1
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one] at h1
    have h2 : ((n - σ.length : ℕ) : ℝ) = (n : ℝ) - σ.length := by
      rw [Nat.cast_sub (by omega)]
    rw [h2] at h1
    have h3 : (4 * (σ.length + N) + 4 : ℝ) = n := by rw [hn]; push_cast; ring
    have h4 : (σ.length : ℝ) * 4 ≤ n := by
      have : σ.length * 4 ≤ n := by omega
      exact_mod_cast this
    nlinarith
  · rw [isOpen_iff_forall_mem_open]
    rintro w ⟨n, hnN, hn⟩
    refine ⟨cantorCylinder (cantorPrefix w n), ?_, isOpen_cantorCylinder _, ?_⟩
    · rintro v hv
      refine ⟨n, hnN, ?_⟩
      have hv' : cantorPrefix v n = cantorPrefix w n := by
        have := (isCantorPrefix_iff_cantorPrefix_eq _ _).1 hv
        simpa using this
      have : Kolmogorov.freqOne v n = Kolmogorov.freqOne w n := by
        unfold Kolmogorov.freqOne; rw [hv']
      rw [this]; exact hn
    · exact (isCantorPrefix_iff_cantorPrefix_eq _ _).2 (by simp)

/-- Step 4 of the proof of `exists_isKurtzRandom_not_isBalanced`: The Baire Category
Theorem implies the intersection of countably many dense open sets is dense (and thus non-empty),
which allows us to find a sequence that is Kurtz random but has frequency of ones $\ge 3/4$
infinitely often. -/
private lemma exists_isKurtzRandom_not_isBalanced_assembly :
    ∃ w : CantorSeq, IsKurtzRandom uniformMeasure w ∧ (∃ᶠ n in atTop, (3 / 4 : ℝ) ≤
        (Kolmogorov.freqOne w n : ℝ)) := by
  let S : Set (ℕ → List BitString) :=
    {f | Computable f ∧ ∀ n, ((f n).map (cantorMass uniformMeasure)).sum ≤ dyadicValue 1 n}
  have hS : S.Countable :=
    exists_isKurtzRandom_not_isBalanced_countable_computable.mono (fun f hf => hf.1)
  have : Countable S := hS.to_subtype
  let U : ℕ → Set CantorSeq := fun N => {w | ∃ n ≥ N, (3 / 4 : ℝ) ≤ (Kolmogorov.freqOne w n : ℝ)}
  let F : ℕ ⊕ S → Set CantorSeq := Sum.elim U (fun f => (⋂ n, ⋃ x ∈ f.1 n,
                                                          {w | IsCantorPrefix x w})ᶜ)
  have hopen : ∀ i, IsOpen (F i) := by
    rintro (N | f)
    · exact (exists_isKurtzRandom_not_isBalanced_dense_freq N).2
    · change IsOpen (⋂ n, ⋃ x ∈ f.1 n, {w | IsCantorPrefix x w})ᶜ
      have hc : IsClosed (⋂ n, ⋃ x ∈ f.1 n, {w | IsCantorPrefix x w}) :=
        isClosed_iInter fun n =>
          (List.finite_toSet (f.1 n)).isClosed_biUnion (fun x _ => isClosed_cantorCylinder x)
      exact hc.isOpen_compl
  have hdense : ∀ i, Dense (F i) := by
    rintro (N | f)
    · exact (exists_isKurtzRandom_not_isBalanced_dense_freq N).1
    · exact exists_isKurtzRandom_not_isBalanced_dense_compl f.1 f.2.2
  obtain ⟨w, hw⟩ := (dense_iInter_of_isOpen hopen hdense).nonempty
  rw [Set.mem_iInter] at hw
  refine ⟨w, ?_, ?_⟩
  · rintro ⟨f, hfc, hf⟩
    have hmem : f ∈ S := ⟨hfc, fun n => (hf n).2⟩
    have h1 := hw (Sum.inr ⟨f, hmem⟩)
    apply h1
    rw [Set.mem_iInter]
    intro n
    have := (hf n).1 (Set.mem_singleton w)
    simpa [cantorCylinder] using this
  · rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, h⟩ := hw (Sum.inl N)
    exact ⟨n, hn, h⟩

/-- Step 5 of the proof of `exists_isKurtzRandom_not_isBalanced`: If the frequency of ones
exceeds 3/4 infinitely often, the sequence is not balanced. -/
private lemma exists_isKurtzRandom_not_isBalanced_not_balanced (w : CantorSeq) :
    (∃ᶠ n in atTop, (3 / 4 : ℝ) ≤ (Kolmogorov.freqOne w n : ℝ)) →
        ¬ (Filter.Tendsto (fun n => (Kolmogorov.freqOne w n : ℝ)) Filter.atTop (𝓝 (1 / 2))) := by
  intro hfreq hbal
  have h_nhds : Set.Iio (3 / 4 : ℝ) ∈ 𝓝 (1 / 2 : ℝ) := by
    apply Iio_mem_nhds
    norm_num
  have h_eventually := hbal h_nhds
  have h_not : ∀ᶠ (x : ℕ) in atTop, ¬(3 / 4 : ℝ) ≤ (Kolmogorov.freqOne w x : ℝ) := by
    filter_upwards [h_eventually] with x hx
    exact not_le.mpr hx
  exact hfreq h_not

/-- **SUV Problem 92 of Section 3.4, cited on p. 284 and p. 310.**  Some Kurtz random sequence does
not satisfy the Strong Law of Large Numbers, so the inclusion above is strict. -/
theorem exists_isKurtzRandom_not_isBalanced :
    ∃ w, IsKurtzRandom uniformMeasure w ∧ ¬ IsBalanced w := by
  have ⟨w, h_kurtz, h_freq⟩ := exists_isKurtzRandom_not_isBalanced_assembly
  exact ⟨w, h_kurtz, exists_isKurtzRandom_not_isBalanced_not_balanced w h_freq⟩

private lemma isBalanced_of_isSchnorrRandom_isSchnorrNull_of_isUniformlyEffectivelyNull_aux_comp
    (q : ℕ × ℕ × ℕ → ℚ) (hq : Computable q) :
    Computable (fun p : ℕ × ℕ => ∑ k ∈ Finset.range (p.2 + 1), q (k, p.1 + k + 1, 2 * p.2 + 2)) :=
        by
  have hn1 : Computable (fun r : (ℕ × ℕ) × (ℕ × ℚ) => r.1.1 + r.2.1 + 1) :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd)) (Computable.const 1)
  have hn2 : Computable (fun r : (ℕ × ℕ) × (ℕ × ℚ) => 2 * r.1.2 + 2) :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 2) (Computable.snd.comp Computable.fst))
      (Computable.const 2)
  have htrip : Computable (fun r : (ℕ × ℕ) × (ℕ × ℚ) =>
      ((r.2.1, r.1.1 + r.2.1 + 1, 2 * r.1.2 + 2) : ℕ × ℕ × ℕ)) :=
    (Computable.fst.comp Computable.snd).pair (hn1.pair hn2)
  have hh : Computable₂ (fun (a : ℕ × ℕ) (r : ℕ × ℚ) =>
      r.2 + q (r.1, a.1 + r.1 + 1, 2 * a.2 + 2)) := by
    have := Computable₂.comp (f := fun a b : ℚ => a + b)
      (g := fun r : (ℕ × ℕ) × (ℕ × ℚ) => r.2.2)
      (h := fun r : (ℕ × ℕ) × (ℕ × ℚ) => q (r.2.1, r.1.1 + r.2.1 + 1, 2 * r.1.2 + 2))
      computable₂_ratAdd
      (Computable.snd.comp Computable.snd) (hq.comp htrip)
    exact this
  have hrec := Computable.nat_rec (f := fun a : ℕ × ℕ => a.2 + 1) (g := fun _ : ℕ × ℕ => (0 : ℚ))
    (h := fun (a : ℕ × ℕ) (r : ℕ × ℚ) => r.2 + q (r.1, a.1 + r.1 + 1, 2 * a.2 + 2))
    (Primrec.nat_add.to_comp.comp Computable.snd (Computable.const 1)) (Computable.const 0) hh
  refine hrec.of_eq fun p => ?_
  have key : ∀ j : ℕ, (Nat.rec (0 : ℚ) (fun y IH => IH + q (y, p.1 + y + 1, 2 * p.2 + 2)) j : ℚ)
      = ∑ k ∈ Finset.range j, q (k, p.1 + k + 1, 2 * p.2 + 2) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [Finset.sum_range_succ, ← ih]
  exact key (p.2 + 1)

private lemma isBalanced_of_isSchnorrRandom_isSchnorrNull_of_isUniformlyEffectivelyNull_aux_geom
    (n : ℕ) : ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + k + 1) = dyadicValue 1 n := by
  have hgeom : ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + k + 1)
      = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) * ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k := by
    rw [ENNReal.tsum_mul_left.symm]
    refine tsum_congr fun k => ?_
    rw [← pow_add]
    ring_nf
  rw [hgeom, ENNReal.tsum_geometric, dyadicValue_one_eq_inv_two_pow']
  have h2 : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
    rw [ENNReal.sub_eq_of_eq_add (by simp) ?_]
    · rw [ENNReal.inv_two_add_inv_two]
  rw [h2, pow_succ]
  rw [mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]

private lemma isBalanced_of_isSchnorrRandom_isSchnorrNull_of_isUniformlyEffectivelyNull_aux_err
    (n t : ℕ) (v : ℕ → ℝ) (qs : ℕ → ℚ)
    (hv0 : ∀ k, 0 ≤ v k) (hvb : ∀ k, v k ≤ (2 : ℝ)⁻¹ ^ (n + k + 1))
    (hqs : ∀ k, k < t + 1 → |(qs k : ℝ) - v k| ≤ (2 : ℝ)⁻¹ ^ (2 * t + 2)) :
    |((∑ k ∈ Finset.range (t + 1), qs k : ℚ) : ℝ) - ∑' k, v k| ≤ (2 : ℝ)⁻¹ ^ t := by
  have hg0 : Summable (fun k : ℕ => (2 : ℝ)⁻¹ ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hgs : Summable (fun k : ℕ => (2 : ℝ)⁻¹ ^ (n + k + 1)) := by
    have : Summable (fun k : ℕ => (2 : ℝ)⁻¹ ^ (n + 1) * (2 : ℝ)⁻¹ ^ k) := hg0.mul_left _
    refine this.congr fun k => ?_
    rw [← pow_add]; ring_nf
  have hsum : Summable v := Summable.of_nonneg_of_le hv0 hvb hgs
  have hsplit := hsum.sum_add_tsum_nat_add (t + 1)
  have htail0 : 0 ≤ ∑' k, v (k + (t + 1)) := tsum_nonneg fun k => hv0 _
  have htail : ∑' k, v (k + (t + 1)) ≤ (2 : ℝ)⁻¹ ^ (t + 1) := by
    have hle : ∀ k, v (k + (t + 1)) ≤ (2 : ℝ)⁻¹ ^ (t + 1) * ((2 : ℝ)⁻¹ ^ (n + 1)) * (2 : ℝ)⁻¹ ^ k :=
        by
      intro k
      refine (hvb _).trans ?_
      have : (2 : ℝ)⁻¹ ^ (n + (k + (t + 1)) + 1)
          = (2 : ℝ)⁻¹ ^ (t + 1) * ((2 : ℝ)⁻¹ ^ (n + 1)) * (2 : ℝ)⁻¹ ^ k := by
        rw [← pow_add, ← pow_add]; ring_nf
      exact this.le
    have hgs2 : Summable (fun k : ℕ => (2 : ℝ)⁻¹ ^ (t + 1) * ((2 : ℝ)⁻¹ ^ (n + 1)) * (2 : ℝ)⁻¹ ^ k)
        :=
      (hg0.mul_left _)
    have hsh : Summable (fun k : ℕ => v (k + (t + 1))) :=
      (summable_nat_add_iff (t + 1)).2 hsum
    refine (Summable.tsum_le_tsum hle hsh hgs2).trans ?_
    rw [tsum_mul_left]
    have hg : ∑' k : ℕ, (2 : ℝ)⁻¹ ^ k = 2 := by
      have := tsum_geometric_two
      simpa using this
    rw [hg]
    have h1 : (2 : ℝ)⁻¹ ^ (n + 1) * 2 ≤ 1 := by
      rw [pow_succ]
      have : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have h0 : 0 ≤ (2 : ℝ)⁻¹ ^ (t + 1) := by positivity
    nlinarith
  have hhead : |∑ k ∈ Finset.range (t + 1), ((qs k : ℝ) - v k)| ≤ (2 : ℝ)⁻¹ ^ (t + 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∑ k ∈ Finset.range (t + 1), |(qs k : ℝ) - v k|
        ≤ ∑ k ∈ Finset.range (t + 1), (2 : ℝ)⁻¹ ^ (2 * t + 2) :=
      Finset.sum_le_sum fun k hk => hqs k (Finset.mem_range.1 hk)
    refine h1.trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h2 : ((t : ℝ) + 1) ≤ 2 ^ (t + 1) := by
      have := Nat.lt_two_pow_self (n := t + 1)
      have h3 : ((t + 1 : ℕ) : ℝ) ≤ ((2 ^ (t + 1) : ℕ) : ℝ) := by exact_mod_cast this.le
      push_cast at h3
      exact h3
    have h4 : (2 : ℝ)⁻¹ ^ (2 * t + 2) = (2 : ℝ)⁻¹ ^ (t + 1) * (2 : ℝ)⁻¹ ^ (t + 1) := by
      rw [← pow_add]; ring_nf
    have h5 : (2 : ℝ)⁻¹ ^ (t + 1) * 2 ^ (t + 1) = 1 := by
      rw [← mul_pow]; simp
    have h6 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (t + 1) := by positivity
    push_cast
    rw [h4]
    calc ((t : ℝ) + 1) * ((2 : ℝ)⁻¹ ^ (t + 1) * (2 : ℝ)⁻¹ ^ (t + 1))
        ≤ 2 ^ (t + 1) * ((2 : ℝ)⁻¹ ^ (t + 1) * (2 : ℝ)⁻¹ ^ (t + 1)) := by
          gcongr
      _ = (2 : ℝ)⁻¹ ^ (t + 1) := by
          calc (2 : ℝ) ^ (t + 1) * ((2 : ℝ)⁻¹ ^ (t + 1) * (2 : ℝ)⁻¹ ^ (t + 1))
              = ((2 : ℝ)⁻¹ ^ (t + 1) * 2 ^ (t + 1)) * (2 : ℝ)⁻¹ ^ (t + 1) := by ring
            _ = _ := by rw [h5, one_mul]
  have hpt : (2 : ℝ)⁻¹ ^ t = (2 : ℝ)⁻¹ ^ (t + 1) + (2 : ℝ)⁻¹ ^ (t + 1) := by
    rw [pow_succ]; ring
  have heq : ((∑ k ∈ Finset.range (t + 1), qs k : ℚ) : ℝ) - ∑' k, v k
      = ∑ k ∈ Finset.range (t + 1), ((qs k : ℝ) - v k) - ∑' k, v (k + (t + 1)) := by
    rw [Finset.sum_sub_distrib]
    push_cast
    linarith
  rw [heq, hpt]
  rw [abs_le] at hhead ⊢
  constructor <;> linarith [hhead.1, hhead.2]

/-- Step 1 of the proof of `isBalanced_of_isSchnorrRandom`: uniform effectively null
union. -/
private theorem isBalanced_of_schnorrNull_union (π :
    Measure CantorSeq) (A : ℕ → Set CantorSeq) (g : ℕ → ℕ → ℕ → Option BitString)
    (hg : Computable fun p : ℕ × ℕ × ℕ => g p.1 p.2.1 p.2.2) (hcover : ∀ k m, A k ⊆ ⋃ i,
    (g k m i).elim ∅ cantorCylinder) (hbound : ∀ k m, ∑' i, coverMass π (g k m i) ≤ dyadicValue 1 m)
    (hreal : ∃ q : ℕ × ℕ × ℕ → ℚ, Computable q ∧ ∀ k m s, |(q (k, m, s) : ℝ) -
    (∑' i, coverMass π (g k m i)).toReal| ≤ (2 : ℝ)⁻¹ ^ s) : IsSchnorrNull π (⋃ k, A k) := by
  obtain ⟨q, hq, hqerr⟩ := hreal
  have hsum : ∀ n, ∑' j, coverMass π (g (Nat.unpair j).1 (n + (Nat.unpair j).1 + 1)
      (Nat.unpair j).2)
      = ∑' k, ∑' i, coverMass π (g k (n + k + 1) i) := by
    intro n
    rw [← ENNReal.tsum_prod (f := fun k i => coverMass π (g k (n + k + 1) i))]
    rw [← Nat.pairEquiv.tsum_eq (fun j => coverMass π
      (g (Nat.unpair j).1 (n + (Nat.unpair j).1 + 1) (Nat.unpair j).2))]
    refine tsum_congr fun p => ?_
    have e : Nat.pairEquiv p = Nat.pair p.1 p.2 := rfl
    rw [e, Nat.unpair_pair]
  have hfin : ∀ k m, ∑' i, coverMass π (g k m i) ≠ ⊤ := by
    intro k m
    refine ne_top_of_le_ne_top ?_ (hbound k m)
    rw [dyadicValue_one_eq_inv_two_pow']
    exact ENNReal.pow_ne_top (by simp)
  refine ⟨fun n j => g (Nat.unpair j).1 (n + (Nat.unpair j).1 + 1) (Nat.unpair j).2, ?_, ?_, ?_, ?_⟩
  · have hu : Computable (fun p : ℕ × ℕ => Nat.unpair p.2) :=
      Computable.unpair.comp Computable.snd
    have hn : Computable (fun p : ℕ × ℕ => p.1 + (Nat.unpair p.2).1 + 1) :=
      Primrec.nat_add.to_comp.comp
        (Primrec.nat_add.to_comp.comp Computable.fst (Computable.fst.comp hu)) (Computable.const 1)
    exact hg.comp ((Computable.fst.comp hu).pair (hn.pair (Computable.snd.comp hu)))
  · intro n x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcover k (n + k + 1) hk)
    exact Set.mem_iUnion.2 ⟨Nat.pair k i, by simpa [Nat.unpair_pair] using hi⟩
  · intro n
    rw [hsum n]
    calc ∑' k, ∑' i, coverMass π (g k (n + k + 1) i)
        ≤ ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + k + 1) := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          have := hbound k (n + k + 1)
          rwa [dyadicValue_one_eq_inv_two_pow'] at this
      _ = dyadicValue 1 n :=
          isBalanced_of_isSchnorrRandom_isSchnorrNull_of_isUniformlyEffectivelyNull_aux_geom n
  · refine ⟨fun p => ∑ k ∈ Finset.range (p.2 + 1), q (k, p.1 + k + 1, 2 * p.2 + 2),
      isBalanced_of_isSchnorrRandom_isSchnorrNull_of_isUniformlyEffectivelyNull_aux_comp q hq,
          ?_⟩
    intro n t
    simp only [hsum n]
    rw [ENNReal.tsum_toReal_eq (fun k => hfin k (n + k + 1))]
    refine isBalanced_of_isSchnorrRandom_isSchnorrNull_of_isUniformlyEffectivelyNull_aux_err n
        t
      (fun k => (∑' i, coverMass π (g k (n + k + 1) i)).toReal)
      (fun k => q (k, n + k + 1, 2 * t + 2)) (fun k => ENNReal.toReal_nonneg) ?_ ?_
    · intro k
      have h1 := ENNReal.toReal_mono (by
        rw [dyadicValue_one_eq_inv_two_pow']
        exact ENNReal.pow_ne_top (by simp)) (hbound k (n + k + 1))
      rw [dyadicValue_one_eq_inv_two_pow', ENNReal.toReal_pow] at h1
      simpa using h1
    · intro k _
      exact hqerr k (n + k + 1) (2 * t + 2)

private lemma isBalanced_of_isSchnorrRandom_g_sumRange (h : BitString → ℝ≥0∞) :
    ∀ L : List BitString, ∑ c ∈ Finset.range L.length, (L[c]?).elim 0 h = (L.map h).sum
  | [] => by simp
  | a :: L => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp [isBalanced_of_isSchnorrRandom_g_sumRange h L, add_comm]

private lemma isBalanced_of_isSchnorrRandom_g_primrecCount :
    Primrec (fun s : BitString => s.count true) := by
  have hstep : Primrec₂ (fun (_ : BitString) (bn : Bool × ℕ) =>
      bif bn.1 then bn.2 + 1 else bn.2) :=
    (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have heq : (fun s : BitString => s.count true)
      = fun s => s.foldr (fun b n => bif b then n + 1 else n) 0 := by
    funext s; induction s with
    | nil => rfl
    | cons b s ih => cases b <;> simp [ih]
  rw [heq]
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) hstep

private noncomputable def isBalanced_of_isSchnorrRandom_g_enum (k m i : ℕ) :
    Option BitString :=
  ((levelList (Kolmogorov.devThresh k m + i.unpair.1))[i.unpair.2]?).bind
    (fun x => bif Kolmogorov.devBool k (Kolmogorov.devThresh k m + i.unpair.1)
      (x.count true) then some x else none)

private lemma isBalanced_of_isSchnorrRandom_g_comp :
    Computable (fun p : ℕ × ℕ × ℕ => isBalanced_of_isSchnorrRandom_g_enum p.1 p.2.1 p.2.2) :=
        by
  have hk : Computable (fun p : ℕ × ℕ × ℕ => p.1) := Computable.fst
  have hm : Computable (fun p : ℕ × ℕ × ℕ => p.2.1) := Computable.fst.comp Computable.snd
  have hi : Computable (fun p : ℕ × ℕ × ℕ => p.2.2) := Computable.snd.comp Computable.snd
  have h1 : Computable (fun p : ℕ × ℕ × ℕ => p.2.2.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp.comp hi
  have h2 : Computable (fun p : ℕ × ℕ × ℕ => p.2.2.unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp hi
  have hT : Computable (fun p : ℕ × ℕ × ℕ => Kolmogorov.devThresh p.1 p.2.1) :=
    Kolmogorov.computable_devThresh hk hm
  have hn : Computable (fun p : ℕ × ℕ × ℕ => Kolmogorov.devThresh p.1 p.2.1 + p.2.2.unpair.1) :=
    Primrec.nat_add.to_comp.comp hT h1
  have hL : Computable (fun p : ℕ × ℕ × ℕ =>
      levelList (Kolmogorov.devThresh p.1 p.2.1 + p.2.2.unpair.1)) :=
    computable_levelList.comp hn
  have hget : Computable (fun p : ℕ × ℕ × ℕ =>
      (levelList (Kolmogorov.devThresh p.1 p.2.1 + p.2.2.unpair.1))[p.2.2.unpair.2]?) :=
    Computable.list_getElem?.comp hL h2
  refine Computable.option_bind hget ?_
  have hx : Computable (fun q : (ℕ × ℕ × ℕ) × BitString => q.2) := Computable.snd
  have hk' : Computable (fun q : (ℕ × ℕ × ℕ) × BitString => q.1.1) :=
    Computable.fst.comp Computable.fst
  have hn' : Computable (fun q : (ℕ × ℕ × ℕ) × BitString =>
      Kolmogorov.devThresh q.1.1 q.1.2.1 + q.1.2.2.unpair.1) := hn.comp Computable.fst
  have hc : Computable (fun q : (ℕ × ℕ × ℕ) × BitString => q.2.count true) :=
    (isBalanced_of_isSchnorrRandom_g_primrecCount.comp Primrec.snd).to_comp
  exact Kolmogorov.Computable.cond_some_none (Kolmogorov.computable_devBool hk' hn' hc) hx

private lemma isBalanced_of_isSchnorrRandom_g_measure (k n : ℕ) :
    uniformMeasure (Kolmogorov.devSet k n) = ∑ x ∈ levelFinset n,
      (if Kolmogorov.devBool k n (x.count true) = true then (1 : ℝ≥0∞) else 0)
        * cantorMass uniformMeasure x := by
  classical
  set f : BitString → ℝ≥0∞ :=
    fun x => if Kolmogorov.devBool k n (x.count true) = true then 1 else 0 with hf
  have hmeas : MeasurableSet (Kolmogorov.devSet k n) := by
    have : Kolmogorov.devSet k n = (fun w => f (cantorPrefix w n)) ⁻¹' {1} := by
      ext w
      simp [Kolmogorov.devSet, hf]
    rw [this]
    exact measurable_comp_cantorPrefix n f (measurableSet_singleton 1)
  rw [← lintegral_indicator_one hmeas]
  have : (Kolmogorov.devSet k n).indicator (1 : CantorSeq → ℝ≥0∞)
      = fun w => f (cantorPrefix w n) := by
    ext w
    by_cases h : w ∈ Kolmogorov.devSet k n
    · have h' : Kolmogorov.devBool k n ((cantorPrefix w n).count true) = true := h
      simp [Set.indicator_of_mem h, hf, h']
    · have h' : ¬ Kolmogorov.devBool k n ((cantorPrefix w n).count true) = true := h
      simp [Set.indicator_of_notMem h, hf, h']
  rw [this, lintegral_comp_cantorPrefix]

private lemma isBalanced_of_isSchnorrRandom_g_inner (k m j : ℕ) :
    ∑' c, coverMass uniformMeasure (isBalanced_of_isSchnorrRandom_g_enum k m (Nat.pair j c))
      = uniformMeasure (Kolmogorov.devSet k (Kolmogorov.devThresh k m + j)) := by
  classical
  set n := Kolmogorov.devThresh k m + j with hn
  set h : BitString → ℝ≥0∞ := fun x =>
    if Kolmogorov.devBool k n (x.count true) = true then cantorMass uniformMeasure x else 0
    with hh
  have hc : ∀ c, coverMass uniformMeasure
      (isBalanced_of_isSchnorrRandom_g_enum k m (Nat.pair j c))
      = ((levelList n)[c]?).elim 0 h := by
    intro c
    rw [isBalanced_of_isSchnorrRandom_g_enum, Nat.unpair_pair]
    simp only [← hn]
    rcases hx : (levelList n)[c]? with _ | x
    · simp [coverMass]
    · by_cases hd : Kolmogorov.devBool k n (x.count true) = true
      · simp [coverMass, hh, hd]
      · simp [coverMass, hh, hd]
  simp_rw [hc]
  rw [tsum_eq_sum (s := Finset.range (levelList n).length)]
  · rw [isBalanced_of_isSchnorrRandom_g_sumRange, ← sum_levelFinset_eq_sum_levelList,
      isBalanced_of_isSchnorrRandom_g_measure]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hd : Kolmogorov.devBool k n (x.count true) = true <;> simp [hh, hd]
  · intro c hc'
    have : (levelList n)[c]? = none := by
      rw [List.getElem?_eq_none_iff]
      simpa using hc'
    simp [this]

private lemma isBalanced_of_isSchnorrRandom_g_sum (k m : ℕ) :
    ∑' i, coverMass uniformMeasure (isBalanced_of_isSchnorrRandom_g_enum k m i)
      = ∑' j, uniformMeasure (Kolmogorov.devSet k (Kolmogorov.devThresh k m + j)) := by
  rw [← Nat.pairEquiv.tsum_eq]
  have : ∀ p : ℕ × ℕ, coverMass uniformMeasure
      (isBalanced_of_isSchnorrRandom_g_enum k m (Nat.pairEquiv p))
      = coverMass uniformMeasure
        (isBalanced_of_isSchnorrRandom_g_enum k m (Nat.pair p.1 p.2)) := fun p => rfl
  simp_rw [this]
  rw [ENNReal.tsum_prod (f := fun a b => coverMass uniformMeasure
    (isBalanced_of_isSchnorrRandom_g_enum k m (Nat.pair a b)))]
  exact tsum_congr fun j => isBalanced_of_isSchnorrRandom_g_inner k m j

private lemma isBalanced_of_isSchnorrRandom_g_cover (k m : ℕ) :
    Kolmogorov.devInfSet k ⊆ ⋃ i, (isBalanced_of_isSchnorrRandom_g_enum k m i).elim ∅
      cantorCylinder := by
  intro x hx
  obtain ⟨n, hn, hxn⟩ := hx (Kolmogorov.devThresh k m)
  have hdev : Kolmogorov.devBool k n ((cantorPrefix x n).count true) = true := hxn
  have hmem : cantorPrefix x n ∈ levelList n := mem_levelList.2 (cantorPrefix_length x n)
  obtain ⟨c, hc⟩ := List.mem_iff_getElem?.1 hmem
  refine Set.mem_iUnion.2 ⟨Nat.pair (n - Kolmogorov.devThresh k m) c, ?_⟩
  have hsum : Kolmogorov.devThresh k m + (n - Kolmogorov.devThresh k m) = n := by omega
  rw [isBalanced_of_isSchnorrRandom_g_enum, Nat.unpair_pair]
  simp only [hsum, hc, Option.bind_some, hdev, Bool.cond_true, Option.elim_some]
  exact mem_cantorCylinder_cantorPrefix x n

/-- Step 2 of the proof of `isBalanced_of_isSchnorrRandom`: computable enumeration g. -/
private theorem isBalanced_of_isSchnorrRandom_g :
    ∃ g : ℕ → ℕ → ℕ → Option BitString, Computable (fun p : ℕ × ℕ × ℕ => g p.1 p.2.1 p.2.2) ∧
    (∀ k m, Kolmogorov.devInfSet k ⊆ ⋃ i, (g k m i).elim ∅ cantorCylinder) ∧
    ∀ k m, ∑' i, coverMass uniformMeasure (g k m i) = ∑' j, uniformMeasure (Kolmogorov.devSet k
        (Kolmogorov.devThresh k m + j)) :=
  ⟨isBalanced_of_isSchnorrRandom_g_enum, isBalanced_of_isSchnorrRandom_g_comp,
    isBalanced_of_isSchnorrRandom_g_cover, isBalanced_of_isSchnorrRandom_g_sum⟩

/-- Step 3 of the proof of `isBalanced_of_isSchnorrRandom`: measure tail bound. -/
private theorem isBalanced_of_isSchnorrRandom_bound :
    ∀ k m, ∑' j, uniformMeasure (Kolmogorov.devSet k (Kolmogorov.devThresh k m + j)) ≤ dyadicValue 1
        m := by
  intro k m
  set T := Kolmogorov.devThresh k m with hTdef
  have hterm : ∀ j : ℕ, uniformMeasure (Kolmogorov.devSet k (T + j))
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2)) := by
    intro j
    have h := Kolmogorov.measure_devSet_le k (T + j)
    push_cast at h
    exact h
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  have hnonneg : ∀ j : ℕ,
      (0 : ℝ) ≤ 2 * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2) := by
    intro j; positivity
  have hsum := (ENNReal.ofReal_tsum_of_nonneg hnonneg (Kolmogorov.expTail_summable k T)).symm
  rw [hsum]
  have hT : (T : ℝ) = ((k : ℝ) + 1) ^ 2 * ((m : ℝ) + 2 * k + 4) := by
    rw [hTdef, Kolmogorov.devThresh]; push_cast; ring
  have hb := Kolmogorov.expTail_le k m T hT
  refine (ENNReal.ofReal_le_ofReal hb).trans ?_
  rw [dyadicValue_one_eq_inv_two_pow']
  rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- Count of the length-`n` strings passing the level-`k` deviation test. -/
private def isBalanced_of_isSchnorrRandom_q_cnt (k n : ℕ) : ℕ :=
  ((levelList n).map fun x => if devBool k n (x.count true) then 1 else 0).sum

private lemma isBalanced_of_isSchnorrRandom_q_measure (k n : ℕ) :
    uniformMeasure (Kolmogorov.devSet k n)
      = (isBalanced_of_isSchnorrRandom_q_cnt k n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n := by
  classical
  set F : BitString → ℝ≥0∞ := fun x => if devBool k n (x.count true) then 1 else 0 with hF
  have hmeas : MeasurableSet (Kolmogorov.devSet k n) := by
    have h := measurable_comp_cantorPrefix n F (measurableSet_singleton (1 : ℝ≥0∞))
    have : (fun w => F (cantorPrefix w n)) ⁻¹' {1} = Kolmogorov.devSet k n := by
      ext w
      simp [hF, Kolmogorov.devSet]
    rwa [this] at h
  have h1 : uniformMeasure (Kolmogorov.devSet k n) = ∫⁻ w, F (cantorPrefix w n) ∂uniformMeasure :=
      by
    rw [← lintegral_indicator_one hmeas]
    refine lintegral_congr fun w => ?_
    by_cases hw : w ∈ Kolmogorov.devSet k n
    · have : devBool k n ((cantorPrefix w n).count true) = true := hw
      simp [hF, Set.indicator_of_mem hw, this]
    · have : devBool k n ((cantorPrefix w n).count true) ≠ true := hw
      simp only [ne_eq, Bool.not_eq_true] at this
      simp [hF, Set.indicator_of_notMem hw, this]
  rw [h1, lintegral_comp_cantorPrefix]
  have h2 : ∀ x ∈ levelFinset n, F x * cantorMass uniformMeasure x = F x * (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro x hx
    rw [cantorMass_uniformMeasure, mem_levelFinset.1 hx]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul, sum_levelFinset_eq_sum_levelList]
  congr 1
  unfold isBalanced_of_isSchnorrRandom_q_cnt
  rw [Nat.cast_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp, hF]
  split_ifs <;> simp

private lemma isBalanced_of_isSchnorrRandom_q_computable_count :
    Computable (fun x : BitString => x.count true) := by
  have h := Kolmogorov.list_countP_primrec
      (f := fun l : BitString => l)
      (p := fun l z => decide (z = true))
      Primrec.id
      (Primrec.eq.decide.comp Primrec.snd (Primrec.const true))
  exact h.to_comp.of_eq (fun y => by simp [List.count_eq_countP, beq_eq_decide])

private lemma isBalanced_of_isSchnorrRandom_q_computable_cnt :
    Computable (fun p : ℕ × ℕ => isBalanced_of_isSchnorrRandom_q_cnt p.1 p.2) := by
  have hL : Computable (fun p : ℕ × ℕ => levelList p.2) :=
    computable_levelList.comp Computable.snd
  have hf : Computable₂ (fun (p : ℕ × ℕ) (x : BitString) =>
      if devBool p.1 p.2 (x.count true) then 1 else 0) := by
    have hd : Computable (fun q : (ℕ × ℕ) × BitString =>
        devBool q.1.1 q.1.2 (q.2.count true)) :=
      computable_devBool (Computable.fst.comp Computable.fst)
        (Computable.snd.comp Computable.fst)
        (isBalanced_of_isSchnorrRandom_q_computable_count.comp Computable.snd)
    refine (Computable.cond hd (Computable.const 1) (Computable.const 0)).of_eq
      fun q => ?_
    dsimp only
    cases h : devBool q.1.1 q.1.2 (q.2.count true) <;> simp
  exact computable_list_sum_map hL hf

/-- The tail of the Hoeffding series starting at `devThresh k m` is at most `2^{-m}`. -/
private lemma isBalanced_of_isSchnorrRandom_q_tail (k m : ℕ) :
    ∑' j : ℕ, uniformMeasure (Kolmogorov.devSet k (Kolmogorov.devThresh k m + j))
      ≤ dyadicValue 1 m := by
  set T := Kolmogorov.devThresh k m with hTdef
  have hterm : ∀ j : ℕ, uniformMeasure (Kolmogorov.devSet k (T + j))
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2)) := by
    intro j
    have h := Kolmogorov.measure_devSet_le k (T + j)
    push_cast at h
    exact h
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  have hnonneg : ∀ j : ℕ,
      (0 : ℝ) ≤ 2 * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2) := by
    intro j; positivity
  have hsum := (ENNReal.ofReal_tsum_of_nonneg hnonneg (Kolmogorov.expTail_summable k T)).symm
  rw [hsum]
  have hT : (T : ℝ) = ((k : ℝ) + 1) ^ 2 * ((m : ℝ) + 2 * k + 4) := by
    rw [hTdef, Kolmogorov.devThresh]; push_cast; ring
  have hb := Kolmogorov.expTail_le k m T hT
  refine (ENNReal.ofReal_le_ofReal hb).trans ?_
  rw [Kolmogorov.dyadicValue_one_eq_inv_two_pow']
  rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

private lemma isBalanced_of_isSchnorrRandom_q_list_range_sum (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ];
                   simp

/-- Number of terms of the finite part of the series. -/
private def isBalanced_of_isSchnorrRandom_q_L (z : ℕ × ℕ × ℕ) : ℕ :=
  Kolmogorov.devThresh z.1 (max z.2.1 z.2.2) - Kolmogorov.devThresh z.1 z.2.1

/-- Numerator of the rational approximation. -/
private def isBalanced_of_isSchnorrRandom_q_N (z : ℕ × ℕ × ℕ) : ℕ :=
  ((List.range (isBalanced_of_isSchnorrRandom_q_L z)).map fun i =>
    isBalanced_of_isSchnorrRandom_q_cnt z.1 (Kolmogorov.devThresh z.1 z.2.1 + i)
      * 2 ^ (isBalanced_of_isSchnorrRandom_q_L z - i)).sum

/-- The rational approximation. -/
private def isBalanced_of_isSchnorrRandom_q_q (z : ℕ × ℕ × ℕ) : ℚ :=
  (isBalanced_of_isSchnorrRandom_q_N z : ℚ)
    / 2 ^ Kolmogorov.devThresh z.1 (max z.2.1 z.2.2)

private lemma isBalanced_of_isSchnorrRandom_q_computable_q :
    Computable isBalanced_of_isSchnorrRandom_q_q := by
  have hk : Computable (fun z : ℕ × ℕ × ℕ => z.1) := Computable.fst
  have hm : Computable (fun z : ℕ × ℕ × ℕ => z.2.1) := Computable.fst.comp Computable.snd
  have hs : Computable (fun z : ℕ × ℕ × ℕ => z.2.2) := Computable.snd.comp Computable.snd
  have hJ : Computable (fun z : ℕ × ℕ × ℕ => max z.2.1 z.2.2) :=
    Primrec.nat_max.to_comp.comp hm hs
  have hT0 : Computable (fun z : ℕ × ℕ × ℕ => Kolmogorov.devThresh z.1 z.2.1) :=
    Kolmogorov.computable_devThresh hk hm
  have hTJ : Computable (fun z : ℕ × ℕ × ℕ => Kolmogorov.devThresh z.1 (max z.2.1 z.2.2)) :=
    Kolmogorov.computable_devThresh hk hJ
  have hL : Computable isBalanced_of_isSchnorrRandom_q_L :=
    Primrec.nat_sub.to_comp.comp hTJ hT0
  have hlist : Computable (fun z : ℕ × ℕ × ℕ =>
      List.range (isBalanced_of_isSchnorrRandom_q_L z)) :=
    Primrec.list_range.to_comp.comp hL
  have hf : Computable₂ (fun (z : ℕ × ℕ × ℕ) (i : ℕ) =>
      isBalanced_of_isSchnorrRandom_q_cnt z.1 (Kolmogorov.devThresh z.1 z.2.1 + i)
        * 2 ^ (isBalanced_of_isSchnorrRandom_q_L z - i)) := by
    have hk' : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ => p.1.1) :=
      Computable.fst.comp Computable.fst
    have hT0' : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ => Kolmogorov.devThresh p.1.1 p.1.2.1) :=
      Computable.comp (f := fun z : ℕ × ℕ × ℕ => Kolmogorov.devThresh z.1 z.2.1)
        (g := fun p : (ℕ × ℕ × ℕ) × ℕ => p.1) hT0 Computable.fst
    have hidx : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ =>
        Kolmogorov.devThresh p.1.1 p.1.2.1 + p.2) :=
      Primrec.nat_add.to_comp.comp hT0' Computable.snd
    have hpr : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ =>
        (p.1.1, Kolmogorov.devThresh p.1.1 p.1.2.1 + p.2)) :=
      Computable.pair hk' hidx
    have hcnt : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ =>
        isBalanced_of_isSchnorrRandom_q_cnt p.1.1
          (Kolmogorov.devThresh p.1.1 p.1.2.1 + p.2)) :=
      Computable.comp
        (f := fun p : ℕ × ℕ => isBalanced_of_isSchnorrRandom_q_cnt p.1 p.2)
        (g := fun p : (ℕ × ℕ × ℕ) × ℕ => (p.1.1, Kolmogorov.devThresh p.1.1 p.1.2.1 + p.2))
        isBalanced_of_isSchnorrRandom_q_computable_cnt hpr
    have hpow : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ =>
        2 ^ (isBalanced_of_isSchnorrRandom_q_L p.1 - p.2)) :=
      Computable.pow2.comp
        (Primrec.nat_sub.to_comp.comp (hL.comp Computable.fst) Computable.snd)
    exact Primrec.nat_mul.to_comp.comp hcnt hpow
  have hN : Computable isBalanced_of_isSchnorrRandom_q_N :=
    computable_list_sum_map hlist hf
  refine computable_of_num_den (N := fun z => ((isBalanced_of_isSchnorrRandom_q_N z : ℕ) : ℤ))
    (D := fun z => 2 ^ Kolmogorov.devThresh z.1 (max z.2.1 z.2.2))
    (ComputableReals.primrec_natCastInt.to_comp.comp hN)
    (Computable.pow2.comp hTJ) (fun z => by positivity) (fun z => ?_)
  simp [isBalanced_of_isSchnorrRandom_q_q]

private lemma isBalanced_of_isSchnorrRandom_q_err (k m s : ℕ) :
    |(isBalanced_of_isSchnorrRandom_q_q (k, m, s) : ℝ)
      - (∑' j, uniformMeasure (Kolmogorov.devSet k (Kolmogorov.devThresh k m + j))).toReal|
      ≤ (2 : ℝ)⁻¹ ^ s := by
  set J := max m s with hJ
  set T := Kolmogorov.devThresh k m with hT
  set TJ := Kolmogorov.devThresh k J with hTJ
  have hmJ : m ≤ J := le_max_left _ _
  have hsJ : s ≤ J := le_max_right _ _
  have hTle : T ≤ TJ := by
    rw [hT, hTJ]; unfold Kolmogorov.devThresh
    exact Nat.mul_le_mul_left _ (by omega)
  set L := TJ - T with hL
  have hTL : T + L = TJ := by omega
  have hLdef : isBalanced_of_isSchnorrRandom_q_L (k, m, s) = L := rfl
  set a : ℕ → ℝ≥0∞ := fun n => uniformMeasure (Kolmogorov.devSet k n) with ha
  have hane : ∀ n, a n ≠ ⊤ := fun n => by
    rw [ha]; dsimp only
    rw [isBalanced_of_isSchnorrRandom_q_measure]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero))
  have hareal : ∀ n, (a n).toReal
      = (isBalanced_of_isSchnorrRandom_q_cnt k n : ℝ) * (2 : ℝ)⁻¹ ^ n := by
    intro n
    rw [ha]; dsimp only
    rw [isBalanced_of_isSchnorrRandom_q_measure, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_inv]
    simp
  -- split the series
  have hsplit : ∑' j, a (T + j) = ∑ i ∈ Finset.range L, a (T + i) + ∑' j, a (TJ + j) := by
    have h : (∑ i ∈ Finset.range L, a (T + i)) + ∑' i, a (T + (i + L)) = ∑' i, a (T + i) :=
      Summable.sum_add_tsum_nat_add' (f := fun j => a (T + j)) (k := L) ENNReal.summable
    rw [← h]
    congr 1
    refine tsum_congr fun j => ?_
    congr 1
    omega
  have htail : ∑' j, a (TJ + j) ≤ dyadicValue 1 J :=
    isBalanced_of_isSchnorrRandom_q_tail k J
  have hdne : dyadicValue 1 J ≠ ⊤ := by
    rw [dyadicValue]
    exact ENNReal.div_ne_top (by simp) (pow_ne_zero _ (by norm_num))
  have htne : ∑' j, a (TJ + j) ≠ ⊤ := ne_top_of_le_ne_top hdne htail
  have hsne : ∑ i ∈ Finset.range L, a (T + i) ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun i _ => (hane _).lt_top).ne
  have hσ : (∑' j, uniformMeasure (Kolmogorov.devSet k (T + j))).toReal
      = ∑ i ∈ Finset.range L, (isBalanced_of_isSchnorrRandom_q_cnt k (T + i) : ℝ)
          * (2 : ℝ)⁻¹ ^ (T + i) + (∑' j, a (TJ + j)).toReal := by
    have : (∑' j, uniformMeasure (Kolmogorov.devSet k (T + j))) = ∑' j, a (T + j) := rfl
    rw [this, hsplit, ENNReal.toReal_add hsne htne, ENNReal.toReal_sum (fun i _ => hane _)]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hareal _
  have hq : (isBalanced_of_isSchnorrRandom_q_q (k, m, s) : ℝ)
      = ∑ i ∈ Finset.range L, (isBalanced_of_isSchnorrRandom_q_cnt k (T + i) : ℝ)
          * (2 : ℝ)⁻¹ ^ (T + i) := by
    have hNsum : isBalanced_of_isSchnorrRandom_q_N (k, m, s)
        = ∑ i ∈ Finset.range L,
            isBalanced_of_isSchnorrRandom_q_cnt k (T + i) * 2 ^ (L - i) := by
      unfold isBalanced_of_isSchnorrRandom_q_N
      rw [hLdef]
      exact isBalanced_of_isSchnorrRandom_q_list_range_sum _ _
    unfold isBalanced_of_isSchnorrRandom_q_q
    rw [hNsum]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < L := Finset.mem_range.1 hi
    have hpow : (2 : ℝ) ^ TJ = 2 ^ (T + i) * 2 ^ (L - i) := by
      rw [← pow_add]; congr 1; omega
    rw [inv_pow, hpow]
    field_simp
  rw [hσ, hq, sub_add_cancel_left, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg]
  have hle : (∑' j, a (TJ + j)).toReal ≤ (dyadicValue 1 J).toReal :=
    ENNReal.toReal_mono hdne htail
  have hdv : (dyadicValue 1 J).toReal = (2 : ℝ)⁻¹ ^ J := by
    rw [dyadicValue, ENNReal.toReal_div]
    simp
  rw [hdv] at hle
  exact hle.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hsJ)

/-- Step 4 of the proof of `isBalanced_of_isSchnorrRandom`: computable real q. -/
private theorem isBalanced_of_isSchnorrRandom_q :
    ∃ q : ℕ × ℕ × ℕ → ℚ, Computable q ∧ ∀ k m s, |(q (k, m, s) : ℝ) -
        (∑' j, uniformMeasure (Kolmogorov.devSet k (Kolmogorov.devThresh k m + j))).toReal| ≤
        (2 : ℝ)⁻¹ ^ s := by
  exact ⟨isBalanced_of_isSchnorrRandom_q_q,
    isBalanced_of_isSchnorrRandom_q_computable_q,
    isBalanced_of_isSchnorrRandom_q_err⟩

/-- **SUV Problem 92 of Section 3.4, cited on p. 310.**  Schnorr random sequences satisfy the Strong
Law of Large Numbers. -/
theorem isBalanced_of_isSchnorrRandom {w : CantorSeq} (hw : IsSchnorrRandom uniformMeasure w) :
    IsBalanced w := by
  have hw_not_null : ¬ IsSchnorrNull uniformMeasure {w} := hw
  by_contra h_not_bal
  have h_not_tendsto : ¬Tendsto (fun n => (freqOne w n : ℝ)) atTop (𝓝 (1 / 2)) := h_not_bal
  have h_not_tendsto_rat : ¬Tendsto (fun n => freqOne w n) atTop (𝓝 (1 / 2 : ℚ)) := by
    intro h
    have h2 : Tendsto (fun n => (freqOne w n : ℝ)) atTop (𝓝 (1 / 2)) := by
      have h3 : (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by norm_num
      rw [h3]
      have hcast : (fun n => (freqOne w n : ℝ)) = fun n => ((freqOne w n : ℚ) : ℝ) := by
        ext n
        rfl
      rw [hcast]
      exact Filter.Tendsto.comp (continuous_algebraMap ℚ ℝ).continuousAt h
    exact h_not_tendsto h2
  have h_in_union : w ∈ ⋃ k, Kolmogorov.devInfSet k := Kolmogorov.notTendsto_subset_iUnion_devInfSet
      h_not_tendsto_rat
  have h_null : IsSchnorrNull uniformMeasure (⋃ k, Kolmogorov.devInfSet k) := by
    rcases isBalanced_of_isSchnorrRandom_g with ⟨g, hg_comp, hg_sub, hg_sum⟩
    rcases isBalanced_of_isSchnorrRandom_q with ⟨q, hq_comp, hq_real⟩
    apply isBalanced_of_schnorrNull_union uniformMeasure
        Kolmogorov.devInfSet g hg_comp hg_sub
    · intro k m
      rw [hg_sum k m]
      exact isBalanced_of_isSchnorrRandom_bound k m
    · use q, hq_comp
      intro k m s
      rw [hg_sum k m]
      exact hq_real k m s
  have h_w_null : IsSchnorrNull uniformMeasure {w} := by
    rcases h_null with ⟨f, hcomp, hsub, hsum, hcomp_real⟩
    use f, hcomp
    constructor
    · intro n
      have hs : {w} ⊆ ⋃ k, Kolmogorov.devInfSet k := Set.singleton_subset_iff.mpr h_in_union
      exact Set.Subset.trans hs (hsub n)
    · exact ⟨hsum, hcomp_real⟩
  exact hw_not_null h_w_null

/-- A Martin-Löf random sequence is Schnorr random: a Schnorr effectively null set is effectively
null. -/
theorem isSchnorrRandom_of_isMartinLofRandom {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {w : CantorSeq} (hw : IsMartinLofRandom π w) : IsSchnorrRandom π w := by
  intro hschnorr
  rcases hschnorr with ⟨f, hcomp, hcover, hbound, hcomp_real⟩
  have heff : IsEffectivelyNull π {w} := by
    use fun n => ⋃ i, (f n i).elim ∅ cantorCylinder
    refine ⟨⟨f, hcomp, fun n => rfl⟩, ?_, ?_⟩
    · intro w' hw'
      rw [Set.mem_iInter]
      intro n
      exact hcover n hw'
    · intro n
      calc
        π (⋃ i, (f n i).elim ∅ cantorCylinder) ≤ ∑' i, π ((f n i).elim ∅ cantorCylinder) :=
            measure_iUnion_le _
        _ = ∑' i, coverMass π (f n i) := by
          apply tsum_congr
          intro i
          cases (f n i)
          · exact measure_empty
          · rfl
        _ ≤ dyadicValue 1 n := hbound n
  unfold IsMartinLofRandom at hw
  rcases heff with ⟨U, hU1, hU2, hU3⟩
  exact hw U ⟨hU1, hU3⟩ (hU2 (Set.mem_singleton w))

end Kolmogorov.FrequencyGames
