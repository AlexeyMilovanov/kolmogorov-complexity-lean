/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz.SchnorrSeries

/-!
# Growth Martingales

Direction "not Schnorr random implies a computable growth-rate martingale win" of the
characterization of Schnorr randomness by computable martingales with a computable growth
rate (Shen–Uspensky–Vereshchagin).  From a computable series witness of non-randomness, the
module groups the cylinders into finite same-length covers of small measure, builds from each
cover a computable fair capital that multiplies by `4 ^ k` on the cover, mixes these capitals
with weights `2⁻ᵏ` into one computable fair capital, and combines it with a computable
strictly increasing growth function so that the mixture exceeds the growth function along
infinitely many prefixes of the non-random sequence.  The main declarations are
`not_isSchnorrRandom_iff_exists_growth_group_and_extend` (grouping of the witness into
covers) and `not_isSchnorrRandom_iff_exists_growth_ltr` (the final implication); the
remaining declarations are its private steps.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped ENNReal

/-- Step 1 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`: extract
precisely the series witness used by the construction. -/
private theorem not_isSchnorrRandom_iff_exists_growth_extract_witness
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (w : CantorSeq) :
    ¬ IsSchnorrRandom π w →
      ∃ x : ℕ → BitString, Computable x ∧
        ∃ N : ℕ → ℕ, Computable N ∧
          (∀ k, ∑' i, cantorMass π (x (N k + i)) ≤ dyadicValue 1 k) ∧
          ∃ᶠ i in atTop, IsCantorPrefix (x i) w := by
  intro hw
  have h1 := not_isSchnorrRandom_iff_exists_series_mp hπ w hw
  obtain ⟨x, hx_comp, ⟨N, hN_comp, hTail⟩, hHit⟩ := h1
  exact ⟨x, hx_comp, N, hN_comp, hTail, hHit⟩

/-- Step 2 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`:
every computable natural-valued function has a computable strictly increasing majorant. -/
private theorem not_isSchnorrRandom_iff_exists_growth_majorant
    (f : ℕ → ℕ) (hf : Computable f) :
    ∃ F : ℕ → ℕ, Computable F ∧ StrictMono F ∧ ∀ k, f k ≤ F k := by
  let F : ℕ → ℕ := fun n => Nat.rec (f 0) (fun k r => max (f (k + 1)) (r + 1)) n
  have hrec : ∀ n, F (n + 1) = max (f (n + 1)) (F n + 1) := fun _ => rfl
  refine ⟨F, ?_, ?_, ?_⟩
  · have hstep : Computable₂ (fun (_ : ℕ) (r : ℕ × ℕ) => max (f (r.1 + 1)) (r.2 + 1)) :=
      Primrec.nat_max.to_comp.comp
        (hf.comp (Computable.succ.comp (Computable.fst.comp Computable.snd)))
        (Computable.succ.comp (Computable.snd.comp Computable.snd))
    exact (Computable.nat_rec Computable.id (Computable.const (f 0)) hstep).of_eq
      (fun _ => rfl)
  · apply strictMono_nat_of_lt_succ
    intro n
    rw [hrec]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  · intro k
    cases k with
    | zero => exact le_rfl
    | succ k => rw [hrec]; exact le_max_left _ _

/-- Step 2 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`:
a duplicate-free list of strings on one level has disjoint cylinders, so its sum of masses is
the measure of its union. -/
private theorem not_isSchnorrRandom_iff_exists_growth_cover_mass
    (π : Measure CantorSeq) (S : List BitString) (hnodup : S.Nodup)
    (L : ℕ) (hlen : ∀ y ∈ S, y.length = L) :
    π (⋃ y ∈ S, cantorCylinder y) = (S.map (cantorMass π)).sum := by
  classical
  have heq : (⋃ y ∈ S, cantorCylinder y) = ⋃ y ∈ S.toFinset, cantorCylinder y := by
    simp
  have hd : (↑S.toFinset : Set BitString).PairwiseDisjoint cantorCylinder := by
    intro y hy z hz hne
    have hy' : y ∈ S := List.mem_toFinset.mp hy
    have hz' : z ∈ S := List.mem_toFinset.mp hz
    exact cantorCylinder_disjoint_of_incompatible
      (fun h => hne (h.eq_of_length ((hlen y hy').trans (hlen z hz').symm)))
      (fun h => hne (h.eq_of_length ((hlen z hz').trans (hlen y hy').symm)).symm)
  rw [heq, measure_biUnion_finset hd (fun y _ => measurableSet_cantorCylinder y),
    List.sum_toFinset _ hnodup]
  rfl

/-- Step 2 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`: group that
witness and extend to a common, strictly increasing length. -/
theorem not_isSchnorrRandom_iff_exists_growth_group_and_extend
    {π : Measure CantorSeq} [IsProbabilityMeasure π] (w : CantorSeq)
    (x : ℕ → BitString) (hx : Computable x)
    (N : ℕ → ℕ) (hN : Computable N)
    (hTail : ∀ k, ∑' i, cantorMass π (x (N k + i)) ≤ dyadicValue 1 k)
    (hHit : ∃ᶠ i in atTop, IsCantorPrefix (x i) w) :
    ∃ ℓ : ℕ → ℕ, Computable ℓ ∧ StrictMono ℓ ∧
    ∃ S : ℕ → List BitString, Computable S ∧
      (∀ k, (S k).Pairwise (· ≠ ·) ∧ (∀ y ∈ S k, y.length = ℓ k) ∧
        ((S k).map (cantorMass π)).sum ≤ dyadicValue 1 (2*k)) ∧
      ∃ᶠ k in atTop, cantorPrefix w (ℓ k) ∈ S k := by
  obtain ⟨B, hBc, hBmono, hBbound⟩ :=
    not_isSchnorrRandom_iff_exists_growth_majorant
      (fun k => N (2 * k)) (hN.comp (Primrec.nat_mul.to_comp.comp (Computable.const 2)
          Computable.id))
  obtain ⟨L, hLc, hLmono, hLbound⟩ :=
    not_isSchnorrRandom_iff_exists_growth_majorant
      (fun i => (x i).length) (Computable.list_length.comp hx)
  let ℓ : ℕ → ℕ := fun k => L (B (k + 1))
  have hℓc : Computable ℓ := hLc.comp (hBc.comp Computable.succ)
  have hℓmono : StrictMono ℓ := fun _ _ h => hLmono (hBmono (Nat.add_lt_add_right h 1))
  let P : ℕ → BitString → Bool := fun k y =>
    (List.range (B (k + 1) - B k)).any fun j => decide (x (B k + j) <+: y)
  have hPc : Computable₂ P := by
    have hgap : Computable fun p : ℕ × BitString => B (p.1 + 1) - B p.1 :=
      Primrec.nat_sub.to_comp.comp (hBc.comp (Computable.succ.comp Computable.fst))
        (hBc.comp Computable.fst)
    have hargs : Computable fun z : (ℕ × BitString) × ℕ => (x (B z.1.1 + z.2), z.1.2) :=
      (hx.comp (Primrec.nat_add.to_comp.comp
        (hBc.comp (Computable.fst.comp Computable.fst)) Computable.snd)).pair
        (Computable.snd.comp Computable.fst)
    have hpred := decide_prefix_primrec.to_comp.comp hargs
    exact computable_list_any (Primrec.list_range.to_comp.comp hgap) hpred
  let S : ℕ → List BitString := fun k => (levelList (ℓ k)).filter (P k)
  have hSc : Computable S := computable_list_filter (computable_levelList.comp hℓc) hPc
  have hmem : ∀ k y, y ∈ S k ↔ y.length = ℓ k ∧
      ∃ j, j < B (k + 1) - B k ∧ x (B k + j) <+: y := by
    intro k y
    simp [S, P, mem_levelList]
  have hSn : ∀ k, (S k).Nodup := fun k => (nodup_levelList _).filter _
  have hSlen : ∀ k, ∀ y ∈ S k, y.length = ℓ k := fun k y hy => (hmem k y).mp hy |>.1
  refine ⟨ℓ, hℓc, hℓmono, S, hSc, ?_, ?_⟩
  · intro k
    refine ⟨hSn k, hSlen k, ?_⟩
    rw [← not_isSchnorrRandom_iff_exists_growth_cover_mass
      π (S k) (hSn k) (ℓ k) (hSlen k)]
    have hsub : (⋃ y ∈ S k, cantorCylinder y) ⊆
        ⋃ j ∈ Finset.range (B (k + 1) - B k), cantorCylinder (x (B k + j)) := by
      intro v hv
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hv
      obtain ⟨hyS, hyv⟩ := Set.mem_iUnion.mp hy
      obtain ⟨j, hj, hpre⟩ := ((hmem k y).mp hyS).2
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
        ⟨Finset.mem_range.mpr hj, cantorCylinder_subset_of_prefix hpre hyv⟩⟩
    have htail : ∑' i, cantorMass π (x (B k + i)) ≤ dyadicValue 1 (2 * k) := by
      have hle := hBbound k
      calc _ = ∑' i, cantorMass π (x (N (2 * k) + (B k - N (2 * k) + i))) := by
              apply tsum_congr
              intro i
              congr 2
              omega
        _ ≤ ∑' i, cantorMass π (x (N (2 * k) + i)) :=
          ENNReal.tsum_comp_le_tsum_of_injective
            (f := fun i => B k - N (2 * k) + i) (fun _ _ h => Nat.add_left_cancel h)
            (fun i => cantorMass π (x (N (2 * k) + i)))
        _ ≤ _ := hTail (2 * k)
    calc _ ≤ π (⋃ j ∈ Finset.range (B (k + 1) - B k), cantorCylinder (x (B k + j))) :=
          measure_mono hsub
      _ ≤ ∑ j ∈ Finset.range (B (k + 1) - B k), cantorMass π (x (B k + j)) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑' i, cantorMass π (x (B k + i)) := ENNReal.sum_le_tsum _
      _ ≤ _ := htail
  · apply Filter.frequently_atTop.mpr
    intro K
    obtain ⟨i, hi, hxi⟩ := Filter.frequently_atTop.mp hHit (B K)
    have hex : ∃ j, i < B (j + 1) :=
      ⟨i, lt_of_lt_of_le (Nat.lt_succ_self i) (hBmono.id_le _)⟩
    let k := Nat.find hex
    have hupper : i < B (k + 1) := Nat.find_spec hex
    have hK : K ≤ k := by
      by_contra h
      have hle : k + 1 ≤ K := by omega
      have := hBmono.monotone hle
      omega
    have hlower : B k ≤ i := by
      by_cases hk : k = 0
      · rw [hk]
        exact (hBmono.monotone (Nat.zero_le K)).trans hi
      · have hm := Nat.find_min hex (show k - 1 < k by omega)
        change ¬ i < B (k - 1 + 1) at hm
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ k), not_lt] at hm
    refine ⟨k, hK, (hmem k _).mpr ⟨cantorPrefix_length _ _, i - B k, by omega, ?_⟩⟩
    have hi_eq : B k + (i - B k) = i := Nat.add_sub_of_le hlower
    rw [hi_eq]
    have hlen : (x i).length ≤ ℓ k :=
      (hLbound i).trans (hLmono.monotone hupper.le)
    have hpre := cantorPrefix_mono w hlen
    rwa [(isCantorPrefix_iff_cantorPrefix_eq (x i) w).mp hxi] at hpre

/-- Step 3 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`:
the conditional-mass capital of a finite cover is fair, bounded, and equals `4^k` on the cover.
This is an analytic statement; duplicate cylinders are allowed. -/
private theorem not_isSchnorrRandom_iff_exists_growth_capital_analytic
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hpos : ∀ x, 0 < cantorMass π x) (k : ℕ) (S : List BitString)
    (hbudget : (S.map (cantorMass π)).sum ≤ dyadicValue 1 (2 * k)) :
    let M : BitString → ℝ := fun x => (4 : ℝ) ^ k *
      (π (cantorCylinder x ∩ ⋃ y ∈ S, cantorCylinder y)).toReal / massR π x
    IsFairCapital π M ∧
      (∀ x, 0 ≤ M x ∧ M x ≤ min (4 ^ k : ℝ) (1 / massR π x)) ∧
      (∀ y ∈ S, M y = 4 ^ k) := by
  let U : Set CantorSeq := ⋃ y ∈ S, cantorCylinder y
  let M : BitString → ℝ := fun x =>
    (4 : ℝ) ^ k * (π (cantorCylinder x ∩ U)).toReal / massR π x
  change IsFairCapital π M ∧ _ ∧ _
  have hU : MeasurableSet U :=
    MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _ => measurableSet_cantorCylinder y
  have hd : ∀ x, 0 < massR π x := fun x =>
    ENNReal.toReal_pos (ne_of_gt (hpos x)) (measure_ne_top π _)
  have hcover : ∀ L : List BitString,
      π (⋃ y ∈ L, cantorCylinder y) ≤ (L.map (cantorMass π)).sum := by
    intro L
    induction L with
    | nil => simp
    | cons y L ih =>
      have heq : (⋃ z ∈ y :: L, cantorCylinder z) =
          cantorCylinder y ∪ ⋃ z ∈ L, cantorCylinder z := by
        ext w
        simp
      rw [heq, List.map_cons, List.sum_cons]
      exact (measure_union_le _ _).trans (add_le_add le_rfl ih)
  have hmass : (π U).toReal ≤ 1 / (4 : ℝ) ^ k := by
    have h := ENNReal.toReal_mono
      (by simp [dyadicValue] : dyadicValue 1 (2 * k) ≠ ⊤)
      ((hcover S).trans hbudget)
    convert h using 1
    norm_num [U, dyadicValue, ENNReal.toReal_div, pow_mul]
  have hprod : ∀ x, M x * massR π x = (4 : ℝ) ^ k *
      (π (cantorCylinder x ∩ U)).toReal := fun x =>
    div_mul_cancel₀ _ (hd x).ne'
  have hnn : ∀ x, 0 ≤ M x := fun x =>
    div_nonneg (mul_nonneg (by positivity) ENNReal.toReal_nonneg) (hd x).le
  refine ⟨⟨hnn, ?_⟩, ?_, ?_⟩
  · intro x
    rw [hprod, hprod, hprod]
    have hadd : (π (cantorCylinder x ∩ U)).toReal =
        (π (cantorCylinder (x ++ [false]) ∩ U)).toReal +
          (π (cantorCylinder (x ++ [true]) ∩ U)).toReal := by
      rw [cantorCylinder_eq_union_children, Set.union_inter_distrib_right,
        measure_union ((cantorCylinder_children_disjoint x).mono
          Set.inter_subset_left Set.inter_subset_left)
          ((measurableSet_cantorCylinder _).inter hU),
        ENNReal.toReal_add (measure_ne_top π _) (measure_ne_top π _)]
    rw [hadd, mul_add]
  · intro x
    refine ⟨hnn x, le_min ?_ ?_⟩
    · apply (div_le_iff₀ (hd x)).mpr
      exact mul_le_mul_of_nonneg_left
        (ENNReal.toReal_mono (measure_ne_top π _) (measure_mono Set.inter_subset_left))
        (by positivity)
    · apply (div_le_div_iff_of_pos_right (hd x)).mpr
      calc (4 : ℝ) ^ k * (π (cantorCylinder x ∩ U)).toReal
          ≤ 4 ^ k * (π U).toReal := mul_le_mul_of_nonneg_left
            (ENNReal.toReal_mono (measure_ne_top π _) (measure_mono Set.inter_subset_right))
            (by positivity)
        _ ≤ 4 ^ k * (1 / 4 ^ k) := mul_le_mul_of_nonneg_left hmass (by positivity)
        _ = 1 := by field_simp
  · intro y hy
    have heq : cantorCylinder y ∩ U = cantorCylinder y :=
      Set.inter_eq_left.mpr (Set.subset_iUnion_of_subset y
        (Set.subset_iUnion_of_subset hy Set.Subset.rfl))
    change 4 ^ k * (π (cantorCylinder y ∩ U)).toReal / massR π y = 4 ^ k
    rw [heq]
    exact mul_div_cancel_right₀ _ (hd y).ne'

/-- Step 4 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`:
rational dyadic weights are computable. -/
private theorem not_isSchnorrRandom_iff_exists_growth_dyadic_computable :
    Computable (fun n : ℕ => (2 : ℚ)⁻¹ ^ n) := by
  apply computable_of_num_den (Computable.const (1 : ℤ)) comp_pow
    (fun n => by positivity)
  intro n
  simp [inv_pow, one_div]

/-- Step 4 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`:
the defining dyadic approximations give computable real cylinder masses. -/
private theorem not_isSchnorrRandom_iff_exists_growth_mass_computable
    {π : Measure CantorSeq} [IsProbabilityMeasure π] (hπ : IsComputableMeasure π) :
    IsComputableOnStrings (massR π) := by
  obtain ⟨a, ha, haerr⟩ := hπ
  refine ⟨fun p => (a p.1 p.2 : ℚ) / 2 ^ p.2, ?_, ?_⟩
  · exact computable_of_num_den (ComputableReals.primrec_natCastInt.to_comp.comp ha)
      (comp_pow.comp Computable.snd) (fun p => by positivity) (fun p => by simp)
  · intro x s
    have hfin : ∀ m, dyadicValue m s ≠ ⊤ := fun m => by
      exact (ENNReal.div_lt_top (by simp) (by simp)).ne
    obtain ⟨h1, h2⟩ := haerr x s
    have h1' := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top π _, hfin 1⟩) h1
    have h2' := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hfin _, hfin 1⟩) h2
    rw [ENNReal.toReal_add (measure_ne_top π _) (hfin 1)] at h1'
    rw [ENNReal.toReal_add (hfin _) (hfin 1)] at h2'
    simp only [dyadicValue, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat, ENNReal.toReal_one, Nat.cast_one] at h1' h2'
    change (a x s : ℝ) / 2 ^ s ≤ (cantorMass π x).toReal + 1 / 2 ^ s at h1'
    push_cast
    rw [massR, abs_le, inv_pow, ← one_div]
    constructor <;> linarith

/-- Step 4 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`:
a positive computable mass admits a computable dyadic lower bound, hence a computable power-of-two
upper bound on its reciprocal. -/
private theorem not_isSchnorrRandom_iff_exists_growth_reciprocal_bound
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) :
    ∃ B : BitString → ℕ, Computable B ∧ ∀ x, 1 / massR π x ≤ (2 : ℝ) ^ B x := by
  obtain ⟨q, hq, hqerr⟩ :=
    not_isSchnorrRandom_iff_exists_growth_mass_computable hπ
  have hd : ∀ x, 0 < massR π x := fun x =>
    ENNReal.toReal_pos (ne_of_gt (hpos x)) (measure_ne_top π _)
  have hex : ∀ x, ∃ s, 2 * (2 : ℚ)⁻¹ ^ s ≤ q (x, s) := by
    intro x
    obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one
      (div_pos (hd x) (by norm_num : (0 : ℝ) < 4))
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    refine ⟨s, ?_⟩
    have h := (abs_le.mp (hqerr x s)).1
    have hs' : 2 * (2 : ℝ)⁻¹ ^ s ≤ (q (x, s) : ℝ) := by linarith [hd x]
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat]
    simpa only [one_div] using hs'
  have hc : Computable (fun x => Nat.find (hex x)) := by
    apply Computable.natFind (P := fun x s => 2 * (2 : ℚ)⁻¹ ^ s ≤ q (x, s)) ?_ hex
    exact ComputableReals.primrec_ratLe.decide.to_comp.comp
      (computable₂_ratMul.comp (Computable.const 2)
        (not_isSchnorrRandom_iff_exists_growth_dyadic_computable.comp
          Computable.snd)) hq
  refine ⟨fun x => Nat.find (hex x), hc, fun x => ?_⟩
  have hqlo : (2 : ℝ) * (2 : ℝ)⁻¹ ^ Nat.find (hex x) ≤ q (x, Nat.find (hex x)) := by
    have h := (Rat.cast_le (K := ℝ)).mpr (Nat.find_spec (hex x))
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat] at h
    simpa only [one_div] using h
  have herr := (abs_le.mp (hqerr x (Nat.find (hex x)))).2
  have hlow : (2 : ℝ)⁻¹ ^ Nat.find (hex x) ≤ massR π x := by linarith
  calc 1 / massR π x ≤ 1 / ((2 : ℝ)⁻¹ ^ Nat.find (hex x)) :=
      one_div_le_one_div_of_le (by positivity) hlow
    _ = 2 ^ Nat.find (hex x) := by simp [inv_pow]

/-- Step 3 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`: division by
a positive computable rational function is computable. -/
private lemma not_isSchnorrRandom_iff_exists_growth_rat_div_pos {α : Type*}
    [Primcodable α] {f d : α → ℚ}
    (hf : Computable f) (hd : Computable d) (hdpos : ∀ a, 0 < d a) :
    Computable (fun a => f a / d a) := by
  have hnum : Computable (fun a => (f a).num * ((d a).den : ℤ)) :=
    Computable₂.comp primrec_intMul.to_comp (computable_ratNum.comp hf)
      (ComputableReals.primrec_natCastInt.to_comp.comp (computable_ratDen.comp hd))
  have hden : Computable (fun a => (f a).den * (d a).num.toNat) :=
    Computable₂.comp Primrec.nat_mul.to_comp (computable_ratDen.comp hf)
      (ComputableReals.primrec_intToNat.to_comp.comp (computable_ratNum.comp hd))
  refine computable_of_num_den (f := fun a => f a / d a) hnum hden (fun a => ?_) (fun a => ?_)
  · exact Nat.mul_pos (f a).pos (by have := Rat.num_pos.2 (hdpos a); omega)
  · have h1 : ((f a).num : ℚ) = f a * ((f a).den : ℚ) := (Rat.mul_den_eq_num (f a)).symm
    have h2 : ((d a).num : ℚ) = d a * ((d a).den : ℚ) := (Rat.mul_den_eq_num (d a)).symm
    have h3 : (((d a).num.toNat : ℕ) : ℚ) = ((d a).num : ℚ) := by
      have hh : ((d a).num.toNat : ℤ) = (d a).num :=
        Int.toNat_of_nonneg (Rat.num_pos.2 (hdpos a)).le
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hh
    have hd1 : ((f a).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (f a).den_nz
    have hd2 : ((d a).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (d a).den_nz
    have hda : d a ≠ 0 := (hdpos a).ne'
    push_cast
    rw [h3, h1, h2]
    field_simp

/-- Step 3 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`:
error bound for dividing approximations to two nonnegative reals with numerator at most the
denominator; the denominator approximation is kept positive by the half-denominator margin. -/
private theorem not_isSchnorrRandom_iff_exists_growth_ratio_error
    (A D a d e : ℝ) (hD : 0 < D) (hA : 0 ≤ A) (hAD : A ≤ D)
    (he : e ≤ D / 2) (ha : |a - A| ≤ e) (hd : |d - D| ≤ e) :
    |a / d - A / D| ≤ 4 * e / D := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans ha
  have hdlo : D / 2 ≤ d := by linarith [(abs_le.mp hd).1]
  have hdpos : 0 < d := lt_of_lt_of_le (by linarith) hdlo
  have hnum : |a * D - A * d| ≤ 2 * e * D := by
    calc _ = |(a - A) * D + A * (D - d)| := by congr 1; ring
      _ ≤ |(a - A) * D| + |A * (D - d)| := abs_add_le _ _
      _ = |a - A| * D + A * |d - D| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hD.le, abs_of_nonneg hA, abs_sub_comm D d]
      _ ≤ e * D + A * e := add_le_add
        (mul_le_mul_of_nonneg_right ha hD.le) (mul_le_mul_of_nonneg_left hd hA)
      _ ≤ 2 * e * D := by nlinarith
  have heq : a / d - A / D = (a * D - A * d) / (d * D) := by field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hdpos hD)]
  apply (div_le_iff₀ (mul_pos hdpos hD)).mpr
  calc _ ≤ 2 * e * D := hnum
    _ ≤ 4 * e * d := by nlinarith
    _ = 4 * e / D * (d * D) := by field_simp

/-- Step 3 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`:
uniform rational approximation is closed under a quotient `A/D` with `0 ≤ A ≤ D`, when a
computable dyadic upper bound for `1/D` is supplied. -/
private theorem not_isSchnorrRandom_iff_exists_growth_ratio_computable
    {α : Type*} [Primcodable α] (A D : α → ℝ)
    (hD : ∀ z, 0 < D z) (hAD : ∀ z, 0 ≤ A z ∧ A z ≤ D z)
    (R : α → ℕ) (hR : Computable R) (hRbound : ∀ z, 1 / D z ≤ (2 : ℝ) ^ R z)
    (qA qD : α × ℕ → ℚ) (hqA : Computable qA) (hqD : Computable qD)
    (heA : ∀ z s, |(qA (z, s) : ℝ) - A z| ≤ (2 : ℝ)⁻¹ ^ s)
    (heD : ∀ z s, |(qD (z, s) : ℝ) - D z| ≤ (2 : ℝ)⁻¹ ^ s) :
    ∃ q : α × ℕ → ℚ, Computable q ∧ ∀ z s,
      |(q (z, s) : ℝ) - A z / D z| ≤ (2 : ℝ)⁻¹ ^ s := by
  let T : α × ℕ → ℕ := fun p => p.2 + R p.1 + 3
  have hT : Computable T := Primrec.nat_add.to_comp.comp
    (Primrec.nat_add.to_comp.comp Computable.snd (hR.comp Computable.fst)) (Computable.const 3)
  have hlo : ∀ z, (2 : ℝ)⁻¹ ^ R z ≤ D z := by
    intro z
    rw [inv_pow, ← one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ R z)).mpr
    simpa [mul_comm] using (div_le_iff₀ (hD z)).mp (hRbound z)
  have herr : ∀ z s, (2 : ℝ)⁻¹ ^ T (z, s) ≤ D z / 2 := by
    intro z s
    calc _ ≤ (2 : ℝ)⁻¹ ^ (R z + 1) := pow_le_pow_of_le_one
          (by norm_num) (by norm_num) (by dsimp [T]; omega)
      _ = (2 : ℝ)⁻¹ ^ R z / 2 := by rw [pow_succ]; ring
      _ ≤ D z / 2 := div_le_div_of_nonneg_right (hlo z) (by norm_num)
  have hqpos : ∀ p, 0 < qD (p.1, T p) := by
    rintro ⟨z, s⟩
    have h1 := (abs_le.mp (heD z (T (z, s)))).1
    have h2 := herr z s
    have h3 : (0 : ℝ) < (qD (z, T (z, s)) : ℝ) := by linarith [hD z]
    exact Rat.cast_pos.mp h3
  refine ⟨fun p => qA (p.1, T p) / qD (p.1, T p), ?_, fun z s => ?_⟩
  · exact not_isSchnorrRandom_iff_exists_growth_rat_div_pos
      (hqA.comp (Computable.fst.pair hT)) (hqD.comp (Computable.fst.pair hT)) hqpos
  · push_cast
    calc _ ≤ 4 * (2 : ℝ)⁻¹ ^ T (z, s) / D z :=
        not_isSchnorrRandom_iff_exists_growth_ratio_error
          _ _ _ _ _ (hD z) (hAD z).1 (hAD z).2 (herr z s)
          (heA z (T (z, s))) (heD z (T (z, s)))
      _ ≤ (4 * (2 : ℝ)⁻¹ ^ T (z, s)) * 2 ^ R z := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hRbound z) (by positivity)
      _ = (2 : ℝ)⁻¹ ^ (s + 1) := by
        have hcancel : (2 : ℝ)⁻¹ ^ R z * 2 ^ R z = 1 := by
          rw [← mul_pow]; norm_num
        change 4 * (2 : ℝ)⁻¹ ^ (s + R z + 3) * 2 ^ R z = _
        calc _ = (4 * (2 : ℝ)⁻¹ ^ (s + 3)) * ((2 : ℝ)⁻¹ ^ R z * 2 ^ R z) := by
              rw [pow_add, pow_add, pow_add]; ring
          _ = _ := by rw [hcancel, mul_one]; rw [pow_succ, pow_succ]; ring
      _ ≤ (2 : ℝ)⁻¹ ^ s := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- Step 3 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`:
intersecting a duplicate-free same-length cover with a cylinder gives a disjoint finite sum. -/
private theorem not_isSchnorrRandom_iff_exists_growth_intersection_sum
    {π : Measure CantorSeq} [IsProbabilityMeasure π] (S : List BitString)
    (hnodup : S.Nodup) (L : ℕ) (hlen : ∀ y ∈ S, y.length = L) (x : BitString) :
    (π (cantorCylinder x ∩ ⋃ y ∈ S, cantorCylinder y)).toReal =
      (S.map fun y => (π (cantorCylinder x ∩ cantorCylinder y)).toReal).sum := by
  classical
  have heq : cantorCylinder x ∩ ⋃ y ∈ S, cantorCylinder y =
      ⋃ y ∈ S.toFinset, cantorCylinder x ∩ cantorCylinder y := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_iUnion, List.mem_toFinset]
    aesop
  have hd : (↑S.toFinset : Set BitString).PairwiseDisjoint
      (fun y => cantorCylinder x ∩ cantorCylinder y) := by
    intro y hy z hz hne
    have hy' : y ∈ S := List.mem_toFinset.mp hy
    have hz' : z ∈ S := List.mem_toFinset.mp hz
    apply Disjoint.mono Set.inter_subset_right Set.inter_subset_right
    exact cantorCylinder_disjoint_of_incompatible
      (fun h => hne (h.eq_of_length ((hlen y hy').trans (hlen z hz').symm)))
      (fun h => hne (h.eq_of_length ((hlen z hz').trans (hlen y hy').symm)).symm)
  rw [heq]
  have h := measureReal_biUnion_finset (μ := π) hd
    (fun y _ => (measurableSet_cantorCylinder x).inter (measurableSet_cantorCylinder y))
  rw [List.sum_toFinset _ hnodup] at h
  exact h

/-- Step 3 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`:
finite duplicate-free covers on computable levels have uniformly computable intersection masses.
Prefix comparison reduces each summand to one cylinder mass or zero. -/
private theorem not_isSchnorrRandom_iff_exists_growth_intersection_computable
    {π : Measure CantorSeq} [IsProbabilityMeasure π] (hπ : IsComputableMeasure π)
    (ℓ : ℕ → ℕ) (S : ℕ → List BitString) (hS : Computable S)
    (hnodup : ∀ k, (S k).Nodup) (hlen : ∀ k, ∀ y ∈ S k, y.length = ℓ k) :
    ∃ q : (ℕ × BitString) × ℕ → ℚ, Computable q ∧ ∀ k x s,
      |(q ((k, x), s) : ℝ) -
        (π (cantorCylinder x ∩ ⋃ y ∈ S k, cantorCylinder y)).toReal| ≤ (2 : ℝ)⁻¹ ^ s := by
  obtain ⟨q, hq, hqerr⟩ :=
    not_isSchnorrRandom_iff_exists_growth_mass_computable hπ
  let J : (BitString × BitString) × ℕ → ℚ := fun p =>
    if p.1.1 <+: p.1.2 then q (p.1.2, p.2)
    else if p.1.2 <+: p.1.1 then q (p.1.1, p.2) else 0
  have hJ : Computable J := by
    have hxy : Computable fun p : (BitString × BitString) × ℕ =>
        decide (p.1.1 <+: p.1.2) := decide_prefix_primrec.to_comp.comp Computable.fst
    have hswap : Computable fun p : (BitString × BitString) × ℕ =>
        (p.1.2, p.1.1) :=
      (Computable.snd.comp Computable.fst).pair (Computable.fst.comp Computable.fst)
    have hswap_test := decide_prefix_primrec.to_comp.comp hswap
    have hyx : Computable fun p : (BitString × BitString) × ℕ =>
        decide (p.1.2 <+: p.1.1) := hswap_test.of_eq (fun _ => rfl)
    have hx : Computable fun p : (BitString × BitString) × ℕ => q (p.1.1, p.2) :=
      hq.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)
    have hy : Computable fun p : (BitString × BitString) × ℕ => q (p.1.2, p.2) :=
      hq.comp ((Computable.snd.comp Computable.fst).pair Computable.snd)
    exact (Computable.cond hxy hy (Computable.cond hyx hx (Computable.const 0))).of_eq
      (fun p => by simp [J])
  have hJerr : ∀ x y t, |(J ((x, y), t) : ℝ) -
      (π (cantorCylinder x ∩ cantorCylinder y)).toReal| ≤ (2 : ℝ)⁻¹ ^ t := by
    intro x y t
    by_cases hxy : x <+: y
    · simpa only [J, ite_eq_left hxy, cantorCylinder_inter_of_prefix hxy, massR, cantorMass]
        using hqerr y t
    · by_cases hyx : y <+: x
      · simpa only [J, ite_eq_right hxy, ite_eq_left hyx, Set.inter_comm (cantorCylinder x),
          cantorCylinder_inter_of_prefix hyx, massR, cantorMass] using hqerr x t
      · simp [J, hxy, hyx, (cantorCylinder_disjoint_of_incompatible hxy hyx).inter_eq]
  let T : (ℕ × BitString) × ℕ → ℕ := fun p => p.2 + (S p.1.1).length
  have hT : Computable T := Primrec.nat_add.to_comp.comp Computable.snd
    (Computable.list_length.comp (hS.comp (Computable.fst.comp Computable.fst)))
  let Q : (ℕ × BitString) × ℕ → ℚ := fun p =>
    ((S p.1.1).map fun y => J ((p.1.2, y), T p)).sum
  have hQc : Computable Q := by
    have hj : Computable fun z : ((ℕ × BitString) × ℕ) × (ℚ × BitString) =>
        J ((z.1.1.2, z.2.2), T z.1) :=
      hJ.comp (((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.snd.comp Computable.snd)).pair (hT.comp Computable.fst))
    have hh : Computable₂ (fun (p : (ℕ × BitString) × ℕ) (r : ℚ × BitString) =>
        r.1 + J ((p.1.2, r.2), T p)) :=
      computable₂_ratAdd.comp (Computable.fst.comp Computable.snd) hj
    have hf := computable_list_foldl (hS.comp (Computable.fst.comp Computable.fst))
      (Computable.const (0 : ℚ)) hh
    refine hf.of_eq fun p => ?_
    dsimp only [Q]
    rw [← List.foldl_map, ← List.sum_eq_foldl]
  refine ⟨Q, hQc, fun k x s => ?_⟩
  have heq : (Q ((k, x), s) : ℝ) =
      ((S k).map fun y => (J ((x, y), T ((k, x), s)) : ℝ)).sum := by
    simp only [Q, Rat.cast_list_sum, List.map_map, Function.comp_def]
  rw [heq, not_isSchnorrRandom_iff_exists_growth_intersection_sum
    (S k) (hnodup k) (ℓ k) (hlen k) x,
    ← List.sum_toFinset _ (hnodup k), ← List.sum_toFinset _ (hnodup k),
    ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ y ∈ (S k).toFinset,
        |(J ((x, y), T ((k, x), s)) : ℝ) - (π (cantorCylinder x ∩ cantorCylinder y)).toReal| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ (S k).toFinset, (2 : ℝ)⁻¹ ^ T ((k, x), s) :=
      Finset.sum_le_sum fun y _ => hJerr x y _
    _ = ((S k).length : ℝ) * (2 : ℝ)⁻¹ ^ (s + (S k).length) := by
      simp [T, List.toFinset_card_of_nodup (hnodup k)]
    _ ≤ (2 : ℝ)⁻¹ ^ s := by
      have hL : ((S k).length : ℝ) ≤ (2 : ℝ) ^ (S k).length := by
        exact_mod_cast (Nat.lt_two_pow_self (n := (S k).length)).le
      have hLe : ((S k).length : ℝ) * (2 : ℝ)⁻¹ ^ (S k).length ≤ 1 := by
        rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
        exact hL
      calc _ = (((S k).length : ℝ) * (2 : ℝ)⁻¹ ^ (S k).length) * (2 : ℝ)⁻¹ ^ s := by
              rw [pow_add]; ring
        _ ≤ 1 * (2 : ℝ)⁻¹ ^ s := mul_le_mul_of_nonneg_right hLe (by positivity)
        _ = _ := one_mul _

/-- Step 3 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`:
finite same-length covers have uniformly computable conditional-mass capitals. The formula fixes
the witness explicitly, and positive cylinder masses make division effective. -/
private theorem not_isSchnorrRandom_iff_exists_growth_capital_computable
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x)
    (ℓ : ℕ → ℕ)
    (S : ℕ → List BitString) (hS_comp : Computable S)
    (hS_nodup : ∀ k, (S k).Nodup)
    (hlen : ∀ k, ∀ y ∈ S k, y.length = ℓ k) :
    ∃ q : (ℕ × BitString) × ℕ → ℚ, Computable q ∧ ∀ k x s,
      |(q ((k, x), s) : ℝ) - (4 : ℝ) ^ k *
        (π (cantorCylinder x ∩ ⋃ y ∈ S k, cantorCylinder y)).toReal / massR π x| ≤
          (2 : ℝ)⁻¹ ^ s := by
  obtain ⟨qA, hqA, hAerr⟩ :=
    not_isSchnorrRandom_iff_exists_growth_intersection_computable
      hπ ℓ S hS_comp hS_nodup hlen
  obtain ⟨qD, hqD, hDerr⟩ :=
    not_isSchnorrRandom_iff_exists_growth_mass_computable hπ
  obtain ⟨R, hR, hRbound⟩ :=
    not_isSchnorrRandom_iff_exists_growth_reciprocal_bound hπ hpos
  let A : ℕ × BitString → ℝ := fun p =>
    (π (cantorCylinder p.2 ∩ ⋃ y ∈ S p.1, cantorCylinder y)).toReal
  have hD : ∀ p : ℕ × BitString, 0 < massR π p.2 := fun p =>
    ENNReal.toReal_pos (ne_of_gt (hpos p.2)) (measure_ne_top π _)
  have hAD : ∀ p : ℕ × BitString, 0 ≤ A p ∧ A p ≤ massR π p.2 := fun p =>
    ⟨ENNReal.toReal_nonneg,
      ENNReal.toReal_mono (measure_ne_top π _) (measure_mono Set.inter_subset_left)⟩
  obtain ⟨q, hq, hqerr⟩ :=
    not_isSchnorrRandom_iff_exists_growth_ratio_computable
      A (fun p : ℕ × BitString => massR π p.2) hD hAD
      (fun p : ℕ × BitString => R p.2) (hR.comp Computable.snd) (fun p => hRbound p.2)
      qA (fun p => qD (p.1.2, p.2)) hqA
      (hqD.comp ((Computable.snd.comp Computable.fst).pair Computable.snd))
      (fun p s => hAerr p.1 p.2 s) (fun p s => hDerr p.2 s)
  refine ⟨fun p => ((4 ^ p.1.1 : ℕ) : ℚ) * q (p.1, p.2 + 2 * p.1.1), ?_, ?_⟩
  · have hscale : Computable fun p : (ℕ × BitString) × ℕ => ((4 ^ p.1.1 : ℕ) : ℚ) :=
      computable_nat_to_rat.comp (nat_pow_primrec₂.to_comp.comp (Computable.const 4)
        (Computable.fst.comp Computable.fst))
    have ht : Computable fun p : (ℕ × BitString) × ℕ => p.2 + 2 * p.1.1 :=
      Primrec.nat_add.to_comp.comp Computable.snd
        (Primrec.nat_mul.to_comp.comp (Computable.const 2) (Computable.fst.comp Computable.fst))
    exact computable₂_ratMul.comp hscale (hq.comp (Computable.fst.pair ht))
  · intro k x s
    change |((((4 ^ k : ℕ) : ℚ) * q ((k, x), s + 2 * k) : ℚ) : ℝ) -
      (4 : ℝ) ^ k * A (k, x) / massR π x| ≤ (2 : ℝ)⁻¹ ^ s
    push_cast
    rw [show (4 : ℝ) ^ k * A (k, x) / massR π x =
      4 ^ k * (A (k, x) / massR π x) by ring, ← mul_sub, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 ^ k)]
    calc _ ≤ (4 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ (s + 2 * k) :=
        mul_le_mul_of_nonneg_left (hqerr (k, x) (s + 2 * k)) (by positivity)
      _ = (2 : ℝ)⁻¹ ^ s := by
        have hcancel : (4 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ (2 * k) = 1 := by
          rw [pow_mul, ← mul_pow]; norm_num
        calc _ = ((4 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ (2 * k)) * (2 : ℝ)⁻¹ ^ s := by
              rw [pow_add]; ring
          _ = _ := by rw [hcancel, one_mul]

/-- Step 3 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`: construct
the level martingales with uniform computability and bounds. -/
private theorem not_isSchnorrRandom_iff_exists_growth_martingales
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π)
    (hpos : ∀ x, 0 < cantorMass π x)
    (ℓ : ℕ → ℕ)
    (S : ℕ → List BitString) (hS_comp : Computable S)
    (hS_nodup : ∀ k, (S k).Nodup)
    (hlen : ∀ k, ∀ y ∈ S k, y.length = ℓ k)
    (hbudget : ∀ k, ((S k).map (cantorMass π)).sum ≤ dyadicValue 1 (2 * k)) :
    ∃ M : ℕ → BitString → ℝ,
      (∃ q : (ℕ × BitString) × ℕ → ℚ, Computable q ∧
        ∀ k x s, |(q ((k,x),s) : ℝ) - M k x| ≤ (2 : ℝ)⁻¹ ^ s) ∧
      (∀ k, IsFairCapital π (M k)) ∧
      (∀ k x, 0 ≤ M k x ∧ M k x ≤ min (4^k : ℝ) (1 / (cantorMass π x).toReal)) ∧
      (∀ k y, y ∈ S k → M k y = 4^k) := by
  refine ⟨fun k x => (4 : ℝ) ^ k *
    (π (cantorCylinder x ∩ ⋃ y ∈ S k, cantorCylinder y)).toReal / massR π x,
    not_isSchnorrRandom_iff_exists_growth_capital_computable
      hπ hpos ℓ S hS_comp hS_nodup hlen, ?_, ?_, ?_⟩
  · exact fun k => (not_isSchnorrRandom_iff_exists_growth_capital_analytic
      hpos k (S k) (hbudget k)).1
  · exact fun k => (not_isSchnorrRandom_iff_exists_growth_capital_analytic
      hpos k (S k) (hbudget k)).2.1
  · exact fun k => (not_isSchnorrRandom_iff_exists_growth_capital_analytic
      hpos k (S k) (hbudget k)).2.2

/-- Step 4 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`:
the common reciprocal-mass bound makes the geometric mixture summable at each string. -/
private theorem not_isSchnorrRandom_iff_exists_growth_summable
    {π : Measure CantorSeq} (M : ℕ → BitString → ℝ)
    (hM_bounds : ∀ k x, 0 ≤ M k x ∧ M k x ≤ min (4 ^ k : ℝ) (1 / massR π x))
    (x : BitString) : Summable (fun k => (2 : ℝ)⁻¹ ^ k * M k x) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (by positivity) (hM_bounds k x).1)
    (fun k => mul_le_mul_of_nonneg_left
      ((hM_bounds k x).2.trans (min_le_right _ _)) (by positivity))
  exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ < 1)).mul_right _

/-- Step 4 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`:
the geometric mixture of uniformly computable capitals with a reciprocal-mass bound is
computable. Positivity and computability of the mass provide an effective truncation length. -/
private theorem not_isSchnorrRandom_iff_exists_growth_mix_computable
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x)
    (M : ℕ → BitString → ℝ)
    (hM_comp : ∃ q : (ℕ × BitString) × ℕ → ℚ, Computable q ∧
      ∀ k x s, |(q ((k, x), s) : ℝ) - M k x| ≤ (2 : ℝ)⁻¹ ^ s)
    (hM_bounds : ∀ k x, 0 ≤ M k x ∧ M k x ≤ min (4 ^ k : ℝ) (1 / massR π x)) :
    IsComputableOnStrings (fun x => ∑' k, (2 : ℝ)⁻¹ ^ k * M k x) := by
  obtain ⟨q, hq, hqerr⟩ := hM_comp
  obtain ⟨B, hB, hBbound⟩ :=
    not_isSchnorrRandom_iff_exists_growth_reciprocal_bound hπ hpos
  have hs := not_isSchnorrRandom_iff_exists_growth_summable M hM_bounds
  have hpow := not_isSchnorrRandom_iff_exists_growth_dyadic_computable
  let K : BitString × ℕ → ℕ := fun p => p.2 + B p.1 + 2
  have hK : Computable K :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp Computable.snd (hB.comp Computable.fst))
      (Computable.const 2)
  let Q : BitString × ℕ → ℚ := fun p => ∑ i ∈ Finset.range (K p),
    (2 : ℚ)⁻¹ ^ i * q ((i, p.1), p.2 + 2)
  have hQc : Computable Q := by
    have hterm : Computable fun z : (BitString × ℕ) × (ℕ × ℚ) =>
        (2 : ℚ)⁻¹ ^ z.2.1 * q ((z.2.1, z.1.1), z.1.2 + 2) :=
      computable₂_ratMul.comp (hpow.comp (Computable.fst.comp Computable.snd))
        (hq.comp ((Computable.pair (Computable.fst.comp Computable.snd)
          (Computable.fst.comp Computable.fst)).pair
            (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.fst)
              (Computable.const 2))))
    have hstep : Computable₂ (fun (p : BitString × ℕ) (r : ℕ × ℚ) =>
        r.2 + (2 : ℚ)⁻¹ ^ r.1 * q ((r.1, p.1), p.2 + 2)) :=
      computable₂_ratAdd.comp (Computable.snd.comp Computable.snd) hterm
    have hr := Computable.nat_rec (σ := ℚ) hK (Computable.const 0) hstep
    refine hr.of_eq fun p => ?_
    have heq : ∀ n, Nat.rec (motive := fun _ => ℚ) 0
        (fun i r => r + (2 : ℚ)⁻¹ ^ i * q ((i, p.1), p.2 + 2)) n =
          ∑ i ∈ Finset.range n, (2 : ℚ)⁻¹ ^ i * q ((i, p.1), p.2 + 2) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ]
        exact congrArg (fun r : ℚ => r + (2 : ℚ)⁻¹ ^ n * q ((n, p.1), p.2 + 2)) ih
    simpa only [Q] using heq (K p)
  refine ⟨Q, hQc, fun x s => ?_⟩
  have hgeom : Summable (fun i : ℕ => (2 : ℝ)⁻¹ ^ i) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hgeomval : ∑' i : ℕ, (2 : ℝ)⁻¹ ^ i = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hweights : ∑ i ∈ Finset.range (K (x, s)), (2 : ℝ)⁻¹ ^ i ≤ 2 := by
    exact (hgeom.sum_le_tsum _ (fun i _ => by positivity)).trans_eq hgeomval
  have hQreal : (Q (x, s) : ℝ) = ∑ i ∈ Finset.range (K (x, s)),
      (2 : ℝ)⁻¹ ^ i * (q ((i, x), s + 2) : ℝ) := by
    dsimp [Q]
    push_cast
    rfl
  have hhead : |(Q (x, s) : ℝ) -
      ∑ i ∈ Finset.range (K (x, s)), (2 : ℝ)⁻¹ ^ i * M i x| ≤ (2 : ℝ)⁻¹ ^ (s + 1) := by
    rw [hQreal, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ i ∈ Finset.range (K (x, s)),
          |(2 : ℝ)⁻¹ ^ i * (q ((i, x), s + 2) : ℝ) - (2 : ℝ)⁻¹ ^ i * M i x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (K (x, s)), (2 : ℝ)⁻¹ ^ i * (2 : ℝ)⁻¹ ^ (s + 2) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹ ^ i)]
        exact mul_le_mul_of_nonneg_left (hqerr i x (s + 2)) (by positivity)
      _ = (∑ i ∈ Finset.range (K (x, s)), (2 : ℝ)⁻¹ ^ i) * (2 : ℝ)⁻¹ ^ (s + 2) :=
        (Finset.sum_mul ..).symm
      _ ≤ 2 * (2 : ℝ)⁻¹ ^ (s + 2) := mul_le_mul_of_nonneg_right hweights (by positivity)
      _ = (2 : ℝ)⁻¹ ^ (s + 1) := by rw [pow_succ]; ring
  have htail : ∑' i, (2 : ℝ)⁻¹ ^ (i + K (x, s)) * M (i + K (x, s)) x ≤
      (2 : ℝ)⁻¹ ^ (s + 1) := by
    have ht := (summable_nat_add_iff (K (x, s))).mpr (hs x)
    calc
      _ ≤ (∑' i, (2 : ℝ)⁻¹ ^ i * ((2 : ℝ)⁻¹ ^ K (x, s) * 2 ^ B x)) := by
        refine Summable.tsum_le_tsum ?_ ht (hgeom.mul_right _)
        intro i
        calc _ ≤ (2 : ℝ)⁻¹ ^ (i + K (x, s)) * 2 ^ B x :=
            mul_le_mul_of_nonneg_left
              (((hM_bounds _ x).2.trans (min_le_right _ _)).trans (hBbound x))
              (by positivity)
          _ = _ := by rw [pow_add]; ring
      _ = 2 * ((2 : ℝ)⁻¹ ^ K (x, s) * 2 ^ B x) := by rw [tsum_mul_right, hgeomval]
      _ = (2 : ℝ)⁻¹ ^ (s + 1) := by
        have hcancel : (2 : ℝ)⁻¹ ^ B x * 2 ^ B x = 1 := by
          rw [← mul_pow]; norm_num
        change 2 * ((2 : ℝ)⁻¹ ^ (s + B x + 2) * 2 ^ B x) = _
        calc _ = (2 * (2 : ℝ)⁻¹ ^ (s + 2)) * ((2 : ℝ)⁻¹ ^ B x * 2 ^ B x) := by
              rw [pow_add, pow_add, pow_add]; ring
          _ = _ := by rw [hcancel, mul_one, pow_succ]; ring
  have htailnn : 0 ≤ ∑' i, (2 : ℝ)⁻¹ ^ (i + K (x, s)) * M (i + K (x, s)) x :=
    tsum_nonneg fun i => mul_nonneg (by positivity) (hM_bounds _ x).1
  change |(Q (x, s) : ℝ) - ∑' k, (2 : ℝ)⁻¹ ^ k * M k x| ≤ (2 : ℝ)⁻¹ ^ s
  rw [← (hs x).sum_add_tsum_nat_add (K (x, s))]
  calc _ = |((Q (x, s) : ℝ) -
        ∑ i ∈ Finset.range (K (x, s)), (2 : ℝ)⁻¹ ^ i * M i x) -
          ∑' i, (2 : ℝ)⁻¹ ^ (i + K (x, s)) * M (i + K (x, s)) x| := by congr 1; ring
    _ ≤ |(Q (x, s) : ℝ) - ∑ i ∈ Finset.range (K (x, s)), (2 : ℝ)⁻¹ ^ i * M i x| +
        |∑' i, (2 : ℝ)⁻¹ ^ (i + K (x, s)) * M (i + K (x, s)) x| := abs_sub _ _
    _ ≤ (2 : ℝ)⁻¹ ^ (s + 1) + (2 : ℝ)⁻¹ ^ (s + 1) := by
      rw [abs_of_nonneg htailnn]
      exact add_le_add hhead htail
    _ = (2 : ℝ)⁻¹ ^ s := by rw [pow_succ]; ring

/-- Step 4 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`: mix
martingale fairness and computability -/
private theorem not_isSchnorrRandom_iff_exists_growth_mix_martingale_fair_comp
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π)
    (hpos : ∀ x, 0 < cantorMass π x)
    (M : ℕ → BitString → ℝ)
    (hM_comp : ∃ q : (ℕ × BitString) × ℕ → ℚ, Computable q ∧
      ∀ k x s, |(q ((k, x), s) : ℝ) - M k x| ≤ (2 : ℝ)⁻¹ ^ s)
    (hM_fair : ∀ k, IsFairCapital π (M k))
    (hM_bounds : ∀ k x, 0 ≤ M k x ∧ M k x ≤ min ((4 : ℝ) ^ k) (1 / (cantorMass π x).toReal)) :
    ∃ m : BitString → ℝ, IsFairCapital π m ∧ IsComputableOnStrings m ∧
    ∀ x, m x = ∑' k, (2 : ℝ)⁻¹ ^ k * M k x := by
  have hs := not_isSchnorrRandom_iff_exists_growth_summable M hM_bounds
  refine ⟨fun x => ∑' k, (2 : ℝ)⁻¹ ^ k * M k x, ⟨?_, ?_⟩,
    not_isSchnorrRandom_iff_exists_growth_mix_computable
      hπ hpos M hM_comp hM_bounds, fun _ => rfl⟩
  · intro x
    exact tsum_nonneg (fun k => mul_nonneg (by positivity) (hM_bounds k x).1)
  · intro x
    rw [← tsum_mul_right, ← tsum_mul_right, ← tsum_mul_right,
      ← ((hs (x ++ [false])).mul_right (massR π (x ++ [false]))).tsum_add
        ((hs (x ++ [true])).mul_right (massR π (x ++ [true])))]
    apply tsum_congr
    intro k
    calc (2 : ℝ)⁻¹ ^ k * M k x * massR π x
        = (2 : ℝ)⁻¹ ^ k * (M k x * massR π x) := by ring
      _ = _ := by rw [(hM_fair k).fair x]; ring

/-- Step 5 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`: preservation
of the lower bound on every `S k`. -/
private theorem not_isSchnorrRandom_iff_exists_growth_mix_martingale_lower_bound
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (M : ℕ → BitString → ℝ)
    (m : BitString → ℝ)
    (h_sum : ∀ x, m x = ∑' k, (2 : ℝ)⁻¹ ^ k * M k x)
    (hM_bounds : ∀ k x, 0 ≤ M k x ∧ M k x ≤ min ((4 : ℝ) ^ k) (1 / (cantorMass π x).toReal))
    (S : ℕ → List BitString)
    (hM_val : ∀ k y, y ∈ S k → M k y = 4 ^ k) :
    ∀ k y, y ∈ S k → (2 : ℝ) ^ k ≤ m y := by
  intro k y hy
  rw [h_sum y]
  have hs := not_isSchnorrRandom_iff_exists_growth_summable M hM_bounds y
  calc (2 : ℝ) ^ k = (2 : ℝ)⁻¹ ^ k * M k y := by
        rw [hM_val k y hy, ← mul_pow]
        norm_num
    _ ≤ ∑' i, (2 : ℝ)⁻¹ ^ i * M i y :=
      hs.le_tsum k (fun i _ => mul_nonneg (by positivity) (hM_bounds i y).1)

/-- Step 6 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`: construction
of computable growth from `ℓ`. -/
private theorem not_isSchnorrRandom_iff_exists_growth_growth
    (ℓ : ℕ → ℕ) (hℓ_comp : Computable ℓ) (hℓ_mono : StrictMono ℓ) :
    ∃ g : ℕ → ℕ, IsComputableGrowth g ∧ ∀ k, (g (ℓ k) : ℝ) = 2 ^ k := by
  have hex : ∀ n, ∃ k, n < ℓ k := fun n =>
    ⟨n + 1, lt_of_lt_of_le (Nat.lt_succ_self n) (hℓ_mono.id_le _)⟩
  have hfind : Computable (fun n => Nat.find (hex n)) := by
    apply Computable.natFind (P := fun n k => n < ℓ k) ?_ hex
    exact Primrec.nat_lt.decide.to_comp.comp Computable.fst (hℓ_comp.comp Computable.snd)
  have hval : ∀ k, Nat.find (hex (ℓ k)) = k + 1 := by
    intro k
    apply (Nat.find_eq_iff _).mpr
    refine ⟨hℓ_mono (Nat.lt_succ_self k), fun j hj => ?_⟩
    exact not_lt.mpr (hℓ_mono.monotone (by omega))
  refine ⟨fun n => 2 ^ (Nat.find (hex n) - 1), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact comp_pow.comp (Primrec.nat_sub.to_comp.comp hfind (Computable.const 1))
  · intro a b hab
    apply Nat.pow_le_pow_right (by decide)
    apply Nat.sub_le_sub_right
    exact Nat.find_mono (fun k hk => lt_of_le_of_lt hab hk)
  · intro B
    refine ⟨ℓ B, ?_⟩
    rw [hval, Nat.add_sub_cancel]
    exact (Nat.lt_two_pow_self).le
  · intro k
    change ((2 ^ (Nat.find (hex (ℓ k)) - 1) : ℕ) : ℝ) = 2 ^ k
    rw [hval, Nat.add_sub_cancel, Nat.cast_pow, Nat.cast_ofNat]

/-- Step 7 of the proof of `not_isSchnorrRandom_iff_exists_growth_ltr`: assembly
helper -/
private theorem not_isSchnorrRandom_iff_exists_growth_assembly
    (w : CantorSeq)
    (m : BitString → ℝ)
    (g : ℕ → ℕ)
    (ℓ : ℕ → ℕ) (hℓ_mono : StrictMono ℓ) (S : ℕ → List BitString)
    (hfreq : ∃ᶠ k in atTop, cantorPrefix w (ℓ k) ∈ S k)
    (hlower : ∀ k y, y ∈ S k → (2 : ℝ) ^ k ≤ m y)
    (h_g_lower : ∀ k, (g (ℓ k) : ℝ) = (2 : ℝ) ^ k) :
    ∃ᶠ n in atTop, (g n : ℝ) ≤ m (cantorPrefix w n) := by
  have h_tends : Filter.Tendsto ℓ Filter.atTop Filter.atTop := StrictMono.tendsto_atTop hℓ_mono
  have hfreq2 : ∃ᶠ k in atTop, (g (ℓ k) : ℝ) ≤ m (cantorPrefix w (ℓ k)) := by
    apply Filter.Frequently.mono hfreq
    intro k hk_in
    have h1 : (2 : ℝ) ^ k ≤ m (cantorPrefix w (ℓ k)) := hlower k _ hk_in
    have h2 : (g (ℓ k) : ℝ) ≤ (2 : ℝ) ^ k := le_of_eq (h_g_lower k)
    exact le_trans h2 h1
  exact Filter.Tendsto.frequently h_tends hfreq2

/-- Step 1 of the proof of `not_isSchnorrRandom_iff_exists_growth`: the forward direction,
constructing the martingale and the growth function. -/
theorem not_isSchnorrRandom_iff_exists_growth_ltr {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) (w : CantorSeq) :
    ¬ IsSchnorrRandom π w → ∃ m g, IsFairCapital π m ∧ IsComputableOnStrings m ∧
      IsComputableGrowth g ∧ ∃ᶠ n in atTop, (g n : ℝ) ≤ m (cantorPrefix w n) := by
  intro hw
  obtain ⟨x, hx_comp, N, hN_comp, hTail, hHit⟩ :=
      not_isSchnorrRandom_iff_exists_growth_extract_witness hπ w hw
  obtain ⟨ℓ, hℓ_comp, hℓ_mono, S, hS_comp, hS_prop, hfreq⟩ :=
      not_isSchnorrRandom_iff_exists_growth_group_and_extend w x hx_comp N hN_comp
      hTail hHit
  have hlen : ∀ k, ∀ y ∈ S k, y.length = ℓ k := fun k => (hS_prop k).2.1
  have hbudget : ∀ k, ((S k).map (cantorMass π)).sum ≤ dyadicValue 1 (2*k) :=
      fun k => (hS_prop k).2.2
  obtain ⟨M, hM_comp, hM_fair, hM_bounds, hM_val⟩ :=
      not_isSchnorrRandom_iff_exists_growth_martingales hπ hpos ℓ S hS_comp
      (fun k => (hS_prop k).1) hlen hbudget
  obtain ⟨m, hm_fair, hm_comp, hm_sum⟩ :=
      not_isSchnorrRandom_iff_exists_growth_mix_martingale_fair_comp hπ hpos M
      hM_comp hM_fair hM_bounds
  have hm_lower : ∀ k y, y ∈ S k → (2 : ℝ) ^ k ≤ m y := by
    apply not_isSchnorrRandom_iff_exists_growth_mix_martingale_lower_bound M m
        hm_sum hM_bounds S hM_val
  obtain ⟨g, hg_growth, hg_val⟩ := not_isSchnorrRandom_iff_exists_growth_growth ℓ
      hℓ_comp hℓ_mono
  use m, g, hm_fair, hm_comp, hg_growth
  exact not_isSchnorrRandom_iff_exists_growth_assembly w m g ℓ hℓ_mono S hfreq
      hm_lower hg_val

end Kolmogorov.FrequencyGames
