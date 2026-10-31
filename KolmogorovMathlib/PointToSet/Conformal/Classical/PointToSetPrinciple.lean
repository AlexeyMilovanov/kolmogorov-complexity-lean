/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.Classical.HausdorffPointToSet
import KolmogorovMathlib.PointToSet.Conformal.Classical.PackingPointDimension

/-!
# The classical point-to-set principle

This module proves the point-to-set principle for the Hausdorff and the (specified-radius)
packing dimension of an arbitrary subset `Z` of a presented metric space: both dimensions are
minima, over oracles `A`, of the supremum over `x ∈ Z` of the relative static point dimensions
`(staticPointDimensions P A x).1` and `(staticPointDimensions P A x).2`.

* `packingAchievingOracle` (blueprint node `conf:packing-achieving`) is the packing counterpart of
  `hausdorffAchievingOracle`: some oracle `A` satisfies
  `⨆ x ∈ Z, dim_P^A x ≤ metricPackingDimension Z`.  For a real `s` above the packing
  dimension, `Z` is covered by countably many pieces of upper box dimension below `s`; each piece
  has, at every large dyadic scale, a cover by few ideal-centred balls, and the finite lists of
  centres are coded in one oracle with the oracle Kraft–Chaitin theorem, using self-delimiting
  scale headers.  Joining the oracles obtained for `s ↓ metricPackingDimension Z` gives the claim.
* `packingAchievingOracle_stable`: the inequality persists above an achieving oracle.
* `classicalPointToSet` and `classicalPointToSet_upper` (blueprint node `conf:classical-pts`)
  combine these achieving oracles with the every-oracle lower bounds of the imported modules;
  `classicalPointToSet_cone`, `classicalPointToSet_cone_upper` and `classicalPointToSet_attained`
  restrict the minima to an arbitrary upper cone of oracles.

The results are used by `KolmogorovMathlib.PointToSet.Conformal.Classical`, which re-exports them,
and through it by the dimension theorem of `KolmogorovMathlib.PointToSet.Conformal.TheoremE`.
-/

namespace Kolmogorov.PointToSet
open Filter TopologicalSpace MeasureTheory Measure
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-- An extended nonnegative number below `ofReal s` lies strictly below `ofReal t` for some
positive `t < s`. -/
private lemma exists_pos_lt_lt_ofReal {d : ℝ≥0∞} {s : ℝ} (hs : d < ENNReal.ofReal s) :
    ∃ t : ℝ, 0 < t ∧ t < s ∧ d < ENNReal.ofReal t := by
  have hd : d ≠ ⊤ := hs.ne_top
  have hs0 : 0 < s := ENNReal.ofReal_pos.mp (bot_le.trans_lt hs)
  have hlt : d.toReal < s := (ENNReal.lt_ofReal_iff_toReal_lt hd).mp hs
  have hd0 : 0 ≤ d.toReal := ENNReal.toReal_nonneg
  exact ⟨(d.toReal + s) / 2, by linarith, by linarith,
    (ENNReal.lt_ofReal_iff_toReal_lt hd).mpr (by linarith)⟩

/-- A finite extended nonnegative number is the limit of a sequence `ofReal (s n)` of strictly
larger numbers. -/
private lemma exists_seq_lt_ofReal_tendsto {d : ℝ≥0∞} (hd : d < ⊤) :
    ∃ s : ℕ → ℝ, (∀ n, d < ENNReal.ofReal (s n)) ∧
      Tendsto (fun n ↦ ENNReal.ofReal (s n)) atTop (𝓝 d) := by
  refine ⟨fun n ↦ d.toReal + 1 / ((n : ℝ) + 1), fun n ↦ ?_, ?_⟩
  · refine (ENNReal.lt_ofReal_iff_toReal_lt hd.ne).mpr ?_
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · have hs : Tendsto (fun n : ℕ ↦ d.toReal + 1 / ((n : ℝ) + 1)) atTop (𝓝 d.toReal) := by
      simpa using (tendsto_const_nhds (x := d.toReal)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hconv := ENNReal.tendsto_ofReal hs
    rwa [ENNReal.ofReal_toReal hd.ne] at hconv

/-- A set whose modified upper box dimension is below `ofReal t` is covered by countably many
sets of upper box dimension below `ofReal t`. -/
private lemma exists_cover_upperBoxDimension_lt (Z : Set X) (t : ℝ)
    (ht : modifiedUpperBoxDimension Z < ENNReal.ofReal t) :
    ∃ Z_cov : ℕ → Set X, Z ⊆ ⋃ i, Z_cov i ∧
      ∀ i, upperBoxDimension (Z_cov i) < ENNReal.ofReal t := by
  unfold modifiedUpperBoxDimension at ht
  obtain ⟨Z_cov, hcov⟩ := iInf_lt_iff.mp ht
  obtain ⟨h_sub, h_sup⟩ := iInf_lt_iff.mp hcov
  exact ⟨Z_cov, h_sub, fun i ↦
    (le_iSup (fun j ↦ upperBoxDimension (Z_cov j)) i).trans_lt h_sup⟩

/-- If the logarithmic rate `log₂ q / n` of a quantity `q` at a positive order `n` is below `a`,
then `q ≤ 2 ^ (a * n)`. -/
private lemma le_ofReal_two_rpow_of_pressureLog_mul_lt
    (q : ℝ≥0∞) (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n)
    (h : (pressureLog q * ((n : ℝ)⁻¹ : ℝ)).toENNReal < ENNReal.ofReal a) :
    q ≤ ENNReal.ofReal ((2 : ℝ) ^ (a * n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rcases eq_or_ne q 0 with rfl | hq
  · exact bot_le
  rcases eq_or_ne q ⊤ with rfl | htop
  · rw [pressureLog, ENNReal.log_top, EReal.top_mul_of_pos (EReal.coe_pos.mpr (inv_pos.2 hlog2)),
      EReal.top_mul_of_pos (EReal.coe_pos.mpr (inv_pos.2 hn0)), EReal.toENNReal_top] at h
    exact absurd h not_top_lt
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos hq htop
  have hrate : pressureLog q * ((n : ℝ)⁻¹ : ℝ) =
      ((Real.log q.toReal * (Real.log 2)⁻¹ * (n : ℝ)⁻¹ : ℝ) : EReal) := by
    rw [pressureLog, ENNReal.log_pos_real hq htop, ← EReal.coe_mul, ← EReal.coe_mul]
  have hcoe : (((Real.log q.toReal * (Real.log 2)⁻¹ * (n : ℝ)⁻¹ : ℝ) : EReal)).toENNReal =
      ENNReal.ofReal (Real.log q.toReal * (Real.log 2)⁻¹ * (n : ℝ)⁻¹) := rfl
  rw [hrate, hcoe] at h
  have h' := (ENNReal.ofReal_lt_ofReal_iff ha).mp h
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_div, div_lt_iff₀ (by positivity)] at h'
  have hlt : q.toReal < (2 : ℝ) ^ (a * n) := by
    rw [Real.lt_rpow_iff_log_lt hq0 two_pos]
    linarith
  calc q = ENNReal.ofReal q.toReal := (ENNReal.ofReal_toReal htop).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hlt.le

/-- If the upper box dimension of `Y` is below `ofReal a`, the external covering numbers of `Y`
by closed balls of radius `2⁻⁽ʳ⁺¹⁾` are eventually at most `2 ^ (a * (r + 1))`. -/
private lemma eventually_externalCoveringNumber_le {Y : Set X} {a : ℝ} (ha : 0 < a)
    (hY : upperBoxDimension Y < ENNReal.ofReal a) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀,
      (Metric.externalCoveringNumber (Real.toNNReal (dyadicRadius (r + 1))) Y : ℝ≥0∞) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (a * (r + 1 : ℝ))) := by
  let q := fun k ↦ (Metric.externalCoveringNumber (Real.toNNReal (dyadicRadius k)) Y : ℝ≥0∞)
  have hlim : limsup (fun n ↦ (pressureRate q n).toENNReal) atTop < ENNReal.ofReal a := by
    rwa [← packingEqModifiedUpperBox_coveringNumber Y]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    (eventually_lt_of_limsup_lt hlim (by isBoundedDefault))
  refine ⟨n₀, fun r hr ↦ ?_⟩
  have h := hn₀ (r + 1) (by omega)
  simp only [pressureRate, r.succ_ne_zero, ↓reduceIte] at h
  have := le_ofReal_two_rpow_of_pressureLog_mul_lt _ a ha (r + 1) (by omega) h
  push_cast at this
  exact this

/-- If the external covering number of `Y` is finite, some finite `ε`-cover realizes it. -/
private lemma exists_finite_isCover_encard_eq {ε : NNReal} {Y : Set X}
    (h : Metric.externalCoveringNumber ε Y ≠ ⊤) :
    ∃ C : Set X, C.Finite ∧ Metric.IsCover ε Y C ∧
      C.encard = Metric.externalCoveringNumber ε Y := by
  simp only [Metric.externalCoveringNumber, ne_eq, iInf_eq_top, Set.encard_eq_top_iff,
    not_forall] at h
  obtain ⟨C₀, hC₀, hfin₀⟩ := h
  have : Nonempty { s : Set X // Metric.IsCover ε Y s } := ⟨⟨C₀, hC₀⟩⟩
  obtain ⟨C, hC⟩ := ENat.exists_eq_iInf
    (fun C : { s : Set X // Metric.IsCover ε Y s } ↦ (C : Set X).encard)
  refine ⟨C, ?_, C.2, ?_⟩
  · refine Set.encard_lt_top_iff.mp ?_
    simp only [hC, iInf_lt_top, Set.encard_lt_top_iff, Subtype.exists, exists_prop]
    exact ⟨C₀, hC₀, Set.not_infinite.mp hfin₀⟩
  · rw [hC]
    simp_rw [iInf_subtype, Metric.externalCoveringNumber]

/-- If the external covering number of `Y` at radius `2⁻⁽ʳ⁺¹⁾` is at most `B`, then `Y` is covered
by the radius-`2⁻ʳ` open balls around at most `B` ideal points. -/
private lemma exists_finset_ideal_cover (P : Presentation X) {Y : Set X} {B : ℝ} {r : ℕ}
    (hB : 0 ≤ B)
    (h_cov : (Metric.externalCoveringNumber (Real.toNNReal (dyadicRadius (r + 1))) Y : ℝ≥0∞) ≤
      ENNReal.ofReal B) :
    ∃ F : Finset ℕ, (Y ⊆ ⋃ i ∈ F, Metric.ball (P.ι i) (dyadicRadius r)) ∧ (F.card : ℝ) ≤ B := by
  have hδ : 0 < dyadicRadius (r + 1) := by unfold dyadicRadius; positivity
  have hne : Metric.externalCoveringNumber (Real.toNNReal (dyadicRadius (r + 1))) Y ≠ ⊤ := by
    intro h
    rw [h] at h_cov
    exact absurd h_cov (by simp)
  obtain ⟨C, hCfin, hC, hCeq⟩ := exists_finite_isCover_encard_eq hne
  choose g hg using fun x : X ↦ P.dense.exists_dist_lt x hδ
  refine ⟨hCfin.toFinset.image g, ?_, ?_⟩
  · intro y hy
    obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.mp (hC.subset_iUnion_closedBall hy)
    refine Set.mem_iUnion₂.mpr ⟨g c, Finset.mem_image_of_mem g (hCfin.mem_toFinset.mpr hc), ?_⟩
    rw [Metric.mem_ball]
    have hyc' : dist y c ≤ dyadicRadius (r + 1) := by
      simpa [Real.coe_toNNReal _ hδ.le] using Metric.mem_closedBall.mp hyc
    have hsum : dyadicRadius r = dyadicRadius (r + 1) + dyadicRadius (r + 1) := by
      simp only [dyadicRadius, pow_succ]
      ring
    linarith [dist_triangle y c (P.ι (g c)), hg c]
  · have hcard : (hCfin.toFinset.card : ℝ≥0∞) ≤ ENNReal.ofReal B := by
      have hcast : (Metric.externalCoveringNumber (Real.toNNReal (dyadicRadius (r + 1))) Y :
          ℝ≥0∞) = hCfin.toFinset.card := by
        rw [← hCeq, hCfin.encard_eq_coe_toFinset_card]
        exact ENat.toENNReal_coe _
      rwa [hcast] at h_cov
    have hcard' : (hCfin.toFinset.card : ℝ) ≤ B := by
      simpa using (ENNReal.le_ofReal_iff_toReal_le (ENNReal.natCast_ne_top _) hB).1 hcard
    exact (Nat.cast_le.mpr Finset.card_image_le).trans hcard'

/-- For `a < t`, the bound `2 ^ (a * (r + 1))` is eventually at most `2 ^ (t * r)`. -/
private lemma exists_rpow_succ_le_rpow {a t : ℝ} (hat : a < t) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀, (2 : ℝ) ^ (a * (r + 1 : ℝ)) ≤ (2 : ℝ) ^ (t * r) := by
  obtain ⟨r₀, hr₀⟩ := exists_nat_ge (a / (t - a))
  refine ⟨r₀, fun r hr ↦ Real.rpow_le_rpow_of_exponent_le one_le_two ?_⟩
  have hr' : (r₀ : ℝ) ≤ r := by exact_mod_cast hr
  have := (div_le_iff₀ (sub_pos.2 hat)).1 (hr₀.trans hr')
  nlinarith

/-- A set of upper box dimension below `ofReal t` is covered, at every large dyadic scale `2⁻ʳ`,
by open balls around at most `2 ^ (t * r)` ideal points. -/
private lemma exists_finset_family_ideal_cover (P : Presentation X) (Y : Set X) {t : ℝ}
    (ht : upperBoxDimension Y < ENNReal.ofReal t) :
    ∃ (r₀ : ℕ) (F : ℕ → Finset ℕ), ∀ r ≥ r₀,
      (Y ⊆ ⋃ i ∈ F r, Metric.ball (P.ι i) (dyadicRadius r)) ∧
      ((F r).card : ℝ) ≤ 2 ^ (t * r) := by
  obtain ⟨a, ha, hat, haY⟩ := exists_pos_lt_lt_ofReal ht
  obtain ⟨r₁, hr₁⟩ := eventually_externalCoveringNumber_le ha haY
  obtain ⟨r₂, hr₂⟩ := exists_rpow_succ_le_rpow hat
  have key : ∀ r, ∃ F : Finset ℕ, max r₁ r₂ ≤ r →
      (Y ⊆ ⋃ i ∈ F, Metric.ball (P.ι i) (dyadicRadius r)) ∧ (F.card : ℝ) ≤ 2 ^ (t * r) := by
    intro r
    by_cases hr : max r₁ r₂ ≤ r
    · obtain ⟨F, hF, hcard⟩ :=
        exists_finset_ideal_cover P (by positivity) (hr₁ r ((le_max_left _ _).trans hr))
      exact ⟨F, fun _ ↦ ⟨hF, hcard.trans (hr₂ r ((le_max_right _ _).trans hr))⟩⟩
    · exact ⟨∅, fun h ↦ absurd h hr⟩
  choose F hF using key
  exact ⟨max r₁ r₂, F, fun r hr ↦ hF r hr⟩

/-- The complexities of the injectively encoded pair headers `(i, r)` satisfy Kraft's
inequality. -/
private lemma tsum_inv_pow_oraclePairComplexity_le_one (A : Set ℕ) :
    (∑' p : ℕ × ℕ, (2 : ℝ≥0∞)⁻¹ ^ oraclePairComplexity A p.1 p.2) ≤ 1 := by
  let U := optimalOraclePrefix A
  have hprefix : IsPrefixMachine U := (exists_optimalOraclePrefix_spec A).2.1
  have hstr : (∑' w : BitString, complexityWeight (KP U w [])) ≤ 1 :=
    (ENNReal.tsum_le_tsum (fun w ↦ complexityWeight_KP_le_aprioriMeasure U w [])).trans
      (tsum_aprioriMeasure_le_one U [] hprefix)
  have hinj : Function.Injective (fun p : ℕ × ℕ ↦ pairCode (natBits p.1) (natBits p.2)) := by
    intro p q hpq
    have h := @pairCode_injective (natBits p.1, natBits p.2) (natBits q.1, natBits q.2) hpq
    exact Prod.ext (natBits_injective (congrArg Prod.fst h))
      (natBits_injective (congrArg Prod.snd h))
  have heq : ∀ p : ℕ × ℕ, (2 : ℝ≥0∞)⁻¹ ^ oraclePairComplexity A p.1 p.2 =
      complexityWeight (KP U (pairCode (natBits p.1) (natBits p.2)) []) := by
    intro p
    change (2 : ℝ≥0∞)⁻¹ ^ oraclePrefixComplexityNat A _ [] = _
    rw [← complexityWeight_coe, oraclePrefixComplexity_coe]
    rfl
  simp_rw [heq]
  exact (ENNReal.tsum_comp_le_tsum_of_injective hinj
    (fun w ↦ complexityWeight (KP U w []))).trans hstr

/-- The `M` indices below `M` fit into a block of `log₂ M + 1` bits whose total Kraft mass is at
most one; this includes the empty and the singleton list. -/
private lemma natCast_mul_inv_two_pow_log2_succ_le_one (M : ℕ) :
    (M : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (Nat.log2 M + 1) ≤ 1 := by
  have hM : M ≤ 2 ^ (Nat.log2 M + 1) := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.lt_pow_succ_log_self (by decide) M).le
  have hcast : (M : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (Nat.log2 M + 1) := by exact_mod_cast hM
  calc
    _ ≤ (2 : ℝ≥0∞) ^ (Nat.log2 M + 1) * (2 : ℝ≥0∞)⁻¹ ^ (Nat.log2 M + 1) :=
      mul_le_mul' hcast le_rfl
    _ = 1 := by rw [← ENNReal.inv_pow, ENNReal.mul_inv_cancel (by simp) (by simp)]

/-- Every stream of optional requests is computable from a single oracle that stores its codes in
an integer table. -/
private lemma exists_oracle_computableIn_requests (req : ℕ → Option (BitString × ℕ)) :
    ∃ A : Set ℕ, ComputableIn {charOracle A} req := by
  classical
  let v : ℕ → ℕ → ℤ := fun n _ ↦ (Encodable.encode (req n) : ℤ)
  obtain ⟨A, _, _, hv⟩ := oracle_joins_tables ∅ (fun _ ↦ ∅) v
  have hcode : ComputableIn {charOracle A} (fun n ↦ Encodable.encode (req n)) := by
    have h := ComputableReals.primrec_intToNat.to_comp.computableIn.comp
      (hv.comp (Computable.id.pair (Computable.const 0)).computableIn)
    simpa only [v, Int.toNat_natCast, id_eq] using h
  have hd : Computable (fun n : ℕ ↦ (Encodable.decode (α := Option (BitString × ℕ)) n).getD none) :=
    Computable.option_getD Computable.decode (Computable.const none)
  exact ⟨A, (hd.computableIn.comp hcode).of_eq fun n ↦ by simp⟩

/-- For a family `F i r` of finite lists, one oracle realizes every entry `x ∈ F i r` with
complexity at most that of the header `(i, r)` plus `log₂ |F i r| + 1`, up to a constant: the
header weight is distributed among the entries and the oracle Kraft–Chaitin theorem applies. -/
private lemma exists_oracle_natComplexity_le_header_add_log (F : ℕ → ℕ → Finset ℕ) :
    ∃ A : Set ℕ, ∃ c : ℕ, ∀ i r x : ℕ, x ∈ F i r →
      oracleNatComplexity A x ≤ oraclePairComplexity ∅ i r +
        (Nat.log2 (F i r).card + 1) + c := by
  classical
  let e : (ℕ × ℕ) × ℕ ≃ ℕ := (Equiv.prodCongr Nat.pairEquiv (Equiv.refl ℕ)).trans Nat.pairEquiv
  let R : (ℕ × ℕ) × ℕ → Option (BitString × ℕ) := fun p ↦
    if p.2 ∈ F p.1.1 p.1.2 then
      some (natBits p.2, oraclePairComplexity ∅ p.1.1 p.1.2 +
        (Nat.log2 (F p.1.1 p.1.2).card + 1)) else none
  let req : ℕ → Option (BitString × ℕ) := fun n ↦ R (e.symm n)
  have hmass : oracleRequestMass req ≤ 1 := by
    unfold oracleRequestMass
    rw [← e.tsum_eq]
    simp only [req, Equiv.symm_apply_apply]
    rw [ENNReal.tsum_prod']
    refine le_trans ?_ (tsum_inv_pow_oraclePairComplexity_le_one ∅)
    refine ENNReal.tsum_le_tsum fun p ↦ ?_
    have hrow : (∑' x : ℕ, (R (p, x)).elim 0 (fun r ↦ (2 : ℝ≥0∞)⁻¹ ^ r.2)) =
        (F p.1 p.2).card * (2 : ℝ≥0∞)⁻¹ ^
          (oraclePairComplexity ∅ p.1 p.2 + (Nat.log2 (F p.1 p.2).card + 1)) := by
      rw [tsum_eq_sum (s := F p.1 p.2) (fun x hx ↦ by simp [R, hx])]
      calc
        _ = ∑ x ∈ F p.1 p.2, (2 : ℝ≥0∞)⁻¹ ^
            (oraclePairComplexity ∅ p.1 p.2 + (Nat.log2 (F p.1 p.2).card + 1)) :=
          Finset.sum_congr rfl fun x hx ↦ by simp [R, hx]
        _ = _ := by simp
    rw [hrow, pow_add]
    calc
      _ = (2 : ℝ≥0∞)⁻¹ ^ oraclePairComplexity ∅ p.1 p.2 *
          ((F p.1 p.2).card * (2 : ℝ≥0∞)⁻¹ ^ (Nat.log2 (F p.1 p.2).card + 1)) := by ring
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ oraclePairComplexity ∅ p.1 p.2 * 1 :=
        mul_le_mul' le_rfl (natCast_mul_inv_two_pow_log2_succ_le_one _)
      _ = _ := mul_one _
  obtain ⟨A, hreq⟩ := exists_oracle_computableIn_requests req
  obtain ⟨c, hc⟩ := oracle_kraftChaitin_bound A req hreq hmass
  refine ⟨A, c, fun i r x hx ↦ ?_⟩
  exact hc (e ((i, r), x)) (natBits x) (oraclePairComplexity ∅ i r + (Nat.log2 (F i r).card + 1))
    (by simp [req, R, hx])

/-- If the lists `F i r` have at most `2 ^ (t * r)` entries for large `r`, one oracle bounds the
complexity of every entry `x ∈ F i r` by `t * r + 2 log₂ (r + 1) + c i`, where the constant `c i`
depends only on `i` and `r` is large. -/
private lemma exists_oracle_natComplexity_le_of_card_le
    (F : ℕ → ℕ → Finset ℕ) (t : ℝ)
    (h_size : ∀ i, ∃ r₀, ∀ r ≥ r₀, ((F i r).card : ℝ) ≤ 2 ^ (t * r)) :
    ∃ A : Set ℕ, ∃ c : ℕ → ℝ,
      ∀ i, ∃ r₀, ∀ r ≥ r₀, ∀ x ∈ F i r,
        (oracleNatComplexity A x : ℝ) ≤ t * r + 2 * Real.logb 2 ((r : ℝ) + 1) + c i := by
  obtain ⟨A, c, hc⟩ := exists_oracle_natComplexity_le_header_add_log F
  obtain ⟨d, hd⟩ := oracle_tuple_bounds_overhead ∅
  refine ⟨A, fun i ↦ (oracleNatComplexity ∅ i : ℝ) + (d : ℝ) + (c : ℝ) + 1, fun i ↦ ?_⟩
  obtain ⟨r₀, hr₀⟩ := h_size i
  refine ⟨r₀, fun r hr x hx ↦ ?_⟩
  have hcomp : (oracleNatComplexity A x : ℝ) ≤
      (oraclePairComplexity ∅ i r : ℝ) + ((Nat.log2 (F i r).card : ℝ) + 1) + (c : ℝ) := by
    exact_mod_cast hc i r x hx
  have hpos : (0 : ℝ) < (F i r).card := by exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩
  have hlog : Real.logb 2 ((F i r).card : ℝ) ≤ t * (r : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num) hpos).mpr (hr₀ r hr)
  have hbits : (Nat.log2 (F i r).card : ℝ) ≤ t * (r : ℝ) := (Real.log2_le_logb _).trans hlog
  have hheader := hd i r
  linarith

/-- The upper static point dimension is the upper limit of the normalized precision complexity
along the dyadic radii `2⁻ʳ`. -/
private lemma staticPointDimensions_snd_eq_limsup_dyadicRadius
    (P : Presentation X) (A : Set ℕ) (y : X) :
    (staticPointDimensions P A y).2 =
      limsup (fun r : ℕ ↦ normalizedPrecisionComplexity P A y (dyadicRadius r)) atTop :=
  dimension_along_scales_upper P A y dyadicRadius
    (fun m ↦ by unfold dyadicRadius; positivity)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    tendsto_log_dyadicRadius_succ_div

/-- The logarithmic overhead is sublinear: `log (r + 1) / r → 0`. -/
private lemma tendsto_log_succ_div_natCast :
    Tendsto (fun r : ℕ ↦ Real.log ((r : ℝ) + 1) / (r : ℝ)) atTop (𝓝 0) := by
  have hsucc : Tendsto (fun r : ℕ ↦ (r : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun r : ℕ ↦ Real.log ((r : ℝ) + 1) / ((r : ℝ) + 1)) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hsucc).tendsto_div_nhds_zero
  have h2 : Tendsto (fun r : ℕ ↦ 1 + 1 / (r : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
  have h3 := h1.mul h2
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  have h0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have h' : (r : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- The normalized error `t + (2 log₂ (r + 1) + c) / r` tends to `t`. -/
private lemma tendsto_const_add_logb_overhead_div (t c : ℝ) :
    Tendsto (fun r : ℕ ↦ t + (2 * Real.logb 2 ((r : ℝ) + 1) + c) / (r : ℝ)) atTop (𝓝 t) := by
  have h1 : Tendsto (fun r : ℕ ↦ (2 / Real.log 2) * (Real.log ((r : ℝ) + 1) / (r : ℝ)) +
      c / (r : ℝ)) atTop (𝓝 ((2 / Real.log 2) * 0 + 0)) :=
    (tendsto_log_succ_div_natCast.const_mul (2 / Real.log 2)).add
      (tendsto_const_div_atTop_nhds_zero_nat c)
  have h2 := h1.const_add t
  simp only [mul_zero, add_zero] at h2
  refine h2.congr fun r ↦ ?_
  simp only [Real.logb]
  ring

/-- The precision complexity at radius `δ` is at most the complexity of any ideal point within
`δ`. -/
private lemma precisionComplexityNat_le_oracleNatComplexity_of_dist_lt
    (P : Presentation X) (A : Set ℕ) (y : X) (δ : ℝ) (i : ℕ) (hi : dist (P.ι i) y < δ) :
    precisionComplexityNat P A y δ ≤ oracleNatComplexity A i := by
  have hle : precisionComplexity P A y δ ≤ (oracleNatComplexity A i : ENat) := by
    unfold precisionComplexity
    exact iInf_le_of_le i (iInf_le_of_le hi le_rfl)
  unfold precisionComplexityNat
  exact (ENat.toNat_le_toNat hle (ENat.natCast_ne_top _)).trans_eq (ENat.toNat_natCast _)

/-- If the ideal points in the covers of `Y` at all large dyadic scales have oracle complexity at
most `t * r + 2 log₂ (r + 1) + c`, then every point of `Y` has upper static dimension at most
`t`: the logarithmic overhead vanishes after normalization. -/
private lemma staticPointDimensions_snd_le_of_cover_complexity
    (P : Presentation X) (Y : Set X) (A : Set ℕ) (t : ℝ) (r₀ : ℕ) (F : ℕ → Finset ℕ) (c : ℝ)
    (h_cover : ∀ r ≥ r₀, Y ⊆ ⋃ i ∈ F r, Metric.ball (P.ι i) (dyadicRadius r))
    (h_bound : ∀ r ≥ r₀, ∀ x ∈ F r,
      (oracleNatComplexity A x : ℝ) ≤ t * r + 2 * Real.logb 2 ((r : ℝ) + 1) + c) :
    ∀ y ∈ Y, (staticPointDimensions P A y).2 ≤ ENNReal.ofReal t := by
  intro y hy
  rw [staticPointDimensions_snd_eq_limsup_dyadicRadius P A y]
  have h_ev : ∀ᶠ r : ℕ in atTop, normalizedPrecisionComplexity P A y (dyadicRadius r) ≤
      ENNReal.ofReal (t + (2 * Real.logb 2 ((r : ℝ) + 1) + c) / (r : ℝ)) := by
    filter_upwards [eventually_ge_atTop (max r₀ 1)] with r hr
    have hr₀ : r₀ ≤ r := (le_max_left _ _).trans hr
    have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
    rw [normalizedPrecisionComplexity_dyadicRadius_eq_ofReal_div P A y r hr1]
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨i, hiF, hiball⟩ := Set.mem_iUnion₂.mp (h_cover r hr₀ hy)
    have hdist : dist (P.ι i) y < dyadicRadius r := by
      rw [dist_comm]
      exact Metric.mem_ball.mp hiball
    have hcost : (precisionComplexityNat P A y (dyadicRadius r) : ℝ) ≤
        t * r + 2 * Real.logb 2 ((r : ℝ) + 1) + c := by
      have h1 := precisionComplexityNat_le_oracleNatComplexity_of_dist_lt P A y _ i hdist
      exact (by exact_mod_cast h1 : (precisionComplexityNat P A y (dyadicRadius r) : ℝ) ≤
        (oracleNatComplexity A i : ℝ)).trans (h_bound r hr₀ i hiF)
    have e : (t + (2 * Real.logb 2 ((r : ℝ) + 1) + c) / (r : ℝ)) * r =
        t * r + 2 * Real.logb 2 ((r : ℝ) + 1) + c := by
      field_simp
      ring
    rw [div_le_iff₀ hrpos, e]
    exact hcost
  exact (limsup_le_limsup h_ev).trans
    (ENNReal.tendsto_ofReal (tendsto_const_add_logb_overhead_div t c)).limsup_eq.le

/-- A bounded additive cost in the precision complexity disappears from the normalized upper
limit. -/
private lemma limsup_div_le_of_le_add (f g : ℝ → ℕ) (c : ℕ)
    (hfg : ∀ δ : ℝ, 0 < δ → g δ ≤ f δ + c) :
    limsup (fun δ ↦ (g δ : ℝ≥0∞) / ENNReal.ofReal (-Real.logb 2 δ)) (𝓝[>] (0 : ℝ)) ≤
      limsup (fun δ ↦ (f δ : ℝ≥0∞) / ENNReal.ofReal (-Real.logb 2 δ)) (𝓝[>] (0 : ℝ)) := by
  let L := 𝓝[>] (0 : ℝ)
  let t (δ : ℝ) := -Real.logb 2 δ
  have ht : Tendsto t L atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (by norm_num))
  let e (δ : ℝ) := ENNReal.ofReal ((c : ℝ) / t δ)
  have he_zero : Tendsto e L (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (Tendsto.const_div_atTop ht (c : ℝ))
  have h_bound : ∀ᶠ δ in L, (g δ : ℝ≥0∞) / ENNReal.ofReal (t δ) ≤
      (f δ : ℝ≥0∞) / ENNReal.ofReal (t δ) + e δ := by
    filter_upwards [self_mem_nhdsWithin, ht.eventually (eventually_gt_atTop 0)] with δ hδ ht_pos
    have h_e_eq : e δ = (c : ℝ≥0∞) / ENNReal.ofReal (t δ) := by
      simp only [e, ENNReal.ofReal_div_of_pos ht_pos, ENNReal.ofReal_natCast]
    rw [h_e_eq, ← ENNReal.add_div]
    exact ENNReal.div_le_div_right (by exact_mod_cast hfg δ hδ) _
  calc _ ≤ limsup (fun δ ↦ (f δ : ℝ≥0∞) / ENNReal.ofReal (t δ) + e δ) L :=
        limsup_le_limsup h_bound (by isBoundedDefault) (by isBoundedDefault)
    _ = _ := ENNReal.limsup_add_of_right_tendsto_zero he_zero _

/-- The upper static point dimension does not increase along Turing reducibility of oracles. -/
private lemma staticPointDimensions_snd_le_of_turingReducible (P : Presentation X) {A B : Set ℕ}
    (hAB : charOracle A ≤ᵀ charOracle B) (x : X) :
    (staticPointDimensions P B x).2 ≤ (staticPointDimensions P A x).2 := by
  obtain ⟨c, hc⟩ := oracle_monotonicity A B hAB
  have h_c_nat : ∀ i, oracleNatComplexity B i ≤ oracleNatComplexity A i + c :=
    fun i ↦ hc (natBits i)
  exact limsup_div_le_of_le_add (precisionComplexityNat P A x) (precisionComplexityNat P B x) c
    (precisionComplexityNat_le_of_oracleNatComplexity_le P A B c h_c_nat x)

/-- For every real `s` above the packing dimension of `Z`, some oracle bounds the upper static
dimensions of all points of `Z` by `s`. -/
private lemma exists_oracle_snd_le_ofReal [SeparableSpace X] (P : Presentation X) (Z : Set X)
    (s : ℝ) (hs : metricPackingDimension Z < ENNReal.ofReal s) :
    ∃ A : Set ℕ, (⨆ x ∈ Z, (staticPointDimensions P A x).2) ≤ ENNReal.ofReal s := by
  obtain ⟨t, ht_pos, hts, ht⟩ := exists_pos_lt_lt_ofReal hs
  obtain ⟨Z_cov, hZ_sub, hZ_dim⟩ :=
    exists_cover_upperBoxDimension_lt Z t (by rwa [← packingEqModifiedUpperBox Z])
  choose r₀ F hF using fun i ↦ exists_finset_family_ideal_cover P (Z_cov i) (hZ_dim i)
  obtain ⟨A, c, hA⟩ := exists_oracle_natComplexity_le_of_card_le F t
    (fun i ↦ ⟨r₀ i, fun r hr ↦ (hF i r hr).2⟩)
  refine ⟨A, le_trans (iSup₂_le fun x hx ↦ ?_) (ENNReal.ofReal_le_ofReal hts.le)⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hZ_sub hx)
  obtain ⟨r₁, hr₁⟩ := hA i
  exact staticPointDimensions_snd_le_of_cover_complexity P (Z_cov i) A t (max (r₀ i) r₁) (F i)
    (c i) (fun r hr ↦ (hF i r ((le_max_left _ _).trans hr)).1)
    (fun r hr x hx ↦ hr₁ r ((le_max_right _ _).trans hr) x hx) x hi

/-- An oracle achieves the upper bound by specified-radius packing dimension.
Blueprint node `conf:packing-achieving`. -/
theorem packingAchievingOracle (P : Presentation X) (Z : Set X) :
    ∃ A : Set ℕ, (⨆ x ∈ Z, (staticPointDimensions P A x).2) ≤ metricPackingDimension Z := by
  by_cases h_inf : metricPackingDimension Z = ⊤
  · exact ⟨∅, h_inf ▸ le_top⟩
  obtain ⟨s, hs_gt, hs_tendsto⟩ := exists_seq_lt_ofReal_tendsto (lt_top_iff_ne_top.mpr h_inf)
  have : SeparableSpace X := SeparableSpace.of_denseRange P.ι P.dense
  choose A hA using fun n ↦ exists_oracle_snd_le_ofReal P Z (s n) (hs_gt n)
  refine ⟨oracleCountableJoin A, ge_of_tendsto hs_tendsto (Eventually.of_forall fun n ↦ ?_)⟩
  exact (iSup₂_mono fun x _ ↦
    staticPointDimensions_snd_le_of_turingReducible P (oracle_joins_countable A n) x).trans (hA n)

/-- The packing achieving bound persists on the upper cone of an achieving oracle.
Blueprint node `conf:packing-achieving`. -/
theorem packingAchievingOracle_stable (P : Presentation X) (Z : Set X) (A B : Set ℕ)
    (hA : (⨆ x ∈ Z, (staticPointDimensions P A x).2) ≤ metricPackingDimension Z)
    (hAB : charOracle A ≤ᵀ charOracle B) :
    (⨆ x ∈ Z, (staticPointDimensions P B x).2) ≤ metricPackingDimension Z :=
  (iSup₂_mono fun x _ ↦ staticPointDimensions_snd_le_of_turingReducible P hAB x).trans hA

/-- Classical Hausdorff dimension is the infimum of all-oracle lower point suprema.
Attainment is supplied by `classicalPointToSet_attained`. Blueprint node `conf:classical-pts`. -/
theorem classicalPointToSet (P : Presentation X) (Z : Set X) :
    _root_.dimH Z = ⨅ A : Set ℕ, ⨆ x ∈ Z, (staticPointDimensions P A x).1 := by
  refine le_antisymm (le_iInf fun A ↦ hausdorffLeSupPointDimension P Z A) ?_
  obtain ⟨A, hA⟩ := hausdorffAchievingOracle P Z
  exact (iInf_le (fun A : Set ℕ ↦ ⨆ x ∈ Z, (staticPointDimensions P A x).1) A).trans hA

/-- Classical specified-radius packing dimension is the corresponding upper point infimum.
Blueprint node `conf:classical-pts`. -/
theorem classicalPointToSet_upper (P : Presentation X) (Z : Set X) :
    metricPackingDimension Z = ⨅ A : Set ℕ, ⨆ x ∈ Z, (staticPointDimensions P A x).2 := by
  refine le_antisymm (le_iInf fun A ↦ packingLeSupPointDimension P Z A) ?_
  obtain ⟨A, hA⟩ := packingAchievingOracle P Z
  exact (iInf_le (fun A : Set ℕ ↦ ⨆ x ∈ Z, (staticPointDimensions P A x).2) A).trans hA

/-- The Hausdorff infimum can be restricted to any prescribed upper oracle cone.
Blueprint node `conf:classical-pts`. -/
theorem classicalPointToSet_cone (P : Presentation X) (Z : Set X) (A₀ : Set ℕ) :
    _root_.dimH Z = ⨅ A : Set ℕ, ⨅ (_ : charOracle A₀ ≤ᵀ charOracle A),
      ⨆ x ∈ Z, (staticPointDimensions P A x).1 := by
  refine le_antisymm (le_iInf fun A ↦ le_iInf fun _ ↦ hausdorffLeSupPointDimension P Z A) ?_
  obtain ⟨A_H, hH⟩ := hausdorffAchievingOracle P Z
  have hH' : charOracle A_H ≤ᵀ charOracle (oracleJoin A_H A₀) := by
    simpa using oracle_joins A_H A₀
  have hA₀' : charOracle A₀ ≤ᵀ charOracle (oracleJoin A_H A₀) := by
    simpa using oracle_joins_right A_H A₀
  have hbound := hausdorffAchievingOracle_stable P Z A_H _ hH hH'
  exact le_trans (iInf_le_of_le (oracleJoin A_H A₀) (iInf_le_of_le hA₀' le_rfl)) hbound

/-- The packing infimum can be restricted to the same arbitrary upper oracle cone.
Blueprint node `conf:classical-pts`. -/
theorem classicalPointToSet_cone_upper (P : Presentation X) (Z : Set X) (A₀ : Set ℕ) :
    metricPackingDimension Z = ⨅ A : Set ℕ, ⨅ (_ : charOracle A₀ ≤ᵀ charOracle A),
      ⨆ x ∈ Z, (staticPointDimensions P A x).2 := by
  refine le_antisymm (le_iInf fun A ↦ le_iInf fun _ ↦ packingLeSupPointDimension P Z A) ?_
  obtain ⟨A₁, hA₁⟩ := packingAchievingOracle P Z
  have hA₀A : charOracle A₀ ≤ᵀ charOracle (oracleJoin A₀ A₁) := oracle_joins A₀ A₁
  have hA₁A : charOracle A₁ ≤ᵀ charOracle (oracleJoin A₀ A₁) := oracle_joins_right A₀ A₁
  have hbound := packingAchievingOracle_stable P Z A₁ _ hA₁ hA₁A
  exact le_trans (iInf_le_of_le (oracleJoin A₀ A₁) (iInf_le_of_le hA₀A le_rfl)) hbound

/-- Above any baseline, one oracle and all its extensions attain both classical minima.
Blueprint node `conf:classical-pts`. -/
theorem classicalPointToSet_attained (P : Presentation X) (Z : Set X) (A₀ : Set ℕ) :
    ∃ A : Set ℕ, charOracle A₀ ≤ᵀ charOracle A ∧
      ∀ B : Set ℕ, charOracle A ≤ᵀ charOracle B →
        _root_.dimH Z = (⨆ x ∈ Z, (staticPointDimensions P B x).1) ∧
        metricPackingDimension Z = ⨆ x ∈ Z, (staticPointDimensions P B x).2 := by
  obtain ⟨A_H, hH⟩ := hausdorffAchievingOracle P Z
  obtain ⟨A_P, hP⟩ := packingAchievingOracle P Z
  refine ⟨oracleJoin (oracleJoin A_H A_P) A₀, oracle_joins_right (oracleJoin A_H A_P) A₀,
    fun B hAB ↦ ?_⟩
  have hbase : charOracle (oracleJoin A_H A_P) ≤ᵀ charOracle B :=
    (oracle_joins (oracleJoin A_H A_P) A₀).trans hAB
  exact ⟨le_antisymm (hausdorffLeSupPointDimension P Z B)
      (hausdorffAchievingOracle_stable P Z A_H B hH ((oracle_joins A_H A_P).trans hbase)),
    le_antisymm (packingLeSupPointDimension P Z B)
      (packingAchievingOracle_stable P Z A_P B hP ((oracle_joins_right A_H A_P).trans hbase))⟩

end Kolmogorov.PointToSet
