/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Upper.UniformNets

/-!
# Oracle attainment for the upper Barreira-Schmeling dimension

This module closes the proof of Main B (`bs:point-to-set`) for the Barreira-Schmeling
dimensions of a set `Z` of points with positive lower Birkhoff average.  It proves

* `pointwiseUpperBSLeEffective` (blueprint node `bs:effective-upper-lower`): an `A`-c.e. uniform
  `s`-net for `Z` bounds the upper pointwise dimension of every point of `Z` by `s`.  The proof
  truncates the net to slices with large Birkhoff sums, bounds the total `2 ^ (-t U)`-mass of the
  truncation by a geometric series, and applies the relative coding theorem to the resulting
  upper semicomputable cost;
* `effectiveUpperBSEqSup` (node `bs:effective-upper-equality`): for admissible oracles the
  effective upper dimension of `Z` is the supremum of the upper pointwise dimensions;
* `bsOracleAttainment` and `bsOracleAttainment_upper` (node `bs:oracle-attainment`): for each
  of the lower and upper BS dimension there is an admissible oracle `A₀` such that every oracle
  above `A₀` is admissible and has effective dimension equal to the classical dimension.  The
  oracle is obtained by joining the characteristic sets of classical null covers (respectively
  uniform nets) of exponents decreasing to the classical dimension;
* `bsPointToSet_all_oracles` (node `bs:point-to-set`): for an arbitrary oracle `A` the classical
  dimension is bounded by the supremum of the pointwise `A`-dimensions.

The last theorem is the lower bound in the point-to-set principle `bsPointToSet`, which is
assembled from these results in `KolmogorovMathlib.PointToSet.BSDimension.Upper`.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-- A finite upper limit of a sequence of extended nonnegative reals gives a finite bound on
all sufficiently late terms. -/
private lemma exists_eventually_le_of_limsup_lt_top (f : ℕ → ℝ≥0∞)
    (hf : limsup f atTop < ⊤) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∃ N : ℕ, ∀ n ≥ N, f n ≤ M := by
  obtain ⟨M, hM, hMtop⟩ := exists_between hf
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hM)
  exact ⟨M, hMtop, N, fun n hn ↦ (hN n hn).le⟩

/-- After a positive linear truncation, a strict exponent increase makes the mass over all late
orders finite, by comparison with a geometric series. -/
private lemma tsum_rpow_truncated_lt_top
    (v : ℕ → ℕ → ℝ) (F : ℕ → Set ℕ) (s t δ : ℝ) (hst : s < t)
    (hδ : 0 < δ) (N₀ : ℕ) (M : ℝ≥0∞) (hM : M < ⊤)
    (hslice : ∀ n ≥ N₀, (∑' i : F n, (2 : ℝ≥0∞) ^ (-s * v n i)) ≤ M) :
    (∑' z : {ni : ℕ × ℕ // N₀ ≤ ni.1 ∧ ni.2 ∈ F ni.1 ∧
        δ * ni.1 / 2 < v ni.1 ni.2},
      (2 : ℝ≥0∞) ^ (-t * v z.val.1 z.val.2)) < ⊤ := by
  let D : ℕ → ℕ → Prop := fun n i ↦ N₀ ≤ n ∧ i ∈ F n ∧ δ * n / 2 < v n i
  let q : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (-(t - s) * δ / 2)
  have hexp : -(t - s) * δ / 2 < 0 := by
    have := mul_pos (sub_pos.mpr hst) hδ
    linarith
  have hq : q < 1 := ENNReal.rpow_lt_one_of_one_lt_of_neg
    (by norm_num : (1 : ℝ≥0∞) < 2) hexp
  have hpoint (n i : ℕ) (hi : D n i) :
      (2 : ℝ≥0∞) ^ (-t * v n i) ≤ q ^ n * (2 : ℝ≥0∞) ^ (-s * v n i) := by
    have he : -(t - s) * v n i ≤ (-(t - s) * δ / 2) * n := by
      have hh := mul_le_mul_of_nonpos_left hi.2.2.le (neg_nonpos.mpr (sub_pos.mpr hst).le)
      nlinarith
    calc
      (2 : ℝ≥0∞) ^ (-t * v n i) =
          (2 : ℝ≥0∞) ^ (-(t - s) * v n i) * (2 : ℝ≥0∞) ^ (-s * v n i) := by
        rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
        congr 1
        ring
      _ ≤ (2 : ℝ≥0∞) ^ ((-(t - s) * δ / 2) * n) * (2 : ℝ≥0∞) ^ (-s * v n i) := by
        exact mul_le_mul_left
          (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) he) _
      _ = q ^ n * (2 : ℝ≥0∞) ^ (-s * v n i) := by
        rw [ENNReal.rpow_mul_natCast]
  have hinner (n : ℕ) :
      (∑' i : {i : ℕ // D n i}, (2 : ℝ≥0∞) ^ (-t * v n i)) ≤ q ^ n * M := by
    by_cases hn : N₀ ≤ n
    · calc
        (∑' i : {i : ℕ // D n i}, (2 : ℝ≥0∞) ^ (-t * v n i)) ≤
            ∑' i : {i : ℕ // D n i}, q ^ n * (2 : ℝ≥0∞) ^ (-s * v n i) :=
          ENNReal.tsum_le_tsum fun i ↦ hpoint n i i.property
        _ = q ^ n * ∑' i : {i : ℕ // D n i}, (2 : ℝ≥0∞) ^ (-s * v n i) := by
          rw [ENNReal.tsum_mul_left]
        _ ≤ q ^ n * ∑' i : F n, (2 : ℝ≥0∞) ^ (-s * v n i) := by
          gcongr
          exact ENNReal.tsum_comp_le_tsum_of_injective
            (f := fun i : {i : ℕ // D n i} ↦ (⟨i.val, i.property.2.1⟩ : F n))
            (fun a b h ↦ Subtype.ext (congrArg (fun z : F n ↦ z.val) h))
            (fun i : F n ↦ (2 : ℝ≥0∞) ^ (-s * v n i))
        _ ≤ q ^ n * M := by gcongr; exact hslice n hn
    · have : IsEmpty {i : ℕ // D n i} := ⟨fun i ↦ hn i.property.1⟩
      simp
  have heq :
      (∑' z : {ni : ℕ × ℕ // D ni.1 ni.2}, (2 : ℝ≥0∞) ^ (-t * v z.val.1 z.val.2)) =
        ∑' n, ∑' i : {i : ℕ // D n i}, (2 : ℝ≥0∞) ^ (-t * v n i) := by
    rw [← ENNReal.tsum_sigma]
    exact (Equiv.subtypeProdEquivSigmaSubtype D).tsum_eq
      (fun z : Σ n, {i : ℕ // D n i} ↦ (2 : ℝ≥0∞) ^ (-t * v z.1 z.2))
  change (∑' z : {ni : ℕ × ℕ // D ni.1 ni.2},
    (2 : ℝ≥0∞) ^ (-t * v z.val.1 z.val.2)) < ⊤
  rw [heq]
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum hinner)
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_lt_top (tsum_geometric_lt_top.mpr hq) hM

/-- A positive rational multiple of a computable real family is upper semicomputable on any
enumerable domain. -/
private lemma isUpperSemicomputableOnIn_ratCast_mul
    {α : Type*} [Primcodable α] (A : Set ℕ) (v : α → ℝ)
    (hv : IsComputableRealFamilyIn A v) (D : α → Prop) (hD : IsREIn A D)
    (t : ℚ) (ht : 0 < t) :
    IsUpperSemicomputableOnIn A D (fun a ↦ (t : ℝ) * v a.val) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have heq (a : α) (q : ℚ) :
      v a < ((q * t⁻¹ : ℚ) : ℝ) ↔ (t : ℝ) * v a < (q : ℝ) := by
    push_cast
    rw [← div_eq_mul_inv, lt_div_iff₀ htR, mul_comm (v a)]
  let U : α × ℚ → Prop := fun aq ↦ D aq.1 ∧ v aq.1 < ((aq.2 * t⁻¹ : ℚ) : ℝ)
  have hU : IsREIn A U := by
    apply IsREIn.and
    · exact hD.comp Computable.fst.computableIn
    · exact (birkhoff_computableIn_lt A v hv).comp
        (f := fun aq : α × ℚ ↦ (aq.1, aq.2 * t⁻¹))
        (Computable.fst.pair
          (computable₂_ratMul.comp Computable.snd (Computable.const t⁻¹))).computableIn
  refine ⟨U, hU, ?_, ?_⟩
  · intro a q ha
    exact ⟨ha.1, (heq a q).mp ha.2⟩
  · intro a ε hε
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (lt_add_of_pos_right ((t : ℝ) * v a.val) hε)
    exact ⟨q, ⟨a.property, (heq a.val q).mpr hq₁⟩, hq₂⟩

/-- An effective encoding with a left inverse transports an upper semicomputable cost with
finite total mass to bit strings, where the relative coding theorem bounds the oracle
complexity of the code by the cost plus a constant. -/
private lemma exists_oracleComplexity_le_of_tsum_lt_top
    {α : Type*} [Primcodable α] (A : Set ℕ) (D : α → Prop) (hD : IsREIn A D)
    (v : α → ℝ) (hv : IsUpperSemicomputableOnIn A D (fun a ↦ v a.val))
    (hmass : (∑' a : Subtype D, (2 : ℝ≥0∞) ^ (-v a.val)) < ⊤)
    (code : α → BitString) (decode : BitString → α)
    (hcode : Computable code) (hleft : Function.LeftInverse decode code) :
    ∃ c : ℕ, ∀ a, D a → (oracleComplexity A (code a) : ℝ) ≤ v a + c := by
  let F : BitString → Prop := fun w ↦ ∃ a, D a ∧ code a = w
  have hF : IsREIn A F := hD.image hcode
  let g : Subtype F → ℝ := fun w ↦ v (decode w.val)
  obtain ⟨U, hU, hUsound, hUclose⟩ := hv
  let V : BitString × ℚ → Prop := fun wq ↦
    ∃ aq : α × ℚ, U aq ∧ (code aq.1, aq.2) = wq
  have hV : IsREIn A V := hU.image (g := fun aq : α × ℚ ↦ (code aq.1, aq.2))
    ((hcode.comp Computable.fst).pair Computable.snd)
  have hg : IsUpperSemicomputableOnIn A F g := by
    refine ⟨V, hV, ?_, ?_⟩
    · intro w q hw
      obtain ⟨⟨a, r⟩, ha, he⟩ := hw
      obtain ⟨haD, hav⟩ := hUsound a r ha
      have hwcode : code a = w := congrArg Prod.fst he
      have hrq : r = q := congrArg Prod.snd he
      refine ⟨⟨a, haD, hwcode⟩, ?_⟩
      simpa [g, ← hwcode, hleft a, hrq] using hav
    · intro w ε hε
      obtain ⟨a, haD, haw⟩ := w.property
      obtain ⟨q, hqU, hq⟩ := hUclose ⟨a, haD⟩ ε hε
      refine ⟨q, ⟨(a, q), hqU, ?_⟩, ?_⟩
      · exact Prod.ext haw rfl
      · simpa [g, ← haw, hleft a] using hq
  have hdecode (w : Subtype F) : D (decode w.val) := by
    obtain ⟨a, ha, haw⟩ := w.property
    simpa [← haw, hleft a] using ha
  let dec : Subtype F → Subtype D := fun w ↦ ⟨decode w.val, hdecode w⟩
  have hdecinj : Function.Injective dec := by
    intro w z he
    obtain ⟨a, haD, haw⟩ := w.property
    obtain ⟨b, hbD, hbz⟩ := z.property
    have hab : a = b := by
      have hd := congrArg (fun a : Subtype D ↦ a.val) he
      simpa [dec, ← haw, ← hbz, hleft a, hleft b] using hd
    exact Subtype.ext (haw.symm.trans ((congrArg code hab).trans hbz))
  have hgmass : (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w)) < ⊤ :=
    lt_of_le_of_lt (ENNReal.tsum_comp_le_tsum_of_injective hdecinj
      (fun a : Subtype D ↦ (2 : ℝ≥0∞) ^ (-v a.val))) hmass
  obtain ⟨c, hc⟩ := oracle_coding_finite_mass A F g hF hg _ le_rfl hgmass
  refine ⟨c, fun a ha ↦ ?_⟩
  have h := hc ⟨code a, ⟨a, ha, rfl⟩⟩
  simpa [g, hleft a] using h

/-- Admissibility and enumerability make the positive rational truncation an effective coding
domain.  Finite total mass then bounds the complexity of each ideal index by its rational cost
plus a constant independent of the index and the order. -/
private lemma exists_oracleNatComplexity_le_of_truncated_mass
    (P : Presentation X) (T : X → X) (u : X → ℝ) (A : Set ℕ)
    (hA : IsAdmissible P T (fun _ : Fin 1 => u) A)
    (E : Set (ℕ × ℕ × ℕ × ℕ)) (hRE : IsREIn A E) (p k N₀ : ℕ)
    (t δ : ℚ) (ht : 0 < t)
    (hmass : (∑' z : {ni : ℕ × ℕ // N₀ ≤ ni.1 ∧ (ni.2, ni.1, p, k) ∈ E ∧
        (δ : ℝ) * ni.1 / 2 < birkhoffSum T u ni.1 (P.ι ni.2)},
      (2 : ℝ≥0∞) ^ (-(t : ℝ) * birkhoffSum T u z.val.1 (P.ι z.val.2))) < ⊤) :
    ∃ c : ℕ, ∀ n ≥ N₀, ∀ i, (i, n, p, k) ∈ E →
      (δ : ℝ) * n / 2 < birkhoffSum T u n (P.ι i) →
      (oracleNatComplexity A i : ℝ) ≤ (t : ℝ) * birkhoffSum T u n (P.ι i) + c := by
  let v : ℕ × ℕ → ℝ := fun ni ↦ birkhoffSum T u ni.1 (P.ι ni.2)
  have hv : IsComputableRealFamilyIn A v := by
    obtain ⟨q, hq, herr⟩ := birkhoff_computableIn P T (fun _ : Fin 1 => u) A hA
    refine ⟨fun nip ↦ q ((0, nip.1), nip.2), ?_, ?_⟩
    · exact hq.comp
        ((((Computable.const (0 : Fin 1)).pair Computable.id).comp Computable.fst).pair
          Computable.snd).computableIn
    · intro ni j
      exact herr (0, ni) j
  let D : ℕ × ℕ → Prop := fun ni ↦ N₀ ≤ ni.1 ∧ (ni.2, ni.1, p, k) ∈ E ∧
    (δ : ℝ) * ni.1 / 2 < v ni
  have htrunc : IsREIn A (fun ni : ℕ × ℕ ↦ (δ : ℝ) * ni.1 / 2 < v ni) := by
    have h := (birkhoff_computableIn_gt A v hv).comp
      (f := fun ni : ℕ × ℕ ↦ (ni, (δ / 2) * (ni.1 : ℚ)))
      (Computable.id.pair
        (computable₂_ratMul.comp (Computable.const (δ / 2))
          (computable_nat_to_rat.comp Computable.fst))).computableIn
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast,
      div_mul_eq_mul_div] using h
  have hD : IsREIn A D := by
    apply IsREIn.and
    · apply isREIn_of_computable_decide
      exact Primrec.nat_le.decide.to_comp.comp (Computable.const N₀) Computable.fst
    · apply IsREIn.and
      · exact hRE.comp
          (f := fun ni : ℕ × ℕ ↦ (ni.2, ni.1, p, k))
          (Computable.snd.pair (Computable.fst.pair
            ((Computable.const p).pair (Computable.const k)))).computableIn
      · exact htrunc
  let code : ℕ × ℕ → BitString := fun ni ↦ pairCode (natBits ni.2) (natBits ni.1)
  let decode : BitString → ℕ × ℕ := fun w ↦
    (decodeBits (decodeSecond w), decodeBits (decodeFirst w))
  have hcode : Computable code := CodedFiniteDistribution.pairCode_primrec.to_comp.comp
    (natBits_computable.comp Computable.snd) (natBits_computable.comp Computable.fst)
  have hleft : Function.LeftInverse decode code := by
    intro ni
    simp [code, decode, decodeFirst_pairCode, decodeSecond_pairCode, natBits,
      decodeBits_natBits]
  have hupper := isUpperSemicomputableOnIn_ratCast_mul A v hv D hD t ht
  obtain ⟨c, hc⟩ := exists_oracleComplexity_le_of_tsum_lt_top A D hD
    (fun ni ↦ (t : ℝ) * v ni) hupper (by simpa only [neg_mul, D, v] using hmass)
    code decode hcode hleft
  obtain ⟨c', hc'⟩ := oracle_tuple_bounds A
  refine ⟨c + c', ?_⟩
  intro n hn i hi hpos
  have hpair := hc (n, i) ⟨hn, hi, hpos⟩
  have hproj : (oracleNatComplexity A i : ℝ) ≤ (oraclePairComplexity A i n : ℝ) + c' := by
    exact_mod_cast hc' i n
  change (oraclePairComplexity A i n : ℝ) ≤
    (t : ℝ) * birkhoffSum T u n (P.ι i) + c at hpair
  push_cast
  linarith

/-- Linear positive denominators make the additive coding constant vanish in the upper time
limit: complexity bounds `t U + c` on witnesses with `U > δ n / 2` bound the upper limit of the
finite-scale cost by `t`. -/
private lemma limsup_finiteScaleBSCost_le_of_complexity_bound
    (P : Presentation X) (T : X → X) (u : X → ℝ) (A : Set ℕ) (x : X)
    (r t δ : ℝ) (hδ : 0 < δ) (c : ℕ)
    (hcode : ∀ᶠ n in atTop, ∃ i, P.ι i ∈ bowenBall T n x r ∧
      δ * n / 2 < birkhoffSum T u n (P.ι i) ∧
      (oracleNatComplexity A i : ℝ) ≤ t * birkhoffSum T u n (P.ι i) + c) :
    limsup (fun n ↦ finiteScaleBSCost P T u A x n r) atTop ≤ ENNReal.ofReal t := by
  let b : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (t + (2 * c / δ) / n)
  have hb : Tendsto b atTop (𝓝 (ENNReal.ofReal t)) := by
    have h := (tendsto_const_nhds (x := t)).add
      (tendsto_const_div_atTop_nhds_zero_nat (2 * (c : ℝ) / δ))
    simpa [b, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
  have hbound : ∀ᶠ n in atTop, finiteScaleBSCost P T u A x n r ≤ b n := by
    filter_upwards [hcode, eventually_ge_atTop 1] with n hn hn1
    obtain ⟨i, hi, hden, hK⟩ := hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hUn : 0 < birkhoffSum T u n (P.ι i) :=
      lt_trans (by positivity) hden
    have hratio : (oracleNatComplexity A i : ℝ) / birkhoffSum T u n (P.ι i) ≤
        t + (2 * c / δ) / n := by
      calc
        (oracleNatComplexity A i : ℝ) / birkhoffSum T u n (P.ι i) ≤
            (t * birkhoffSum T u n (P.ι i) + c) / birkhoffSum T u n (P.ι i) :=
          div_le_div_of_nonneg_right hK hUn.le
        _ = t + (c : ℝ) / birkhoffSum T u n (P.ι i) := by
          rw [add_div, mul_div_cancel_right₀ _ hUn.ne']
        _ ≤ t + (c : ℝ) / (δ * n / 2) := by
          gcongr
        _ = t + (2 * c / δ) / n := by field_simp
    unfold finiteScaleBSCost
    rw [ite_eq_right (by omega : n ≠ 0)]
    refine iInf_le_of_le i (iInf_le_of_le hi (iInf_le_of_le hUn ?_))
    calc
      (oracleNatComplexity A i : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n (P.ι i)) =
          ENNReal.ofReal ((oracleNatComplexity A i : ℝ) / birkhoffSum T u n (P.ι i)) := by
        rw [ENNReal.ofReal_div_of_pos hUn, ENNReal.ofReal_natCast]
      _ ≤ b n := ENNReal.ofReal_le_ofReal hratio
  exact (limsup_le_limsup hbound).trans_eq hb.limsup_eq

/-- Bounds at every sufficiently fine dyadic radius bound the full supremum over scales
defining the upper pointwise dimension. -/
private lemma pointwiseBSDimension_snd_le_of_dyadic_limsup_le
    (P : Presentation X) (T : X → X) (u : X → ℝ) (A : Set ℕ) (x : X)
    (p₀ : ℕ) (t : ℝ)
    (hcost : ∀ p ≥ p₀, limsup (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p))
      atTop ≤ ENNReal.ofReal t) :
    (pointwiseBSDimension P T u A x).2 ≤ ENNReal.ofReal t := by
  change (⨆ p : ℕ, limsup (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p))
    atTop) ≤ _
  apply iSup_le
  intro p
  have hsmall : dyadicRadius (max p p₀) ≤ dyadicRadius p := by
    dsimp [dyadicRadius]
    exact _root_.pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left p p₀)
  have hlim := limsup_le_limsup (f := atTop) (Eventually.of_forall (fun n ↦
    pointwiseBSDimension_antitone_radius P T u A x n hsmall))
  exact hlim.trans (hcost (max p p₀) (le_max_right p p₀))

/-- Bounds by `ofReal t` at all rational `t` strictly above a real exponent `s` imply the bound
at `s` itself. -/
private lemma le_ofReal_of_forall_rat_lt (d : ℝ≥0∞) (s : ℝ)
    (h : ∀ t : ℚ, s < (t : ℝ) → d ≤ ENNReal.ofReal (t : ℝ)) :
    d ≤ ENNReal.ofReal s := by
  apply le_of_forall_gt
  intro b hb
  obtain ⟨z, hz, hzb⟩ := exists_between hb
  have hztop : z ≠ ⊤ := ne_top_of_lt hzb
  have hsz : s < z.toReal := by
    have hzpos : 0 < z := lt_of_le_of_lt (bot_le : 0 ≤ ENNReal.ofReal s) hz
    by_cases hs : 0 ≤ s
    · exact (ENNReal.ofReal_lt_iff_lt_toReal hs hztop).mp hz
    · exact (lt_of_not_ge hs).trans (ENNReal.toReal_pos hzpos.ne' hztop)
  obtain ⟨t, hst, htz⟩ := exists_rat_btwn hsz
  exact (h t hst).trans_lt ((ENNReal.ofReal_le_ofReal htz.le).trans_lt
    ((ENNReal.ofReal_toReal hztop).trans_lt hzb))

/-- Coding positive truncations of a net bounds every positive-average point's upper
dimension, without a positivity assumption on other points.
Blueprint node `bs:effective-upper-lower`. -/
theorem pointwiseUpperBSLeEffective (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ)
    (hA : IsAdmissible P T (fun _ : Fin 1 => u) A) (Z : Set X) (s : ℝ) (hs : 0 ≤ s)
    (E : Set (ℕ × ℕ × ℕ × ℕ)) (hE : IsUniformBSNet P T u Z s E) (hRE : IsREIn A E)
    (x : X) (hx : x ∈ Z) (hpos : 0 < lowerBirkhoffAverage T u x) :
    (pointwiseBSDimension P T u A x).2 ≤ ENNReal.ofReal s := by
  apply le_ofReal_of_forall_rat_lt
  intro t ht
  have htpos : 0 < t := by exact_mod_cast (lt_of_le_of_lt hs ht)
  obtain ⟨δ, hδ, r₀, hr₀, hrealizer⟩ :=
    birkhoffRealizerBounds_positive P T hT u hu x hpos
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ℕ, dyadicRadius p₀ ≤ r₀ := by
    obtain ⟨p₀, hp₀⟩ := exists_pow_lt_of_lt_one hr₀ (by norm_num : (2⁻¹ : ℝ) < 1)
    exact ⟨p₀, hp₀.le⟩
  apply pointwiseBSDimension_snd_le_of_dyadic_limsup_le P T u A x p₀ (t : ℝ)
  intro p hp
  have hr : 0 < dyadicRadius p := by dsimp [dyadicRadius]; positivity
  have hrle : dyadicRadius p ≤ r₀ := by
    apply le_trans _ hp₀
    dsimp [dyadicRadius]
    exact _root_.pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
  obtain ⟨N, hN, hNbound⟩ := hrealizer (dyadicRadius p) hr hrle
  obtain ⟨k, hk⟩ := hE.2 p x hx
  obtain ⟨M, hM, N₀, hslice⟩ :=
    exists_eventually_le_of_limsup_lt_top _ (hE.1 p k)
  have hmass := tsum_rpow_truncated_lt_top
    (fun n i ↦ birkhoffSum T u n (P.ι i))
    (fun n ↦ {i : ℕ | (i, n, p, k) ∈ E}) s (t : ℝ) (δ : ℝ) ht hδR N₀ M hM
    (by
      intro n hn
      simpa only [uniformBSSum, uniformPressureSum, birkhoffSum, Finset.mul_sum]
        using hslice n hn)
  obtain ⟨c, hc⟩ := exists_oracleNatComplexity_le_of_truncated_mass
    P T u A hA E hRE p k N₀ t δ htpos hmass
  apply limsup_finiteScaleBSCost_le_of_complexity_bound P T u A x (dyadicRadius p) (t : ℝ)
    (δ : ℝ) hδR c
  apply eventually_atTop.mpr
  refine ⟨max N N₀, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left N N₀).trans hn
  have hnN₀ : N₀ ≤ n := (le_max_right N N₀).trans hn
  obtain ⟨i, hiE, hiBall⟩ := hk n (hN.trans hnN)
  have hi : P.ι i ∈ bowenBall T n x (dyadicRadius p) := by
    dsimp [bowenBall] at hiBall ⊢
    rw [Dynamics.mem_dynEntourage] at hiBall ⊢
    intro j hj
    change dist (T^[j] x) (T^[j] (P.ι i)) < dyadicRadius p
    have hij : dist (T^[j] (P.ι i)) (T^[j] x) < dyadicRadius p := hiBall j hj
    rwa [dist_comm] at hij
  have hposn : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hcut : (δ : ℝ) * n / 2 < birkhoffSum T u n (P.ι i) := by
    have hlinear := (hNbound n hnN i hi).1
    have := mul_pos hδR hposn
    linarith
  exact ⟨i, hi, hcut, hc n hnN₀ i hiE hcut⟩

/-- Effective upper dimension equals the upper pointwise supremum for admissible oracles.
Blueprint node `bs:effective-upper-equality`. -/
theorem effectiveUpperBSEqSup (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ)
    (hA : IsAdmissible P T (fun _ : Fin 1 => u) A) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    effectiveUpperBSDimension P T u A Z = ⨆ x ∈ Z, (pointwiseBSDimension P T u A x).2 := by
  apply le_antisymm
  · exact effectiveUpperBSLeSup P T hT u hu A hA Z hZ
  · refine iSup₂_le fun x hx ↦ ?_
    unfold effectiveUpperBSDimension
    refine le_iInf₂ fun s hs ↦ le_iInf₂ fun E h ↦ ?_
    exact pointwiseUpperBSLeEffective P T hT u hu A hA Z s hs E h.1 h.2 x hx (hZ x hx)

/-- A set is enumerable relative to the join of the set of its codes with any oracle. -/
private lemma isREIn_oracleJoin_encode_image {α : Type*} [Primcodable α] (E : Set α)
    (C : Set ℕ) :
    IsREIn (oracleJoin (Encodable.encode '' E) C) E :=
  (isREIn_encode_image E).mono_oracle (oracle_joins (Encodable.encode '' E) C)

/-- Effective lower BS dimension is antitone with respect to oracle strengthening. -/
private lemma effectiveLowerBSDimension_antitone_oracle (P : Presentation X) (T : X → X)
    (u : X → ℝ) (Z : Set X) {A B : Set ℕ}
    (hAB : TuringReducible (charOracle A) (charOracle B)) :
    effectiveLowerBSDimension P T u B Z ≤ effectiveLowerBSDimension P T u A Z := by
  unfold effectiveLowerBSDimension
  refine le_iInf₂ fun s hs ↦ le_iInf₂ fun E hE ↦ ?_
  exact iInf_le_of_le s (iInf_le_of_le hs (iInf_le_of_le E
    (iInf_le_of_le ⟨hE.1, hE.2.mono_oracle hAB⟩ le_rfl)))

/-- Effective upper BS dimension is antitone with respect to oracle strengthening. -/
private lemma effectiveUpperBSDimension_antitone_oracle (P : Presentation X) (T : X → X)
    (u : X → ℝ) (Z : Set X) {A B : Set ℕ}
    (hAB : TuringReducible (charOracle A) (charOracle B)) :
    effectiveUpperBSDimension P T u B Z ≤ effectiveUpperBSDimension P T u A Z := by
  unfold effectiveUpperBSDimension
  refine le_iInf₂ fun s hs ↦ le_iInf₂ fun E hE ↦ ?_
  exact iInf_le_of_le s (iInf_le_of_le hs (iInf_le_of_le E
    (iInf_le_of_le ⟨hE.1, hE.2.mono_oracle hAB⟩ le_rfl)))

/-- Computable presentations remain computable relative to stronger oracles. -/
private lemma computablePresentationIn_mono_oracle (P : Presentation X) {A B : Set ℕ}
    (hAB : TuringReducible (charOracle A) (charOracle B))
    (hA : ComputablePresentationIn P A) : ComputablePresentationIn P B := by
  unfold ComputablePresentationIn IsComputableRealFamilyIn at hA ⊢
  obtain ⟨q, hq, hqapprox⟩ := hA
  refine ⟨q, RecursiveIn.subst hq fun g hg ↦ ?_, hqapprox⟩
  obtain rfl := Set.mem_singleton_iff.mp hg
  exact hAB

/-- Maps represented relative to an oracle remain represented relative to stronger oracles. -/
private lemma isRepresentedMapIn_mono_oracle {Y : Type*} [MetricSpace Y]
    (P : Presentation X) (Q : Presentation Y) {A B : Set ℕ}
    (hAB : TuringReducible (charOracle A) (charOracle B))
    (f : X → Y) (hf : IsRepresentedMapIn P Q A f) : IsRepresentedMapIn P Q B f := by
  unfold IsRepresentedMapIn at hf ⊢
  obtain ⟨R, hR, hsound, hcomplete⟩ := hf
  exact ⟨R, hR.mono_oracle hAB, hsound, hcomplete⟩

/-- Admissibility is preserved under oracle strengthening. -/
private lemma isAdmissible_mono_oracle (P : Presentation X) (T : X → X) (u : X → ℝ)
    {A B : Set ℕ} (hAB : TuringReducible (charOracle A) (charOracle B))
    (hA : IsAdmissible P T (fun _ : Fin 1 => u) A) :
    IsAdmissible P T (fun _ : Fin 1 => u) B := by
  unfold IsAdmissible at hA ⊢
  obtain ⟨hP, hT, hu⟩ := hA
  exact ⟨computablePresentationIn_mono_oracle P hAB hP,
    isRepresentedMapIn_mono_oracle P P hAB T hT,
    fun j ↦ isRepresentedMapIn_mono_oracle P realPresentation hAB _ (hu j)⟩

/-- A real number strictly above an extended real `d` and below `ofReal r` can be taken to be
nonnegative and finite, i.e. of the form `ofReal s`. -/
private lemma exists_nonneg_real_between {d : ℝ≥0∞} {r : ℝ} (hlt : d < ENNReal.ofReal r) :
    ∃ s : ℝ, 0 ≤ s ∧ d < ENNReal.ofReal s ∧ ENNReal.ofReal s < ENNReal.ofReal r := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_between hlt
  have hs : ENNReal.ofReal s.toReal = s := ENNReal.ofReal_toReal (ne_top_of_lt hs₂)
  refine ⟨s.toReal, ENNReal.toReal_nonneg, ?_, ?_⟩
  · rwa [hs]
  · rwa [hs]

/-- Joining an oracle `C` with the codes of a classical null cover gives a stronger oracle with
effective lower dimension below any rational bound exceeding the classical lower dimension. -/
private lemma exists_oracle_effectiveLowerBSDimension_lt (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (C : Set ℕ) (r : ℚ)
    (hlt : lowerBSDimension T u Z < ENNReal.ofReal (r : ℝ)) :
    ∃ A, TuringReducible (charOracle C) (charOracle A) ∧
      effectiveLowerBSDimension P T u A Z < ENNReal.ofReal (r : ℝ) := by
  obtain ⟨s, hs, hlts, hsr⟩ := exists_nonneg_real_between hlt
  obtain ⟨E, hE⟩ := lowerBSNullCoverCharacterization P T hT u hu Z hZ s hs hlts
  refine ⟨oracleJoin (Encodable.encode '' E) C, oracle_joins_right (Encodable.encode '' E) C,
    lt_of_le_of_lt ?_ hsr⟩
  unfold effectiveLowerBSDimension
  exact iInf_le_of_le s (iInf_le_of_le hs (iInf_le_of_le E
    (iInf_le_of_le ⟨hE, isREIn_oracleJoin_encode_image E C⟩ le_rfl)))

/-- Joining an oracle `C` with the codes of a classical uniform net gives a stronger oracle with
effective upper dimension below any rational bound exceeding the classical upper dimension. -/
private lemma exists_oracle_effectiveUpperBSDimension_lt (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (C : Set ℕ) (r : ℚ)
    (hlt : upperBSDimension T u Z < ENNReal.ofReal (r : ℝ)) :
    ∃ A, TuringReducible (charOracle C) (charOracle A) ∧
      effectiveUpperBSDimension P T u A Z < ENNReal.ofReal (r : ℝ) := by
  obtain ⟨s, hs, hlts, hsr⟩ := exists_nonneg_real_between hlt
  obtain ⟨E, hE⟩ := upperBSUniformNetCharacterization P T hT u hu Z hZ s hs hlts
  refine ⟨oracleJoin (Encodable.encode '' E) C, oracle_joins_right (Encodable.encode '' E) C,
    lt_of_le_of_lt ?_ hsr⟩
  unfold effectiveUpperBSDimension
  exact iInf_le_of_le s (iInf_le_of_le hs (iInf_le_of_le E
    (iInf_le_of_le ⟨hE, isREIn_oracleJoin_encode_image E C⟩ le_rfl)))

/-- Abstract oracle attainment: if a quantity `q` on oracles decreases along oracle
strengthening, is bounded below by `Q` on admissible oracles, and approaches `Q` from above in
every upper cone, then some admissible cone has `q = Q` throughout. -/
private lemma exists_admissible_cone_eq (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (q : Set ℕ → ℝ≥0∞) (Q : ℝ≥0∞)
    (hanti : ∀ A B, TuringReducible (charOracle A) (charOracle B) → q B ≤ q A)
    (hge : ∀ B, IsAdmissible P T (fun _ : Fin 1 => u) B → Q ≤ q B)
    (happrox : ∀ C : Set ℕ, ∀ r : ℚ, Q < ENNReal.ofReal (r : ℝ) →
      ∃ A, TuringReducible (charOracle C) (charOracle A) ∧ q A < ENNReal.ofReal (r : ℝ)) :
    ∃ A₀ : Set ℕ, IsAdmissible P T (fun _ : Fin 1 => u) A₀ ∧
      ∀ B : Set ℕ, charOracle A₀ ≤ᵀ charOracle B →
        IsAdmissible P T (fun _ : Fin 1 => u) B ∧ q B = Q := by
  obtain ⟨C, hC⟩ := exists_admissible_base P T hT (fun _ : Fin 1 => u) fun _ ↦ hu.continuous
  have hadm : ∀ B, TuringReducible (charOracle C) (charOracle B) →
      IsAdmissible P T (fun _ : Fin 1 => u) B :=
    fun B hCB ↦ isAdmissible_mono_oracle P T u hCB (hC C TuringReducible.rfl)
  have hlower : ∀ A, TuringReducible (charOracle C) (charOracle A) → Q ≤ q A :=
    fun A hA ↦ hge A (hadm A hA)
  obtain ⟨A₀, hCA₀, hA₀⟩ :=
    exists_achieving_oracle_ennreal q Q C hanti hlower fun r _ hr ↦ happrox C r hr
  exact ⟨A₀, hadm A₀ hCA₀, fun B hAB ↦ ⟨hadm B (TuringReducible.trans hCA₀ hAB),
    exists_achieving_oracle_ennreal_stable q Q C A₀ hanti hlower hCA₀ hA₀ B hAB⟩⟩

/-- An admissible upper cone attains the classical lower dimension by effective dimension: every
oracle above `A₀` is admissible and has effective lower BS dimension equal to the classical one.
Blueprint node `bs:oracle-attainment`. -/
theorem bsOracleAttainment (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    ∃ A₀ : Set ℕ, IsAdmissible P T (fun _ : Fin 1 => u) A₀ ∧
      ∀ B : Set ℕ, charOracle A₀ ≤ᵀ charOracle B →
        IsAdmissible P T (fun _ : Fin 1 => u) B ∧
          effectiveLowerBSDimension P T u B Z = lowerBSDimension T u Z :=
  exists_admissible_cone_eq P T hT u hu (fun A ↦ effectiveLowerBSDimension P T u A Z)
    (lowerBSDimension T u Z)
    (fun _ _ hAB ↦ effectiveLowerBSDimension_antitone_oracle P T u Z hAB)
    (fun B hB ↦ effectiveBSDimensions_ge P T hT u hu B hB Z hZ)
    (fun C r hr ↦ exists_oracle_effectiveLowerBSDimension_lt P T hT u hu Z hZ C r hr)

/-- An admissible upper cone attains the classical upper dimension by effective dimension.
Blueprint node `bs:oracle-attainment`. -/
theorem bsOracleAttainment_upper (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    ∃ A₀ : Set ℕ, IsAdmissible P T (fun _ : Fin 1 => u) A₀ ∧
      ∀ B : Set ℕ, charOracle A₀ ≤ᵀ charOracle B →
        IsAdmissible P T (fun _ : Fin 1 => u) B ∧
          effectiveUpperBSDimension P T u B Z = upperBSDimension T u Z :=
  exists_admissible_cone_eq P T hT u hu (fun A ↦ effectiveUpperBSDimension P T u A Z)
    (upperBSDimension T u Z)
    (fun _ _ hAB ↦ effectiveUpperBSDimension_antitone_oracle P T u Z hAB)
    (fun B hB ↦ effectiveBSDimensions_ge_upper P T hT u hu B hB Z hZ)
    (fun C r hr ↦ exists_oracle_effectiveUpperBSDimension_lt P T hT u hu Z hZ C r hr)

/-- Oracle strengthening decreases either pointwise dimension on the positive-average locus.
Blueprint node `bs:point-to-set`. -/
theorem bsPointToSet_mono_oracle (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (A B : Set ℕ)
    (hAB : charOracle A ≤ᵀ charOracle B) (x : X)
    (hx : 0 < lowerBirkhoffAverage T u x) (σ : LimitSide) :
    σ.choose (pointwiseBSDimension P T u B x) ≤
      σ.choose (pointwiseBSDimension P T u A x) := by
  cases σ with
  | lower => exact normalized_additive_slack_bs P T hT u hu A B hAB x hx
  | upper => exact normalized_additive_slack_bs_upper P T hT u hu A B hAB x hx

/-- Every oracle, including a nonadmissible one, satisfies the lower bound in Main B.
Blueprint node `bs:point-to-set`. -/
theorem bsPointToSet_all_oracles (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (A : Set ℕ) (σ : LimitSide) :
    σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z) ≤
      ⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x) := by
  cases σ with
  | lower =>
    obtain ⟨A₀, -, hattain⟩ := bsOracleAttainment P T hT u hu Z hZ
    obtain ⟨hB, hBeq⟩ := hattain (oracleJoin A₀ A) (oracle_joins A₀ A)
    calc lowerBSDimension T u Z
        = effectiveLowerBSDimension P T u (oracleJoin A₀ A) Z := hBeq.symm
      _ = ⨆ x ∈ Z, (pointwiseBSDimension P T u (oracleJoin A₀ A) x).1 :=
        effectiveLowerBSEqSup P T hT u hu _ hB Z hZ
      _ ≤ _ := iSup₂_mono fun x hx ↦ bsPointToSet_mono_oracle P T hT u hu
        A _ (oracle_joins_right A₀ A) x (hZ x hx) LimitSide.lower
  | upper =>
    obtain ⟨A₀, -, hattain⟩ := bsOracleAttainment_upper P T hT u hu Z hZ
    obtain ⟨hB, hBeq⟩ := hattain (oracleJoin A₀ A) (oracle_joins A₀ A)
    calc upperBSDimension T u Z
        = effectiveUpperBSDimension P T u (oracleJoin A₀ A) Z := hBeq.symm
      _ = ⨆ x ∈ Z, (pointwiseBSDimension P T u (oracleJoin A₀ A) x).2 :=
        effectiveUpperBSEqSup P T hT u hu _ hB Z hZ
      _ ≤ _ := iSup₂_mono fun x hx ↦ bsPointToSet_mono_oracle P T hT u hu
        A _ (oracle_joins_right A₀ A) x (hZ x hx) LimitSide.upper

end Kolmogorov.PointToSet
