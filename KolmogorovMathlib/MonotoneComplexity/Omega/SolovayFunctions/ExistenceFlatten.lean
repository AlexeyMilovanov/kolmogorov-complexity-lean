import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.SolovayProperty
import KolmogorovMathlib.MonotoneComplexity.Omega.Prediction
import KolmogorovMathlib.MonotoneComplexity.Omega.BusyBeaverInfra
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctionComputable
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealCantor
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealKraft
import KolmogorovMathlib.MonotoneComplexity.Omega.AntitoneSplit
import KolmogorovMathlib.MonotoneComplexity.Omega.ModulusRandom
import KolmogorovMathlib.MonotoneComplexity.Omega.CappedScaling
import KolmogorovMathlib.MonotoneComplexity.Omega.IntervalCover
import KolmogorovMathlib.MonotoneComplexity.Omega.NeighbourhoodCover
import KolmogorovMathlib.MonotoneComplexity.Omega.BusyBeaverSearch
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaBitsFromApprox
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.BusyBeaver
import KolmogorovMathlib.Complexity.NatComplexity
import KolmogorovMathlib.Prefix.UpperSemicomputableBound
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.ExistenceSum

/-!
# Tightness of a complexity bound and randomness of its sum

For an upper semicomputable `f` with `∑ₙ 2 ^ (-f n) < ∞`, the sum is random exactly when the
bound is tight infinitely often, that is `K(n) ≥ f n - c` for some `c`:
`isMartinLofRandomReal_of_tight`, `tight_of_isMartinLofRandomReal` and the equivalence
`tight_iff_isMartinLofRandomReal`. The criterion is stated in the strengthened form of the source
(`not_isMartinLofRandomReal_iff_ratioTendstoZero_two_pow_neg`, and for summands presented as
lower semicomputable numbers `not_isMartinLofRandomReal_iff_ratioTendstoZero_of_lsc_terms`), and
`hasSolovayProperty_add` records that the Solovay property is upward closed. The closing sections
set up busy beavers and convergence moduli: the sublevel sets `plainKNatSublevel` and their
counting bounds (`kpNatSublevel_finite`, `plainKNatSublevel_finite`).

Source: SUV §5.7.6–5.7.7, pp. 167–170, Theorems 111 and 113.
-/

namespace Kolmogorov
open MeasureTheory ENNReal

/-- The summands may be presented as lower semicomputable numbers, each with only finitely many
different approximations: `rᵢ = limₙ r(i,n)` with `r` computable, non-decreasing in `n`, and
with finitely many different values for every `i`. Then `∑ rᵢ` is not ML-random iff `rᵢ/m(i)
→ 0`.  SUV p. 168, strengthening of Theorem 111. -/
theorem not_isMartinLofRandomReal_iff_ratioTendstoZero_of_lsc_terms {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m)
    {R : ℕ → ℕ → ℚ} (hR : Computable₂ R) (hR0 : ∀ i n, 0 ≤ R i n)
    (hmono : ∀ i, Monotone (R i)) (_hfin : ∀ i, (Set.range (R i)).Finite)
    {r : ℕ → ℚ} (hlim : ∀ i, ∃ n₀, ∀ n, n₀ ≤ n → R i n = r i)
    {α : ℝ} (hsum : Filter.Tendsto (fun n => (partialSums r n : ℝ)) Filter.atTop (nhds α)) :
    ¬ IsMartinLofRandomReal α ↔ RatioTendstoZero m r := by
  classical
  -- the double series of increments
  set a : ℕ → ℕ → ℚ := fun i j => Nat.casesOn (motive := fun _ => ℚ) j (R i 0)
    (fun k => R i (k + 1) - R i k) with hadef
  have hacomp : Computable₂ a := by
    have hf : Computable (fun p : ℕ × ℕ => p.2) := Computable.snd
    have hg : Computable (fun p : ℕ × ℕ => R p.1 0) :=
      hR.comp Computable.fst (Computable.const 0)
    have hh : Computable₂ (fun (p : ℕ × ℕ) (k : ℕ) => R p.1 (k + 1) - R p.1 k) := by
      have h1 : Computable (fun z : (ℕ × ℕ) × ℕ => R z.1.1 (z.2 + 1)) :=
        hR.comp (Computable.fst.comp Computable.fst)
          (Primrec.nat_add.to_comp.comp Computable.snd (Computable.const 1))
      have h2 : Computable (fun z : (ℕ × ℕ) × ℕ => R z.1.1 z.2) :=
        hR.comp (Computable.fst.comp Computable.fst) Computable.snd
      exact computable₂_ratSub.comp h1 h2
    exact Computable.nat_casesOn hf hg hh
  have ha0 : ∀ i j, 0 ≤ a i j := by
    intro i j
    cases j with
    | zero => exact hR0 i 0
    | succ k => exact sub_nonneg.2 (hmono i (Nat.le_succ k))
  have hasum : ∀ i J : ℕ, ∑ j ∈ Finset.range (J + 1), a i j = R i J := by
    intro i J
    induction J with
    | zero => simp [hadef]
    | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      change R i J + (R i (J + 1) - R i J) = R i (J + 1)
      ring
  have hRle : ∀ i J : ℕ, R i J ≤ r i := by
    intro i J
    obtain ⟨n₀, hn₀⟩ := hlim i
    calc R i J ≤ R i (max J n₀) := hmono i (le_max_left _ _)
      _ = r i := hn₀ _ (le_max_right _ _)
  have hr0 : ∀ i, 0 ≤ r i := fun i => le_trans (hR0 i 0) (hRle i 0)
  have hrow : ∀ i J : ℕ, ∑ j ∈ Finset.range J, a i j ≤ r i := by
    intro i J
    cases J with
    | zero => simpa using hr0 i
    | succ K => rw [hasum i K]; exact hRle i K
  have hgroup : ∀ i : ℕ, ∃ J : ℕ, ∀ K : ℕ, J ≤ K →
      ∑ j ∈ Finset.range (K + 1), a i j = r i := by
    intro i
    obtain ⟨n₀, hn₀⟩ := hlim i
    exact ⟨n₀, fun K hK => by rw [hasum i K]; exact hn₀ K hK⟩
  have hafin : ∀ i, {j : ℕ | a i j ≠ 0}.Finite := by
    intro i
    obtain ⟨n₀, hn₀⟩ := hlim i
    refine Set.Finite.subset (Set.finite_Iic n₀) (fun j hj => ?_)
    by_contra hjle
    simp only [Set.mem_Iic, not_le] at hjle
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hk : n₀ ≤ k := by omega
    have : a i (k + 1) = 0 := by
      change R i (k + 1) - R i k = 0
      rw [hn₀ (k + 1) (by omega), hn₀ k hk, sub_self]
    exact hj this
  have hatsum : ∀ i : ℕ,
      (∑' j, ENNReal.ofReal ((a i j : ℝ))) = ENNReal.ofReal ((r i : ℝ)) := by
    intro i
    obtain ⟨n₀, hn₀⟩ := hlim i
    have hzero : ∀ j ∉ Finset.range (n₀ + 1), ENNReal.ofReal ((a i j : ℝ)) = 0 := by
      intro j hj
      have hjge : n₀ + 1 ≤ j := by
        by_contra hc
        exact hj (Finset.mem_range.2 (by omega))
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hk : n₀ ≤ k := by omega
      have : a i (k + 1) = 0 := by
        change R i (k + 1) - R i k = 0
        rw [hn₀ (k + 1) (by omega), hn₀ k hk, sub_self]
      rw [this]
      simp
    rw [tsum_eq_sum hzero, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => by
      exact_mod_cast ha0 i j)]
    congr 1
    have : (∑ j ∈ Finset.range (n₀ + 1), ((a i j : ℚ) : ℝ))
        = ((∑ j ∈ Finset.range (n₀ + 1), a i j : ℚ) : ℝ) := by push_cast; ring
    rw [this, hasum i n₀, hn₀ n₀ le_rfl]
  -- the flattened series
  set b : ℕ → ℚ := fun k => a k.unpair.1 k.unpair.2 with hbdef
  have hbcomp : Computable b := by
    have h1 : Computable (fun k : ℕ => k.unpair.1) := (Primrec.fst.comp Primrec.unpair).to_comp
    have h2 : Computable (fun k : ℕ => k.unpair.2) := (Primrec.snd.comp Primrec.unpair).to_comp
    exact hacomp.comp h1 h2
  have hb0 : ∀ k, 0 ≤ b k := fun k => ha0 _ _
  have hbsum := tendsto_partialSums_unpair ha0 hgroup hrow hsum
  have h111 := isMartinLofRandomReal_iff_hasSolovayProperty hm hbcomp hb0 hbsum
  -- the two index sets are the same set, read through `Nat.pair`
  have hconv : ∀ ε : ℝ≥0∞,
      {p : ℕ × ℕ | ε * aprioriPair m p.1 p.2 ≤ ENNReal.ofReal ((a p.1 p.2 : ℝ))}
        = (fun p : ℕ × ℕ => Nat.pair p.1 p.2) ⁻¹'
            {k : ℕ | ε * m k ≤ ENNReal.ofReal ((b k : ℝ))} := by
    intro ε
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, aprioriPair_eq, hbdef, Nat.unpair_pair]
  have hconv2 : ∀ ε : ℝ≥0∞,
      {k : ℕ | ε * m k ≤ ENNReal.ofReal ((b k : ℝ))}
        = Nat.unpair ⁻¹'
            {p : ℕ × ℕ | ε * aprioriPair m p.1 p.2 ≤ ENNReal.ofReal ((a p.1 p.2 : ℝ))} := by
    intro ε
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, aprioriPair_eq, hbdef, Nat.pair_unpair]
  have hgrpeq : ∀ ε : ℝ≥0∞,
      {i : ℕ | ε * m i ≤ ∑' j, ENNReal.ofReal ((a i j : ℝ))}
        = {i : ℕ | ε * m i ≤ ENNReal.ofReal ((r i : ℝ))} := by
    intro ε
    ext i
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hatsum i]
  constructor
  · intro hnr ε hε
    have hbratio : RatioTendstoZero m b :=
      (not_hasSolovayProperty_iff m b).1 (fun hs => hnr (h111.2 hs))
    have hpair : ∀ δ : ℝ≥0∞, 0 < δ →
        {p : ℕ × ℕ | δ * aprioriPair m p.1 p.2
          ≤ ENNReal.ofReal ((a p.1 p.2 : ℝ))}.Finite := by
      intro δ hδ
      rw [hconv δ]
      exact Set.Finite.preimage (fun x _ y _ hxy => by
        simpa [Prod.ext_iff] using congrArg Nat.unpair hxy) (hbratio δ hδ)
    have := ratioTendstoZero_group_of_pair hm hacomp ha0 hafin hpair ε hε
    rwa [hgrpeq ε] at this
  · intro hr hrand
    have hgrp : ∀ δ : ℝ≥0∞, 0 < δ →
        {i : ℕ | δ * m i ≤ ∑' j, ENNReal.ofReal ((a i j : ℝ))}.Finite := by
      intro δ hδ
      rw [hgrpeq δ]
      exact hr δ hδ
    have hpair := ratioTendstoZero_pair_of_group hm hacomp ha0 hafin hgrp
    have hbratio : RatioTendstoZero m b := by
      intro δ hδ
      rw [hconv2 δ]
      exact Set.Finite.preimage (fun x _ y _ hxy => by
        simpa using congrArg (fun p : ℕ × ℕ => Nat.pair p.1 p.2) hxy) (hpair δ hδ)
    exact (not_hasSolovayProperty_iff m b).2 hbratio (h111.1 hrand)

/-! ### Theorem 113 -/

/-! #### Theorem 113, decomposed

The source reads Theorem 113 as Theorem 111 applied to the series `rₙ = 2^{-f(n)}`, whose
terms are only *lower semicomputable* (`f` is upper semicomputable) — hence the
strengthening `not_isMartinLofRandomReal_iff_ratioTendstoZero_of_lsc_terms` rather than
plain Theorem 111.  The two leaves below are exactly the two translations that the reading
needs; the frozen statements are then assembled from them. -/

/-! The two ingredients of Theorem 113 that Section 5.7.5 already needs — the recalled
Theorem 62 and the tightness bridge `hasSolovayProperty_two_pow_neg_iff_tight` — are stated
earlier in this file, right after `not_hasSolovayProperty_iff`, because the corrected
Solovay-function characterisation of p. 165 is proved from them. -/

/-- **SUV p. 168.** Theorem 111, in the strengthened form of p. 168,
applied to the lower semicomputable series `2^{-f(n)}`. -/
theorem not_isMartinLofRandomReal_iff_ratioTendstoZero_two_pow_neg {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {f : ℕ → ℕ} (hf : IsUpperSemicomputableNat f)
    (hfin : (∑' n, (2 : ℝ≥0∞)⁻¹ ^ f n) ≠ ⊤)
    {α : ℝ} (hα : ENNReal.ofReal α = ∑' n, (2 : ℝ≥0∞)⁻¹ ^ f n) :
    ¬ IsMartinLofRandomReal α ↔ RatioTendstoZero m (fun n => ((2 : ℚ)⁻¹) ^ f n) := by
  obtain ⟨g, hgc, hgstep, hgstab⟩ := hf
  have hganti : ∀ i, Antitone (fun s => g s i) := fun i =>
    antitone_nat_of_succ_le (fun s => hgstep s i)
  have hR : Computable₂ (fun i s : ℕ => ((2 : ℚ)⁻¹) ^ g s i) :=
    computable_inv_two_pow_rat.comp (hgc.comp Computable.snd Computable.fst)
  have hR0 : ∀ i s : ℕ, 0 ≤ ((2 : ℚ)⁻¹) ^ g s i := fun i s => by positivity
  have hRmono : ∀ i : ℕ, Monotone (fun s : ℕ => ((2 : ℚ)⁻¹) ^ g s i) := by
    intro i s t hst
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hganti i hst)
  have hRfin : ∀ i : ℕ, (Set.range (fun s : ℕ => ((2 : ℚ)⁻¹) ^ g s i)).Finite := by
    intro i
    have hsub : Set.range (fun s : ℕ => g s i) ⊆ Set.Iic (g 0 i) := by
      rintro _ ⟨s, rfl⟩
      exact hganti i (Nat.zero_le s)
    have h1 : (Set.range (fun s : ℕ => g s i)).Finite :=
      Set.Finite.subset (Set.finite_Iic (g 0 i)) hsub
    have h2 : Set.range (fun s : ℕ => ((2 : ℚ)⁻¹) ^ g s i)
        = (fun k : ℕ => ((2 : ℚ)⁻¹) ^ k) '' Set.range (fun s : ℕ => g s i) := by
      rw [← Set.range_comp]
      rfl
    rw [h2]
    exact h1.image _
  have hlim : ∀ i : ℕ, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ((2 : ℚ)⁻¹) ^ g n i = ((2 : ℚ)⁻¹) ^ f i := by
    intro i
    obtain ⟨s₀, hs₀⟩ := hgstab i
    exact ⟨s₀, fun n hn => by rw [hs₀ n hn]⟩
  -- the real sum of the series `2^{-f(n)}` is `α`
  have hposα : 0 < ENNReal.ofReal α := by
    rw [hα]
    exact lt_of_lt_of_le (pos_iff_ne_zero.2 (pow_ne_zero (f 0) (by simp)))
      (ENNReal.le_tsum (f := fun n => (2 : ℝ≥0∞)⁻¹ ^ f n) 0)
  have hαpos : 0 < α := ENNReal.ofReal_pos.1 hposα
  have hsummable : Summable (fun n : ℕ => ((2 : ℝ)⁻¹) ^ f n) := by
    refine (ENNReal.summable_toReal hfin).congr (fun n => ?_)
    simp
  have hval : (∑' n : ℕ, ((2 : ℝ)⁻¹) ^ f n) = α := by
    have h1 : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n).toReal
        = ∑' n : ℕ, ((2 : ℝ≥0∞)⁻¹ ^ f n).toReal :=
      ENNReal.tsum_toReal_eq (fun n => ENNReal.pow_ne_top (by simp))
    rw [← hα, ENNReal.toReal_ofReal hαpos.le] at h1
    rw [h1]
    exact tsum_congr (fun n => by simp)
  have htend : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, ((2 : ℝ)⁻¹) ^ f i)
      Filter.atTop (nhds α) := by
    rw [← hval]
    exact hsummable.hasSum.tendsto_sum_nat
  have hsum : Filter.Tendsto (fun n => (partialSums (fun i => ((2 : ℚ)⁻¹) ^ f i) n : ℝ))
      Filter.atTop (nhds α) := by
    refine htend.congr (fun n => ?_)
    simp only [partialSums]
    push_cast
    ring
  exact not_isMartinLofRandomReal_iff_ratioTendstoZero_of_lsc_terms hm hR hR0 hRmono hRfin hlim hsum

/-- If the bound is tight for infinitely many `n`, then `∑ₙ 2^{-f(n)}` is random. *Proof.*
Tightness is the Solovay property of `2^{-f(n)}`
(`hasSolovayProperty_two_pow_neg_iff_tight`), i.e. the failure of `RatioTendstoZero`
(`not_hasSolovayProperty_iff`), i.e. randomness of the sum
(`not_isMartinLofRandomReal_iff_ratioTendstoZero_two_pow_neg`).  SUV Theorem 113 (Section
5.7, p. 168), forward direction. -/
theorem isMartinLofRandomReal_of_tight {U : Map}
    (hU : IsOptimalPrefixConditional U) {f : ℕ → ℕ} (hf : IsUpperSemicomputableNat f)
    (hfin : (∑' n, (2 : ℝ≥0∞)⁻¹ ^ f n) ≠ ⊤)
    {α : ℝ} (hα : ENNReal.ofReal α = ∑' n, (2 : ℝ≥0∞)⁻¹ ^ f n)
    (h : ∃ c : ℕ, {n : ℕ | (f n : ENat) ≤ KPNat U n + (c : ENat)}.Infinite) :
    IsMartinLofRandomReal α := by
  obtain ⟨m, hm⟩ := exists_isUniversalSemimeasureNat
  by_contra hnr
  exact (not_hasSolovayProperty_iff m (fun n => ((2 : ℚ)⁻¹) ^ f n)).2
    ((not_isMartinLofRandomReal_iff_ratioTendstoZero_two_pow_neg hm hf hfin hα).1 hnr)
    ((hasSolovayProperty_two_pow_neg_iff_tight hm hU).2 h)

/-- If the sum `∑ 2 ^ (-f n)` of an upper semicomputable function `f` is finite and its value
is Martin-Löf random, then `f` is tight: `f n ≤ KP(n) + c` for infinitely many `n`. One
direction of SUV Theorem 113. -/
theorem tight_of_isMartinLofRandomReal {U : Map}
    (hU : IsOptimalPrefixConditional U) {f : ℕ → ℕ} (hf : IsUpperSemicomputableNat f)
    (hfin : (∑' n, (2 : ℝ≥0∞)⁻¹ ^ f n) ≠ ⊤)
    {α : ℝ} (hα : ENNReal.ofReal α = ∑' n, (2 : ℝ≥0∞)⁻¹ ^ f n)
    (h : IsMartinLofRandomReal α) :
    ∃ c : ℕ, {n : ℕ | (f n : ENat) ≤ KPNat U n + (c : ENat)}.Infinite := by
  obtain ⟨m, hm⟩ := exists_isUniversalSemimeasureNat
  refine (hasSolovayProperty_two_pow_neg_iff_tight hm hU).1 ?_
  by_contra hns
  exact (not_isMartinLofRandomReal_iff_ratioTendstoZero_two_pow_neg hm hf hfin hα).2
    ((not_hasSolovayProperty_iff m (fun n => ((2 : ℚ)⁻¹) ^ f n)).1 hns) h

/-- The bound `f` is tight for infinitely many `n` (i.e. `K(n) ≥ f(n) - c` for some `c` and
infinitely many `n`) if and only if the sum `∑ₙ 2^{-f(n)}` is random.  SUV Theorem 113
(Section 5.7, p. 168). -/
theorem tight_iff_isMartinLofRandomReal {U : Map}
    (hU : IsOptimalPrefixConditional U) {f : ℕ → ℕ} (hf : IsUpperSemicomputableNat f)
    (hfin : (∑' n, (2 : ℝ≥0∞)⁻¹ ^ f n) ≠ ⊤)
    {α : ℝ} (hα : ENNReal.ofReal α = ∑' n, (2 : ℝ≥0∞)⁻¹ ^ f n) :
    (∃ c : ℕ, {n : ℕ | (f n : ENat) ≤ KPNat U n + (c : ENat)}.Infinite) ↔
      IsMartinLofRandomReal α :=
  ⟨isMartinLofRandomReal_of_tight hU hf hfin hα,
    tight_of_isMartinLofRandomReal hU hf hfin hα⟩

/-- **SUV p. 168 (last paragraph of 5.7.6).** The Solovay property is upward closed
with respect to Solovay reducibility: if `∑ aᵢ` converges slowly and `bᵢ ≥ 0`, then
`∑ (aᵢ + bᵢ)` converges slowly as well. -/
theorem hasSolovayProperty_add {m : ℕ → ℝ≥0∞} (_hm : IsUniversalSemimeasureNat m)
    {a b : ℕ → ℚ} (hb0 : ∀ i, 0 ≤ b i) (h : HasSolovayProperty m a) :
    HasSolovayProperty m (fun i => a i + b i) := by
  obtain ⟨ε, hε, hinf⟩ := h
  refine ⟨ε, hε, Set.Infinite.mono ?_ hinf⟩
  intro i hi
  refine le_trans hi (ENNReal.ofReal_le_ofReal ?_)
  have hb : (0 : ℝ) ≤ ((b i : ℚ) : ℝ) := by exact_mod_cast hb0 i
  push_cast
  linarith

/-! ### Section 5.7.7: busy beavers and convergence moduli (SUV pp. 169–170) -/

/-! #### `ℕ∞`-valued minima: no cutoff can be faked by a junk `0`

Every "minimal `N` such that …" of pp. 169–170 is a *partial* function: the defining
set can be empty (the series need not converge, the a priori probability need not drop
below `2^{-k}`).  Raw `sInf : Set ℕ → ℕ` returns `0` there, i.e. it reports the
*strongest possible* cutoff exactly when none exists.  We
therefore take the infimum in `ℕ∞ = WithTop ℕ`, where `sInf ∅ = ⊤`. -/

/-- The `ℕ∞`-valued minimum of a set of naturals: `⊤` exactly on the empty set. -/
noncomputable def natSInfTop (S : Set ℕ) : ℕ∞ := sInf ((fun n : ℕ => (n : ℕ∞)) '' S)

/-- A member of `S` bounds `natSInfTop S` from above. -/
theorem natSInfTop_le_coe {S : Set ℕ} {n : ℕ} (hn : n ∈ S) : natSInfTop S ≤ (n : ℕ∞) :=
  sInf_le ⟨n, hn, rfl⟩

/-- `natSInfTop S = ⊤` says precisely that no cutoff exists. -/
theorem natSInfTop_eq_top_iff (S : Set ℕ) : natSInfTop S = ⊤ ↔ S = ∅ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨n, hn⟩ := Set.nonempty_iff_ne_empty.2 hne
    exact (ENat.natCast_ne_top n) (top_le_iff.1 (h ▸ natSInfTop_le_coe hn))
  · rintro rfl
    simp [natSInfTop]

/-- On a nonempty set `natSInfTop` is the ordinary minimum. -/
theorem natSInfTop_eq_coe_sInf {S : Set ℕ} (hS : S.Nonempty) :
    natSInfTop S = ((sInf S : ℕ) : ℕ∞) :=
  le_antisymm (natSInfTop_le_coe (Nat.sInf_mem hS))
    (le_sInf (by
      rintro _ ⟨n, hn, rfl⟩
      change ((sInf S : ℕ) : ℕ∞) ≤ (n : ℕ∞)
      exact_mod_cast Nat.sInf_le hn))

/-! #### Busy beavers (SUV pp. 21, 169)

`BP` and `B` *are* maxima of sublevel sets, so the honest guard is not a carrier
change but the two domain facts that make `sSup` meaningful: the sublevel set is
finite (there are only finitely many programs of length `≤ n`, hence `sSup` is not the
junk `0` of an unbounded set) and, from some point on, nonempty.  Both are recorded
below, together with the characterisation `BP_mem_and_le` which is what every use of
`BP` actually needs. -/

/-- The sublevel set of prefix complexity: the naturals `k` with `K(k) ≤ n`. -/
def kpNatSublevel (U : Map) (n : ℕ) : Set ℕ := {k : ℕ | KPNat U k ≤ (n : ENat)}

/-- The sublevel set of plain complexity (SUV Section 1.2, p. 21). -/
def plainKNatSublevel (V : Map) (n : ℕ) : Set ℕ := {k : ℕ | plainKNat V k ≤ (n : ENat)}

/-- **The counting fact behind `BP` (SUV p. 21/169).** There are at most
`#{p : |p| ≤ n}` naturals of prefix complexity `≤ n`, so the sublevel set is finite
and its supremum is a genuine maximum, not the `sSup`-of-an-unbounded-set junk value.
The elementary counting step is
`Kolmogorov.card_KPPlain_le_boundedPrograms_length` (`Prefix/TotalCountingBound.lean`),
transported along the injection `natToBitString`. -/
theorem kpNatSublevel_finite (U : Map) (n : ℕ) : (kpNatSublevel U n).Finite :=
  finite_setOf_condK_le U natToBitString natToBitString_injective n

/-- The same counting fact for plain complexity. -/
theorem plainKNatSublevel_finite (V : Map) (n : ℕ) : (plainKNatSublevel V n).Finite :=
  finite_setOf_condK_le V Nat.bits natBits_injective n

end Kolmogorov
