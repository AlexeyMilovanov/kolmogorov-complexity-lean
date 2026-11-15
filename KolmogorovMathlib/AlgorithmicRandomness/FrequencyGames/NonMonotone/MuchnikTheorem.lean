/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.MuchnikCoding
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.MuchnikWitnesses
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.MuchnikStages

/-!
# Muchnik Theorem

This module assembles the lemmas of the neighbouring `Muchnik*` modules (coding, witnesses,
stages) into the proof that a sequence with infinitely many prefixes of plain complexity below
`α n`, `α < 1`, is not Mises--Kolmogorov--Loveland random (SUV, after Theorem 193).
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-- Step 8 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
a finite pigeonhole argument extracts one admissible rule with arbitrarily long
deviating output prefixes from a finite family of admissible rules. -/
private lemma not_isMisesKLRandom_of_plainK_lt_pigeonhole
    (w : CantorSeq) (M : ℕ) (R : Fin M → KLRule) (hR : ∀ j, (R j).IsAdmissible)
    (δ : ℝ) (hs : ∀ N : ℕ, ∃ j t,
      N ≤ ((R j).outputChain w t).length ∧
      δ * ((R j).outputChain w t).length ≤
        |(((R j).outputChain w t).count true : ℝ) -
          ((R j).outputChain w t).count false|) :
    ∃ ρ : KLRule, ρ.IsAdmissible ∧ ∀ N : ℕ, ∃ t : ℕ,
      N ≤ (ρ.outputChain w t).length ∧
      δ * (ρ.outputChain w t).length ≤
        |((ρ.outputChain w t).count true : ℝ) - (ρ.outputChain w t).count false| := by
  have hf : ∃ᶠ N : ℕ in atTop, ∃ j : Fin M, ∃ t : ℕ,
      N ≤ ((R j).outputChain w t).length ∧
      δ * ((R j).outputChain w t).length ≤
        |(((R j).outputChain w t).count true : ℝ) -
          ((R j).outputChain w t).count false| :=
    (Filter.Eventually.of_forall hs).frequently
  obtain ⟨j, hj⟩ := Filter.frequently_exists.mp hf
  refine ⟨R j, hR j, ?_⟩
  intro N
  obtain ⟨n, ⟨t, ht, hd⟩, hn⟩ := (hj.and_eventually (eventually_ge_atTop N)).exists
  exact ⟨t, hn.trans ht, hd⟩

/-- Step 9 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
arbitrarily long prefixes with a fixed proportional discrepancy rule out both a
finite output and an infinite output whose frequency tends to one half. -/
private lemma not_isMisesKLRandom_of_plainK_lt_frequency
    (c : ℕ → BitString) (hc : ∀ t, c t <+: c (t + 1)) (δ : ℝ) (hδ : 0 < δ)
    (hdev : ∀ N : ℕ, ∃ t : ℕ, N ≤ (c t).length ∧
      δ * (c t).length ≤ |((c t).count true : ℝ) - (c t).count false|) :
    ¬ FiniteOrFreq (1 / 2) (streamOfChain c hc) := by
  have hprefix (t : ℕ) : BitStream.finite (c t) ≤ streamOfChain c hc :=
    (BitStream.finite_le_ofPrefixSet_iff (isStreamPrefixSet_chainPrefixSet hc) _).mpr
      ⟨t, List.prefix_rfl⟩
  cases hs : streamOfChain c hc with
  | finite x =>
      obtain ⟨t, hlen, _⟩ := hdev (x.length + 1)
      have hp := hprefix t
      rw [hs] at hp
      have : (c t).length ≤ x.length := List.IsPrefix.length_le hp
      omega
  | infinite u =>
      intro hu
      change HasLimitFreq (1 / 2) u at hu
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu (δ / 4) (by positivity)
      obtain ⟨t, ht, hd⟩ := hdev (max N 1)
      have hlen : 0 < (c t).length := by omega
      have hp := hprefix t
      rw [hs] at hp
      have heq : cantorPrefix u (c t).length = c t :=
        (isCantorPrefix_iff_cantorPrefix_eq _ _).mp hp
      have hf := hN (c t).length (by omega)
      rw [Real.dist_eq] at hf
      have hf' : |((c t).count true : ℝ) / (c t).length - 1 / 2| < δ / 4 := by
        simpa only [freqOne, Rat.cast_div, Rat.cast_natCast, heq] using hf
      have hsum : ((c t).count true : ℝ) + (c t).count false = (c t).length := by
        exact_mod_cast List.count_true_add_count_false (c t)
      have hn : (0 : ℝ) < (c t).length := by exact_mod_cast hlen
      have hid : ((c t).count true : ℝ) - (c t).count false =
          2 * ((c t).length : ℝ) *
            (((c t).count true : ℝ) / (c t).length - 1 / 2) := by
        field_simp
        nlinarith
      rw [hid, abs_mul, abs_of_pos (by positivity : 0 < 2 * ((c t).length : ℝ))] at hd
      nlinarith

/-- **SUV Theorem 193, p. 293 (Muchnik).**  If `C(ω_0 … ω_{n-1}) < αn` for some `α < 1` and all
sufficiently large `n`, then `ω` is not Mises-Kolmogorov-Loveland random. -/
theorem not_isMisesKLRandom_of_plainK_lt (V : Map) (hV : isOptimalConditional V) {α : ℝ}
    (hα : α < 1) {w : CantorSeq}
    (hC : ∀ᶠ n : ℕ in atTop, ((plainK V (cantorPrefix w n)).toNat : ℝ) < α * n) :
    ¬ IsMisesKLRandom w := by
  have hC' : ∃ᶠ n : ℕ in atTop, ((plainK V (cantorPrefix w n)).toNat : ℝ) < α * n :=
    hC.frequently
  have hdim := not_isMisesKLRandom_of_plainK_lt_low_dimension ∅ V hV hα hC'
  obtain ⟨β, hαβ, hβ1⟩ := exists_rat_btwn hα
  have hβ0 : (0 : ℝ) < β :=
    (not_isMisesKLRandom_of_plainK_lt_nonneg ∅ w).trans_lt (hdim.trans_lt hαβ)
  have hβ0' : (0 : ℚ) < β := by exact_mod_cast hβ0
  have hβ1' : β < (1 : ℚ) := by exact_mod_cast hβ1
  obtain ⟨k, r, hr, h₀, h₁⟩ :=
    not_isMisesKLRandom_of_plainK_lt_split w β (hdim.trans_lt hαβ)
  obtain ⟨E, hE, hweight, hhit⟩ :=
    not_isMisesKLRandom_of_plainK_lt_enumeration
      (not_isMisesKLRandom_of_plainK_lt_background w k r) β hβ0' hβ1'
  obtain ⟨M, ε, F, hM, hε, hε1, hF, hlocal⟩ :=
    not_isMisesKLRandom_of_plainK_lt_finite_selection β hβ0' hβ1'
  have hh : ∀ b : Bool, ∀ m N : ℕ, ∃ n t : ℕ, N < n ∧
      E t = some (cantorPrefix (fun i =>
        not_isMisesKLRandom_of_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n) := by
    intro b
    cases b
    · simpa using hhit _ h₀
    · simpa using hhit _ h₁
  obtain ⟨R, hR, hs⟩ := not_isMisesKLRandom_of_plainK_lt_scheduler
    w k r hr β E hE hweight hh M ε F hM hε hε1 hF hlocal
  obtain ⟨ρ, hρ, hdev⟩ := not_isMisesKLRandom_of_plainK_lt_pigeonhole
    w (2 * M) R hR ((ε : ℝ) / 4) hs
  have hδ : (0 : ℝ) < (ε : ℝ) / 4 := div_pos (by exact_mod_cast hε) (by norm_num)
  intro hw
  exact not_isMisesKLRandom_of_plainK_lt_frequency
    (ρ.outputChain w) (ρ.outputChain_prefix w) ((ε : ℝ) / 4) hδ hdev (hw ρ hρ)


/-- The subsequence in residue class `r` modulo `2 ^ k`. -/
private def not_isMisesKLRandom_of_frequently_plainK_lt_column
    (w : CantorSeq) (k r : ℕ) : CantorSeq := fun n => w (2 ^ k * n + r)

/-- The bits outside a dyadic column, with all positions in the column masked to zero. -/
private def not_isMisesKLRandom_of_frequently_plainK_lt_background
    (w : CantorSeq) (k r : ℕ) : Set ℕ := {n | n % 2 ^ k ≠ r ∧ w n = true}

/-- Step 1 of the proof of `not_isMisesKLRandom_of_frequently_plainK_lt`:
an oracle prefix description can encode an ordinary shortest plain program with a
self-delimiting description of its length. The overhead is logarithmic in that length. -/
private lemma not_isMisesKLRandom_of_frequently_plainK_lt_prefix_cost
    (A : Set ℕ) (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x : BitString,
      PointToSet.oracleComplexity A x ≤ (plainK V x).toNat +
        2 * (Nat.bits (plainK V x).toNat).length + c := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c₁, hc₁⟩ := (PointToSet.exists_optimalOraclePrefix_spec A).2.2 U
    ((PointToSet.isDecompressorIn_iff_partrecIn _ _).mpr hU.isDecompressor.partrecIn)
    hU.isPrefixMachine
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨c₃, hc₃⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c₁ + c₂ + c₃, fun x => ?_⟩
  have hfinite : plainK V x ≠ ⊤ := by
    obtain ⟨c, hc⟩ := plainK_le_length V hV
    exact ne_top_of_le_natCast_add (hc x)
  have hx : plainK V x = ((plainK V x).toNat : ℕ∞) :=
    (ENat.natCast_toNat hfinite).symm
  have h : KPPlain (PointToSet.optimalOraclePrefix A) x ≤
      (((plainK V x).toNat + 2 * (Nat.bits (plainK V x).toNat).length +
        (c₁ + c₂ + c₃) : ℕ) : ℕ∞) := by
    calc
      KPPlain (PointToSet.optimalOraclePrefix A) x ≤ KPPlain U x + c₁ := hc₁ x []
      _ ≤ ((plainK V x).toNat : ℕ∞) +
          KPPlain U (Nat.bits (plainK V x).toNat) + c₂ + c₁ := by
        gcongr
        exact hc₂ x _ hx
      _ ≤ ((plainK V x).toNat : ℕ∞) +
          (2 * ((Nat.bits (plainK V x).toNat).length : ℕ∞) + c₃) + c₂ + c₁ := by
        gcongr
        exact hc₃ _
      _ = _ := by push_cast; ring
  exact ENat.natCast_le_natCast.mp (by
    simpa only [PointToSet.oracleComplexity, PointToSet.oraclePrefixComplexity_coe,
      PointToSet.oraclePrefixComplexity, KPPlain] using h)

/-- Step 2 of the proof of `not_isMisesKLRandom_of_frequently_plainK_lt`:
infinitely often plain compression bounds the lower prefix-complexity density, even
with an oracle; the logarithmic conversion cost in Step 1 vanishes after normalization. -/
private lemma not_isMisesKLRandom_of_frequently_plainK_lt_low_dimension
    (A : Set ℕ) (V : Map) (hV : isOptimalConditional V) {α : ℝ} (hα : α < 1)
    {w : CantorSeq}
    (hC : ∃ᶠ n : ℕ in atTop, ((plainK V (cantorPrefix w n)).toNat : ℝ) < α * n) :
    Applications.oraclePrefixDim A w ≤ α := by
  obtain ⟨c, hc⟩ := not_isMisesKLRandom_of_frequently_plainK_lt_prefix_cost A V hV
  apply le_of_forall_gt_imp_ge_of_dense
  intro β hαβ
  have hs := PointToSet.normalized_additive_slack_logSlack (c + 2)
  have he : ∀ᶠ n : ℕ in atTop, (logSlack (c + 2) n : ℝ) / n < β - α :=
    hs.eventually (gt_mem_nhds (sub_pos.mpr hαβ))
  have hf : ∃ᶠ n : ℕ in atTop,
      (PointToSet.oracleComplexity A (cantorPrefix w n) : ℝ) / n ≤ β := by
    apply ((hC.and_eventually he).and_eventually (eventually_gt_atTop 0)).mono
    rintro n ⟨⟨hn, hslack⟩, hnpos⟩
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hk : (plainK V (cantorPrefix w n)).toNat ≤ n := by
      have hkn : ((plainK V (cantorPrefix w n)).toNat : ℝ) < n := by
        nlinarith
      exact_mod_cast hkn.le
    have hbits : (Nat.bits (plainK V (cantorPrefix w n)).toNat).length ≤
        (Nat.bits n).length := by
      simpa only [← Nat.size_eq_bits_len] using Nat.size_le_size hk
    have hover : 2 * (Nat.bits (plainK V (cantorPrefix w n)).toNat).length + c ≤
        logSlack (c + 2) n := by
      unfold logSlack
      nlinarith
    have hcost : (PointToSet.oracleComplexity A (cantorPrefix w n) : ℝ) ≤
        (plainK V (cantorPrefix w n)).toNat + (logSlack (c + 2) n : ℝ) := by
      have hcost := hc (cantorPrefix w n)
      have hcost' : PointToSet.oracleComplexity A (cantorPrefix w n) ≤
          (plainK V (cantorPrefix w n)).toNat + logSlack (c + 2) n := by omega
      exact_mod_cast hcost'
    apply (div_le_iff₀ hnR).mpr
    have hh := (div_lt_iff₀ hnR).mp hslack
    nlinarith
  exact liminf_le_of_frequently_le hf (isBoundedUnder_of ⟨0, fun n => by positivity⟩)

/-- Step 3 of the proof of `not_isMisesKLRandom_of_frequently_plainK_lt`:
relative prefix-complexity densities are nonnegative. -/
private lemma not_isMisesKLRandom_of_frequently_plainK_lt_nonneg
    (A : Set ℕ) (u : CantorSeq) : 0 ≤ Applications.oraclePrefixDim A u := by
  unfold Applications.oraclePrefixDim
  rw [Filter.liminf_eq]
  exact Real.sSup_nonneg' ⟨0, Filter.Eventually.of_forall (fun n => by positivity), le_rfl⟩

/-- Step 4 of the proof of `not_isMisesKLRandom_of_frequently_plainK_lt`:
literal prefix descriptions bound the relative prefix complexity by twice the
length plus a constant, ensuring bounded normalized complexities. -/
private lemma not_isMisesKLRandom_of_frequently_plainK_lt_length_bound
    (A : Set ℕ) :
    ∃ c : ℕ, ∀ x : BitString, PointToSet.oracleComplexity A x ≤ 2 * x.length + c := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c₁, hc₁⟩ := (PointToSet.exists_optimalOraclePrefix_spec A).2.2 U
    ((PointToSet.isDecompressorIn_iff_partrecIn _ _).mpr hU.isDecompressor.partrecIn)
    hU.isPrefixMachine
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c₂ + c₁, fun x => ?_⟩
  have hb : KPPlain (PointToSet.optimalOraclePrefix A) x ≤
      ((2 * x.length + (c₂ + c₁) : ℕ) : ℕ∞) := by
    calc
      KPPlain (PointToSet.optimalOraclePrefix A) x ≤ KPPlain U x + c₁ := hc₁ x []
      _ ≤ (2 * (x.length : ℕ∞) + c₂) + c₁ := by gcongr; exact hc₂ x
      _ = _ := by push_cast; ring
  exact ENat.natCast_le_natCast.mp (by
    simpa only [PointToSet.oracleComplexity, PointToSet.oraclePrefixComplexity_coe,
      PointToSet.oraclePrefixComplexity, KPPlain] using hb)

/-- Step 4 of the proof of `not_isMisesKLRandom_of_frequently_plainK_lt`:
normalized relative prefix complexities are bounded above, as needed for real
liminf arguments. -/
private lemma not_isMisesKLRandom_of_frequently_plainK_lt_bounded
    (A : Set ℕ) (u : CantorSeq) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (PointToSet.oracleComplexity A (cantorPrefix u n) : ℝ) / n) := by
  obtain ⟨c, hc⟩ := not_isMisesKLRandom_of_frequently_plainK_lt_length_bound A
  refine ⟨2 + (c : ℝ), ?_⟩
  change ∀ᶠ n : ℕ in atTop,
    (PointToSet.oracleComplexity A (cantorPrefix u n) : ℝ) / n ≤ 2 + (c : ℝ)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcost : (PointToSet.oracleComplexity A (cantorPrefix u n) : ℝ) ≤ 2 * n + c := by
    have h := hc (cantorPrefix u n)
    rw [cantorPrefix_length] at h
    exact_mod_cast h
  apply (div_le_iff₀ hnR).mpr
  nlinarith [show (0 : ℝ) ≤ c by positivity]

/-- Step 4 of the proof of `not_isMisesKLRandom_of_frequently_plainK_lt`:
normalizing a finite chain inequality and letting its logarithmic slack vanish
gives the corresponding lower-density inequality. -/
private lemma not_isMisesKLRandom_of_frequently_plainK_lt_normalize
    (a b p : ℕ → ℕ) (c : ℕ)
    (hp : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (p n : ℝ) / n))
    (hfinite : ∀ n, a (n / 2) + b (n / 2) ≤ p n + logSlack c n) :
    ((liminf (fun n : ℕ => (a n : ℝ) / n) atTop) +
      liminf (fun n : ℕ => (b n : ℝ) / n) atTop) / 2 ≤
      liminf (fun n : ℕ => (p n : ℝ) / n) atTop := by
  have hhalf : Tendsto (fun n : ℕ => ((n / 2 : ℕ) : ℝ) / n) atTop (𝓝 (1 / 2)) := by
    have hmod := tendsto_mod_div_atTop_nhds_zero_nat (show 0 < (2 : ℕ) by omega)
    have heq : (fun n : ℕ => ((n / 2 : ℕ) : ℝ) / n) =ᶠ[atTop]
        (fun n : ℕ => (1 - ((n % 2 : ℕ) : ℝ) / n) / 2) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have h : ((n % 2 : ℕ) : ℝ) + 2 * ((n / 2 : ℕ) : ℝ) = n := by
        exact_mod_cast (Nat.mod_add_div n 2)
      field_simp
      nlinarith
    exact Tendsto.congr' heq.symm (by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hmod).div_const 2)
  let da := liminf (fun n : ℕ => (a n : ℝ) / n) atTop
  let db := liminf (fun n : ℕ => (b n : ℝ) / n) atTop
  let dp := liminf (fun n : ℕ => (p n : ℝ) / n) atTop
  have hbnd (v : ℕ → ℕ) : IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => (v n : ℝ) / n) := isBoundedUnder_of ⟨0, fun n => by positivity⟩
  have hlow (x y : ℝ) (hx : x < da) (hy : y < db) : (x + y) / 2 ≤ dp := by
    have ha := (Nat.tendsto_div_const_atTop (show 2 ≠ 0 by omega)).eventually
      (eventually_lt_of_lt_liminf hx (hbnd a))
    have hb := (Nat.tendsto_div_const_atTop (show 2 ≠ 0 by omega)).eventually
      (eventually_lt_of_lt_liminf hy (hbnd b))
    have ht : Tendsto (fun n : ℕ =>
        (x + y) * (((n / 2 : ℕ) : ℝ) / n) - (logSlack c n : ℝ) / n)
        atTop (𝓝 ((x + y) / 2)) := by
      simpa [div_eq_mul_inv] using (hhalf.const_mul (x + y)).sub
        (PointToSet.normalized_additive_slack_logSlack c)
    have he : ∀ᶠ n : ℕ in atTop,
        (x + y) * (((n / 2 : ℕ) : ℝ) / n) - (logSlack c n : ℝ) / n ≤ (p n : ℝ) / n := by
      filter_upwards [ha, hb, eventually_ge_atTop 2] with n han hbn hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hdivR : (0 : ℝ) < (n / 2 : ℕ) := by exact_mod_cast (show 0 < n / 2 by omega)
      have han' := (lt_div_iff₀ hdivR).mp han
      have hbn' := (lt_div_iff₀ hdivR).mp hbn
      have hfn : (a (n / 2) : ℝ) + (b (n / 2) : ℝ) ≤ p n + (logSlack c n : ℝ) := by
        exact_mod_cast hfinite n
      rw [← mul_div_assoc, ← sub_div, div_le_div_iff_of_pos_right hnR]
      nlinarith
    by_contra! hlt
    obtain ⟨z, hz₀, hz₁⟩ := exists_between hlt
    have hf := frequently_lt_of_liminf_lt hp.isCoboundedUnder_ge hz₀
    obtain ⟨n, ⟨hn, hne⟩, hnt⟩ :=
      ((hf.and_eventually he).and_eventually (ht.eventually (lt_mem_nhds hz₁))).exists
    linarith
  by_contra! hlt
  have hx : da - ((da + db) / 2 - dp) / 2 < da := by linarith
  have hy : db - ((da + db) / 2 - dp) / 2 < db := by linarith
  have h := hlow _ _ hx hy
  linarith

/-- Step 4 of the proof of `not_isMisesKLRandom_of_frequently_plainK_lt`:
the finite, relativized chain inequality for a column and its even and odd parts.
In each ordering, the second description may use the first part as an oracle.
Relative symmetry of information, followed by encoding the length and the first
complexity in logarithmic space, gives this inequality. Both children have length
`n / 2`, so an odd final bit of the parent is simply discarded. -/
private lemma not_isMisesKLRandom_of_frequently_plainK_lt_finite_chain
    (w : CantorSeq) (k r : ℕ) (hr : r < 2 ^ k) :
    let col := not_isMisesKLRandom_of_frequently_plainK_lt_column w
    let bg := not_isMisesKLRandom_of_frequently_plainK_lt_background w
    ∃ c : ℕ, ∀ n : ℕ,
      PointToSet.oracleComplexity (bg k r) (cantorPrefix (col (k + 1) r) (n / 2)) +
          PointToSet.oracleComplexity (bg (k + 1) (r + 2 ^ k))
            (cantorPrefix (col (k + 1) (r + 2 ^ k)) (n / 2)) ≤
        PointToSet.oracleComplexity (bg k r) (cantorPrefix (col k r) n) + logSlack c n ∧
      PointToSet.oracleComplexity (bg k r)
          (cantorPrefix (col (k + 1) (r + 2 ^ k)) (n / 2)) +
          PointToSet.oracleComplexity (bg (k + 1) r) (cantorPrefix (col (k + 1) r) (n / 2)) ≤
        PointToSet.oracleComplexity (bg k r) (cantorPrefix (col k r) n) + logSlack c n := by
  intro col bg
  exact not_isMisesKLRandom_of_plainK_lt_finite_chain w k r hr

/-- Step 4 of the proof of `not_isMisesKLRandom_of_frequently_plainK_lt`:
the relativized complexity chain rule for a dyadic column and its two halves.
In either ordering, its density is at least half the density of the first half
with the old background plus half the density of the second half with the first
half added to the background. This is the equal-density instance of Lemma 40 of
Merkle--Miller--Nies--Reimann--Stephan, *Kolmogorov-Loveland randomness and stochasticity*.
The additional oracle is exactly the complement of the second column, not an
arbitrarily chosen oracle. -/
private lemma not_isMisesKLRandom_of_frequently_plainK_lt_chain
    (w : CantorSeq) (k r : ℕ) (hr : r < 2 ^ k) :
    let col := not_isMisesKLRandom_of_frequently_plainK_lt_column w
    let bg := not_isMisesKLRandom_of_frequently_plainK_lt_background w
    (Applications.oraclePrefixDim (bg k r) (col (k + 1) r) +
        Applications.oraclePrefixDim (bg (k + 1) (r + 2 ^ k))
          (col (k + 1) (r + 2 ^ k))) / 2 ≤
      Applications.oraclePrefixDim (bg k r) (col k r) ∧
    (Applications.oraclePrefixDim (bg k r) (col (k + 1) (r + 2 ^ k)) +
        Applications.oraclePrefixDim (bg (k + 1) r) (col (k + 1) r)) / 2 ≤
      Applications.oraclePrefixDim (bg k r) (col k r) := by
  let col := not_isMisesKLRandom_of_frequently_plainK_lt_column w
  let bg := not_isMisesKLRandom_of_frequently_plainK_lt_background w
  obtain ⟨c, hc⟩ := not_isMisesKLRandom_of_frequently_plainK_lt_finite_chain w k r hr
  have hp := not_isMisesKLRandom_of_frequently_plainK_lt_bounded (bg k r) (col k r)
  constructor
  · exact not_isMisesKLRandom_of_frequently_plainK_lt_normalize
      (fun n => PointToSet.oracleComplexity (bg k r) (cantorPrefix (col (k + 1) r) n))
      (fun n => PointToSet.oracleComplexity (bg (k + 1) (r + 2 ^ k))
        (cantorPrefix (col (k + 1) (r + 2 ^ k)) n))
      (fun n => PointToSet.oracleComplexity (bg k r) (cantorPrefix (col k r) n))
      c hp (fun n => (hc n).1)
  · exact not_isMisesKLRandom_of_frequently_plainK_lt_normalize
      (fun n => PointToSet.oracleComplexity (bg k r)
        (cantorPrefix (col (k + 1) (r + 2 ^ k)) n))
      (fun n => PointToSet.oracleComplexity (bg (k + 1) r) (cantorPrefix (col (k + 1) r) n))
      (fun n => PointToSet.oracleComplexity (bg k r) (cantorPrefix (col k r) n))
      c hp (fun n => (hc n).2)

/-- Step 5 of the proof of `not_isMisesKLRandom_of_frequently_plainK_lt`:
choose a column whose conditional density is near the infimum over all dyadic
columns. Applying Step 4 in both orders gives two halves whose densities, relative
to the same complementary bits, are below the prescribed strict upper bound.
This is the strict-bound version of Bienvenu's splitting argument (Lemma 12 of
*Kolmogorov-Loveland stochasticity and Kolmogorov complexity*). -/
private lemma not_isMisesKLRandom_of_frequently_plainK_lt_split
    (w : CantorSeq) (β : ℝ) (hw : Applications.oraclePrefixDim ∅ w < β) :
    ∃ k r : ℕ, r < 2 ^ k ∧
      Applications.oraclePrefixDim
        (not_isMisesKLRandom_of_frequently_plainK_lt_background w k r)
        (not_isMisesKLRandom_of_frequently_plainK_lt_column w (k + 1) r) < β ∧
      Applications.oraclePrefixDim
        (not_isMisesKLRandom_of_frequently_plainK_lt_background w k r)
        (not_isMisesKLRandom_of_frequently_plainK_lt_column w (k + 1) (r + 2 ^ k)) < β := by
  let col := not_isMisesKLRandom_of_frequently_plainK_lt_column w
  let bg := not_isMisesKLRandom_of_frequently_plainK_lt_background w
  let D : Set ℝ := {d | ∃ k r : ℕ, r < 2 ^ k ∧ d =
    Applications.oraclePrefixDim (bg k r) (col k r)}
  have hroot : Applications.oraclePrefixDim ∅ w ∈ D := by
    refine ⟨0, 0, by norm_num, ?_⟩
    have hb0 : bg 0 0 = ∅ := by
      ext n
      simp [bg, not_isMisesKLRandom_of_frequently_plainK_lt_background, Nat.mod_one]
    have hc0 : col 0 0 = w := by
      funext n
      simp [col, not_isMisesKLRandom_of_frequently_plainK_lt_column]
    rw [hb0, hc0]
  have hD : D.Nonempty := ⟨_, hroot⟩
  have hb : BddBelow D := by
    refine ⟨0, ?_⟩
    rintro d ⟨k, r, hr, rfl⟩
    exact not_isMisesKLRandom_of_frequently_plainK_lt_nonneg _ _
  have ht : sInf D < β := (csInf_le hb hroot).trans_lt hw
  obtain ⟨d, ⟨k, r, hr, rfl⟩, hd⟩ :=
    exists_lt_of_csInf_lt hD (show sInf D < (β + sInf D) / 2 by linarith)
  have hr₀ : r < 2 ^ (k + 1) := by rw [pow_succ]; omega
  have hr₁ : r + 2 ^ k < 2 ^ (k + 1) := by rw [pow_succ]; omega
  have h₀ : sInf D ≤ Applications.oraclePrefixDim (bg (k + 1) r) (col (k + 1) r) :=
    csInf_le hb ⟨k + 1, r, hr₀, rfl⟩
  have h₁ : sInf D ≤ Applications.oraclePrefixDim (bg (k + 1) (r + 2 ^ k))
      (col (k + 1) (r + 2 ^ k)) :=
    csInf_le hb ⟨k + 1, r + 2 ^ k, hr₁, rfl⟩
  have hchain := not_isMisesKLRandom_of_frequently_plainK_lt_chain w k r hr
  change (_ + _) / 2 ≤ _ ∧ (_ + _) / 2 ≤ _ at hchain
  exact ⟨k, r, hr, by change Applications.oraclePrefixDim (bg k r) _ < β; linarith [hchain.1],
    by change Applications.oraclePrefixDim (bg k r) _ < β; linarith [hchain.2]⟩

/-- Step 6 of the proof of `not_isMisesKLRandom_of_frequently_plainK_lt`:
dropping a fixed number of symbols costs only a constant in relative complexity.
Thus a strict bound on lower complexity density gives arbitrarily long
compressible prefixes of each tail, with the same strict rate bound. -/
private lemma not_isMisesKLRandom_of_frequently_plainK_lt_tails
    (A : Set ℕ) (u : CantorSeq) (β : ℝ)
    (hu : Applications.oraclePrefixDim A u < β) (m N : ℕ) :
    ∃ n : ℕ, N < n ∧
      (PointToSet.oracleComplexity A (cantorPrefix (fun i => u (m + i)) n) : ℝ) < β * n := by
  let z : ℕ → ℝ := fun n => (PointToSet.oracleComplexity A (cantorPrefix u n) : ℝ) / n
  have hb : IsBoundedUnder (· ≤ ·) atTop z :=
    not_isMisesKLRandom_of_frequently_plainK_lt_bounded A u
  obtain ⟨γ, hγ₀, hγ₁⟩ := exists_between hu
  have hf : ∃ᶠ n : ℕ in atTop, z n < γ :=
    frequently_lt_of_liminf_lt hb.isCoboundedUnder_ge hγ₀
  let F : List BitString →. BitString := fun xs => Part.some (xs.headI.drop m)
  have hF : PartrecIn {charOracle A} F :=
    ((Primrec.list_drop.comp (Primrec.const m) Primrec.list_headI).to_comp).computableIn.partrecIn
  obtain ⟨c, hc⟩ := PointToSet.oracle_tuple_bounds_composition A 1 F hF
  have hdrop (x : BitString) : PointToSet.oracleComplexity A (x.drop m) ≤
      PointToSet.oracleComplexity A x + c := by
    simpa using hc [x] (x.drop m) (by simp) (by simp [F])
  obtain ⟨L, hL⟩ := exists_nat_gt (((c : ℝ) + β * m) / (β - γ))
  obtain ⟨n, hn, hnlarge⟩ :=
    (hf.and_eventually (eventually_gt_atTop (max L (m + N)))).exists
  have hmn : m ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hLn : (L : ℝ) ≤ n := by exact_mod_cast (show L ≤ n by omega)
  have hmargin : (c : ℝ) + β * m < (β - γ) * n := by
    have := (div_lt_iff₀ (sub_pos.mpr hγ₁)).mp hL
    nlinarith
  have hpre : (PointToSet.oracleComplexity A (cantorPrefix u n) : ℝ) < γ * n :=
    (div_lt_iff₀ hnR).mp hn
  have heq : (cantorPrefix u n).drop m =
      cantorPrefix (fun i => u (m + i)) (n - m) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_drop, cantorPrefix_getElem]
  have hcost : (PointToSet.oracleComplexity A
      (cantorPrefix (fun i => u (m + i)) (n - m)) : ℝ) ≤
      PointToSet.oracleComplexity A (cantorPrefix u n) + c := by
    exact_mod_cast (heq ▸ hdrop (cantorPrefix u n))
  refine ⟨n - m, by omega, ?_⟩
  rw [Nat.cast_sub hmn]
  nlinarith

/-- Step 6 of the proof of `not_isMisesKLRandom_of_frequently_plainK_lt`:
relative prefix complexity supplies a Kraft bound on every finite set of strings
whose complexities are less than `β` times their lengths. -/
private lemma not_isMisesKLRandom_of_frequently_plainK_lt_kraft
    (A : Set ℕ) (β : ℝ) (D : Finset BitString)
    (hD : ∀ x ∈ D, (PointToSet.oracleComplexity A x : ℝ) < β * x.length) :
    ∑ x ∈ D, (2 : ℝ) ^ (-β * x.length) ≤ 1 := by
  let U := PointToSet.optimalOraclePrefix A
  have hterm (x : BitString) : complexityWeight (KP U x []) =
      (2 : ENNReal)⁻¹ ^ PointToSet.oracleComplexity A x := by
    rw [← complexityWeight_coe, PointToSet.oracleComplexity,
      PointToSet.oraclePrefixComplexity_coe]
    rfl
  have hsum : (∑' x : BitString, complexityWeight (KP U x [])) ≤ 1 :=
    (ENNReal.tsum_le_tsum (fun x => complexityWeight_KP_le_aprioriMeasure U x [])).trans
      (tsum_aprioriMeasure_le_one U [] (PointToSet.exists_optimalOraclePrefix_spec A).2.1)
  have hfinite : ∀ x ∈ D, complexityWeight (KP U x []) ≠ ⊤ := by
    intro x hx
    rw [hterm]
    exact ENNReal.pow_ne_top (by norm_num)
  have hreal := ENNReal.toReal_mono ENNReal.one_ne_top ((ENNReal.sum_le_tsum D).trans hsum)
  rw [ENNReal.toReal_sum hfinite, ENNReal.toReal_one] at hreal
  have hbound : ∑ x ∈ D, (2 : ℝ)⁻¹ ^ PointToSet.oracleComplexity A x ≤ 1 := by
    simpa only [hterm, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat] using hreal
  apply le_trans (Finset.sum_le_sum (fun x hx => ?_)) hbound
  calc
    (2 : ℝ) ^ (-β * x.length) ≤ (2 : ℝ) ^ (-(PointToSet.oracleComplexity A x : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by have := hD x hx; linarith)
    _ = (2 : ℝ)⁻¹ ^ PointToSet.oracleComplexity A x := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]

/-- Step 6 of the proof of `not_isMisesKLRandom_of_frequently_plainK_lt`:
enumerate the strings with relative prefix complexity below `β` times their
length. Kraft's inequality bounds every finite subset of the enumeration, and
every tail of a sequence of relative dimension below `β` has arbitrarily long
prefixes in it. The same enumeration works for every such sequence and every
tail; no sequence-dependent subsequence of lengths is supplied to the algorithm. -/
private lemma not_isMisesKLRandom_of_frequently_plainK_lt_enumeration
    (A : Set ℕ) (β : ℚ) :
    ∃ E : ℕ → Option BitString,
      ComputableIn {charOracle A} E ∧
      (∀ D : Finset BitString, (∀ x ∈ D, ∃ t, E t = some x) →
        ∑ x ∈ D, (2 : ℝ) ^ (-(β : ℝ) * x.length) ≤ 1) ∧
      ∀ u : CantorSeq, Applications.oraclePrefixDim A u < β →
        ∀ m N : ℕ, ∃ n t : ℕ, N < n ∧
          E t = some (cantorPrefix (fun i => u (m + i)) n) := by
  have hthreshold : Computable (fun x : BitString => (x, β * (x.length : ℚ))) :=
    Computable.id.pair (computable₂_ratMul.comp (Computable.const β)
      (computable_nat_to_rat.comp Computable.list_length))
  have hRE : PointToSet.IsREIn A
      (fun x : BitString => (PointToSet.oracleComplexity A x : ℝ) < (β : ℝ) * x.length) := by
    simpa only [Rat.cast_mul, Rat.cast_natCast] using
      (PointToSet.isREIn_oracleComplexity_lt A).comp hthreshold.computableIn
  obtain ⟨E, hE, henum⟩ := (PointToSet.relative_enumeration A _).mp hRE
  refine ⟨E, hE, ?_, ?_⟩
  · intro D hD
    exact not_isMisesKLRandom_of_frequently_plainK_lt_kraft A β D
      (fun x hx => (henum x).mpr (hD x hx))
  · intro u hu m N
    obtain ⟨n, hn, hcost⟩ :=
      not_isMisesKLRandom_of_frequently_plainK_lt_tails A u β hu m N
    obtain ⟨t, ht⟩ := (henum (cantorPrefix (fun i => u (m + i)) n)).mp (by simpa using hcost)
    exact ⟨n, t, hn, ht⟩

/-- Step 8 of the proof of `not_isMisesKLRandom_of_frequently_plainK_lt`:
a finite pigeonhole argument extracts one admissible rule with arbitrarily long
deviating output prefixes from a finite family of admissible rules. -/
private lemma not_isMisesKLRandom_of_frequently_plainK_lt_pigeonhole
    (w : CantorSeq) (M : ℕ) (R : Fin M → KLRule) (hR : ∀ j, (R j).IsAdmissible)
    (δ : ℝ) (hs : ∀ N : ℕ, ∃ j t,
      N ≤ ((R j).outputChain w t).length ∧
      δ * ((R j).outputChain w t).length ≤
        |(((R j).outputChain w t).count true : ℝ) -
          ((R j).outputChain w t).count false|) :
    ∃ ρ : KLRule, ρ.IsAdmissible ∧ ∀ N : ℕ, ∃ t : ℕ,
      N ≤ (ρ.outputChain w t).length ∧
      δ * (ρ.outputChain w t).length ≤
        |((ρ.outputChain w t).count true : ℝ) - (ρ.outputChain w t).count false| := by
  have hf : ∃ᶠ N : ℕ in atTop, ∃ j : Fin M, ∃ t : ℕ,
      N ≤ ((R j).outputChain w t).length ∧
      δ * ((R j).outputChain w t).length ≤
        |(((R j).outputChain w t).count true : ℝ) -
          ((R j).outputChain w t).count false| :=
    (Filter.Eventually.of_forall hs).frequently
  obtain ⟨j, hj⟩ := Filter.frequently_exists.mp hf
  refine ⟨R j, hR j, ?_⟩
  intro N
  obtain ⟨n, ⟨t, ht, hd⟩, hn⟩ := (hj.and_eventually (eventually_ge_atTop N)).exists
  exact ⟨t, hn.trans ht, hd⟩

/-- Step 9 of the proof of `not_isMisesKLRandom_of_frequently_plainK_lt`:
arbitrarily long prefixes with a fixed proportional discrepancy rule out both a
finite output and an infinite output whose frequency tends to one half. -/
private lemma not_isMisesKLRandom_of_frequently_plainK_lt_frequency
    (c : ℕ → BitString) (hc : ∀ t, c t <+: c (t + 1)) (δ : ℝ) (hδ : 0 < δ)
    (hdev : ∀ N : ℕ, ∃ t : ℕ, N ≤ (c t).length ∧
      δ * (c t).length ≤ |((c t).count true : ℝ) - (c t).count false|) :
    ¬ FiniteOrFreq (1 / 2) (streamOfChain c hc) := by
  have hprefix (t : ℕ) : BitStream.finite (c t) ≤ streamOfChain c hc :=
    (BitStream.finite_le_ofPrefixSet_iff (isStreamPrefixSet_chainPrefixSet hc) _).mpr
      ⟨t, List.prefix_rfl⟩
  cases hs : streamOfChain c hc with
  | finite x =>
      obtain ⟨t, hlen, _⟩ := hdev (x.length + 1)
      have hp := hprefix t
      rw [hs] at hp
      have : (c t).length ≤ x.length := List.IsPrefix.length_le hp
      omega
  | infinite u =>
      intro hu
      change HasLimitFreq (1 / 2) u at hu
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu (δ / 4) (by positivity)
      obtain ⟨t, ht, hd⟩ := hdev (max N 1)
      have hlen : 0 < (c t).length := by omega
      have hp := hprefix t
      rw [hs] at hp
      have heq : cantorPrefix u (c t).length = c t :=
        (isCantorPrefix_iff_cantorPrefix_eq _ _).mp hp
      have hf := hN (c t).length (by omega)
      rw [Real.dist_eq] at hf
      have hf' : |((c t).count true : ℝ) / (c t).length - 1 / 2| < δ / 4 := by
        simpa only [freqOne, Rat.cast_div, Rat.cast_natCast, heq] using hf
      have hsum : ((c t).count true : ℝ) + (c t).count false = (c t).length := by
        exact_mod_cast List.count_true_add_count_false (c t)
      have hn : (0 : ℝ) < (c t).length := by exact_mod_cast hlen
      have hid : ((c t).count true : ℝ) - (c t).count false =
          2 * ((c t).length : ℝ) *
            (((c t).count true : ℝ) / (c t).length - 1 / 2) := by
        field_simp
        nlinarith
      rw [hid, abs_mul, abs_of_pos (by positivity : 0 < 2 * ((c t).length : ℝ))] at hd
      nlinarith

/-- **SUV p. 293, after Theorem 193**, reported by the book as a later strengthening, without proof
or citation there: the inequality for infinitely many `n` is enough. -/
theorem not_isMisesKLRandom_of_frequently_plainK_lt (V : Map) (hV : isOptimalConditional V) {α : ℝ}
    (hα : α < 1) {w : CantorSeq}
    (hC : ∃ᶠ n : ℕ in atTop, ((plainK V (cantorPrefix w n)).toNat : ℝ) < α * n) :
    ¬ IsMisesKLRandom w := by
  have hdim := not_isMisesKLRandom_of_frequently_plainK_lt_low_dimension ∅ V hV hα hC
  obtain ⟨β, hαβ, hβ1⟩ := exists_rat_btwn hα
  have hβ0 : (0 : ℝ) < β :=
    (not_isMisesKLRandom_of_frequently_plainK_lt_nonneg ∅ w).trans_lt (hdim.trans_lt hαβ)
  have hβ0' : (0 : ℚ) < β := by exact_mod_cast hβ0
  have hβ1' : β < (1 : ℚ) := by exact_mod_cast hβ1
  obtain ⟨k, r, hr, h₀, h₁⟩ :=
    not_isMisesKLRandom_of_frequently_plainK_lt_split w β (hdim.trans_lt hαβ)
  obtain ⟨E, hE, hweight, hhit⟩ :=
    not_isMisesKLRandom_of_frequently_plainK_lt_enumeration
      (not_isMisesKLRandom_of_frequently_plainK_lt_background w k r) β
  obtain ⟨M, ε, F, hM, hε, hε1, hF, hlocal⟩ :=
    not_isMisesKLRandom_of_plainK_lt_finite_selection β hβ0' hβ1'
  have hh : ∀ b : Bool, ∀ m N : ℕ, ∃ n t : ℕ, N < n ∧
      E t = some (cantorPrefix (fun i =>
        not_isMisesKLRandom_of_frequently_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n) := by
    intro b
    cases b
    · simpa using hhit _ h₀
    · simpa using hhit _ h₁
  obtain ⟨R, hR, hs⟩ := not_isMisesKLRandom_of_plainK_lt_scheduler
    w k r hr β E hE hweight hh M ε F hM hε hε1 hF hlocal
  obtain ⟨ρ, hρ, hdev⟩ := not_isMisesKLRandom_of_frequently_plainK_lt_pigeonhole
    w (2 * M) R hR ((ε : ℝ) / 4) hs
  have hδ : (0 : ℝ) < (ε : ℝ) / 4 := div_pos (by exact_mod_cast hε) (by norm_num)
  intro hw
  exact not_isMisesKLRandom_of_frequently_plainK_lt_frequency
    (ρ.outputChain w) (ρ.outputChain_prefix w) ((ε : ℝ) / 4) hδ hdev (hw ρ hρ)

end Kolmogorov.FrequencyGames
