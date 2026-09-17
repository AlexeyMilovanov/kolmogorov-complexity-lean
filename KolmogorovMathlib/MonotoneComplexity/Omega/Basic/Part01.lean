/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.Interface.ComputableReals.ClosureProperties
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveReal
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.MonotoneComplexity.SharedCoding
import KolmogorovMathlib.Prefix.OptimalExistence
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria
import KolmogorovMathlib.MonotoneComplexity.Omega.LscBasic
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaPrefixCore
import KolmogorovMathlib.MonotoneComplexity.Omega.UniversalCover
import KolmogorovMathlib.MonotoneComplexity.Omega.PrefixTransfer

/-!
# SUV Section 5.7: the random number `Ω` — basic layer

This module fixes the vocabulary of SUV Section 5.7 (Shen–Uspensky–Vereshchagin,
*Kolmogorov Complexity and Algorithmic Randomness*, pp. 157–172):

* lower semicomputable reals (p. 158: "a real number `α` is lower semicomputable if
  `α` is the limit of some computable non-decreasing sequence of rational numbers");
* effectively null sets of reals and ML-randomness of a *real number* (p. 157);
* the value `cantorReal w` of a binary expansion `w : CantorSeq`;
* the discrete a priori probability indexed by `ℕ`, i.e. maximal lower
  semicomputable semimeasures on the natural numbers (p. 157);
* Chaitin's number `Ω = ∑ₙ m(n)` and the class of `Ω`-numbers (pp. 157, 160);
* **Theorem 100** (p. 157): the binary representation of `Ω` is ML-random.

## Definitional choices frozen here

* Lower semicomputability of a real uses **rational** monotone computable
  approximations, exactly as on p. 158, and is a predicate on `ℝ` (not `ℝ≥0∞`).
  The existing `IsLowerSemicomputableENNReal` is the `ℝ≥0∞`/dyadic rendering used
  by the Chapter 3/4 layers; `isLowerSemicomputableReal_iff_ofReal` is the bridge.
* `Ω` is the **sum of a maximal lower semicomputable semimeasure on `ℕ`**, which is
  the book's definition. The library's `IsUniversalSemimeasure` is indexed by
  `BitString`; `IsUniversalSemimeasureNat` is *defined as its transport* along the
  canonical computable bijection `natBitStringEquiv : ℕ ≃ BitString` of
  `SharedCoding`, so there is exactly one semimeasure hierarchy, and
  `exists_isUniversalSemimeasureNat` is **proved** from `exists_universalSemimeasure`.
* ML-randomness of a real is the p. 157 definition by effectively null sets of
  reals covered by *open* rational intervals; the bridge to sequence randomness is
  Problem 158 in `Exercises.lean`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal
open ComputableReals

/-! ### Lower semicomputable reals (SUV p. 158) -/

/-- Every term of a monotone rational approximation stays below the limit. -/
theorem rat_le_of_monotone_tendsto {α : ℝ} {a : ℕ → ℚ} (hmono : Monotone a)
    (hlim : Filter.Tendsto (fun n => ((a n : ℚ) : ℝ)) Filter.atTop (nhds α)) (n : ℕ) :
    ((a n : ℚ) : ℝ) ≤ α := by
  have hm : Monotone (fun n => ((a n : ℚ) : ℝ)) := fun i j hij => Rat.cast_le.mpr (hmono hij)
  exact hm.ge_of_tendsto hlim n

/-- **SUV Section 5.7.1 (p. 158), the parenthetical equivalent definition.** A real
`α` is lower semicomputable if and only if the set of rational numbers less than
`α` is enumerable. -/
theorem isLowerSemicomputableReal_iff_re_lt (α : ℝ) :
    IsLowerSemicomputableReal α ↔
      ∃ e : ℕ → Option ℚ, Computable e ∧ ∀ r : ℚ, ((r : ℝ) < α ↔ ∃ i, e i = some r) := by
  constructor
  · rintro ⟨a, ha, hamono, halim⟩
    have hu1 : Computable (fun k : ℕ => k.unpair.1) := (Primrec.fst.comp Primrec.unpair).to_comp
    have hu2 : Computable (fun k : ℕ => k.unpair.2) := (Primrec.snd.comp Primrec.unpair).to_comp
    have hro : Computable (fun k : ℕ => ratOfCode k.unpair.1) := computable_ratOfCode.comp hu1
    have han : Computable (fun k : ℕ => a k.unpair.2) := ha.comp hu2
    have hlt : Computable (fun k : ℕ => ratLtPair (ratOfCode k.unpair.1, a k.unpair.2)) :=
      computable_ratLtPair.comp (Computable.pair hro han)
    refine ⟨fun k => if ratOfCode k.unpair.1 < a k.unpair.2 then some (ratOfCode k.unpair.1)
      else none, ?_, ?_⟩
    · refine (Computable.cond hlt (Computable.option_some.comp hro)
        (Computable.const none)).of_eq (fun k => ?_)
      simp only [ratLtPair, Bool.cond_decide]
    · intro r
      constructor
      · intro hr
        obtain ⟨n, hn⟩ := exists_rat_lt_of_tendsto halim hr
        refine ⟨Nat.pair (ratCode r) n, ?_⟩
        simp only [Nat.unpair_pair, ratOfCode_ratCode]
        rw [if_pos hn]
      · rintro ⟨i, hi⟩
        simp only at hi
        by_cases hcase : ratOfCode i.unpair.1 < a i.unpair.2
        · rw [if_pos hcase] at hi
          have hr : r = ratOfCode i.unpair.1 := (Option.some_injective _ hi).symm
          have h1 : ((r : ℚ) : ℝ) < ((a i.unpair.2 : ℚ) : ℝ) := by
            rw [hr]; exact_mod_cast hcase
          exact lt_of_lt_of_le h1 (rat_le_of_monotone_tendsto hamono halim _)
        · rw [if_neg hcase] at hi
          exact absurd hi (by simp)
  · rintro ⟨e, he, hspec⟩
    obtain ⟨r0, hr0⟩ := exists_rat_lt α
    set f : ℕ → ℚ := fun k => (e k).getD r0 with hf
    have hfc : Computable f := Computable.option_getD he (Computable.const r0)
    have hflt : ∀ k, ((f k : ℚ) : ℝ) < α := by
      intro k
      rcases hek : e k with _ | r
      · have : f k = r0 := by simp [hf, hek]
        rw [this]; exact hr0
      · have : f k = r := by simp [hf, hek]
        rw [this]
        exact (hspec r).2 ⟨k, hek⟩
    have hbdd : ∀ n, ((ratRunMax f n : ℚ) : ℝ) ≤ α := by
      intro n
      induction n with
      | zero => exact (hflt 0).le
      | succ n ih =>
          rw [ratRunMax_succ]
          rcases max_cases (ratRunMax f n) (f (n + 1)) with ⟨he2, _⟩ | ⟨he2, _⟩
          · rw [he2]; exact ih
          · rw [he2]; exact (hflt (n + 1)).le
    have hmono : Monotone (fun n => ((ratRunMax f n : ℚ) : ℝ)) :=
      fun i j hij => Rat.cast_le.mpr (monotone_ratRunMax f hij)
    have hbddAbove : BddAbove (Set.range (fun n => ((ratRunMax f n : ℚ) : ℝ))) := by
      refine ⟨α, ?_⟩
      rintro y ⟨n, rfl⟩
      exact hbdd n
    have hsup : (⨆ n, ((ratRunMax f n : ℚ) : ℝ)) = α := by
      refine le_antisymm (ciSup_le hbdd) ?_
      by_contra hcon
      push Not at hcon
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hcon
      obtain ⟨k, hk⟩ := (hspec r).1 hr2
      have hfk : f k = r := by simp [hf, hk]
      have hle : ((r : ℚ) : ℝ) ≤ ⨆ n, ((ratRunMax f n : ℚ) : ℝ) := by
        refine le_trans ?_ (le_ciSup hbddAbove k)
        rw [← hfk]
        exact_mod_cast le_ratRunMax f k
      linarith
    refine ⟨ratRunMax f, computable_ratRunMax hfc, monotone_ratRunMax f, ?_⟩
    rw [← hsup]
    exact tendsto_atTop_ciSup hmono hbddAbove

/-- Forward direction of `isLowerSemicomputableReal_iff_ofReal`. -/
private theorem isLowerSemicomputableENNReal_ofReal_of_isLowerSemicomputableReal
    {α : ℝ} (hα : 0 ≤ α) (h : IsLowerSemicomputableReal α) :
    IsLowerSemicomputableENNReal (ENNReal.ofReal α) := by
  have hofne : ENNReal.ofReal α ≠ ⊤ := ENNReal.ofReal_ne_top
  have hoftoReal : (ENNReal.ofReal α).toReal = α := ENNReal.toReal_ofReal hα
  obtain ⟨a, ha, hamono, halim⟩ := h
  set y : ℕ → ℚ := fun s => max 0 (a s) with hy
  have hyc : Computable y := Computable₂.comp computable₂_ratMax (Computable.const 0) ha
  have hymono : Monotone y := fun i j hij => max_le_max le_rfl (hamono hij)
  have hynn : ∀ s, (0 : ℚ) ≤ y s := fun s => le_max_left _ _
  have hyle : ∀ s, ((y s : ℚ) : ℝ) ≤ α := by
    intro s
    have h1 : ((a s : ℚ) : ℝ) ≤ α := rat_le_of_monotone_tendsto hamono halim s
    rw [hy]
    push_cast
    exact max_le hα h1
  have hylim : Filter.Tendsto (fun s => ((y s : ℚ) : ℝ)) Filter.atTop (nhds α) := by
    have hcast : (fun s => ((y s : ℚ) : ℝ)) = fun s => max 0 ((a s : ℚ) : ℝ) := by
      funext s; rw [hy]; push_cast; rfl
    rw [hcast]
    have hmax := Filter.Tendsto.max (tendsto_const_nhds (x := (0 : ℝ))) halim
    rwa [max_eq_right hα] at hmax
  set n : ℕ → ℕ := fun s => ratDyadicFloor (y s) s with hn
  have hnc : Computable n :=
    Computable₂.comp computable_ratDyadicFloor hyc Computable.id
  have hnfl : ∀ s, n s = ⌊y s * ((2 ^ s : ℕ) : ℚ)⌋₊ :=
    fun s => ratDyadicFloor_eq_natFloor (hynn s) s
  have hnmono : ∀ s, 2 * n s ≤ n (s + 1) := by
    intro s
    rw [hnfl s, hnfl (s + 1)]
    refine Nat.le_floor ?_
    calc ((2 * ⌊y s * ((2 ^ s : ℕ) : ℚ)⌋₊ : ℕ) : ℚ)
        = 2 * (⌊y s * ((2 ^ s : ℕ) : ℚ)⌋₊ : ℚ) := by push_cast; ring
      _ ≤ 2 * (y s * ((2 ^ s : ℕ) : ℚ)) := by
          have hfl : (⌊y s * ((2 ^ s : ℕ) : ℚ)⌋₊ : ℚ) ≤ y s * ((2 ^ s : ℕ) : ℚ) :=
            Nat.floor_le (by positivity)
          linarith
      _ = y s * ((2 ^ (s + 1) : ℕ) : ℚ) := by push_cast; ring
      _ ≤ y (s + 1) * ((2 ^ (s + 1) : ℕ) : ℚ) :=
          mul_le_mul_of_nonneg_right (hymono (Nat.le_succ s)) (by positivity)
  have hdmono : ∀ s, dyadicValue (n s) s ≤ dyadicValue (n (s + 1)) (s + 1) := by
    intro s
    rw [← dyadicValue_two_mul_succ (n s) s]
    exact dyadicValue_le_of_le (hnmono s)
  have hele : ∀ s, ((n s : ℕ) : ℝ) / 2 ^ s ≤ α := by
    intro s
    have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    rw [div_le_iff₀ hp]
    have hfl : ((n s : ℕ) : ℚ) ≤ y s * ((2 ^ s : ℕ) : ℚ) := by
      rw [hnfl s]
      exact Nat.floor_le (by positivity)
    have hflR : ((n s : ℕ) : ℝ) ≤ ((y s : ℚ) : ℝ) * (2 : ℝ) ^ s := by
      have := (Rat.cast_le (K := ℝ)).2 hfl
      push_cast at this
      exact this
    have h2 := hyle s
    nlinarith [hp, h2, hflR]
  have helim : Filter.Tendsto (fun s => ((n s : ℕ) : ℝ) / 2 ^ s) Filter.atTop (nhds α) := by
    have hlow : ∀ s, ((y s : ℚ) : ℝ) - (1 : ℝ) / 2 ^ s ≤ ((n s : ℕ) : ℝ) / 2 ^ s := by
      intro s
      have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
      have hfl : y s * ((2 ^ s : ℕ) : ℚ) < ((n s : ℕ) : ℚ) + 1 := by
        rw [hnfl s]
        exact Nat.lt_floor_add_one _
      have hflR : ((y s : ℚ) : ℝ) * (2 : ℝ) ^ s < ((n s : ℕ) : ℝ) + 1 := by
        have := (Rat.cast_lt (K := ℝ)).2 hfl
        push_cast at this
        exact this
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hp]
      nlinarith [hflR, hp]
    have hup : ∀ s, ((n s : ℕ) : ℝ) / 2 ^ s ≤ ((y s : ℚ) : ℝ) := by
      intro s
      have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
      rw [div_le_iff₀ hp]
      have hfl : ((n s : ℕ) : ℚ) ≤ y s * ((2 ^ s : ℕ) : ℚ) := by
        rw [hnfl s]
        exact Nat.floor_le (by positivity)
      have := (Rat.cast_le (K := ℝ)).2 hfl
      push_cast at this
      exact this
    have hzero : Filter.Tendsto (fun s : ℕ => ((y s : ℚ) : ℝ) - (1 : ℝ) / 2 ^ s)
        Filter.atTop (nhds α) := by
      have hg : Filter.Tendsto (fun s : ℕ => (1 : ℝ) / 2 ^ s) Filter.atTop (nhds 0) := by
        have h12_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
        have h12_lt : (1 : ℝ) / 2 < 1 := by norm_num
        simpa using tendsto_pow_atTop_nhds_zero_of_lt_one h12_nn h12_lt
      have := hylim.sub hg
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hzero hylim hlow hup
  refine ⟨n, hdmono, ?_, hnc⟩
  have hdval : ∀ s, dyadicValue (n s) s = ENNReal.ofReal (((n s : ℕ) : ℝ) / 2 ^ s) :=
    fun s => (ofReal_toReal_dyadicValue (n s) s).symm
  refine le_antisymm (iSup_le (fun s => ?_)) ?_
  · rw [hdval s]
    exact ENNReal.ofReal_le_ofReal (hele s)
  · by_contra hcon
    push Not at hcon
    have hSne : (⨆ s, dyadicValue (n s) s) ≠ ⊤ := ne_top_of_lt hcon
    have hStoReal : (⨆ s, dyadicValue (n s) s).toReal < α := by
      rw [← hoftoReal]
      exact (ENNReal.toReal_lt_toReal hSne hofne).2 hcon
    have hex : ∃ s, (⨆ s, dyadicValue (n s) s).toReal < ((n s : ℕ) : ℝ) / 2 ^ s := by
      by_contra hcon2
      push Not at hcon2
      have := le_of_tendsto' helim hcon2
      linarith
    obtain ⟨s, hs⟩ := hex
    have h1 : (⨆ t, dyadicValue (n t) t) < dyadicValue (n s) s := by
      rw [hdval s]
      rw [← ENNReal.ofReal_toReal hSne]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2 hs
    exact absurd (le_iSup (fun t => dyadicValue (n t) t) s) (not_le.2 h1)

/-- Backward direction of `isLowerSemicomputableReal_iff_ofReal`. -/
private theorem isLowerSemicomputableReal_of_isLowerSemicomputableENNReal_ofReal
    {α : ℝ} (hα : 0 ≤ α) (h : IsLowerSemicomputableENNReal (ENNReal.ofReal α)) :
    IsLowerSemicomputableReal α := by
  have hofne : ENNReal.ofReal α ≠ ⊤ := ENNReal.ofReal_ne_top
  have hoftoReal : (ENNReal.ofReal α).toReal = α := ENNReal.toReal_ofReal hα
  obtain ⟨approx, hmono, hsup, hac⟩ := h
  set c : ℕ → ℚ := fun s => (approx s : ℚ) / 2 ^ s with hc
  have hcc : Computable c := by
    refine computable_of_num_den (f := c) (N := fun s => ((approx s : ℕ) : ℤ))
      (D := fun s => 2 ^ s) (ComputableReals.primrec_natCastInt.to_comp.comp hac)
      (((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id).to_comp)
      (fun s => by positivity) (fun s => ?_)
    rw [hc]
    push_cast
    ring
  have hdle : ∀ s, dyadicValue (approx s) s ≤ ENNReal.ofReal α := by
    intro s
    rw [← hsup]
    exact le_iSup (fun t => dyadicValue (approx t) t) s
  have hdne : ∀ s, dyadicValue (approx s) s ≠ ⊤ := fun s => dyadicValue_ne_top _ _
  have hcast : ∀ s, ((c s : ℚ) : ℝ) = (dyadicValue (approx s) s).toReal := by
    intro s
    rw [toReal_dyadicValue, hc]
    push_cast
    ring
  have hble : ∀ s, ((c s : ℚ) : ℝ) ≤ α := by
    intro s
    rw [hcast s, ← hoftoReal]
    exact ENNReal.toReal_mono hofne (hdle s)
  have hmonoR : Monotone (fun s => ((c s : ℚ) : ℝ)) := by
    refine monotone_nat_of_le_succ (fun s => ?_)
    rw [hcast s, hcast (s + 1)]
    exact ENNReal.toReal_mono (hdne (s + 1)) (hmono s)
  have hbddAbove : BddAbove (Set.range (fun s => ((c s : ℚ) : ℝ))) := by
    refine ⟨α, ?_⟩
    rintro z ⟨s, rfl⟩
    exact hble s
  have hc0 : (0 : ℝ) ≤ ⨆ s, ((c s : ℚ) : ℝ) := by
    refine le_trans ?_ (le_ciSup hbddAbove 0)
    rw [hcast 0]
    exact ENNReal.toReal_nonneg
  have hsupR : (⨆ s, ((c s : ℚ) : ℝ)) = α := by
    refine le_antisymm (ciSup_le hble) ?_
    by_contra hcon
    push Not at hcon
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hcon
    have hrpos : (0 : ℝ) ≤ ((r : ℚ) : ℝ) := le_of_lt (lt_of_le_of_lt hc0 hr1)
    have hlt : ENNReal.ofReal ((r : ℚ) : ℝ) < ENNReal.ofReal α := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal hrpos hofne, hoftoReal]
      exact hr2
    rw [← hsup] at hlt
    obtain ⟨s, hs⟩ := lt_iSup_iff.mp hlt
    have hrs : ((r : ℚ) : ℝ) < ((c s : ℚ) : ℝ) := by
      rw [hcast s, ← ENNReal.ofReal_lt_iff_lt_toReal hrpos (hdne s)]
      exact hs
    have hle2 := le_ciSup hbddAbove s
    linarith
  refine ⟨c, hcc, ?_, ?_⟩
  · intro i j hij
    have hij2 : ((c i : ℚ) : ℝ) ≤ ((c j : ℚ) : ℝ) := hmonoR hij
    exact_mod_cast hij2
  · rw [← hsupR]
    exact tendsto_atTop_ciSup hmonoR hbddAbove

/-- Bridge to the Chapter 3/4 `ℝ≥0∞` rendering of lower semicomputability: for a
nonnegative real the p. 158 notion agrees with `IsLowerSemicomputableENNReal`. -/
theorem isLowerSemicomputableReal_iff_ofReal {α : ℝ} (hα : 0 ≤ α) :
    IsLowerSemicomputableReal α ↔ IsLowerSemicomputableENNReal (ENNReal.ofReal α) :=
  ⟨isLowerSemicomputableENNReal_ofReal_of_isLowerSemicomputableReal hα,
    isLowerSemicomputableReal_of_isLowerSemicomputableENNReal_ofReal hα⟩

/-- A computable real is lower semicomputable (SUV p. 158, immediate). -/
theorem IsComputableReal.isLowerSemicomputableReal {α : ℝ}
    (h : ComputableReals.IsComputableReal α) :
    IsLowerSemicomputableReal α := by
  obtain ⟨approx, hcomp, hb⟩ := (isComputableReal_iff_exists_computable_lowerApprox α).1 h
  have hac : Computable (fun n : ℕ => approx (invSucc n)) := hcomp.comp computable_invSucc
  refine ⟨ratRunMax (fun n => approx (invSucc n)), computable_ratRunMax hac,
    monotone_ratRunMax _, ?_⟩
  have hle : ∀ n : ℕ, ((approx (invSucc n) : ℚ) : ℝ) ≤ α := fun n => (hb _ (invSucc_pos n)).1
  refine tendsto_ratRunMax ?_ hle
  have hlow : ∀ n : ℕ, α - ((invSucc n : ℚ) : ℝ) ≤ ((approx (invSucc n) : ℚ) : ℝ) := by
    intro n
    have h2 := (hb _ (invSucc_pos n)).2
    linarith
  have h1 : Filter.Tendsto (fun n : ℕ => α - ((invSucc n : ℚ) : ℝ)) Filter.atTop (nhds α) := by
    simpa using tendsto_invSucc.const_sub α
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hlow hle

/-- **SUV Section 5.7.1 (p. 158).** An approximation of a lower semicomputable real
`α` from below: a computable, strictly increasing sequence of rationals converging
to `α`. The source writes `aᵢ → α` for exactly this data. -/
structure LowerApprox (α : ℝ) where
  /-- The approximating sequence of rationals. -/
  seq : ℕ → ℚ
  /-- The sequence is computable. -/
  isComputable : Computable seq
  /-- The source requires a *strictly* increasing approximation. -/
  isStrictMono : StrictMono seq
  /-- The sequence converges to `α`. -/
  tendsto : Filter.Tendsto (fun n => (seq n : ℝ)) Filter.atTop (nhds α)

/-- Every lower semicomputable real admits a strictly increasing computable rational
approximation (SUV p. 158, "computable strictly increasing sequences"): subtract
`2⁻ⁿ` from a non-decreasing approximation. -/
theorem exists_lowerApprox_of_isLowerSemicomputableReal {α : ℝ}
    (h : IsLowerSemicomputableReal α) : Nonempty (LowerApprox α) := by
  obtain ⟨a, ha, hmono, hlim⟩ := h
  refine ⟨{ seq := fun n => a n - invSucc n
            isComputable := Computable₂.comp computable₂_ratSub ha computable_invSucc
            isStrictMono := strictMono_nat_of_lt_succ (fun n => ?_)
            tendsto := ?_ }⟩
  · have h1 : a n ≤ a (n + 1) := hmono (Nat.le_succ n)
    have h2 : invSucc (n + 1) < invSucc n := invSucc_succ_lt n
    linarith
  · have hcast : (fun n => ((a n - invSucc n : ℚ) : ℝ))
        = fun n => ((a n : ℚ) : ℝ) - ((invSucc n : ℚ) : ℝ) := by
      funext n; push_cast; ring
    rw [hcast]
    simpa using hlim.sub tendsto_invSucc

/-! ### Elementary closure properties of lower semicomputable reals -/

/-- A `LowerApprox` witnesses lower semicomputability. -/
theorem LowerApprox.isLowerSemicomputableReal {α : ℝ} (a : LowerApprox α) :
    IsLowerSemicomputableReal α :=
  ⟨a.seq, a.isComputable, a.isStrictMono.monotone, a.tendsto⟩

/-- Terms of a `LowerApprox` are `≤` the limit. -/
theorem LowerApprox.seq_le {α : ℝ} (a : LowerApprox α) (n : ℕ) :
    ((a.seq n : ℚ) : ℝ) ≤ α :=
  rat_le_of_monotone_tendsto a.isStrictMono.monotone a.tendsto n

/-- Terms of a `LowerApprox` are **strictly** below the limit (SUV p. 158). -/
theorem LowerApprox.seq_lt {α : ℝ} (a : LowerApprox α) (n : ℕ) : ((a.seq n : ℚ) : ℝ) < α := by
  have h1 : ((a.seq n : ℚ) : ℝ) < ((a.seq (n + 1) : ℚ) : ℝ) := by
    exact_mod_cast a.isStrictMono (Nat.lt_succ_self n)
  exact lt_of_lt_of_le h1 (a.seq_le (n + 1))

/-- A `LowerApprox` eventually passes every rational strictly below the limit. -/
theorem LowerApprox.exists_lt {α : ℝ} (a : LowerApprox α) {r : ℚ} (hr : (r : ℝ) < α) :
    ∃ n, r < a.seq n := exists_rat_lt_of_tendsto a.tendsto hr

/-- A nonnegative rational multiple of a lower semicomputable real is lower
semicomputable (SUV p. 160, the "convenient notation" `α ≼_c β`). -/
theorem ComputableReals.IsLowerSemicomputableReal.rat_mul {c : ℚ} (hc : 0 ≤ c) {α : ℝ}
    (hα : IsLowerSemicomputableReal α) : IsLowerSemicomputableReal ((c : ℝ) * α) := by
  obtain ⟨a, ha, hma, hla⟩ := hα
  refine ⟨fun n => c * a n, Computable₂.comp computable₂_ratMul (Computable.const c) ha,
    fun i j hij => mul_le_mul_of_nonneg_left (hma hij) hc, ?_⟩
  have hcast : (fun n => ((c * a n : ℚ) : ℝ)) = fun n => (c : ℝ) * ((a n : ℚ) : ℝ) := by
    funext n; push_cast; ring
  rw [hcast]
  exact hla.const_mul (c : ℝ)

/-- **SUV p. 159.** The sum of a computable series of nonnegative rationals is a lower
semicomputable real: the partial sums are a computable non-decreasing approximation. -/
theorem isLowerSemicomputableReal_of_series {r : ℕ → ℚ} {α : ℝ} (hr : Computable r)
    (hr0 : ∀ i, 0 ≤ r i)
    (hsum : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, ((r i : ℚ) : ℝ))
      Filter.atTop (nhds α)) : IsLowerSemicomputableReal α := by
  have hcast : ∀ n : ℕ, ((ratRangeSum r n : ℚ) : ℝ)
      = ∑ i ∈ Finset.range n, ((r i : ℚ) : ℝ) := by
    intro n; rw [ratRangeSum_eq]; push_cast; ring
  refine ⟨ratRangeSum r, computable_ratRangeSum hr,
    monotone_nat_of_le_succ (fun n => ?_), ?_⟩
  · rw [ratRangeSum]
    linarith [hr0 n]
  · simp only [hcast]
    exact hsum

/-- **SUV p. 158 (used for Problem 161 and for `solovayDominates_nsmul_succ`).** A real
that is lower semicomputable together with its negation is computable: the two
approximations sandwich it, and the sandwich is found by a search. -/
theorem isComputableReal_of_lowerSemicomputable_neg {α : ℝ}
    (h1 : IsLowerSemicomputableReal α) (h2 : IsLowerSemicomputableReal (-α)) :
    ComputableReals.IsComputableReal α := by
  obtain ⟨a⟩ := exists_lowerApprox_of_isLowerSemicomputableReal h1
  obtain ⟨b⟩ := exists_lowerApprox_of_isLowerSemicomputableReal h2
  have hsum : Filter.Tendsto (fun n => ((a.seq n + b.seq n : ℚ) : ℝ))
      Filter.atTop (nhds 0) := by
    have hcast : (fun n => ((a.seq n + b.seq n : ℚ) : ℝ))
        = fun n => ((a.seq n : ℚ) : ℝ) + ((b.seq n : ℚ) : ℝ) := by
      funext n; push_cast; ring
    rw [hcast]
    have hab := a.tendsto.add b.tendsto
    simpa using hab
  have hdom : ∀ k : ℕ,
      (ratSearchPair a.seq (fun n => a.seq n + b.seq n) (-invSucc k)).Dom := by
    intro k
    refine ratSearchPair_dom (exists_rat_lt_of_tendsto hsum ?_)
    have hpos : (0 : ℝ) < ((invSucc k : ℚ) : ℝ) := by exact_mod_cast invSucc_pos k
    push_cast
    linarith
  have hgc : Computable (fun k : ℕ =>
      (ratSearchPair a.seq (fun n => a.seq n + b.seq n) (-invSucc k)).get (hdom k)) := by
    refine computable_of_partrec_total ?_ hdom
    exact (partrec_ratSearchPair a.isComputable
      (Computable₂.comp computable₂_ratAdd a.isComputable b.isComputable)).comp
      (ComputableReals.computable_ratNeg.comp computable_invSucc)
  have gspec : ∀ k : ℕ, |(((ratSearchPair a.seq (fun n => a.seq n + b.seq n)
      (-invSucc k)).get (hdom k) : ℚ) : ℝ) - α| ≤ ((invSucc k : ℚ) : ℝ) := by
    intro k
    obtain ⟨n, hn, hq⟩ := mem_ratSearchPair (Part.get_mem (hdom k))
    rw [hq]
    have hlt : ((a.seq n : ℚ) : ℝ) < α := a.seq_lt n
    have hblt : ((b.seq n : ℚ) : ℝ) < -α := b.seq_lt n
    have hnR : ((-invSucc k : ℚ) : ℝ) < ((a.seq n + b.seq n : ℚ) : ℝ) := by exact_mod_cast hn
    push_cast at hnR
    rw [abs_le]
    constructor <;> linarith
  have hden : ∀ ε : ℚ, 0 < ε → invSucc ε.den ≤ ε := by
    intro ε hε
    have hd : (0 : ℚ) < (ε.den : ℚ) := by exact_mod_cast ε.pos
    have h1 : (1 : ℚ) / (ε.den : ℚ) ≤ ε := by
      nth_rw 2 [← Rat.num_div_den ε]
      apply div_le_div_of_nonneg_right
      · have hp : 0 < ε.num := Rat.num_pos.mpr hε
        exact_mod_cast hp
      · exact_mod_cast (le_of_lt ε.pos)
    have h2 : invSucc ε.den ≤ (1 : ℚ) / (ε.den : ℚ) := by
      rw [invSucc]
      exact one_div_le_one_div_of_le hd (by linarith)
    linarith
  refine ⟨fun ε => (ratSearchPair a.seq (fun n => a.seq n + b.seq n)
    (-invSucc ε.den)).get (hdom ε.den), hgc.comp computable_ratDen, fun ε hε => ?_⟩
  have h2 : ((invSucc ε.den : ℚ) : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hden ε hε
  rw [abs_sub_comm]
  exact le_trans (gspec ε.den) h2

/-! ### Effectively null sets of reals and ML-random reals (SUV p. 157) -/

/-- The open interval with rational endpoints coded by a pair `I = (l, r)`. -/
def ratInterval (I : ℚ × ℚ) : Set ℝ := Set.Ioo (I.1 : ℝ) (I.2 : ℝ)

/-- The length (Lebesgue measure) of the rational interval coded by `I = (l, r)`. -/
noncomputable def ratIntervalLength (I : ℚ × ℚ) : ℝ≥0∞ := ENNReal.ofReal ((I.2 : ℝ) - (I.1 : ℝ))

/-- **SUV Section 5.7 (p. 157).** A set `X` of reals is an *effectively null set* if
there is an algorithm that for any rational `ε > 0` enumerates a cover of `X` by
intervals with rational endpoints and total measure (length) at most `ε`. -/
def IsEffectivelyNullReal (X : Set ℝ) : Prop :=
  ∃ cover : ℚ → ℕ → Option (ℚ × ℚ), Computable₂ cover ∧
    ∀ ε : ℚ, 0 < ε →
      X ⊆ (⋃ i, (cover ε i).elim ∅ ratInterval) ∧
      (∑' i, (cover ε i).elim 0 ratIntervalLength) ≤ ENNReal.ofReal (ε : ℝ)

/-- **SUV Section 5.7 (p. 157).** A real number is *ML-random* (with respect to the
standard measure on `ℝ`) if it does not belong to any effectively null set. -/
def IsMartinLofRandomReal (α : ℝ) : Prop :=
  ∀ X : Set ℝ, IsEffectivelyNullReal X → α ∉ X

/-- The interval-length bookkeeping of `Omega/UniversalCover.lean` agrees with
`ratIntervalLength`. -/
theorem ofReal_covLen_eq (I : Option (ℚ × ℚ)) :
    ENNReal.ofReal ((covLen I : ℚ) : ℝ) = I.elim 0 ratIntervalLength := by
  cases I with
  | none => simp [covLen]
  | some J =>
      have hJ : (some J).elim (0 : ℝ≥0∞) ratIntervalLength = ratIntervalLength J := rfl
      rw [hJ, ratIntervalLength, covLen_some]
      by_cases h : J.2 - J.1 ≤ 0
      · have h0 : max (0 : ℚ) (J.2 - J.1) = 0 := max_eq_left h
        have hR : ((J.2 : ℚ) : ℝ) - ((J.1 : ℚ) : ℝ) ≤ 0 := by exact_mod_cast h
        rw [h0, ENNReal.ofReal_of_nonpos hR]
        simp
      · have h0 : max (0 : ℚ) (J.2 - J.1) = J.2 - J.1 := max_eq_right (not_le.mp h).le
        rw [h0]
        congr 1
        push_cast
        ring

/-- **SUV Section 5.7 (p. 157), the parenthetical "= does not belong to the largest
effectively null set".** There is a largest effectively null set of reals. -/
theorem exists_largest_effectivelyNullReal :
    ∃ X : Set ℝ, IsEffectivelyNullReal X ∧ ∀ Y, IsEffectivelyNullReal Y → Y ⊆ X := by
  classical
  refine ⟨{x : ℝ | ∀ ε : ℚ, 0 < ε → x ∈ ⋃ n, (covEnum ε n).elim ∅ ratInterval}, ?_, ?_⟩
  · refine ⟨covEnum, computable₂_covEnum, fun ε hε => ⟨fun x hx => hx ε hε, ?_⟩⟩
    have h1 : (∑' n, (covEnum ε n).elim 0 ratIntervalLength)
        = ∑' n, ENNReal.ofReal ((covLen (covEnum ε n) : ℚ) : ℝ) :=
      tsum_congr (fun n => (ofReal_covLen_eq _).symm)
    rw [h1]
    refine le_trans (tsum_covLen_covEnum_le hε) ?_
    rw [tsum_ofReal_covBudget hε]
    refine ENNReal.ofReal_le_ofReal ?_
    have hεR : (0 : ℝ) < ((ε : ℚ) : ℝ) := by exact_mod_cast hε
    linarith
  · rintro Y ⟨c, hc, hspec⟩ y hy ε hε
    have hlen : ∀ δ : ℚ, 0 < δ →
        (∑' i, ENNReal.ofReal ((covLen (c δ i) : ℚ) : ℝ)) ≤ ENNReal.ofReal ((δ : ℚ) : ℝ) := by
      intro δ hδ
      have h3 : (∑' i, ENNReal.ofReal ((covLen (c δ i) : ℚ) : ℝ))
          = ∑' i, (c δ i).elim 0 ratIntervalLength :=
        tsum_congr (fun i => ofReal_covLen_eq _)
      rw [h3]
      exact (hspec δ hδ).2
    obtain ⟨δ, hδ, hall⟩ := exists_code_covEnum hc hlen hε
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ((hspec δ hδ).1 hy)
    obtain ⟨n, hn⟩ := hall i
    exact Set.mem_iUnion.mpr ⟨n, by rw [hn]; exact hi⟩

/-- **SUV p. 157 / p. 161, the transport used for "randomness does not change if we
add a rational number or multiply by a positive rational factor".** The image of an
effectively null set of reals under a positive rational affine map `x ↦ c x + t` is
effectively null: every covering interval maps to an interval of `c` times the length,
so running the given cover at budget `ε / c` gives total length `≤ ε`. -/
theorem IsEffectivelyNullReal.affine {X : Set ℝ} {c t : ℚ} (hc : 0 < c)
    (hX : IsEffectivelyNullReal X) :
    IsEffectivelyNullReal ((fun x : ℝ => (c : ℝ) * x + (t : ℝ)) '' X) := by
  obtain ⟨cover, hcov, hspec⟩ := hX
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hmap : ∀ {β : Type} (d : β) (f : ℚ × ℚ → β) (g : ℚ × ℚ → ℚ × ℚ)
      (o : Option (ℚ × ℚ)), (o.map g).elim d f = o.elim d (fun I => f (g I)) := by
    intro β d f g o; cases o <;> rfl
  refine ⟨fun ε i => (cover (ε / c) i).map (fun I => (c * I.1 + t, c * I.2 + t)), ?_, ?_⟩
  · have hcov' : Computable (fun p : ℚ × ℕ => cover p.1 p.2) := hcov
    have h1 : Computable (fun p : ℚ × ℕ => cover (p.1 / c) p.2) :=
      Computable.comp hcov' (Computable.pair
        ((computable_ratDivConst hc).comp Computable.fst) Computable.snd)
    have hg1 : Computable (fun r : (ℚ × ℕ) × (ℚ × ℚ) => c * r.2.1 + t) :=
      Computable₂.comp computable₂_ratAdd
        (Computable₂.comp computable₂_ratMul (Computable.const c)
          (Computable.fst.comp Computable.snd)) (Computable.const t)
    have hg2 : Computable (fun r : (ℚ × ℕ) × (ℚ × ℚ) => c * r.2.2 + t) :=
      Computable₂.comp computable₂_ratAdd
        (Computable₂.comp computable₂_ratMul (Computable.const c)
          (Computable.snd.comp Computable.snd)) (Computable.const t)
    exact Computable.option_map h1 (Computable.pair hg1 hg2)
  · intro ε hε
    obtain ⟨hsub, hlen⟩ := hspec (ε / c) (div_pos hε hc)
    constructor
    · rintro y ⟨x, hx, rfl⟩
      have hxc := hsub hx
      rw [Set.mem_iUnion] at hxc
      obtain ⟨i, hi⟩ := hxc
      rw [Set.mem_iUnion]
      refine ⟨i, ?_⟩
      rw [hmap]
      rcases hcase : cover (ε / c) i with _ | I
      · rw [hcase] at hi; simp at hi
      · rw [hcase] at hi
        simp only [Option.elim, ratInterval, Set.mem_Ioo] at hi ⊢
        have h1 := mul_lt_mul_of_pos_left hi.1 hcR
        have h2 := mul_lt_mul_of_pos_left hi.2 hcR
        push_cast
        exact ⟨by linarith, by linarith⟩
    · have hterm : ∀ i, ((cover (ε / c) i).map
          (fun I => (c * I.1 + t, c * I.2 + t))).elim 0 ratIntervalLength
          = ENNReal.ofReal (c : ℝ) * ((cover (ε / c) i).elim 0 ratIntervalLength) := by
        intro i
        rw [hmap]
        rcases hcase : cover (ε / c) i with _ | I
        · simp
        · simp only [Option.elim, ratIntervalLength]
          rw [← ENNReal.ofReal_mul hcR.le]
          congr 1
          push_cast
          ring
      calc (∑' i, ((cover (ε / c) i).map
              (fun I => (c * I.1 + t, c * I.2 + t))).elim 0 ratIntervalLength)
          = ENNReal.ofReal (c : ℝ) * ∑' i, (cover (ε / c) i).elim 0 ratIntervalLength := by
            rw [tsum_congr hterm, ENNReal.tsum_mul_left]
        _ ≤ ENNReal.ofReal (c : ℝ) * ENNReal.ofReal (((ε / c : ℚ)) : ℝ) := by
            gcongr
        _ = ENNReal.ofReal (ε : ℝ) := by
            rw [← ENNReal.ofReal_mul hcR.le]
            congr 1
            push_cast
            field_simp

/-- Randomness of a real is invariant under adding a rational number (used on
p. 160 to reduce the general case of Section 5.7.2 to the interval `(0,1)`). -/
theorem isMartinLofRandomReal_add_rat (α : ℝ) (q : ℚ) :
    IsMartinLofRandomReal (α + (q : ℝ)) ↔ IsMartinLofRandomReal α := by
  constructor
  · intro h X hX hmem
    refine h _ (hX.affine (c := 1) (t := q) one_pos) ⟨α, hmem, ?_⟩
    push_cast
    ring
  · intro h X hX hmem
    refine h _ (hX.affine (c := 1) (t := -q) one_pos) ⟨α + (q : ℝ), hmem, ?_⟩
    push_cast
    ring

/-- Randomness of a real is invariant under multiplication by a positive rational
factor (p. 161: "randomness does not change if we multiply a real by a rational
factor"). -/
theorem isMartinLofRandomReal_rat_mul {q : ℚ} (hq : 0 < q) (α : ℝ) :
    IsMartinLofRandomReal ((q : ℝ) * α) ↔ IsMartinLofRandomReal α := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  constructor
  · intro h X hX hmem
    refine h _ (hX.affine (c := q) (t := 0) hq) ⟨α, hmem, ?_⟩
    push_cast
    ring
  · intro h X hX hmem
    refine h _ (hX.affine (c := q⁻¹) (t := 0) (inv_pos.2 hq)) ⟨(q : ℝ) * α, hmem, ?_⟩
    push_cast
    rw [add_zero, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hqR), one_mul]

/-- A single rational point is an effectively null set of reals: cover it by the one
interval of length `ε/2` centred at it. -/
theorem isEffectivelyNullReal_singleton_rat (q : ℚ) : IsEffectivelyNullReal {(q : ℝ)} := by
  refine ⟨fun ε i => Nat.casesOn (motive := fun _ => Option (ℚ × ℚ)) i
    (some (q - ε / 4, q + ε / 4)) (fun _ => none), ?_, ?_⟩
  · have hdiv : Computable (fun ε : ℚ => ε / 4) := computable_ratDivConst (by norm_num)
    have hlo : Computable (fun p : ℚ × ℕ => q - p.1 / 4) :=
      Computable₂.comp computable₂_ratSub (Computable.const q) (hdiv.comp Computable.fst)
    have hhi : Computable (fun p : ℚ × ℕ => q + p.1 / 4) :=
      Computable₂.comp computable₂_ratAdd (Computable.const q) (hdiv.comp Computable.fst)
    exact Computable.nat_casesOn Computable.snd
      (Computable.option_some.comp (Computable.pair hlo hhi)) (Computable.const none)
  · intro ε hε
    have hεR : (0 : ℝ) < ((ε : ℚ) : ℝ) := by exact_mod_cast hε
    constructor
    · rintro y hy
      have hyq : y = (q : ℝ) := hy
      rw [Set.mem_iUnion]
      refine ⟨0, ?_⟩
      change y ∈ ratInterval (q - ε / 4, q + ε / 4)
      rw [hyq, ratInterval]
      refine Set.mem_Ioo.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith
    · have hzero : ∀ i : ℕ, i ≠ 0 →
          (Nat.casesOn (motive := fun _ => Option (ℚ × ℚ)) i
            (some (q - ε / 4, q + ε / 4)) (fun _ => none)).elim (0 : ℝ≥0∞)
              ratIntervalLength = 0 := by
        intro i hi
        cases i with
        | zero => exact absurd rfl hi
        | succ k => rfl
      rw [tsum_eq_single 0 hzero]
      change ratIntervalLength (q - ε / 4, q + ε / 4) ≤ ENNReal.ofReal ((ε : ℚ) : ℝ)
      rw [ratIntervalLength]
      refine ENNReal.ofReal_le_ofReal ?_
      push_cast
      linarith

/-- **An ML-random real is irrational** (SUV p. 160, used to separate `Ω` from `1`):
a single rational point is an effectively null set. -/
theorem ne_ratCast_of_isMartinLofRandomReal {α : ℝ} (h : IsMartinLofRandomReal α) (q : ℚ) :
    α ≠ (q : ℝ) := fun hq => h {(q : ℝ)} (isEffectivelyNullReal_singleton_rat q) hq

/-- The computable rational padding `ε / 2^(i+2)`, whose total mass is `ε / 2`. -/
def ratPad (ε : ℚ) (i : ℕ) : ℚ := ε / 2 ^ (i + 2)

/-- The padding term is computable in the budget and the index. -/
theorem computable₂_ratPad : Computable₂ ratPad := by
  have hden : Computable (fun p : ℚ × ℕ => (1 : ℚ) / 2 ^ (p.2 + 2)) := by
    have hnat : Primrec (fun n : ℕ => 2 ^ (n + 2)) :=
      ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2)
        (Primrec.succ.comp Primrec.succ))
    refine computable_of_num_den (N := fun _ : ℚ × ℕ => (1 : ℤ))
      (D := fun p : ℚ × ℕ => 2 ^ (p.2 + 2)) (Computable.const 1)
      (hnat.to_comp.comp Computable.snd) (fun _ => by positivity) (fun p => ?_)
    push_cast
    ring
  refine (Computable₂.comp computable₂_ratMul Computable.fst hden).of_eq (fun p => ?_)
  rw [ratPad]
  ring

/-- The padding term is positive at a positive budget. -/
theorem ratPad_pos {ε : ℚ} (hε : 0 < ε) (i : ℕ) : 0 < ratPad ε i := by
  rw [ratPad]
  positivity

/-- The total mass of the padding is `ε / 2`. -/
theorem tsum_ofReal_ratPad {ε : ℚ} (hε : 0 < ε) :
    (∑' i : ℕ, ENNReal.ofReal ((ratPad ε i : ℚ) : ℝ)) = ENNReal.ofReal (((ε : ℚ) : ℝ) / 2) := by
  have hεR : (0 : ℝ) < ((ε : ℚ) : ℝ) := by exact_mod_cast hε
  have hcast : ∀ i : ℕ, ((ratPad ε i : ℚ) : ℝ) = ((ε : ℚ) : ℝ) * ((1 : ℝ) / 2) ^ (i + 2) := by
    intro i
    rw [ratPad]
    push_cast
    rw [div_pow, one_pow]
    ring
  have hgeom : Summable (fun i : ℕ => ((1 : ℝ) / 2) ^ i) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : ∑' i : ℕ, ((1 : ℝ) / 2) ^ i = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hshift : ∀ i : ℕ, ((1 : ℝ) / 2) ^ (i + 2) = ((1 : ℝ) / 2) ^ i * ((1 : ℝ) / 4) := by
    intro i
    rw [pow_add]
    norm_num
  have hs2 : Summable (fun i : ℕ => ((ε : ℚ) : ℝ) * ((1 : ℝ) / 2) ^ (i + 2)) := by
    have := (hgeom.mul_right ((1 : ℝ) / 4)).mul_left ((ε : ℚ) : ℝ)
    refine this.congr (fun i => ?_)
    rw [hshift i]
  have hval : ∑' i : ℕ, ((ε : ℚ) : ℝ) * ((1 : ℝ) / 2) ^ (i + 2) = ((ε : ℚ) : ℝ) / 2 := by
    rw [tsum_congr (fun i => by rw [hshift i]), tsum_mul_left, hgeom.tsum_mul_right, hsum]
    ring
  rw [tsum_congr (fun i => congrArg ENNReal.ofReal (hcast i)),
    ← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hs2, hval]

/-- **The cover behind SUV Theorems 104 and 105 (pp. 161–162).**  If `a` is a computable
rational sequence strictly below `α`, and for every rational `ε > 0` one can effectively
find nonnegative rationals `H ε i` of total mass `< ε` with `α ≤ a i + H ε i` for some
`i`, then `α` is not ML-random: the intervals `(a i, a i + H (ε/2) i + ε/2^(i+2))` cover
`α` and have total length `< ε`. -/
theorem not_isMartinLofRandomReal_of_covering {a : ℕ → ℚ} {α : ℝ}
    (ha : Computable a) (hlt : ∀ i, ((a i : ℚ) : ℝ) < α)
    {H : ℚ → ℕ → ℚ} (hH : Computable₂ H) (hnn : ∀ ε : ℚ, 0 < ε → ∀ i, 0 ≤ H ε i)
    (hsum : ∀ ε : ℚ, 0 < ε →
      (∑' i, ENNReal.ofReal ((H ε i : ℚ) : ℝ)) < ENNReal.ofReal ((ε : ℚ) : ℝ))
    (hcov : ∀ ε : ℚ, 0 < ε → ∃ i, α ≤ ((a i : ℚ) : ℝ) + ((H ε i : ℚ) : ℝ)) :
    ¬ IsMartinLofRandomReal α := by
  intro hrand
  refine hrand {α} ⟨fun ε i => some (a i, a i + H (ε / 2) i + ratPad ε i), ?_, ?_⟩ rfl
  · have h1 : Computable (fun p : ℚ × ℕ => a p.2) := ha.comp Computable.snd
    have hhalf : Computable (fun ε : ℚ => ε / 2) :=
      computable_ratDivConst (c := 2) (by norm_num)
    have hfst : Computable (fun p : ℚ × ℕ => p.1 / 2) := hhalf.comp Computable.fst
    have hsnd : Computable (fun p : ℚ × ℕ => p.2) := Computable.snd
    have h2 : Computable (fun p : ℚ × ℕ => H (p.1 / 2) p.2) :=
      Computable₂.comp hH hfst hsnd
    have h3 : Computable (fun p : ℚ × ℕ => ratPad p.1 p.2) := computable₂_ratPad
    have h4 : Computable (fun p : ℚ × ℕ => a p.2 + H (p.1 / 2) p.2 + ratPad p.1 p.2) :=
      Computable₂.comp computable₂_ratAdd (Computable₂.comp computable₂_ratAdd h1 h2) h3
    exact Computable.option_some.comp (Computable.pair h1 h4)
  · intro ε hε
    have hε2 : (0 : ℚ) < ε / 2 := by positivity
    constructor
    · rintro y hy
      have hyα : y = α := hy
      obtain ⟨i, hi⟩ := hcov (ε / 2) hε2
      rw [Set.mem_iUnion]
      refine ⟨i, ?_⟩
      change y ∈ ratInterval (a i, a i + H (ε / 2) i + ratPad ε i)
      rw [hyα, ratInterval]
      have hpad : (0 : ℝ) < ((ratPad ε i : ℚ) : ℝ) := by exact_mod_cast ratPad_pos hε i
      refine Set.mem_Ioo.mpr ⟨hlt i, ?_⟩
      push_cast
      linarith
    · have hterm : ∀ i : ℕ,
          (some (a i, a i + H (ε / 2) i + ratPad ε i)).elim (0 : ℝ≥0∞) ratIntervalLength
            = ENNReal.ofReal ((H (ε / 2) i : ℚ) : ℝ)
              + ENNReal.ofReal ((ratPad ε i : ℚ) : ℝ) := by
        intro i
        change ratIntervalLength (a i, a i + H (ε / 2) i + ratPad ε i) = _
        have hval : ((a i + H (ε / 2) i + ratPad ε i : ℚ) : ℝ) - ((a i : ℚ) : ℝ)
            = ((H (ε / 2) i : ℚ) : ℝ) + ((ratPad ε i : ℚ) : ℝ) := by push_cast; ring
        rw [ratIntervalLength, hval, ENNReal.ofReal_add
          (by exact_mod_cast hnn (ε / 2) hε2 i) (by exact_mod_cast (ratPad_pos hε i).le)]
      rw [tsum_congr hterm, ENNReal.tsum_add, tsum_ofReal_ratPad hε]
      have hhalf : ENNReal.ofReal (((ε / 2 : ℚ)) : ℝ) = ENNReal.ofReal (((ε : ℚ) : ℝ) / 2) := by
        congr 1
        push_cast
        ring
      have h1 := hsum (ε / 2) hε2
      rw [hhalf] at h1
      have h2 : ENNReal.ofReal (((ε : ℚ) : ℝ) / 2) + ENNReal.ofReal (((ε : ℚ) : ℝ) / 2)
          = ENNReal.ofReal ((ε : ℚ) : ℝ) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      calc (∑' i, ENNReal.ofReal ((H (ε / 2) i : ℚ) : ℝ))
            + ENNReal.ofReal (((ε : ℚ) : ℝ) / 2)
          ≤ ENNReal.ofReal (((ε : ℚ) : ℝ) / 2) + ENNReal.ofReal (((ε : ℚ) : ℝ) / 2) :=
            add_le_add h1.le le_rfl
        _ = ENNReal.ofReal ((ε : ℚ) : ℝ) := h2

/-! ### Binary expansions -/

/-- The real number of `[0,1]` whose binary expansion is the sequence `w`, i.e.
`0.w₀w₁w₂…`. This is the map implicit in "the binary representation of `Ω`"
(SUV p. 157) and in Problem 158 (p. 158). -/
noncomputable def cantorReal (w : CantorSeq) : ℝ :=
  ∑' k : ℕ, (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0)

/-- `cantorReal` lands in the unit interval. -/
theorem cantorReal_mem_Icc (w : CantorSeq) : cantorReal w ∈ Set.Icc (0 : ℝ) 1 := by
  have hnn : ∀ k : ℕ, 0 ≤ (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0) := by
    intro k; by_cases h : w k <;> simp [h]
  have hdom : ∀ k : ℕ,
      (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0) ≤ ((1 : ℝ) / 2) ^ (k + 1) := by
    intro k
    have hpow : ((1 : ℝ) / 2) ^ (k + 1) = (1 : ℝ) / 2 ^ (k + 1) := by
      rw [div_pow, one_pow]
    rw [hpow]
    by_cases h : w k
    · simp [h]
    · simp only [h]
      positivity
  have hgeom : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hshift : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ (k + 1)) := by
    simpa [pow_succ] using hgeom.mul_right ((1 : ℝ) / 2)
  have hsum : ∑' k : ℕ, ((1 : ℝ) / 2) ^ k = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have htsum : ∑' k : ℕ, ((1 : ℝ) / 2) ^ (k + 1) = 1 := by
    have hc : ∀ k : ℕ, ((1 : ℝ) / 2) ^ (k + 1) = ((1 : ℝ) / 2) ^ k * ((1 : ℝ) / 2) :=
      fun k => pow_succ _ _
    rw [tsum_congr hc, hgeom.tsum_mul_right, hsum]
    norm_num
  have hsummable : Summable (fun k : ℕ => (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0)) :=
    Summable.of_nonneg_of_le hnn hdom hshift
  refine ⟨tsum_nonneg hnn, ?_⟩
  calc cantorReal w ≤ ∑' k : ℕ, ((1 : ℝ) / 2) ^ (k + 1) :=
        Summable.tsum_le_tsum hdom hsummable hshift
    _ = 1 := htsum

/-! ### The discrete a priori probability on `ℕ` (SUV p. 157)

The book indexes the a priori probability by natural numbers; the library's frozen
hierarchy (`KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure`) is indexed
by `BitString`.  These are **not** two hierarchies.  The three `ℕ`-indexed notions
below are literal *transports* of the `BitString`-indexed ones along the canonical
computable bijection `natBitStringEquiv : ℕ ≃ BitString` of `SharedCoding`: `m` has a
property iff `m ∘ bitStringToNat` has the frozen one.  Consequently the existence
statement is **derived** from `exists_universalSemimeasure` rather than re-postulated. -/

/-- Lower semicomputability of an `ℕ`-indexed nonnegative function: the transport of
the library's `IsLSC` along the canonical bijection `ℕ ≃ BitString` (`SharedCoding`).
The dummy `BitString` context is the one the unary `IsLSC` interface uses. -/
def IsLSCNat (m : ℕ → ℝ≥0∞) : Prop := IsLSC (fun x _ => m (bitStringToNat x))

/-- A lower semicomputable semimeasure on the natural numbers (SUV p. 157): the
transport of `IsLowerSemicomputableSemimeasure` along `natBitStringEquiv`.  Total mass
at most `1` is recovered by `IsLowerSemicomputableSemimeasureNat.tsum_le_one`. -/
def IsLowerSemicomputableSemimeasureNat (m : ℕ → ℝ≥0∞) : Prop :=
  IsLowerSemicomputableSemimeasure (fun x => m (bitStringToNat x))

/-- **SUV p. 157.** A *maximal* (universal) lower semicomputable semimeasure on the
set of natural numbers: the transport of the library's `IsUniversalSemimeasure` along
`natBitStringEquiv`.  The book writes `m` for such a function and calls `m(n)` the
discrete a priori probability of `n`. -/
def IsUniversalSemimeasureNat (m : ℕ → ℝ≥0∞) : Prop :=
  IsUniversalSemimeasure (fun x => m (bitStringToNat x))

/-- The transported semimeasure condition really is "total mass at most `1`" on `ℕ`. -/
theorem IsLowerSemicomputableSemimeasureNat.tsum_le_one {m : ℕ → ℝ≥0∞}
    (hm : IsLowerSemicomputableSemimeasureNat m) : (∑' n, m n) ≤ 1 := by
  have h : (∑' x : BitString, m (bitStringToNat x)) ≤ 1 := hm.1
  rwa [tsum_comp_bitStringToNat] at h

/-- A maximal semimeasure on `ℕ` is in particular a semimeasure on `ℕ`. -/
theorem IsUniversalSemimeasureNat.isLowerSemicomputableSemimeasureNat {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) : IsLowerSemicomputableSemimeasureNat m := hm.1

/-- Total mass of a maximal lower semicomputable semimeasure on `ℕ` is at most `1`. -/
theorem IsUniversalSemimeasureNat.tsum_le_one {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) : (∑' n, m n) ≤ 1 :=
  hm.isLowerSemicomputableSemimeasureNat.tsum_le_one

/-- The transported maximality really is pointwise domination on `ℕ` (this is the
shape in which SUV p. 157 uses it). -/
theorem IsUniversalSemimeasureNat.dominates {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    {m' : ℕ → ℝ≥0∞} (hm' : IsLowerSemicomputableSemimeasureNat m') :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ n, c * m' n ≤ m n := by
  obtain ⟨c, hc, hdom⟩ := hm.2 _ hm'
  refine ⟨c, hc, fun n => ?_⟩
  simpa using hdom (natToBitString n)

/-- Transport of the library's `BitString`-indexed maximal lower semicomputable
semimeasure to the book's `ℕ`-indexed one along the canonical computable **bijection**
`natBitStringEquiv` (`Nat.bits` is not onto, so it cannot be used here).
SUV Chapter 4: the index set is immaterial up to a computable bijection. -/
theorem exists_isUniversalSemimeasureNat_comp_natToBitString :
    ∃ M : BitString → ℝ≥0∞, IsUniversalSemimeasure M ∧
      IsUniversalSemimeasureNat (fun n => M (natToBitString n)) := by
  obtain ⟨M, hM⟩ := exists_universalSemimeasure
  exact ⟨M, hM, by simpa [IsUniversalSemimeasureNat] using hM⟩

/-- A maximal lower semicomputable semimeasure on `ℕ` exists (SUV Chapter 4,
restated here in the index set used by Section 5.7).  Proved, not postulated: it is
the transport of `exists_universalSemimeasure`. -/
theorem exists_isUniversalSemimeasureNat : ∃ m : ℕ → ℝ≥0∞, IsUniversalSemimeasureNat m :=
  let ⟨_, _, h⟩ := exists_isUniversalSemimeasureNat_comp_natToBitString
  ⟨_, h⟩

/- Prefix complexity of a natural number, `K(n)` in the book's notation (SUV p. 165:
"prefix complexity `K(i) = -log m(i)`"), is the shared `KPNat` of
`KolmogorovMathlib.MonotoneComplexity.SharedCoding`: `KPNat U n = KPPlain U (natToBitString n)`,
where `natToBitString` is the canonical computable *bijection* `ℕ ≃ BitString`
(`Nat.bits` is not onto).  The re-coding costs `O(1)`: `exists_const_KPNat_natBits_equiv`. -/

/-- **The coding theorem in the form used throughout Section 5.7 (SUV p. 165).**
`K(i) = -log m(i)` up to an additive constant: the a priori probability and the
prefix complexity weight of a natural number dominate each other. -/
theorem exists_const_KPNat_aprioriNat_equiv {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ c₁ c₂ : ℝ≥0∞, 0 < c₁ ∧ 0 < c₂ ∧
      (∀ n, c₁ * m n ≤ complexityWeight (KPNat U n)) ∧
      (∀ n, c₂ * complexityWeight (KPNat U n) ≤ m n) := by
  obtain ⟨c1, c2, hc1, hc2, hfwd, hbwd⟩ := universalSemimeasure_equiv_prefixComplexity hm hU
  refine ⟨c1, c2, hc1, hc2, fun n => ?_, fun n => ?_⟩
  · simpa [prefixComplexityWeight, KPNat, KPPlain] using hfwd (natToBitString n)
  · simpa [prefixComplexityWeight, KPNat, KPPlain] using hbwd (natToBitString n)

/-! ### The Dirac semimeasure on `ℕ` -/

/-- The Dirac semimeasure concentrated at `0`.  It is a *computable* — hence lower
semicomputable — semimeasure on `ℕ`, and it is the witness that makes the sum of a
maximal semimeasure strictly positive (`omegaReal_pos`, SUV p. 160). -/
def diracNat (n : ℕ) : ℝ≥0∞ := if n = 0 then 1 else 0

/-- The Dirac semimeasure on the naturals gives mass one to zero. -/
@[simp] theorem diracNat_zero : diracNat 0 = 1 := by simp [diracNat]

/-- The stage-`s` dyadic numerator of `diracNat`: `2 ^ s` at the code of `0` and `0`
elsewhere, so that every stage has the exact value `1`, resp. `0`.  Written with
`Nat.casesOn` rather than `if`, so that `Computable.nat_casesOn` applies directly. -/
def diracApprox (s : ℕ) (x : BitString) : ℕ :=
  Nat.casesOn (motive := fun _ => ℕ) (bitStringToNat x) (2 ^ s) (fun _ => 0)

/-- The stage-`s` approximation of the Dirac semimeasure is `2 ^ s` on the code of zero and zero
elsewhere. -/
theorem diracApprox_eq (s : ℕ) (x : BitString) :
    diracApprox s x = if bitStringToNat x = 0 then 2 ^ s else 0 := by
  rcases hb : bitStringToNat x with _ | k <;> simp [diracApprox, hb]

end Kolmogorov
