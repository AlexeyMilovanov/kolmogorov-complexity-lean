/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.Hausdorff
import KolmogorovMathlib.MonotoneComplexity.Dimension.ChangeOfMeasure
import KolmogorovMathlib.MonotoneComplexity.Dimension.AlphaNullCriterion
import KolmogorovMathlib.MonotoneComplexity.Dimension.PullbackTest
import KolmogorovMathlib.MonotoneComplexity.Dimension.ImageDeficiency
import KolmogorovMathlib.MonotoneComplexity.Dimension.DilutionReal
import KolmogorovMathlib.MonotoneComplexity.Dimension.ArithmeticStreamMap
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.MonotoneComplexity.Dimension.DimensionLSC

/-!
# Required exercises of SUV §§5.8-5.9

The exercises of `PLAN_CHAPTER_5.md`'s `required-planned` list that occur in
`SUV_CHAPTER_5_8_9.txt` are Problems 169, 170, 174, 176, 185 and 187.  (The
other required problems -- 135, 140, 143-147, 158, 161, 162, 165 -- belong to
§§5.1-5.7 and are outside this source file.)

## Rendering decisions

* Problem 169 (p. 173) is printed in the book as "the difference `αn - K(n)`
  has no upper bounds".  `K(n)` there is a misprint: the quantity has to depend
  on `ω`, and the hint refers to the prefix-complexity Levin-Schnorr criterion,
  so the intended quantity is `K((ω)_n)`, the prefix complexity of the `n`-bit
  prefix of `ω`.  This was checked against the scan (book p. 173); the printed
  text really is `K(n)`.  The statement below uses `K((ω)_n)`.
* "has no upper bound" is rendered as the negation of `∃ c, ∀ n, … ≤ c`, which
  is the source's phrase and avoids a limit.
* Problem 174 (p. 175) introduces a second cover notion
  (`IsInfinitelyCoveredCover`) and asserts that the resulting infimum is the
  same number as `effectiveHausdorffDim`.
* Problems 185 and 187 (pp. 182, 185) are stated in the setting of §5.9.3:
  `μ` a computable probability measure, `f` a computable stream map, `ν` the
  image measure.  Problem 185 uses the *expectation-bounded* deficiency of
  infinite sequences (§3.5), i.e. the binary logarithm of a maximal
  expectation-bounded test; Problem 187 uses the a priori deficiency `d` of
  finite strings (p. 177).
* Problem 187 quantifies over `1 ≤ d`, the log convention fixed in
  `Dimension/ChangeOfMeasure.lean` for Theorem 124 and reused verbatim here;
  the book's hint calls Problem 187 "a generalization of Theorem 124" (p. 185),
  so the two statements must agree on it.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ## Problem 169 -/

/-- **SUV Problem 169 (§5.8, p. 173).** The largest effectively `α`-null set
consists of all the sequences `ω` such that the difference `αn - K((ω)_n)` has
no upper bound.

`U` is an optimal prefix decompressor, so `KPPlain U` is the prefix complexity
`K` of the source. -/
theorem problem_169_largest_isEffectiveAlphaNull_eq (U : Map)
    (hU : IsOptimalPrefixConditional U) (α : ℚ) (hα : 0 < α) {A : Set CantorSeq}
    (hA : IsEffectiveAlphaNull (α : ℝ) A)
    (hmax : ∀ B : Set CantorSeq, IsEffectiveAlphaNull (α : ℝ) B → B ⊆ A) :
    A = {w : CantorSeq | ¬ ∃ c : ℝ, ∀ n : ℕ,
      (α : ℝ) * n - ((KPPlain U (cantorPrefix w n)).toNat : ℝ) ≤ c} := by
  have hiff : ∀ w : CantorSeq,
      (¬ ∃ c : ℝ, ∀ n : ℕ, (α : ℝ) * n - ((KPPlain U (cantorPrefix w n)).toNat : ℝ) ≤ c)
        ↔ ∀ C : ℝ, ∃ n : ℕ,
            C < ((α : ℚ) : ℝ) * n - ((KPPlain U (cantorPrefix w n)).toNat : ℝ) := by
    intro w
    constructor
    · intro h C
      by_contra hcon
      push_neg at hcon
      exact h ⟨C, hcon⟩
    · rintro h ⟨c, hc⟩
      obtain ⟨n, hn⟩ := h c
      exact absurd (hc n) (not_le.2 hn)
  have hset : {w : CantorSeq | ¬ ∃ c : ℝ, ∀ n : ℕ,
      (α : ℝ) * n - ((KPPlain U (cantorPrefix w n)).toNat : ℝ) ≤ c}
      = {w : CantorSeq | ∀ C : ℝ, ∃ n : ℕ,
          C < ((α : ℚ) : ℝ) * n - ((KPPlain U (cantorPrefix w n)).toNat : ℝ)} :=
    Set.ext hiff
  rw [hset]
  refine Set.Subset.antisymm (fun w hw => ?_) (hmax _ ?_)
  · intro C
    exact exists_lt_alpha_mul_sub_KPPlain_of_isEffectiveAlphaNull U hU α hα
      (hA.mono_set (Set.singleton_subset_iff.2 hw)) C
  · exact isEffectiveAlphaNull_setOf_unbounded_gap U hU α hα

/-! ## Problem 170 -/

/-- **SUV Problem 170 (§5.8, p. 175).** For any real `α ∈ [0,1]` there exists a
set -- and even a singleton -- that has effective Hausdorff dimension `α`.

The witness is `rdilate α ω` for a uniformly Martin-Löf random `ω`: the bits
of `ω` placed where `⌈α·n⌉` grows, zeros elsewhere
(`Dimension/DilutionReal.lean`). -/
theorem problem_170_exists_singleton_effectiveHausdorffDim_eq (α : ℝ)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    ∃ w : CantorSeq, effectiveHausdorffDim {w} = α :=
  exists_effectiveHausdorffDim_singleton_eq hα.1 hα.2

/-! ## Problem 174 -/

/-- The alternative cover notion of SUV Problem 174 (§5.8, p. 175): a
*computable* sequence of intervals with finite sum of `r`-th powers of the
measures that covers each element of `A` infinitely many times. -/
def IsInfinitelyCoveredCover (r : ℝ) (A : Set CantorSeq) : Prop :=
  ∃ I : ℕ → BitString, Computable I ∧ (∑' k, intervalAlphaMass r (I k)) ≠ ⊤ ∧
    ∀ w ∈ A, {k : ℕ | IsCantorPrefix (I k) w}.Infinite

/-- A series of nonnegative terms bounded below by a fixed positive value on an
infinite index set diverges. -/
lemma tsum_eq_top_of_infinite_ge {f : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ 0) {T : Set ℕ}
    (hT : T.Infinite) (hge : ∀ k ∈ T, c ≤ f k) : (∑' k, f k) = ⊤ := by
  by_contra hne
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hne
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (ENNReal.inv_ne_top.2 hc)
  have hone : (1 : ℝ≥0∞) ≤ (m : ℝ≥0∞) * c := by
    by_cases htop : c = ⊤
    · rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · rw [hm0] at hm; simp at hm
      · have : (1 : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by exact_mod_cast hm0
        rw [htop]
        simp [ENNReal.mul_top, (by exact_mod_cast hm0.ne' : (m : ℝ≥0∞) ≠ 0)]
    · calc (1 : ℝ≥0∞) = c⁻¹ * c := (ENNReal.inv_mul_cancel hc htop).symm
        _ ≤ (m : ℝ≥0∞) * c := mul_le_mul' hm.le le_rfl
  obtain ⟨t, htsub, htcard⟩ := hT.exists_subset_card_eq (N * m)
  have h1 : (N * m : ℕ) • c ≤ ∑ k ∈ t, f k := by
    rw [← htcard]
    exact Finset.card_nsmul_le_sum t f c (fun k hk => hge k (htsub hk))
  have h2 : (∑ k ∈ t, f k) ≤ ∑' k, f k := ENNReal.sum_le_tsum t
  have h3 : (N : ℝ≥0∞) ≤ (N * m : ℕ) • c := by
    rw [nsmul_eq_mul]
    push_cast
    calc (N : ℝ≥0∞) = (N : ℝ≥0∞) * 1 := (mul_one _).symm
      _ ≤ (N : ℝ≥0∞) * ((m : ℝ≥0∞) * c) := mul_le_mul' le_rfl hone
      _ = (N : ℝ≥0∞) * (m : ℝ≥0∞) * c := by ring
  exact absurd hN (not_lt.2 (le_trans h3 (le_trans h1 h2)))

/-- **Problem 174, the easy direction**.  An effective
`α`-null set has an infinitely-covering computable cover of finite `α`-weight:
run the cover algorithm at `ε = 1/2, 1/4, …` and concatenate, as in the proof of
Theorem 120 (SUV p. 175, "Let us do this for `ε = 1, 1/2, 1/4, …`.  In this way
we get a sequence of intervals that have finite sum of `r`th powers of their
measures, and infinitely many of them cover `ω`"). -/
theorem isInfinitelyCoveredCover_of_isEffectiveAlphaNull {α : ℝ} (hα : 0 < α)
    {A : Set CantorSeq} (h : IsEffectiveAlphaNull α A) : IsInfinitelyCoveredCover α A := by
  classical
  obtain ⟨I, hIcomp, hI⟩ := h
  set eps : ℕ → ℚ := fun j => (2 : ℚ)⁻¹ ^ (j + 1) with hepsdef
  have hepspos : ∀ j, 0 < eps j := fun j => by positivity
  set E : ℕ → Option BitString := fun m => I (eps (Nat.unpair m).1) (Nat.unpair m).2 with hEdef
  have hEcomp : Computable E := by
    have h1 : Computable (fun m : ℕ => eps (Nat.unpair m).1) :=
      computable_pow_half.comp
        ((Primrec.succ.comp (Primrec.fst.comp Primrec.unpair)).to_comp)
    exact hIcomp.comp h1 ((Primrec.snd.comp Primrec.unpair).to_comp)
  set pad : ℕ → BitString := fun m => (List.range m).map (fun _ => false) with hpaddef
  have hpadlen : ∀ m, (pad m).length = m := by
    intro m; simp [hpaddef]
  have hpadcomp : Computable pad :=
    (Primrec.list_map Primrec.list_range (Primrec.const false).to₂).to_comp
  set J : ℕ → BitString := fun m => (E m).getD (pad m) with hJdef
  have hJcomp : Computable J := by
    have hcase := Computable.option_casesOn hEcomp hpadcomp
      (Computable.snd (α := ℕ) (β := BitString)).to₂
    refine hcase.of_eq (fun m => ?_)
    cases h : E m <;> simp [hJdef, h]
  refine ⟨J, hJcomp, ?_, ?_⟩
  · -- the weight is finite
    have hbound : ∀ m, intervalAlphaMass α (J m)
        ≤ coverAlphaMass α (E m) + intervalAlphaMass α (pad m) := by
      intro m
      cases hm : E m with
      | none => simp [hJdef, hm]
      | some z => simp [hJdef, hm]
    have hlevel : ∀ j : ℕ,
        (∑' k, coverAlphaMass α (I (eps j) k)) ≤ ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) := by
      intro j
      refine le_of_lt (lt_of_lt_of_le (hI (eps j) (hepspos j)).2 (le_of_eq ?_))
      rw [hepsdef, ofReal_pow_half_eq_dyadicValue, dyadicValue_one_eq_inv_two_pow']
    have hEsum : (∑' m, coverAlphaMass α (E m)) ≤ 1 := by
      have hsplit : (∑' m, coverAlphaMass α (E m))
          = ∑' j, ∑' k, coverAlphaMass α (I (eps j) k) := by
        rw [tsum_nat_pair]
        exact tsum_congr (fun j => tsum_congr (fun k => by simp [hEdef]))
      have hgeo : (∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1)) = 1 := by
        simpa using tsum_inv_two_pow_shift 0
      rw [hsplit, ← hgeo]
      exact ENNReal.tsum_le_tsum hlevel
    have hq : (((2 : ℝ≥0∞)⁻¹) ^ α) < 1 := ENNReal.rpow_lt_one (by norm_num) hα
    have hpadsum : (∑' m, intervalAlphaMass α (pad m)) ≠ ⊤ := by
      have hval : ∀ m, intervalAlphaMass α (pad m) = (((2 : ℝ≥0∞)⁻¹) ^ α) ^ m := by
        intro m
        rw [intervalAlphaMass_eq_inv_two_pow, hpadlen,
          ← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) m, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_natCast ((((2 : ℝ≥0∞)⁻¹) ^ α)) m, ← ENNReal.rpow_mul, mul_comm]
      rw [tsum_congr hval, ENNReal.tsum_geometric]
      refine ENNReal.inv_ne_top.2 ?_
      intro hzero
      exact absurd (tsub_eq_zero_iff_le.1 hzero) (not_le.2 hq)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top ENNReal.one_ne_top hEsum, hpadsum⟩
  · -- every point of `A` is covered infinitely often
    intro w hw
    have hchoice : ∀ j : ℕ, ∃ k : ℕ, IsCantorPrefix (J (Nat.pair j k)) w := by
      intro j
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 ((hI (eps j) (hepspos j)).1 hw)
      refine ⟨k, ?_⟩
      cases hz : I (eps j) k with
      | none => rw [hz] at hk; simp at hk
      | some z =>
        rw [hz] at hk
        have hJ : J (Nat.pair j k) = z := by simp [hJdef, hEdef, hz]
        rw [hJ]
        exact hk
    choose kf hkf using hchoice
    refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => Nat.pair j (kf j)) ?_ ?_
    · intro a b hab
      have := congrArg (fun n => (Nat.unpair n).1) hab
      simpa using this
    · intro j
      exact hkf j

/-- **Problem 174, the effective direction**.  An
infinitely-covering cover of finite `r`-weight makes `A` an effective `r'`-null
set for every rational `r' > r`: keep only the intervals of length at least
`L(ε)`, which still cover every point of `A` (each point is covered infinitely
often and, the weight being finite, only finitely many intervals are short). -/
theorem isEffectiveAlphaNull_of_isInfinitelyCoveredCover {r : ℝ} (hr : 0 < r) {r' : ℚ}
    (hrr' : r < (r' : ℝ)) {A : Set CantorSeq} (h : IsInfinitelyCoveredCover r A) :
    IsEffectiveAlphaNull ((r' : ℚ) : ℝ) A := by
  classical
  obtain ⟨I, hIcomp, hsum, hcov⟩ := h
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hrr'
  have hspos : (0 : ℝ) < (s : ℝ) := lt_trans hr hs1
  have hsposQ : (0 : ℚ) < s := by exact_mod_cast hspos
  have hsum_s : (∑' k, intervalAlphaMass ((s : ℚ) : ℝ) (I k)) ≠ ⊤ :=
    ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum (fun k => intervalAlphaMass_mono hs1.le (I k)))
  obtain ⟨B, hB⟩ : ∃ B : ℕ, (∑' k, intervalAlphaMass ((s : ℚ) : ℝ) (I k)) ≤ (2 : ℝ≥0∞) ^ B := by
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hsum_s
    refine ⟨N, le_of_lt (lt_of_lt_of_le hN ?_)⟩
    have : N ≤ 2 ^ N := le_of_lt (Nat.lt_two_pow_self)
    calc (N : ℝ≥0∞) ≤ ((2 ^ N : ℕ) : ℝ≥0∞) := by exact_mod_cast this
      _ = (2 : ℝ≥0∞) ^ N := by push_cast; ring
  have hδpos : (0 : ℚ) < r' - s := by
    have : (s : ℝ) < (r' : ℝ) := hs2
    have : s < r' := by exact_mod_cast this
    linarith
  set M : ℕ := (r' - s).den with hMdef
  have hMpos : 0 < M := (r' - s).pos
  set L : ℚ → ℕ := fun ε => M * (ε.den + B + 1) with hLdef
  have hLcomp : Computable L := by
    refine Primrec.nat_mul.to_comp.comp (Computable.const M) ?_
    exact Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp computable_ratDen (Computable.const B))
      (Computable.const 1)
  -- the exponent gap at the cutoff
  have hfloor : ∀ ε : ℚ, ε.den + B + 1 ≤ alphaFloor (r' - s) (L ε) := by
    intro ε
    have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
    have hone : (1 : ℝ) / (M : ℝ) ≤ (((r' - s : ℚ)) : ℝ) := one_div_den_le_rat hδpos
    have hLR : ((L ε : ℕ) : ℝ) = (M : ℝ) * ((ε.den + B + 1 : ℕ) : ℝ) := by
      rw [hLdef]; push_cast; ring
    have hge : ((ε.den + B + 1 : ℕ) : ℝ) ≤ (((r' - s : ℚ)) : ℝ) * ((L ε : ℕ) : ℝ) := by
      rw [hLR]
      have hnn : (0 : ℝ) ≤ (M : ℝ) * ((ε.den + B + 1 : ℕ) : ℝ) := by positivity
      have hcancel : (1 / (M : ℝ)) * ((M : ℝ) * ((ε.den + B + 1 : ℕ) : ℝ))
          = ((ε.den + B + 1 : ℕ) : ℝ) := by field_simp
      have h2 := mul_le_mul_of_nonneg_right hone hnn
      rwa [hcancel] at h2
    have hspec := (alphaFloor_spec (r' - s) hδpos (L ε)).2
    have : ((ε.den + B + 1 : ℕ) : ℝ) < ((alphaFloor (r' - s) (L ε) : ℕ) : ℝ) + 1 := by
      calc ((ε.den + B + 1 : ℕ) : ℝ) ≤ (((r' - s : ℚ)) : ℝ) * ((L ε : ℕ) : ℝ) := hge
        _ < ((alphaFloor (r' - s) (L ε) : ℕ) : ℝ) + 1 := hspec
    have hnat : ε.den + B + 1 < alphaFloor (r' - s) (L ε) + 1 := by exact_mod_cast this
    omega
  refine ⟨fun ε k => bif decide (L ε ≤ (I k).length) then some (I k) else none, ?_,
    fun ε hε => ⟨?_, ?_⟩⟩
  · -- computability
    have hlen : Computable (fun p : ℚ × ℕ => (I p.2).length) :=
      Primrec.list_length.to_comp.comp (hIcomp.comp Computable.snd)
    have hble : Computable (fun q : ℕ × ℕ => decide (q.1 ≤ q.2)) :=
      ((PrimrecRel.comp Primrec.nat_le Primrec.fst Primrec.snd).decide).to_comp
    have htest : Computable (fun p : ℚ × ℕ => decide (L p.1 ≤ (I p.2).length)) :=
      hble.comp (Computable.pair (hLcomp.comp Computable.fst) hlen)
    exact (Computable.cond htest
      (Computable.option_some.comp (hIcomp.comp Computable.snd)) (Computable.const none)).to₂
  · -- the retained intervals still cover `A`
    intro x hx
    have hinf := hcov x hx
    by_contra hcon
    have hshort : ∀ k ∈ {k : ℕ | IsCantorPrefix (I k) x},
        (((2 : ℝ≥0∞)⁻¹) ^ (L ε)) ^ ((s : ℚ) : ℝ) ≤ intervalAlphaMass ((s : ℚ) : ℝ) (I k) := by
      intro k hk
      have hlt : (I k).length < L ε := by
        by_contra hge
        push_neg at hge
        refine hcon (Set.mem_iUnion.2 ⟨k, ?_⟩)
        simp only [decide_eq_true hge, cond_true, Option.elim_some]
        exact hk
      have h1 : ((2 : ℝ≥0∞)⁻¹) ^ (L ε) ≤ ((2 : ℝ≥0∞)⁻¹) ^ (I k).length :=
        inv_two_pow_antitone (le_of_lt hlt)
      rw [intervalAlphaMass_eq_inv_two_pow]
      exact ENNReal.rpow_le_rpow h1 hspos.le
    have hbase : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ (L ε) := by
      have hne : ((2 : ℝ≥0∞)⁻¹) ^ (L ε) ≠ 0 :=
        pow_ne_zero _ (ENNReal.inv_ne_zero.2 (by norm_num))
      exact lt_of_le_of_ne (zero_le _) (Ne.symm hne)
    have hbasetop : ((2 : ℝ≥0∞)⁻¹) ^ (L ε) ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (by norm_num))
    have hcne : (((2 : ℝ≥0∞)⁻¹) ^ (L ε)) ^ ((s : ℚ) : ℝ) ≠ 0 :=
      ne_of_gt (ENNReal.rpow_pos hbase hbasetop)
    have htop : (∑' k, intervalAlphaMass ((s : ℚ) : ℝ) (I k)) = ⊤ :=
      tsum_eq_top_of_infinite_ge (f := fun k => intervalAlphaMass ((s : ℚ) : ℝ) (I k))
        hcne hinf hshort
    exact hsum_s htop
  · -- the weight of the retained intervals
    have hδR : (0 : ℝ) < (((r' - s : ℚ)) : ℝ) := by exact_mod_cast hδpos
    have hne0 : ((2 : ℝ≥0∞)⁻¹) ≠ 0 := ENNReal.inv_ne_zero.2 (by norm_num)
    have hnetop : ((2 : ℝ≥0∞)⁻¹) ≠ ⊤ := ENNReal.inv_ne_top.2 (by norm_num)
    have hterm : ∀ k, coverAlphaMass ((r' : ℚ) : ℝ)
        (bif decide (L ε ≤ (I k).length) then some (I k) else none)
        ≤ intervalAlphaMass ((s : ℚ) : ℝ) (I k)
            * ((2 : ℝ≥0∞)⁻¹) ^ (alphaFloor (r' - s) (L ε)) := by
      intro k
      by_cases hk : L ε ≤ (I k).length
      · rw [decide_eq_true hk, cond_true, coverAlphaMass_some]
        have hsplit : ((r' : ℚ) : ℝ) = ((s : ℚ) : ℝ) + (((r' - s : ℚ)) : ℝ) := by
          push_cast; ring
        rw [intervalAlphaMass_eq_inv_two_pow, intervalAlphaMass_eq_inv_two_pow, hsplit,
          ENNReal.rpow_add _ _ (pow_ne_zero _ hne0) (ENNReal.pow_ne_top hnetop)]
        refine mul_le_mul' le_rfl ?_
        have h1 : ((2 : ℝ≥0∞)⁻¹) ^ (I k).length ≤ ((2 : ℝ≥0∞)⁻¹) ^ (L ε) :=
          inv_two_pow_antitone hk
        refine le_trans (ENNReal.rpow_le_rpow h1 hδR.le) ?_
        rw [← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) (L ε), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) (alphaFloor (r' - s) (L ε))]
        refine ENNReal.rpow_le_rpow_of_exponent_ge (by norm_num) ?_
        have := (alphaFloor_spec (r' - s) hδpos (L ε)).1
        calc ((alphaFloor (r' - s) (L ε) : ℕ) : ℝ)
            ≤ (((r' - s : ℚ)) : ℝ) * ((L ε : ℕ) : ℝ) := this
          _ = ((L ε : ℕ) : ℝ) * (((r' - s : ℚ)) : ℝ) := by ring
      · rw [decide_eq_false hk, cond_false, coverAlphaMass_none]
        exact zero_le _
    have hmain : (∑' k, coverAlphaMass ((r' : ℚ) : ℝ)
        (bif decide (L ε ≤ (I k).length) then some (I k) else none))
        ≤ ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + 1) := by
      calc (∑' k, coverAlphaMass ((r' : ℚ) : ℝ)
              (bif decide (L ε ≤ (I k).length) then some (I k) else none))
          ≤ ∑' k, intervalAlphaMass ((s : ℚ) : ℝ) (I k)
              * ((2 : ℝ≥0∞)⁻¹) ^ (alphaFloor (r' - s) (L ε)) := ENNReal.tsum_le_tsum hterm
        _ = (∑' k, intervalAlphaMass ((s : ℚ) : ℝ) (I k))
              * ((2 : ℝ≥0∞)⁻¹) ^ (alphaFloor (r' - s) (L ε)) := ENNReal.tsum_mul_right
        _ ≤ (2 : ℝ≥0∞) ^ B * ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + B + 1) :=
            mul_le_mul' hB (inv_two_pow_antitone (hfloor ε))
        _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + 1) := two_pow_mul_inv_two_pow_le (by omega)
    refine lt_of_le_of_lt hmain ?_
    have hden : ((2 : ℝ≥0∞)⁻¹) ^ ε.den ≤ ENNReal.ofReal (ε : ℝ) := by
      rw [← dyadicValue_one_eq_inv_two_pow']
      exact dyadicValue_den_le_rat hε
    refine lt_of_lt_of_le ?_ hden
    have hne0' : ((2 : ℝ≥0∞)⁻¹) ^ ε.den ≠ 0 := pow_ne_zero _ hne0
    have hnetop' : ((2 : ℝ≥0∞)⁻¹) ^ ε.den ≠ ⊤ := ENNReal.pow_ne_top hnetop
    have hhalf : (2 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_lt_one.2 (by norm_num)
    calc ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + 1) = ((2 : ℝ≥0∞)⁻¹) ^ ε.den * (2 : ℝ≥0∞)⁻¹ := pow_succ _ _
      _ < ((2 : ℝ≥0∞)⁻¹) ^ ε.den * 1 := ENNReal.mul_lt_mul_right hne0' hnetop' hhalf
      _ = ((2 : ℝ≥0∞)⁻¹) ^ ε.den := mul_one _

/-- **SUV Problem 174 (§5.8, p. 175).** The definition of the effective
Hausdorff dimension of a set `A` remains the same if we require the existence of
a computable sequence of intervals that has finite sum of `r`-th powers of the
measures and that covers each element of `A` infinitely many times.

The two infima are equal because the two families of exponents are cofinal in
each other: every effective `α`-null exponent is an infinitely-covering one
(`isInfinitelyCoveredCover_of_isEffectiveAlphaNull`), and every rational above an
infinitely-covering exponent is an effective-null one
(`isEffectiveAlphaNull_of_isInfinitelyCoveredCover`). -/
theorem problem_174_effectiveHausdorffDim_eq_sInf_infinitelyCovered (A : Set CantorSeq) :
    effectiveHausdorffDim A = sInf {r : ℝ | 0 < r ∧ IsInfinitelyCoveredCover r A} := by
  have hST : {α : ℝ | 0 < α ∧ IsEffectiveAlphaNull α A}
      ⊆ {r : ℝ | 0 < r ∧ IsInfinitelyCoveredCover r A} := by
    rintro α ⟨hα, hnull⟩
    exact ⟨hα, isInfinitelyCoveredCover_of_isEffectiveAlphaNull hα hnull⟩
  have hSne := nonempty_effectiveAlphaSet A
  have hTne : ({r : ℝ | 0 < r ∧ IsInfinitelyCoveredCover r A}).Nonempty :=
    hSne.mono hST
  have hTbdd : BddBelow {r : ℝ | 0 < r ∧ IsInfinitelyCoveredCover r A} :=
    ⟨0, fun x hx => hx.1.le⟩
  refine le_antisymm (le_csInf hTne ?_) (csInf_le_csInf hTbdd hSne hST)
  rintro r ⟨hrpos, hcov⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨r', hr'1, hr'2⟩ := exists_rat_btwn hcon
  have hr'pos : (0 : ℝ) < (r' : ℝ) := lt_trans hrpos hr'1
  have hle : effectiveHausdorffDim A ≤ (r' : ℝ) :=
    csInf_le (bddBelow_effectiveAlphaSet A)
      ⟨hr'pos, isEffectiveAlphaNull_of_isInfinitelyCoveredCover hrpos hr'1 hcov⟩
  linarith

/-! ## Problem 176 -/

/-- **SUV Problem 176 (§5.9.2, p. 178).** For every string `x` the deficiency of
at least one of the strings `x0` and `x1` does not exceed the deficiency of `x`
(the computable measure `P` used in the definition of the deficiency being
fixed). -/
theorem problem_176_deficiency_child_le (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (hP : IsComputableMeasure P) (x : BitString) :
    deficiency P (x ++ [false]) ≤ deficiency P x ∨
      deficiency P (x ++ [true]) ≤ deficiency P x := by
  -- the computability of `P` is not needed: the statement holds for every
  -- probability measure, because the argument only uses `P(Ω_x0) + P(Ω_x1) = P(Ω_x)`
  have _ := hP
  have hsemi : IsContinuousTreeSemimeasure universalContinuousSemimeasure :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  have hane : ∀ y : BitString, universalContinuousSemimeasure y ≠ ⊤ := hsemi.ne_top
  have hapos : ∀ y : BitString, 0 < universalContinuousSemimeasure y :=
    universalContinuousSemimeasure_pos
  have haR : ∀ y : BitString, 0 < (universalContinuousSemimeasure y).toReal := fun y =>
    ENNReal.toReal_pos (ne_of_gt (hapos y)) (hane y)
  have hmassne : ∀ y : BitString, cantorMass P y ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  by_cases hx : cantorMass P x = 0
  · exact Or.inl (by rw [(deficiency_eq_top_iff P x).2 hx]; exact le_top)
  have hp : 0 < (cantorMass P x).toReal := ENNReal.toReal_pos hx (hmassne x)
  -- the comparison of deficiencies is the comparison of the ratios `a(y)/P(Ω_y)`
  have key : ∀ b : Bool, cantorMass P (x ++ [b]) ≠ 0 →
      (universalContinuousSemimeasure (x ++ [b])).toReal * (cantorMass P x).toReal
        ≤ (universalContinuousSemimeasure x).toReal * (cantorMass P (x ++ [b])).toReal →
      deficiency P (x ++ [b]) ≤ deficiency P x := by
    intro b hb hle
    have hpb : 0 < (cantorMass P (x ++ [b])).toReal := ENNReal.toReal_pos hb (hmassne _)
    rw [deficiency_of_ne_zero hb, deficiency_of_ne_zero hx, EReal.coe_le_coe_iff]
    have hdiv : (universalContinuousSemimeasure (x ++ [b])).toReal
          / (cantorMass P (x ++ [b])).toReal
        ≤ (universalContinuousSemimeasure x).toReal / (cantorMass P x).toReal := by
      have hstep : (universalContinuousSemimeasure x).toReal / (cantorMass P x).toReal
          - (universalContinuousSemimeasure (x ++ [b])).toReal
            / (cantorMass P (x ++ [b])).toReal
          = ((universalContinuousSemimeasure x).toReal * (cantorMass P (x ++ [b])).toReal
              - (universalContinuousSemimeasure (x ++ [b])).toReal * (cantorMass P x).toReal)
            / ((cantorMass P x).toReal * (cantorMass P (x ++ [b])).toReal) := by
        field_simp
      have hnn : 0 ≤ (universalContinuousSemimeasure x).toReal / (cantorMass P x).toReal
          - (universalContinuousSemimeasure (x ++ [b])).toReal
            / (cantorMass P (x ++ [b])).toReal := by
        rw [hstep]
        exact div_nonneg (by linarith) (mul_nonneg hp.le hpb.le)
      linarith
    have hratio :
        Real.logb 2 ((universalContinuousSemimeasure (x ++ [b])).toReal
            / (cantorMass P (x ++ [b])).toReal)
          ≤ Real.logb 2 ((universalContinuousSemimeasure x).toReal / (cantorMass P x).toReal) :=
      (Real.logb_le_logb (by norm_num) (div_pos (haR _) hpb) (div_pos (haR x) hp)).mpr hdiv
    rw [Real.logb_div (ne_of_gt (haR _)) (ne_of_gt hpb),
      Real.logb_div (ne_of_gt (haR x)) (ne_of_gt hp)] at hratio
    unfold KA
    linarith
  by_cases h0 : cantorMass P (x ++ [false]) = 0
  · refine Or.inr (key true ?_ ?_)
    · rw [cantorMass_add P x, h0, zero_add] at hx
      exact hx
    · have hmass1 : cantorMass P (x ++ [true]) = cantorMass P x := by
        rw [cantorMass_add P x, h0, zero_add]
      rw [hmass1]
      exact mul_le_mul_of_nonneg_right
        (ENNReal.toReal_mono (hane x) (hsemi.child_true_le x)) hp.le
  by_cases h1 : cantorMass P (x ++ [true]) = 0
  · refine Or.inl (key false ?_ ?_)
    · rw [cantorMass_add P x, h1, add_zero] at hx
      exact hx
    · have hmass0 : cantorMass P (x ++ [false]) = cantorMass P x := by
        rw [cantorMass_add P x, h1, add_zero]
      rw [hmass0]
      exact mul_le_mul_of_nonneg_right
        (ENNReal.toReal_mono (hane x) (hsemi.child_false_le x)) hp.le
  -- both children carry positive mass: the semimeasure inequality forbids both failures
  by_contra hcon
  push_neg at hcon
  obtain ⟨hn0, hn1⟩ := hcon
  have hf : (universalContinuousSemimeasure x).toReal * (cantorMass P (x ++ [false])).toReal
      < (universalContinuousSemimeasure (x ++ [false])).toReal * (cantorMass P x).toReal := by
    by_contra hle
    push_neg at hle
    exact absurd (key false h0 hle) (not_le.2 hn0)
  have ht : (universalContinuousSemimeasure x).toReal * (cantorMass P (x ++ [true])).toReal
      < (universalContinuousSemimeasure (x ++ [true])).toReal * (cantorMass P x).toReal := by
    by_contra hle
    push_neg at hle
    exact absurd (key true h1 hle) (not_le.2 hn1)
  have hpsum : (cantorMass P x).toReal
      = (cantorMass P (x ++ [false])).toReal + (cantorMass P (x ++ [true])).toReal := by
    rw [cantorMass_add P x, ENNReal.toReal_add (hmassne _) (hmassne _)]
  have hAsum : (universalContinuousSemimeasure (x ++ [false])).toReal
      + (universalContinuousSemimeasure (x ++ [true])).toReal
      ≤ (universalContinuousSemimeasure x).toReal := by
    rw [← ENNReal.toReal_add (hane _) (hane _)]
    exact ENNReal.toReal_mono (hane x) (hsemi.2 x)
  have hexp : (universalContinuousSemimeasure x).toReal * (cantorMass P x).toReal
      = (universalContinuousSemimeasure x).toReal * (cantorMass P (x ++ [false])).toReal
        + (universalContinuousSemimeasure x).toReal * (cantorMass P (x ++ [true])).toReal := by
    rw [hpsum]
    ring
  have hmul : ((universalContinuousSemimeasure (x ++ [false])).toReal
      + (universalContinuousSemimeasure (x ++ [true])).toReal) * (cantorMass P x).toReal
      ≤ (universalContinuousSemimeasure x).toReal * (cantorMass P x).toReal :=
    mul_le_mul_of_nonneg_right hAsum hp.le
  linarith [hf, ht, hexp, hmul]

/-! ## Problem 185 -/

/-- **SUV Problem 185 (§5.9.3, p. 182).** A quantitative version of
Theorem 123(a): the expectation-bounded deficiency of the sequence `f(ω)` with
respect to `ν` is bounded by the expectation-bounded deficiency of `ω` with
respect to `μ` plus a constant that depends on the measures and the mapping but
not on `ω`.

The expectation-bounded deficiencies are the binary logarithms of maximal
expectation-bounded tests `u` for `μ` and `v` for `ν` (SUV §3.5, Theorem 42);
the constant is chosen before `ω`. -/
theorem problem_185_image_expectationDeficiency_le {μ ν : Measure CantorSeq}
    {f : BitStream → BitStream} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsComputableMeasure μ) (hf : IsComputableStreamMap f)
    (hν : IsImageMeasure μ f ν) {u v : CantorSeq → ℝ≥0∞}
    (hu : IsMaximalExpectationBoundedTest μ u)
    (hv : IsMaximalExpectationBoundedTest ν v) :
    ∃ c : ℝ, ∀ w t : CantorSeq, f (BitStream.infinite w) = BitStream.infinite t →
      ennrealLogbTwo (v t) ≤ ennrealLogbTwo (u w) + (c : EReal) := by
  classical
  obtain ⟨V, hV, hge⟩ := exists_expectationBoundedTest_comp hμ hf hν hv.1
  obtain ⟨c, hc⟩ := hu.2 V hV
  refine ⟨Real.logb 2 (c : ℝ), fun w t hft => ?_⟩
  have hvt : v t ≤ (c : ℝ≥0∞) * u w := le_trans (hge w t hft) (hc w)
  -- the degenerate values of `u w` are immediate
  rcases eq_or_ne (u w) ⊤ with hutop | hutop
  · have h1 : ennrealLogbTwo (u w) = ⊤ := by
      unfold ennrealLogbTwo
      rw [hutop]
      simp
    rw [h1]
    have h2 : (⊤ : EReal) + ((Real.logb 2 (c : ℝ) : ℝ) : EReal) = ⊤ := by
      exact EReal.top_add_coe _
    rw [h2]
    exact le_top
  rcases eq_or_ne (v t) 0 with hv0 | hv0
  · rw [hv0]
    unfold ennrealLogbTwo
    rw [if_pos rfl]
    exact bot_le
  -- `v t` is then finite and positive, and so is `u w`
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hvt
    exact hv0 (le_antisymm hvt (zero_le _))
  have hcR : (0 : ℝ) < (c : ℝ) := by
    have hcne : c ≠ 0 := by
      intro h
      exact hc0 (by rw [h]; simp)
    exact lt_of_le_of_ne c.coe_nonneg (Ne.symm (by exact_mod_cast hcne))
  have hu0 : u w ≠ 0 := by
    intro h
    rw [h, mul_zero] at hvt
    exact hv0 (le_antisymm hvt (zero_le _))
  have hvtop : v t ≠ ⊤ := by
    intro h
    rw [h] at hvt
    have : ((c : ℝ≥0∞) * u w) = ⊤ := le_antisymm le_top hvt
    rcases ENNReal.mul_eq_top.1 this with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hutop h2
    · exact (ENNReal.coe_ne_top) h1
  -- the real computation
  have hreal : (v t).toReal ≤ (c : ℝ) * (u w).toReal := by
    have h1 : ((c : ℝ≥0∞) * u w).toReal = (c : ℝ) * (u w).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
    rw [← h1]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hutop) hvt
  have hvpos : (0 : ℝ) < (v t).toReal := ENNReal.toReal_pos hv0 hvtop
  have hupos : (0 : ℝ) < (u w).toReal := ENNReal.toReal_pos hu0 hutop
  have hlog : Real.logb 2 (v t).toReal ≤ Real.logb 2 (u w).toReal + Real.logb 2 (c : ℝ) := by
    have h2 : Real.logb 2 (v t).toReal ≤ Real.logb 2 ((c : ℝ) * (u w).toReal) := by
      gcongr
      norm_num
    rw [Real.logb_mul (ne_of_gt hcR) (ne_of_gt hupos)] at h2
    linarith
  unfold ennrealLogbTwo
  rw [if_neg hv0, if_neg hvtop, if_neg hu0, if_neg hutop]
  rw [← EReal.coe_add]
  exact_mod_cast hlog

/-! ## Problem 187 -/

/-- The sharp form of "a bound on `x - 2 log₂ x` bounds `x`". -/
lemma le_add_two_logb_of_sub_two_logb_le {x M : ℝ} (hx : 1 ≤ x) (hM : 1 ≤ M)
    (h : x - 2 * Real.logb 2 x ≤ M) : x ≤ M + 2 * Real.logb 2 M + 32 := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlogpos : (0 : ℝ) < Real.log 2 := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hlogMnn : (0 : ℝ) ≤ Real.logb 2 M := Real.logb_nonneg (by norm_num) hM
  by_cases hcase : x ≤ 2 * M
  · -- `log₂ x ≤ 1 + log₂ M`
    have h1 : Real.logb 2 x ≤ Real.logb 2 (2 * M) :=
      (Real.logb_le_logb (by norm_num) hxpos (by positivity)).mpr hcase
    have h2 : Real.logb 2 (2 * M) = 1 + Real.logb 2 M := by
      rw [Real.logb_mul (by norm_num) hMpos.ne', Real.logb_self_eq_one (by norm_num)]
    linarith
  · -- `x > 2M` forces `x < 4 log₂ x`, hence `x ≤ 32`
    have hxM : 2 * M < x := not_le.1 hcase
    have hkey : x < 4 * Real.logb 2 x := by linarith
    have hx32 : x ≤ 32 := by
      by_contra hcon
      push_neg at hcon
      -- for `x ≥ 32` one has `4 log₂ x ≤ x`
      have hstep : Real.log (x / 32) ≤ x / 32 - 1 := Real.log_le_sub_one_of_pos (by positivity)
      have hlog32 : Real.log (x / 32) = Real.log x - 5 * Real.log 2 := by
        rw [Real.log_div hxpos.ne' (by norm_num), show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num,
          Real.log_pow]
        push_cast
        ring
      have hlogx : Real.log x ≤ x / 32 - 1 + 5 * Real.log 2 := by
        rw [hlog32] at hstep
        linarith
      have hlogbx : Real.logb 2 x = Real.log x / Real.log 2 := by rw [Real.logb]
      have hprod : 32 * Real.log 2 < x * Real.log 2 := by
        exact mul_lt_mul_of_pos_right hcon hlogpos
      have hbound : 4 * Real.logb 2 x ≤ x := by
        rw [hlogbx, mul_div_assoc', div_le_iff₀ hlogpos]
        nlinarith [hlogx, hlogpos, hcon, hprod, hlog2]
      linarith
    linarith

/-- **SUV Problem 187 (§5.9.3, p. 185).** A finitary version of Theorem 123(a):
if `u` and `w` are binary strings such that `u ⪯ f(w)`, then

`d_ν(u) ≤ d_μ(w) + 2 log d_μ(w) + O(1)`.

As in Theorem 124, the hypothesis `deficiency μ w = (d : EReal)` isolates the
finite-deficiency case in which `2 log d_μ(w)` is meaningful, and `1 ≤ d` is the
log convention of `Dimension/ChangeOfMeasure.lean`: for `d < 1` the term
`2 log d` is negative and the printed bound would be strictly stronger than the
source's `O(1)` statement.  The book's hint calls this problem "a generalization
of Theorem 124" (p. 185), so the two must use the *same* convention -- they do.
The constant is chosen before `u` and `w`. -/
theorem problem_187_finitary_image_deficiency_le {μ ν : Measure CantorSeq}
    {f : BitStream → BitStream} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsComputableMeasure μ) (hf : IsComputableStreamMap f)
    (hν : IsImageMeasure μ f ν) :
    ∃ c : ℝ, ∀ (u w : BitString) (d : ℝ), 1 ≤ d →
      BitStream.finite u ≤ f (BitStream.finite w) → deficiency μ w = (d : EReal) →
        deficiency ν u ≤ ((d + 2 * Real.logb 2 d + c : ℝ) : EReal) := by
  classical
  obtain ⟨S, hScont, hSdom⟩ := exists_imageDeficiencyWeightedSemimeasure hμ hf hν
  obtain ⟨c₁, hc₁top, hc₁⟩ := universalContinuousSemimeasure_isMaximal S hScont
  set C₁ : ℝ := (c₁ + 1).toReal with hC₁
  have hC₁pos : 0 < C₁ := by
    rw [hC₁]
    exact ENNReal.toReal_pos (by simp) (by simp [hc₁top])
  have hC₁one : (1 : ℝ) ≤ C₁ := by
    have h1 : ((1 : ℝ≥0∞)).toReal ≤ ((c₁ + 1 : ℝ≥0∞)).toReal :=
      ENNReal.toReal_mono (by simp [hc₁top]) le_add_self
    simpa [hC₁] using h1
  have hC₁log : 0 ≤ Real.logb 2 C₁ := Real.logb_nonneg (by norm_num) hC₁one
  set E : ℝ := 3 + Real.logb 2 C₁ with hE
  have hEpos : (0 : ℝ) ≤ E := by rw [hE]; linarith
  refine ⟨E + 2 * Real.logb 2 (1 + E) + 32 + 2, ?_⟩
  intro u w d hd hle hdw
  have hwne : cantorMass μ w ≠ 0 := by
    intro h0
    rw [deficiency, if_pos h0] at hdw
    exact absurd hdw.symm (EReal.coe_ne_top d)
  have hmono : cantorMass μ w ≤ cantorMass ν u := by
    rw [hν u]
    refine measure_mono fun x hx => ?_
    have hwx : BitStream.finite w ≤ BitStream.infinite x := BitStream.finite_le_infinite_iff.2 hx
    exact le_trans hle (hf.1.1 hwx)
  have hune : cantorMass ν u ≠ 0 := by
    intro h0
    rw [h0] at hmono
    exact hwne (le_antisymm hmono (zero_le _))
  set D : ℝ := -Real.logb 2 (cantorMass ν u).toReal - KA u with hDdef
  have hdefu : deficiency ν u = (D : EReal) := deficiency_of_ne_zero hune
  rw [hdefu, EReal.coe_le_coe_iff]
  have hlogd : 0 ≤ Real.logb 2 d := Real.logb_nonneg (by norm_num) hd
  have hlog1E : 0 ≤ Real.logb 2 (1 + E) := Real.logb_nonneg (by norm_num) (by linarith)
  by_cases hbig : (2 : ℝ) ≤ D
  case neg =>
    have hDsmall : D < 2 := not_le.1 hbig
    linarith
  case pos =>
    have hAtop : universalContinuousSemimeasure w ≠ ⊤ :=
      universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top w
    set A : ℝ := (universalContinuousSemimeasure w).toReal with hA
    have hApos : 0 < A := by
      rw [hA]
      exact ENNReal.toReal_pos (universalContinuousSemimeasure_pos w).ne' hAtop
    set Pw : ℝ := (cantorMass μ w).toReal with hPw
    have hPwtop : cantorMass μ w ≠ ⊤ := measure_ne_top μ _
    have hPwpos : 0 < Pw := by
      rw [hPw]
      exact ENNReal.toReal_pos hwne hPwtop
    have hdval : d = -Real.logb 2 Pw + Real.logb 2 A := by
      have hdef := deficiency_of_ne_zero (P := μ) (x := w) hwne
      rw [hdw] at hdef
      have h3 : d = -Real.logb 2 Pw - KA w := by exact_mod_cast hdef
      rw [h3, KA, hA]
      ring
    set k : ℕ := ⌊D⌋₊ - 1 with hk
    have hfloor_le : (⌊D⌋₊ : ℝ) ≤ D := Nat.floor_le (by linarith)
    have hfloor_lt : D < (⌊D⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one D
    have hfloor2 : 2 ≤ ⌊D⌋₊ := Nat.le_floor (by exact_mod_cast hbig)
    have hk1 : 1 ≤ k := by omega
    have hkR : (k : ℝ) = (⌊D⌋₊ : ℝ) - 1 := by
      rw [hk]
      have h1 : (1 : ℕ) ≤ ⌊D⌋₊ := by omega
      push_cast [Nat.cast_sub h1]
      ring
    have hklt : (k : ℝ) < D := by rw [hkR]; linarith
    have hkge : D - 2 ≤ (k : ℝ) := by rw [hkR]; linarith
    have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hdom := hSdom k u w D hk1 hle hdefu hklt
    have hbound : ENNReal.ofReal ((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2)) * cantorMass μ w
        ≤ (c₁ + 1) * universalContinuousSemimeasure w :=
      le_trans hdom (le_trans (hc₁ w) (by gcongr; exact le_self_add))
    have hqpos : 0 < (2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2) := by positivity
    have hreal : ((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2)) * Pw ≤ C₁ * A := by
      have hmono2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp [hc₁top]) hAtop) hbound
      rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hqpos.le,
        ← hPw, ← hA, ← hC₁] at hmono2
    have hlogs : Real.logb 2 (((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2)) * Pw) ≤ Real.logb 2 (C₁ * A) :=
      (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).mpr hreal
    have hexpand : Real.logb 2 (((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2)) * Pw)
        = (k : ℝ) - (1 + 2 * Real.logb 2 k) + Real.logb 2 Pw := by
      rw [Real.logb_mul (by positivity) hPwpos.ne', Real.logb_div (by positivity) (by positivity),
        Real.logb_pow, Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one
          (by norm_num), Real.logb_pow]
      push_cast
      ring
    have hlogk : Real.logb 2 (k : ℝ) ≤ Real.logb 2 D :=
      (Real.logb_le_logb (by norm_num) (by linarith) (by linarith)).mpr (le_of_lt hklt)
    have hsplit : Real.logb 2 (C₁ * A) = Real.logb 2 C₁ + Real.logb 2 A :=
      Real.logb_mul hC₁pos.ne' hApos.ne'
    rw [hexpand, hsplit] at hlogs
    have hstep : D - 2 * Real.logb 2 D ≤ d + E := by
      rw [hdval, hE]
      linarith
    have hM1 : (1 : ℝ) ≤ d + E := by linarith
    have hD1 : (1 : ℝ) ≤ D := by linarith
    have hfinal := le_add_two_logb_of_sub_two_logb_le hD1 hM1 hstep
    have hle2 : Real.logb 2 (d + E) ≤ Real.logb 2 d + Real.logb 2 (1 + E) := by
      have h1 : d + E ≤ d * (1 + E) := by nlinarith
      have h2 : Real.logb 2 (d + E) ≤ Real.logb 2 (d * (1 + E)) :=
        (Real.logb_le_logb (by norm_num) (by linarith) (by nlinarith)).mpr h1
      rwa [Real.logb_mul (by linarith) (by linarith)] at h2
    linarith

end Kolmogorov
