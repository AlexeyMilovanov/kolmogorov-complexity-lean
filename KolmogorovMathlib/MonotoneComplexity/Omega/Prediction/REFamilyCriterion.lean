import KolmogorovMathlib.MonotoneComplexity.Omega.Prediction.Part01
import KolmogorovMathlib.MonotoneComplexity.Omega.Solovay
import KolmogorovMathlib.MonotoneComplexity.Omega.PredictCover
import KolmogorovMathlib.MonotoneComplexity.Omega.PaintEnum
import KolmogorovMathlib.MonotoneComplexity.Omega.DisjointCover
import KolmogorovMathlib.MonotoneComplexity.Omega.MultiCover

/-!
# Non-randomness of a lower semicomputable real through enumerable families

The criterion that replaces the prediction game by a covering condition: the sum of a computable
series of nonnegative rationals fails to be random exactly when it admits a uniformly enumerable
family of small total mass covering it
(`not_isMartinLofRandomReal_iff_exists_smallMassREFamily`, with the one-directional
`not_isMartinLofRandomReal_of_exists_smallMassREFamily`). Since every lower semicomputable real
is a rational plus such a series (`exists_series_of_isLowerSemicomputableReal`), the criterion
applies to all of them, and combining two families at half the budget
(`isUniformlyREFamily_inter_half`, `tsum_subtype_mono`) gives
`not_isMartinLofRandomReal_add`: a sum of two non-random lower semicomputable reals is
non-random.

Source: SUV §5.7.3, Theorems 107–109.
-/

namespace Kolmogorov

open ComputableReals
open MeasureTheory ENNReal

/-- A direct consequence of Theorem 108 with `aᵢ = r₀ + ⋯ + rᵢ₋₁` and `hᵢ = rᵢ` for `i ∈ W`.
SUV Theorem 109 (Section 5.7, p. 164), reverse direction. -/
theorem not_isMartinLofRandomReal_of_exists_smallMassREFamily
    {r : ℕ → ℚ} {α : ℝ} (hr : Computable r) (hr0 : ∀ i, 0 ≤ r i)
    (hsum : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (r i : ℝ)) Filter.atTop (nhds α))
    (h : ∃ W : ℚ → Set ℕ, IsUniformlyREFamily W ∧ ∀ ε : ℚ, 0 < ε →
      (∑' i : (W ε : Set ℕ), ENNReal.ofReal ((r (i : ℕ) : ℝ))) < ENNReal.ofReal (ε : ℝ) ∧
      {i : ℕ | i ∉ W ε}.Finite) :
    ¬ IsMartinLofRandomReal α := by
  classical
  obtain ⟨W, ⟨e, he, hW⟩, hspec⟩ := h
  -- the partial sums `aᵢ = r₀ + ⋯ + rᵢ₋₁`
  have haval : ∀ n, ratRangeSum r n = ∑ i ∈ Finset.range n, r i := ratRangeSum_eq r
  have ha : Computable (ratRangeSum r) := computable_ratRangeSum hr
  have hmono : Monotone (ratRangeSum r) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rw [haval, haval, Finset.sum_range_succ]
    linarith [hr0 n]
  have hcast : ∀ n : ℕ, ((ratRangeSum r n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, ((r i : ℚ) : ℝ) := by
    intro n
    rw [haval]
    push_cast
    ring
  have hlim : Filter.Tendsto (fun n => ((ratRangeSum r n : ℚ) : ℝ)) Filter.atTop (nhds α) := by
    refine Filter.Tendsto.congr (fun n => (hcast n).symm) hsum
  -- the series is summable with sum `α`
  have hpmono : Monotone (fun n => ∑ i ∈ Finset.range n, ((r i : ℚ) : ℝ)) := by
    refine monotone_nat_of_le_succ (fun m => ?_)
    rw [Finset.sum_range_succ]
    have hm : (0 : ℝ) ≤ ((r m : ℚ) : ℝ) := by exact_mod_cast hr0 m
    linarith
  have hbdd : ∀ n, ∑ i ∈ Finset.range n, ((r i : ℚ) : ℝ) ≤ α := hpmono.ge_of_tendsto hsum
  have hS : Summable (fun i => ((r i : ℚ) : ℝ)) :=
    summable_of_sum_range_le (fun i => by exact_mod_cast hr0 i) hbdd
  have hSval : ∑' i, ((r i : ℚ) : ℝ) = α :=
    tendsto_nhds_unique hS.hasSum.tendsto_sum_nat hsum
  -- the enumeration test
  have hE : Computable₂ (fun (p : ℚ × ℕ) (k : ℕ) => decide (e p.1 k = some p.2)) := by
    have h1 : Computable (fun z : (ℚ × ℕ) × ℕ => e z.1.1 z.2) :=
      he.comp (Computable.fst.comp Computable.fst) Computable.snd
    have h2 : Computable (fun z : (ℚ × ℕ) × ℕ => (some z.1.2 : Option ℕ)) :=
      Computable.option_some.comp (Computable.snd.comp Computable.fst)
    have heq : Computable₂ (fun x y : Option ℕ => decide (x = y)) :=
      (PrimrecRel.decide (Primrec.eq (α := Option ℕ))).to_comp
    have h3 := Computable₂.comp heq h1 h2
    exact h3.of_eq (fun z => rfl)
  have hEiff : ∀ p : ℚ × ℕ,
      (∃ k, (fun (p : ℚ × ℕ) (k : ℕ) => decide (e p.1 k = some p.2)) p k = true)
        ↔ p.2 ∈ W p.1 := by
    intro p
    rw [hW]
    simp
  refine not_isMartinLofRandomReal_of_stagePaint ha hmono hlim
    (v := enumStageVal (fun (p : ℚ × ℕ) (k : ℕ) => decide (e p.1 k = some p.2)) r)
    (computable_enumStageVal hE hr) (fun p => enumStageVal_nonneg hr0 p 0)
    (enumStageVal_mono hr0) (fun ε hε => ?_) (fun ε hε => ?_)
  · -- the total paint is the mass the hypothesis bounds
    have hlen := (hspec ε hε).1
    have hkey : (∑' i, ⨆ s, ENNReal.ofReal
        ((enumStageVal (fun (p : ℚ × ℕ) (k : ℕ) => decide (e p.1 k = some p.2)) r
          (ε, i) s : ℚ) : ℝ))
        = ∑' i : (W ε : Set ℕ), ENNReal.ofReal ((r (i : ℕ) : ℚ) : ℝ) := by
      rw [tsum_subtype (W ε) (fun i => ENNReal.ofReal ((r i : ℚ) : ℝ))]
      refine tsum_congr (fun i => ?_)
      rw [Set.indicator_apply]
      by_cases hi : i ∈ W ε
      · rw [if_pos hi]
        exact iSup_ofReal_enumStageVal_of_fires hr0 (ε, i) ((hEiff (ε, i)).2 hi)
      · rw [if_neg hi]
        exact iSup_ofReal_enumStageVal_of_never (ε, i)
          (fun k hk => hi ((hEiff (ε, i)).1 ⟨k, hk⟩))
    rw [hkey]
    exact hlen.le
  · -- from the last index outside `W ε` on, the paint is the whole tail of the series
    obtain ⟨hlen, hfin⟩ := hspec ε hε
    obtain ⟨N, hN⟩ : ∃ N, ∀ i, N ≤ i → i ∈ W ε := by
      obtain ⟨B, hB⟩ := hfin.bddAbove
      refine ⟨B + 1, fun i hi => ?_⟩
      by_contra hc
      have hiB : i ≤ B := hB (show i ∈ {i : ℕ | i ∉ W ε} from hc)
      omega
    refine ⟨N, ?_⟩
    have hterm : ∀ i, (if N ≤ i then ⨆ s, ENNReal.ofReal
        ((enumStageVal (fun (p : ℚ × ℕ) (k : ℕ) => decide (e p.1 k = some p.2)) r
          (ε, i) s : ℚ) : ℝ) else 0)
        = (if N ≤ i then ENNReal.ofReal ((r i : ℚ) : ℝ) else 0) := by
      intro i
      by_cases hi : N ≤ i
      · rw [if_pos hi, if_pos hi]
        exact iSup_ofReal_enumStageVal_of_fires hr0 (ε, i) ((hEiff (ε, i)).2 (hN i hi))
      · rw [if_neg hi, if_neg hi]
    rw [tsum_congr hterm]
    have hshift : (∑' i : ℕ, (if N ≤ i then ENNReal.ofReal ((r i : ℚ) : ℝ) else 0))
        = ∑' m, ENNReal.ofReal ((r (m + N) : ℚ) : ℝ) := by
      refine tsum_shift_nat N (fun i hi => if_neg (by omega)) (fun m => ?_)
      rw [if_pos (Nat.le_add_left N m)]
    rw [hshift]
    have hS2 : Summable (fun m => ((r (m + N) : ℚ) : ℝ)) := (summable_nat_add_iff N).2 hS
    have hnn : ∀ m : ℕ, (0 : ℝ) ≤ ((r (m + N) : ℚ) : ℝ) := fun m => by exact_mod_cast hr0 _
    have htail : ∑' m, ((r (m + N) : ℚ) : ℝ) = α - ((ratRangeSum r N : ℚ) : ℝ) := by
      have hsplit := hS.sum_add_tsum_nat_add N
      rw [hSval] at hsplit
      rw [hcast N]
      linarith
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hS2, htail]

/-- The sum `α` of a computable series `∑ rᵢ` of nonnegative rationals fails to be random if
and only if, for every rational `ε > 0`, one can effectively produce a co-finite enumerable
set `W` of indices whose `r`-mass is below `ε`.  SUV Theorem 109 (Section 5.7, p. 164). -/
theorem not_isMartinLofRandomReal_iff_exists_smallMassREFamily
    {r : ℕ → ℚ} {α : ℝ} (hr : Computable r) (hr0 : ∀ i, 0 ≤ r i)
    (hsum : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (r i : ℝ)) Filter.atTop (nhds α)) :
    ¬ IsMartinLofRandomReal α ↔
      ∃ W : ℚ → Set ℕ, IsUniformlyREFamily W ∧ ∀ ε : ℚ, 0 < ε →
        (∑' i : (W ε : Set ℕ), ENNReal.ofReal ((r (i : ℕ) : ℝ))) < ENNReal.ofReal (ε : ℝ) ∧
        {i : ℕ | i ∉ W ε}.Finite :=
  ⟨exists_smallMassREFamily_of_not_isMartinLofRandomReal hr hr0 hsum,
    not_isMartinLofRandomReal_of_exists_smallMassREFamily hr hr0 hsum⟩

/-! ### Theorem 107, placed after Theorem 109

The statement below is placed here, rather than between Theorems 106 and 108,
because its proof consumes Theorem 109 in both directions (`IsUniformlyREFamily` and the
two halves of Theorem 109 are declared above).  Nothing between Theorems 106 and 109 uses
it. -/

/-- A lower semicomputable real is a rational plus the sum of a computable series of
nonnegative rationals: take the increments of a monotone computable approximation. -/
theorem exists_series_of_isLowerSemicomputableReal {α : ℝ} (h : IsLowerSemicomputableReal α) :
    ∃ (q : ℚ) (r : ℕ → ℚ), Computable r ∧ (∀ i, 0 ≤ r i) ∧
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, ((r i : ℚ) : ℝ)) Filter.atTop
        (nhds (α - (q : ℝ))) := by
  obtain ⟨a, ha, hmono, hlim⟩ := h
  refine ⟨a 0, fun i => a (i + 1) - a i, ?_, ?_, ?_⟩
  · exact Computable₂.comp computable₂_ratSub (ha.comp Primrec.succ.to_comp) ha
  · intro i
    simp only [sub_nonneg]
    exact hmono (Nat.le_succ i)
  · refine Filter.Tendsto.congr (fun n => ?_) (hlim.sub_const ((a 0 : ℚ) : ℝ))
    rw [← Finset.sum_range_sub (fun i => ((a i : ℚ) : ℝ)) n]
    exact Finset.sum_congr rfl (fun i _ => by push_cast; ring)

/-- A sum over a subset of `ℕ` is at most the sum over a superset. -/
theorem tsum_subtype_mono {S T : Set ℕ} (hST : S ⊆ T) (f : ℕ → ℝ≥0∞) :
    (∑' i : S, f (i : ℕ)) ≤ ∑' i : T, f (i : ℕ) := by
  rw [tsum_subtype S f, tsum_subtype T f]
  refine ENNReal.tsum_le_tsum (fun i => ?_)
  by_cases hi : i ∈ S
  · rw [Set.indicator_of_mem hi, Set.indicator_of_mem (hST hi)]
  · rw [Set.indicator_of_notMem hi]
    exact zero_le _

/-- The intersection of two uniformly enumerable families, taken at half the budget, is
again a uniformly enumerable family: dovetail the two enumerators through `Nat.unpair` and
keep an index only when both enumerators produce it. -/
theorem isUniformlyREFamily_inter_half {W₁ W₂ : ℚ → Set ℕ} (h₁ : IsUniformlyREFamily W₁)
    (h₂ : IsUniformlyREFamily W₂) :
    IsUniformlyREFamily (fun ε => W₁ (ε / 2) ∩ W₂ (ε / 2)) := by
  classical
  obtain ⟨e₁, he₁, hW₁⟩ := h₁
  obtain ⟨e₂, he₂, hW₂⟩ := h₂
  refine ⟨fun ε k => cond (decide (e₁ (ε / 2) k.unpair.1 = e₂ (ε / 2) k.unpair.2))
    (e₁ (ε / 2) k.unpair.1) none, ?_, ?_⟩
  · have hhalf : Computable (fun p : ℚ × ℕ => p.1 / 2) :=
      (computable_ratDivConst (c := 2) (by norm_num)).comp Computable.fst
    have hu1 : Computable (fun p : ℚ × ℕ => p.2.unpair.1) :=
      (Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd
    have hu2 : Computable (fun p : ℚ × ℕ => p.2.unpair.2) :=
      (Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.snd
    have hx : Computable (fun p : ℚ × ℕ => e₁ (p.1 / 2) p.2.unpair.1) := he₁.comp hhalf hu1
    have hy : Computable (fun p : ℚ × ℕ => e₂ (p.1 / 2) p.2.unpair.2) := he₂.comp hhalf hu2
    have heq : Computable₂ (fun x y : Option ℕ => decide (x = y)) :=
      (PrimrecRel.decide (Primrec.eq (α := Option ℕ))).to_comp
    have hb := Computable₂.comp heq hx hy
    have hres := Computable.cond hb hx
      (Computable.const (none : Option ℕ) : Computable (fun _ : ℚ × ℕ => (none : Option ℕ)))
    exact hres.of_eq (fun p => rfl)
  · intro ε n
    constructor
    · rintro ⟨hn1, hn2⟩
      obtain ⟨k₁, hk₁⟩ := (hW₁ (ε / 2) n).1 hn1
      obtain ⟨k₂, hk₂⟩ := (hW₂ (ε / 2) n).1 hn2
      refine ⟨Nat.pair k₁ k₂, ?_⟩
      simp [Nat.unpair_pair, hk₁, hk₂]
    · rintro ⟨k, hk⟩
      cases hd : decide (e₁ (ε / 2) k.unpair.1 = e₂ (ε / 2) k.unpair.2) with
      | false =>
          simp only [hd, cond_false] at hk
          exact absurd hk (by simp)
      | true =>
          simp only [hd, cond_true] at hk
          have hk1 : e₁ (ε / 2) k.unpair.1 = some n := hk
          have hd' : e₁ (ε / 2) k.unpair.1 = e₂ (ε / 2) k.unpair.2 := of_decide_eq_true hd
          exact ⟨(hW₁ (ε / 2) n).2 ⟨k.unpair.1, hk1⟩,
            (hW₂ (ε / 2) n).2 ⟨k.unpair.2, hd' ▸ hk1⟩⟩

/-! ### Theorem 107 -/

/-- If `α` and `β` are non-random lower semicomputable reals, their sum `α + β` is non-random
too.  SUV Theorem 107 (Section 5.7, pp. 162–163). -/
theorem not_isMartinLofRandomReal_add {α β : ℝ}
    (hα : IsLowerSemicomputableReal α) (hβ : IsLowerSemicomputableReal β)
    (hα' : ¬ IsMartinLofRandomReal α) (hβ' : ¬ IsMartinLofRandomReal β) :
    ¬ IsMartinLofRandomReal (α + β) := by
  classical
  obtain ⟨qa, r, hr, hr0, hrlim⟩ := exists_series_of_isLowerSemicomputableReal hα
  obtain ⟨qb, r', hr', hr'0, hr'lim⟩ := exists_series_of_isLowerSemicomputableReal hβ
  -- the two shifted reals are non-random
  have hAα : ¬ IsMartinLofRandomReal (α - (qa : ℝ)) := by
    intro hcon
    exact hα' (by simpa using (isMartinLofRandomReal_add_rat (α - (qa : ℝ)) qa).2 hcon)
  have hAβ : ¬ IsMartinLofRandomReal (β - (qb : ℝ)) := by
    intro hcon
    exact hβ' (by simpa using (isMartinLofRandomReal_add_rat (β - (qb : ℝ)) qb).2 hcon)
  obtain ⟨W₁, hW₁re, hW₁⟩ :=
    exists_smallMassREFamily_of_not_isMartinLofRandomReal hr hr0 hrlim hAα
  obtain ⟨W₂, hW₂re, hW₂⟩ :=
    exists_smallMassREFamily_of_not_isMartinLofRandomReal hr' hr'0 hr'lim hAβ
  -- the merged series and the intersected index sets
  have ht : Computable (fun i => r i + r' i) := Computable₂.comp computable₂_ratAdd hr hr'
  have ht0 : ∀ i, 0 ≤ r i + r' i := fun i => add_nonneg (hr0 i) (hr'0 i)
  have htlim : Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n, ((r i + r' i : ℚ) : ℝ)) Filter.atTop
      (nhds ((α - (qa : ℝ)) + (β - (qb : ℝ)))) := by
    refine Filter.Tendsto.congr (fun n => ?_) (hrlim.add hr'lim)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by push_cast; ring)
  have hmerge : ¬ IsMartinLofRandomReal ((α - (qa : ℝ)) + (β - (qb : ℝ))) := by
    refine not_isMartinLofRandomReal_of_exists_smallMassREFamily ht ht0 htlim
      ⟨fun ε => W₁ (ε / 2) ∩ W₂ (ε / 2), ?_, fun ε hε => ?_⟩
    · exact isUniformlyREFamily_inter_half hW₁re hW₂re
    · have hε2 : (0 : ℚ) < ε / 2 := by linarith
      obtain ⟨hlen₁, hfin₁⟩ := hW₁ (ε / 2) hε2
      obtain ⟨hlen₂, hfin₂⟩ := hW₂ (ε / 2) hε2
      constructor
      · have hsplit : (∑' i : ((W₁ (ε / 2) ∩ W₂ (ε / 2) : Set ℕ) : Set ℕ),
            ENNReal.ofReal (((r (i : ℕ) + r' (i : ℕ) : ℚ)) : ℝ))
            = (∑' i : ((W₁ (ε / 2) ∩ W₂ (ε / 2) : Set ℕ) : Set ℕ),
                ENNReal.ofReal ((r (i : ℕ) : ℚ) : ℝ))
              + ∑' i : ((W₁ (ε / 2) ∩ W₂ (ε / 2) : Set ℕ) : Set ℕ),
                ENNReal.ofReal ((r' (i : ℕ) : ℚ) : ℝ) := by
          rw [← ENNReal.tsum_add]
          refine tsum_congr (fun i => ?_)
          rw [← ENNReal.ofReal_add (by exact_mod_cast hr0 _) (by exact_mod_cast hr'0 _)]
          congr 1
          push_cast
          ring
        rw [hsplit]
        have hsub1 : W₁ (ε / 2) ∩ W₂ (ε / 2) ⊆ W₁ (ε / 2) := Set.inter_subset_left
        have hsub2 : W₁ (ε / 2) ∩ W₂ (ε / 2) ⊆ W₂ (ε / 2) := Set.inter_subset_right
        have hs1 := tsum_subtype_mono hsub1 (fun i => ENNReal.ofReal ((r i : ℚ) : ℝ))
        have hs2 := tsum_subtype_mono hsub2 (fun i => ENNReal.ofReal ((r' i : ℚ) : ℝ))
        have hsum : ENNReal.ofReal (((ε / 2 : ℚ)) : ℝ) + ENNReal.ofReal (((ε / 2 : ℚ)) : ℝ)
            = ENNReal.ofReal ((ε : ℚ) : ℝ) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          push_cast
          ring
        calc _ ≤ (∑' i : ((W₁ (ε / 2) : Set ℕ) : Set ℕ),
                    ENNReal.ofReal ((r (i : ℕ) : ℚ) : ℝ))
                  + ∑' i : ((W₂ (ε / 2) : Set ℕ) : Set ℕ),
                    ENNReal.ofReal ((r' (i : ℕ) : ℚ) : ℝ) := add_le_add hs1 hs2
          _ < ENNReal.ofReal (((ε / 2 : ℚ)) : ℝ) + ENNReal.ofReal (((ε / 2 : ℚ)) : ℝ) :=
              ENNReal.add_lt_add hlen₁ hlen₂
          _ = ENNReal.ofReal ((ε : ℚ) : ℝ) := hsum
      · have hsub : {i : ℕ | i ∉ W₁ (ε / 2) ∩ W₂ (ε / 2)}
            ⊆ {i : ℕ | i ∉ W₁ (ε / 2)} ∪ {i : ℕ | i ∉ W₂ (ε / 2)} := by
          intro i hi
          by_cases h1 : i ∈ W₁ (ε / 2)
          · exact Or.inr (fun h2 => hi ⟨h1, h2⟩)
          · exact Or.inl h1
        exact Set.Finite.subset (hfin₁.union hfin₂) hsub
  intro hcon
  refine hmerge ?_
  have hrewrite : α + β = ((α - (qa : ℝ)) + (β - (qb : ℝ))) + ((qa + qb : ℚ) : ℝ) := by
    push_cast
    ring
  rw [hrewrite] at hcon
  exact (isMartinLofRandomReal_add_rat _ (qa + qb)).1 hcon

end Kolmogorov
