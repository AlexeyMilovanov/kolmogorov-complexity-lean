



/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.Solovay
import KolmogorovMathlib.MonotoneComplexity.Omega.PredictCover
import KolmogorovMathlib.MonotoneComplexity.Omega.PaintEnum
import KolmogorovMathlib.MonotoneComplexity.Omega.DisjointCover
import KolmogorovMathlib.MonotoneComplexity.Omega.MultiCover

/-!
# SUV Section 5.7.3: randomness and the prediction game (milestone C11)

This module states the prediction game of SUV Section 5.7.3 (pp. 161–164) and the
randomness criteria that come with it:

* the game itself (`PredictionStrategy`, `ObserverWins`, p. 161);
* **Theorem 104** (p. 161): the observer has a computable winning strategy iff the
  limit is not random;
* **Theorem 105** (p. 162): the game-free reformulation with a computable sequence
  `hᵢ` of nonnegative rationals;
* **Theorem 106** (p. 162): the Borel–Cantelli ("infinitely many `i`") version;
* **Theorem 107** (pp. 162–163): the sum of two non-random lower semicomputable
  reals is non-random;
* **Theorem 108** (p. 163): the two weakenings — lower semicomputable `hᵢ` and the
  tail `hᵢ + hᵢ₊₁ + ⋯`;
* **Theorem 109** (p. 164): the criterion in terms of an enumerable co-finite set of
  indices of a computable series.

## Definitional choices frozen here

* The budget `ε` is "given to the observer in advance" (p. 161), so a strategy is a
  function of `ε` *and* of the observed history, and "computable winning strategy"
  means one `Computable₂` object working for every rational `ε > 0`. This is also
  what makes Theorem 105's "one can effectively find" the same statement.
* Predictions are `Option ℚ`-valued: the observer may stay silent at a step. The
  book's normalisation ("every prediction can be safely postponed, so we may assume
  that the next prediction is made only if the previous one becomes invalid") is a
  remark about strategies, not part of the winning condition, so it is not built
  into `ObserverWins`.
* Sums of nonnegative rationals are taken in `ℝ≥0∞`, so no summability side
  condition is smuggled into a statement.
-/

namespace Kolmogorov


open ComputableReals
open MeasureTheory ENNReal

/-! ### The prediction game (SUV p. 161) -/

/-- **SUV Section 5.7.3 (p. 161).** A strategy for the observer: given the budget
`ε` announced in advance and the history `[a₀, …, aᵢ]` observed so far, it either
announces a prediction `some δ` — "the sequence will never increase by more than
`δ`", compared to its current value — or stays silent. -/
abbrev PredictionStrategy := ℚ → List ℚ → Option ℚ

/-- The prediction (if any) announced by `σ` at step `i` of the play against `a`. -/
def predictionAt (σ : PredictionStrategy) (ε : ℚ) (a : ℕ → ℚ) (i : ℕ) : Option ℚ :=
  σ ε ((List.range (i + 1)).map a)

/-- **SUV p. 161, winning condition (2).** The sum of all numbers `δ` used in the
predictions. -/
noncomputable def predictionCost (σ : PredictionStrategy) (ε : ℚ) (a : ℕ → ℚ) : ℝ≥0∞ :=
  ∑' i, (predictionAt σ ε a i).elim 0 (fun δ => ENNReal.ofReal (δ : ℝ))

/-- **SUV p. 161, winning condition (1).** The prediction `δ` made at step `i`
remains true forever: the sequence never increases by more than `δ` above `aᵢ`. -/
def PredictionHolds (a : ℕ → ℚ) (i : ℕ) (δ : ℚ) : Prop := ∀ j, a j ≤ a i + δ

/-- **SUV Section 5.7.3 (p. 161).** The observer wins the game against the increasing
sequence `a` with budget `ε`: all announced `δ` are nonnegative rationals, one of
the predictions remains true forever, and the sum of all `δ` is less than `ε`. -/
def ObserverWins (σ : PredictionStrategy) (ε : ℚ) (a : ℕ → ℚ) : Prop :=
  (∀ i δ, predictionAt σ ε a i = some δ → 0 ≤ δ) ∧
  (∃ i δ, predictionAt σ ε a i = some δ ∧ PredictionHolds a i δ) ∧
  predictionCost σ ε a < ENNReal.ofReal (ε : ℝ)

/-- **SUV Section 5.7.3 (p. 161).** The observer has a computable winning strategy
against `a`: one algorithm that wins for every rational budget `ε > 0` given to it
in advance. -/
def HasComputableWinningStrategy (a : ℕ → ℚ) : Prop :=
  ∃ σ : PredictionStrategy, Computable₂ σ ∧ ∀ ε : ℚ, 0 < ε → ObserverWins σ ε a

/-! ### Theorem 104 -/

/-- A computable winning strategy gives a computable sequence of prediction intervals of small
total measure one of which contains `α`, so `α` is not random.  SUV Theorem 104 (Section
5.7, p. 161), forward direction. -/
theorem not_isMartinLofRandomReal_of_hasComputableWinningStrategy
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : StrictMono a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    (h : HasComputableWinningStrategy a) : ¬ IsMartinLofRandomReal α := by
  obtain ⟨σ, hσ, hwin⟩ := h
  have hlt : ∀ i, ((a i : ℚ) : ℝ) < α := by
    intro i
    have h1 : ((a i : ℚ) : ℝ) < ((a (i + 1) : ℚ) : ℝ) := by
      exact_mod_cast hmono (Nat.lt_succ_self i)
    have h2 : ((a (i + 1) : ℚ) : ℝ) ≤ α :=
      rat_le_of_monotone_tendsto hmono.monotone hlim (i + 1)
    linarith
  have hpa : ∀ (ε : ℚ) (i : ℕ), predictionAt σ ε a i = σ ε (listPrefix a i) := by
    intro ε i
    rw [predictionAt, listPrefix_eq]
  set H : ℚ → ℕ → ℚ := fun ε i => (predictionAt σ ε a i).getD 0 with hH
  have hHc : Computable₂ H := by
    have h1 : Computable (fun p : ℚ × ℕ => σ p.1 (listPrefix a p.2)) :=
      Computable₂.comp hσ Computable.fst ((computable_listPrefix ha).comp Computable.snd)
    have h2 : Computable (fun p : ℚ × ℕ => (σ p.1 (listPrefix a p.2)).getD 0) :=
      Computable.option_getD h1 (Computable.const 0)
    refine h2.of_eq (fun p => ?_)
    simp only [hH, hpa]
  refine not_isMartinLofRandomReal_of_covering ha hlt hHc ?_ ?_ ?_
  · intro ε hε i
    rcases hp : predictionAt σ ε a i with _ | δ
    · simp [hH, hp]
    · have hδ := (hwin ε hε).1 i δ hp
      simpa [hH, hp] using hδ
  · intro ε hε
    have hcost : (∑' i, ENNReal.ofReal ((H ε i : ℚ) : ℝ)) = predictionCost σ ε a := by
      rw [predictionCost]
      refine tsum_congr (fun i => ?_)
      rcases hp : predictionAt σ ε a i with _ | δ
      · simp [hH, hp]
      · simp [hH, hp]
    rw [hcost]
    exact (hwin ε hε).2.2
  · intro ε hε
    obtain ⟨i, δ, hp, hhold⟩ := (hwin ε hε).2.1
    refine ⟨i, ?_⟩
    have hHval : H ε i = δ := by simp [hH, hp]
    rw [hHval]
    refine le_of_tendsto' hlim (fun j => ?_)
    have hj : ((a j : ℚ) : ℝ) ≤ ((a i + δ : ℚ) : ℝ) := by exact_mod_cast hhold j
    push_cast at hj
    exact hj

/-! ### Theorem 105 -/

/-- The source's "increasing sequence" (p. 161) is used only through `aᵢ ≤ α`, so `StrictMono a`
can be weakened to `Monotone a` — which is what the downstream users need, since the partial
sums of a series with zero terms are only non-decreasing.  The strict form below is
derived from this one.  SUV Theorem 105 (Section 5.7, p. 162), forward direction,
monotone form. -/
theorem exists_uniform_slack_family_of_not_isMartinLofRandomReal_of_monotone
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : Monotone a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    (h : ¬ IsMartinLofRandomReal α) :
    ∃ H : ℚ → ℕ → ℚ, Computable₂ H ∧ ∀ ε : ℚ, 0 < ε →
      (∀ i, 0 ≤ H ε i) ∧
      (∑' i, ENNReal.ofReal ((H ε i : ℝ))) < ENNReal.ofReal (ε : ℝ) ∧
      ∃ i, α ≤ (a i : ℝ) + (H ε i : ℝ) := by
  rw [IsMartinLofRandomReal] at h
  push_neg at h
  obtain ⟨X, hX, hαX⟩ := h
  obtain ⟨cover, hcov, hspec⟩ := hX
  have hle : ∀ i, ((a i : ℚ) : ℝ) ≤ α := rat_le_of_monotone_tendsto hmono hlim
  refine ⟨fun ε i => coverH cover a (ε / 2) i, ?_, ?_⟩
  · have hhalf : Computable (fun ε : ℚ => ε / 2) :=
      computable_ratDivConst (c := 2) (by norm_num)
    exact (computable_coverH cover a hcov ha).comp (hhalf.comp Computable.fst) Computable.snd
  · intro ε hε
    have hε2 : (0 : ℚ) < ε / 2 := by positivity
    obtain ⟨hsub, hlen⟩ := hspec (ε / 2) hε2
    refine ⟨fun i => coverH_nonneg cover a _ i, ?_, ?_⟩
    · have hεR : (0 : ℝ) < ((ε : ℚ) : ℝ) := by exact_mod_cast hε
      calc (∑' i, ENNReal.ofReal ((coverH cover a (ε / 2) i : ℚ) : ℝ))
          ≤ ∑' k, (cover (ε / 2) k).elim 0 ratIntervalLength :=
            tsum_ofReal_coverH_le cover a _
        _ ≤ ENNReal.ofReal (((ε / 2 : ℚ)) : ℝ) := hlen
        _ < ENNReal.ofReal ((ε : ℚ) : ℝ) := by
              rw [ENNReal.ofReal_lt_ofReal_iff hεR]
              push_cast
              linarith
    · exact exists_le_add_coverH cover a _ hmono hle hlim (hsub hαX)


/-- If `α` is not random then for every rational `ε > 0` one can effectively find a computable
sequence `h₀, h₁, …` of nonnegative rationals with `∑ hᵢ < ε` and `α ≤ aᵢ + hᵢ` for some
`i`. Effectivity in `ε` is expressed by one `Computable₂` family.  SUV Theorem 105 (Section
5.7, p. 162), forward direction. -/
theorem exists_uniform_slack_family_of_not_isMartinLofRandomReal
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : StrictMono a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    (h : ¬ IsMartinLofRandomReal α) :
    ∃ H : ℚ → ℕ → ℚ, Computable₂ H ∧ ∀ ε : ℚ, 0 < ε →
      (∀ i, 0 ≤ H ε i) ∧
      (∑' i, ENNReal.ofReal ((H ε i : ℝ))) < ENNReal.ofReal (ε : ℝ) ∧
      ∃ i, α ≤ (a i : ℝ) + (H ε i : ℝ) :=
  exists_uniform_slack_family_of_not_isMartinLofRandomReal_of_monotone ha hmono.monotone hlim h

/- The two declarations below are unchanged; they follow Theorem 105's forward
direction because their proof consumes it (SUV p. 162: the game "corresponds to the
game where predictions `hᵢ` are made on every step"). -/

/-- As for Theorem 105, `StrictMono a` is only used through `aᵢ ≤ α`; this monotone form is what
downstream users need, and the strict form is derived from it.  SUV
Theorem 104 (Section 5.7, p. 161), reverse direction, monotone form. -/
theorem hasComputableWinningStrategy_of_not_isMartinLofRandomReal_of_monotone
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : Monotone a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    (h : ¬ IsMartinLofRandomReal α) : HasComputableWinningStrategy a := by
  obtain ⟨H, hH, hspec⟩ :=
    exists_uniform_slack_family_of_not_isMartinLofRandomReal_of_monotone ha hmono hlim h
  have hle : ∀ i, ((a i : ℚ) : ℝ) ≤ α := rat_le_of_monotone_tendsto hmono hlim
  refine ⟨fun ε L => some (H ε (L.length - 1)), ?_, ?_⟩
  · have hlen : Computable (fun p : ℚ × List ℚ => p.2.length - 1) :=
      Primrec.nat_sub.to_comp.comp
        (Primrec.list_length.to_comp.comp Computable.snd) (Computable.const 1)
    exact Computable.option_some.comp (Computable₂.comp hH Computable.fst hlen)
  · intro ε hε
    obtain ⟨hnn, hsum, i, hi⟩ := hspec ε hε
    have hpa : ∀ j : ℕ,
        predictionAt (fun ε L => some (H ε (L.length - 1))) ε a j = some (H ε j) := by
      intro j
      simp [predictionAt]
    refine ⟨fun j δ hj => ?_, ⟨i, H ε i, hpa i, fun j => ?_⟩, ?_⟩
    · rw [hpa j] at hj
      rw [← Option.some.inj hj]
      exact hnn j
    · have hj1 : ((a j : ℚ) : ℝ) ≤ α := hle j
      have hj2 : ((a j : ℚ) : ℝ) ≤ ((a i + H ε i : ℚ) : ℝ) := by push_cast; linarith
      exact_mod_cast hj2
    · rw [predictionCost, tsum_congr (fun j => by rw [hpa j])]
      exact hsum


/-- From a sequence of intervals covering `α` with small total measure the observer builds a
computable winning strategy: wait until the current approximation enters a covering interval
and predict that it never leaves it.  SUV Theorem 104 (Section 5.7, p. 161), reverse
direction. -/
theorem hasComputableWinningStrategy_of_not_isMartinLofRandomReal
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : StrictMono a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    (h : ¬ IsMartinLofRandomReal α) : HasComputableWinningStrategy a :=
  hasComputableWinningStrategy_of_not_isMartinLofRandomReal_of_monotone
    ha hmono.monotone hlim h

/-- For a computable increasing sequence of rationals converging to `α`, the observer has a
computable winning strategy in the prediction game if and only if `α` is not random.  SUV
Theorem 104 (Section 5.7, p. 161). -/
theorem hasComputableWinningStrategy_iff_not_isMartinLofRandomReal
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : StrictMono a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α)) :
    HasComputableWinningStrategy a ↔ ¬ IsMartinLofRandomReal α :=
  ⟨not_isMartinLofRandomReal_of_hasComputableWinningStrategy ha hmono hlim,
    hasComputableWinningStrategy_of_not_isMartinLofRandomReal ha hmono hlim⟩

/-- If, for every rational `ε > 0`, one can effectively find a computable sequence `hᵢ ≥ 0`
of rationals with `∑ hᵢ < ε` and `α ≤ aᵢ + hᵢ` for some `i`, then `α` is not random.  SUV
Theorem 105 (Section 5.7, p. 162), reverse direction. -/
theorem not_isMartinLofRandomReal_of_exists_uniform_slack_family
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : StrictMono a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    (h : ∃ H : ℚ → ℕ → ℚ, Computable₂ H ∧ ∀ ε : ℚ, 0 < ε →
      (∀ i, 0 ≤ H ε i) ∧
      (∑' i, ENNReal.ofReal ((H ε i : ℝ))) < ENNReal.ofReal (ε : ℝ) ∧
      ∃ i, α ≤ (a i : ℝ) + (H ε i : ℝ)) :
    ¬ IsMartinLofRandomReal α := by
  obtain ⟨H, hH, hspec⟩ := h
  have hlt : ∀ i, ((a i : ℚ) : ℝ) < α := by
    intro i
    have h1 : ((a i : ℚ) : ℝ) < ((a (i + 1) : ℚ) : ℝ) := by
      exact_mod_cast hmono (Nat.lt_succ_self i)
    have h2 : ((a (i + 1) : ℚ) : ℝ) ≤ α :=
      rat_le_of_monotone_tendsto hmono.monotone hlim (i + 1)
    linarith
  exact not_isMartinLofRandomReal_of_covering ha hlt hH
    (fun ε hε i => (hspec ε hε).1 i) (fun ε hε => (hspec ε hε).2.1)
    (fun ε hε => (hspec ε hε).2.2)

/-! ### Theorem 106 -/

/-- The monotone hypothesis suffices; the strict form is derived from it.  SUV
Theorem 106 (Section 5.7, p. 162), forward direction, monotone form. -/
theorem exists_summable_slack_of_not_isMartinLofRandomReal_of_monotone
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : Monotone a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    (h : ¬ IsMartinLofRandomReal α) :
    ∃ H : ℕ → ℚ, Computable H ∧ (∀ i, 0 ≤ H i) ∧
      (∑' i, ENNReal.ofReal ((H i : ℝ))) ≠ ⊤ ∧
      {i : ℕ | α ≤ (a i : ℝ) + (H i : ℝ)}.Infinite := by
  obtain ⟨H, hH, hspec⟩ :=
    exists_uniform_slack_family_of_not_isMartinLofRandomReal_of_monotone ha hmono hlim h
  set b : ℕ → ℚ := fun n => ratPad 1 n with hbdef
  have hbpos : ∀ n, 0 < b n := fun n => ratPad_pos (by norm_num) n
  have hbc : Computable b := computable₂_ratPad.comp (Computable.const 1) Computable.id
  have hnn : ∀ (n i : ℕ), 0 ≤ H (b n) i := fun n i => (hspec (b n) (hbpos n)).1 i
  set G : ℕ → ℚ := fun i => ∑ n ∈ Finset.range (i + 1), H (b n) (i - n) with hGdef
  have hu : Computable₂ (fun (i : ℕ) (n : ℕ) => H (b n) (i - n)) :=
    Computable₂.comp hH (hbc.comp Computable.snd)
      (Primrec.nat_sub.to_comp.comp Computable.fst Computable.snd)
  refine ⟨G, ?_, fun i => Finset.sum_nonneg (fun n _ => hnn n (i - n)), ?_, ?_⟩
  · have hd : Computable (fun i : ℕ => (i, i + 1)) :=
      Computable.pair Computable.id Primrec.succ.to_comp
    refine ((computable_ratRangeSumP hu).comp hd).of_eq (fun i => ?_)
    rw [ratRangeSumP_eq]
  · -- the total mass is at most the total budget `∑ₙ b n = 1/2`
    set T : ℕ → ℕ → ℝ≥0∞ := fun n i =>
      if n < i + 1 then ENNReal.ofReal ((H (b n) (i - n) : ℚ) : ℝ) else 0 with hTdef
    have hrow : ∀ i, ENNReal.ofReal ((G i : ℚ) : ℝ) = ∑' n, T n i := by
      intro i
      have hzero : ∀ n, n ∉ Finset.range (i + 1) → T n i = 0 := by
        intro n hn
        have hn' : i < n := by simpa using Finset.mem_range.not.mp hn
        simp only [hTdef]
        rw [if_neg (by omega)]
      have hTval : ∀ n ∈ Finset.range (i + 1),
          T n i = ENNReal.ofReal ((H (b n) (i - n) : ℚ) : ℝ) := by
        intro n hn
        simp only [hTdef]
        rw [if_pos (Finset.mem_range.mp hn)]
      have hnonneg : ∀ n ∈ Finset.range (i + 1), (0 : ℝ) ≤ ((H (b n) (i - n) : ℚ) : ℝ) :=
        fun n _ => by exact_mod_cast hnn n (i - n)
      have hcast : (((G i : ℚ)) : ℝ)
          = ∑ n ∈ Finset.range (i + 1), ((H (b n) (i - n) : ℚ) : ℝ) := by
        simp only [hGdef]
        push_cast
        ring
      rw [tsum_eq_sum hzero, Finset.sum_congr rfl hTval, hcast,
        ENNReal.ofReal_sum_of_nonneg hnonneg]
    have hcol : ∀ n, (∑' i, T n i) ≤ ENNReal.ofReal ((b n : ℚ) : ℝ) := by
      intro n
      have hshift : (∑' i, T n i) = ∑' m, ENNReal.ofReal ((H (b n) m : ℚ) : ℝ) := by
        refine tsum_shift_nat n (fun i hi => ?_) (fun m => ?_)
        · simp only [hTdef]
          rw [if_neg (by omega)]
        · simp only [hTdef]
          rw [if_pos (by omega), Nat.add_sub_cancel]
      rw [hshift]
      exact le_of_lt (hspec (b n) (hbpos n)).2.1
    have hbound : (∑' i, ENNReal.ofReal ((G i : ℚ) : ℝ))
        ≤ ENNReal.ofReal (((1 : ℚ) : ℝ) / 2) := by
      rw [tsum_congr hrow, ENNReal.tsum_comm, ← tsum_ofReal_ratPad (by norm_num : (0 : ℚ) < 1)]
      exact ENNReal.tsum_le_tsum hcol
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  · intro hfin
    obtain ⟨B, hB⟩ := hfin.bddAbove
    obtain ⟨i0, hi0⟩ := (hspec (b (B + 1)) (hbpos _)).2.2
    have hmem : i0 + (B + 1) ∈ {i : ℕ | α ≤ ((a i : ℚ) : ℝ) + ((G i : ℚ) : ℝ)} := by
      have hterm : H (b (B + 1)) i0
          ≤ ∑ n ∈ Finset.range (i0 + (B + 1) + 1), H (b n) (i0 + (B + 1) - n) := by
        have hb1 : B + 1 ∈ Finset.range (i0 + (B + 1) + 1) :=
          Finset.mem_range.mpr (by omega)
        have hsub : i0 + (B + 1) - (B + 1) = i0 := by omega
        calc H (b (B + 1)) i0 = H (b (B + 1)) (i0 + (B + 1) - (B + 1)) := by rw [hsub]
          _ ≤ _ := Finset.single_le_sum
              (f := fun n => H (b n) (i0 + (B + 1) - n))
              (fun n _ => hnn n (i0 + (B + 1) - n)) hb1
      have h1 : ((H (b (B + 1)) i0 : ℚ) : ℝ) ≤ ((G (i0 + (B + 1)) : ℚ) : ℝ) := by
        rw [hGdef]; exact_mod_cast hterm
      have h2 : ((a i0 : ℚ) : ℝ) ≤ ((a (i0 + (B + 1)) : ℚ) : ℝ) := by
        exact_mod_cast hmono (by omega : i0 ≤ i0 + (B + 1))
      have h3 : α ≤ ((a i0 : ℚ) : ℝ) + ((H (b (B + 1)) i0 : ℚ) : ℝ) := hi0
      change α ≤ ((a (i0 + (B + 1)) : ℚ) : ℝ) + ((G (i0 + (B + 1)) : ℚ) : ℝ)
      linarith
    have := hB hmem
    omega


/-- The Solovay (Borel–Cantelli) form: if `α` is not random then there is one computable
sequence `hᵢ ≥ 0` of rationals with `∑ hᵢ < ∞` and `α ≤ aᵢ + hᵢ` for infinitely many `i`.
SUV Theorem 106 (Section 5.7, p. 162), forward direction. -/
theorem exists_summable_slack_of_not_isMartinLofRandomReal
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : StrictMono a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    (h : ¬ IsMartinLofRandomReal α) :
    ∃ H : ℕ → ℚ, Computable H ∧ (∀ i, 0 ≤ H i) ∧
      (∑' i, ENNReal.ofReal ((H i : ℝ))) ≠ ⊤ ∧
      {i : ℕ | α ≤ (a i : ℝ) + (H i : ℝ)}.Infinite :=
  exists_summable_slack_of_not_isMartinLofRandomReal_of_monotone ha hmono.monotone hlim h

/-- Bounds the multiplicity integer factor for rational budget `ε`. -/
private lemma rat_multiplicity_bound (C : ℚ) (hC : 0 < C) {ε : ℚ} (hε : 0 < ε) :
    (2 * C : ℚ) ≤ ((2 * C * (ε.den : ℚ)).num.toNat + 1 : ℕ) * ε := by
  set q : ℚ := 2 * C * (ε.den : ℚ) with hq
  have hqpos : 0 < q := by
    have : (0 : ℚ) < (ε.den : ℚ) := by exact_mod_cast ε.pos
    positivity
  have hqd : (0 : ℚ) < ((q.den : ℕ) : ℚ) := by exact_mod_cast q.pos
  have hnum : q ≤ ((q.num.toNat : ℕ) : ℚ) := by
    have h1 : (0 : ℤ) < q.num := Rat.num_pos.2 hqpos
    have h2 : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg h1.le
    have h3 : ((q.num.toNat : ℕ) : ℚ) = ((q.num : ℤ) : ℚ) := by exact_mod_cast h2
    rw [h3]
    have h4 : ((q.num : ℤ) : ℚ) = q * ((q.den : ℕ) : ℚ) :=
      (div_eq_iff (ne_of_gt hqd)).1 (Rat.num_div_den q)
    have h5 : (1 : ℚ) ≤ ((q.den : ℕ) : ℚ) := by exact_mod_cast q.pos
    nlinarith [hqpos.le]
  have hd : (0 : ℚ) < ((ε.den : ℕ) : ℚ) := by exact_mod_cast ε.pos
  have hden : (1 : ℚ) / ((ε.den : ℕ) : ℚ) ≤ ε := by
    have h1 : (1 : ℤ) ≤ ε.num := Rat.num_pos.2 hε
    have h2 : (1 : ℚ) ≤ ((ε.num : ℤ) : ℚ) := by exact_mod_cast h1
    have h3 : ((ε.num : ℤ) : ℚ) = ε * ((ε.den : ℕ) : ℚ) :=
      (div_eq_iff (ne_of_gt hd)).1 (Rat.num_div_den ε)
    rw [div_le_iff₀ hd]
    linarith
  have hkey : q ≤ ((q.num.toNat + 1 : ℕ) : ℚ) := by
    push_cast
    linarith
  calc (2 * C : ℚ) = q / ((ε.den : ℕ) : ℚ) := by rw [hq]; field_simp
    _ = q * (1 / ((ε.den : ℕ) : ℚ)) := by ring
    _ ≤ ((q.num.toNat + 1 : ℕ) : ℚ) * ε :=
        mul_le_mul hkey hden (by positivity) (by push_cast; linarith)

/-- Computability of right endpoints in `not_isMartinLofRandomReal_of_exists_summable_slack`. -/
private lemma computable_summable_slack_right_endpoint
    {a : ℕ → ℚ} {H : ℕ → ℚ} (ha : Computable a) (hH : Computable H) (C : ℚ) :
    Computable (fun p : ℚ × ℕ =>
      min (a p.2 + (H p.2 + ratPad 1 p.2))
        (topRat (fun i => a i + (H i + ratPad 1 i)) (a 0)
          ((2 * C * ((p.1).den : ℚ)).num.toNat + 1) p.2)) := by
  have hpadc : Computable (fun i : ℕ => ratPad 1 i) :=
    computable₂_ratPad.comp (Computable.const 1) Computable.id
  have hGc : Computable (fun i => H i + ratPad 1 i) :=
    Computable₂.comp computable₂_ratAdd hH hpadc
  have hbc : Computable (fun i => a i + (H i + ratPad 1 i)) :=
    Computable₂.comp computable₂_ratAdd ha hGc
  have hm : Computable (fun p : ℚ × ℕ => (2 * C * ((p.1).den : ℚ)).num.toNat + 1) := by
    have h1 : Computable (fun p : ℚ × ℕ => ((p.1).den : ℕ)) :=
      computable_ratDen.comp Computable.fst
    have h2 : Computable (fun p : ℚ × ℕ => (((p.1).den : ℕ) : ℚ)) :=
      computable_nat_to_rat.comp h1
    have h3 : Computable (fun p : ℚ × ℕ => 2 * C * (((p.1).den : ℕ) : ℚ)) :=
      Computable₂.comp computable₂_ratMul (Computable.const (2 * C)) h2
    have h4 : Computable (fun p : ℚ × ℕ => (2 * C * (((p.1).den : ℕ) : ℚ)).num) :=
      computable_ratNum.comp h3
    exact Primrec.succ.to_comp.comp (ComputableReals.primrec_intToNat.to_comp.comp h4)
  have htop := computable_topRat hbc (a 0)
  have h5 := htop.comp hm (Computable.snd : Computable (fun p : ℚ × ℕ => p.2))
  have h6 := hbc.comp (Computable.snd : Computable (fun p : ℚ × ℕ => p.2))
  exact Computable₂.comp computable₂_ratMin h6 h5

/-- If there is one computable sequence `hᵢ ≥ 0` of rationals with `∑ hᵢ < ∞` and
`α ≤ aᵢ + hᵢ` for infinitely many `i`, then `α` is not random.  SUV Theorem 106
(Section 5.7, p. 162), reverse direction. -/
theorem not_isMartinLofRandomReal_of_exists_summable_slack
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : StrictMono a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    (h : ∃ H : ℕ → ℚ, Computable H ∧ (∀ i, 0 ≤ H i) ∧
      (∑' i, ENNReal.ofReal ((H i : ℝ))) ≠ ⊤ ∧
      {i : ℕ | α ≤ (a i : ℝ) + (H i : ℝ)}.Infinite) :
    ¬ IsMartinLofRandomReal α := by
  classical
  obtain ⟨H, hH, hH0, hHfin, hinf⟩ := h
  -- the padded intervals `(aᵢ, aᵢ + Hᵢ + 2^{-(i+2)})`
  have hG0 : ∀ i, 0 < H i + ratPad 1 i := fun i =>
    lt_of_lt_of_le (ratPad_pos one_pos i) (by linarith [hH0 i])
  have hGmass : (∑' i, ENNReal.ofReal (((H i + ratPad 1 i : ℚ)) : ℝ))
      = (∑' i, ENNReal.ofReal ((H i : ℝ))) + ENNReal.ofReal (((1 : ℚ) : ℝ) / 2) := by
    rw [← tsum_ofReal_ratPad (ε := (1 : ℚ)) one_pos, ← ENNReal.tsum_add]
    refine tsum_congr (fun i => ?_)
    rw [← ENNReal.ofReal_add (by exact_mod_cast hH0 i)
      (by exact_mod_cast (ratPad_pos one_pos i).le)]
    congr 1
    push_cast
    ring
  have hmassne : (∑' i, ENNReal.ofReal (((H i + ratPad 1 i : ℚ)) : ℝ)) ≠ ⊤ := by
    rw [hGmass]
    exact ENNReal.add_ne_top.2 ⟨hHfin, ENNReal.ofReal_ne_top⟩
  -- a rational bound on the total mass
  obtain ⟨C, hC0, hCmass⟩ : ∃ C : ℚ, 0 < C ∧
      (∑' i, ENNReal.ofReal (((H i + ratPad 1 i : ℚ)) : ℝ)) < ENNReal.ofReal ((C : ℚ) : ℝ) := by
    obtain ⟨C, hC1, hC2⟩ := exists_rat_btwn (lt_add_one
      (max ((∑' i, ENNReal.ofReal (((H i + ratPad 1 i : ℚ)) : ℝ)).toReal) 0))
    refine ⟨C, ?_, ?_⟩
    · exact_mod_cast lt_of_le_of_lt (le_max_right _ 0) hC1
    · rw [← ENNReal.ofReal_toReal hmassne]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2
        (lt_of_le_of_lt (le_max_left _ _) hC1)
  -- the multiplicity used for the budget `ε`
  have hmpos : ∀ ε : ℚ, 0 < ε → (2 * C : ℚ) ≤ ((2 * C * (ε.den : ℚ)).num.toNat + 1 : ℕ) * ε :=
    fun ε hε => rat_multiplicity_bound C hC0 hε
  refine not_isMartinLofRandomReal_of_monotoneLeftCover
    (l := fun _ j => a j)
    (r := fun ε j => min (a j + (H j + ratPad 1 j))
      (topRat (fun i => a i + (H i + ratPad 1 i)) (a 0) ((2 * C * (ε.den : ℚ)).num.toNat + 1) j))
    (ha.comp Computable.snd) (computable_summable_slack_right_endpoint ha hH C)
    (fun ε j => (hmono (Nat.lt_succ_self j)).le) ?_ ?_
  · -- the measure of the multiply covered set
    intro ε hε
    set m : ℕ := (2 * C * (ε.den : ℚ)).num.toNat + 1 with hm
    set b : ℕ → ℚ := fun i => a i + (H i + ratPad 1 i) with hb
    set A : Set ℝ := ⋃ j, Set.Ioo ((a j : ℝ)) (((min (b j) (topRat b (a 0) m j) : ℚ)) : ℝ)
      with hA
    have hAmeas : MeasurableSet A := MeasurableSet.iUnion (fun j => measurableSet_Ioo)
    have hJmeas : ∀ i, MeasurableSet (Set.Ioo ((a i : ℝ)) ((b i : ℚ) : ℝ)) :=
      fun i => measurableSet_Ioo
    have hmult : ∀ x ∈ A, ∃ F : Finset ℕ, m + 1 ≤ F.card ∧
        ∀ i ∈ F, x ∈ Set.Ioo ((a i : ℝ)) ((b i : ℚ) : ℝ) := by
      intro x hx
      rw [hA, Set.mem_iUnion] at hx
      obtain ⟨j, hj⟩ := hx
      have hcast : (((min (b j) (topRat b (a 0) m j) : ℚ)) : ℝ)
          = min ((b j : ℚ) : ℝ) ((topRat b (a 0) m j : ℚ) : ℝ) := by push_cast; ring
      rw [hcast] at hj
      have haj : ((a j : ℚ) : ℝ) < x := hj.1
      have hbj : x < ((b j : ℚ) : ℝ) := lt_of_lt_of_le hj.2 (min_le_left _ _)
      have htj : x < ((topRat b (a 0) m j : ℚ) : ℝ) := lt_of_lt_of_le hj.2 (min_le_right _ _)
      have ha0 : ((a 0 : ℚ) : ℝ) ≤ x := by
        have : ((a 0 : ℚ) : ℝ) ≤ ((a j : ℚ) : ℝ) := by
          exact_mod_cast hmono.monotone (Nat.zero_le j)
        linarith
      obtain ⟨F₀, hF₀card, hF₀⟩ := exists_finset_of_lt_topRat ha0 htj
      refine ⟨insert j F₀, ?_, ?_⟩
      · have hjnot : j ∉ F₀ := fun hc => absurd (hF₀ j hc).1 (lt_irrefl j)
        rw [Finset.card_insert_of_notMem hjnot]
        omega
      · intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi'
        · exact ⟨haj, hbj⟩
        · have hij := hF₀ i hi'
          have hai : ((a i : ℚ) : ℝ) ≤ ((a j : ℚ) : ℝ) := by
            exact_mod_cast hmono.monotone hij.1.le
          exact ⟨lt_of_le_of_lt hai haj, hij.2⟩
    have hmarkov := measure_le_of_multiplicity hJmeas hAmeas hmult
    have hJvol : ∀ i, volume (Set.Ioo ((a i : ℝ)) ((b i : ℚ) : ℝ))
        = ENNReal.ofReal (((H i + ratPad 1 i : ℚ)) : ℝ) := by
      intro i
      rw [Real.volume_Ioo]
      congr 1
      rw [hb]
      push_cast
      ring
    rw [tsum_congr hJvol] at hmarkov
    have hCbound : ((m : ℝ≥0∞) + 1) * volume A ≤ ENNReal.ofReal ((C : ℚ) : ℝ) := by
      refine le_trans (le_of_eq ?_) (le_trans hmarkov hCmass.le)
      congr 1
      push_cast
      ring
    -- `m · ε / 2 ≥ C`, so the multiply covered set is small
    have hεR : (0 : ℝ) < ((ε : ℚ) : ℝ) := by exact_mod_cast hε
    have hCle : ENNReal.ofReal ((C : ℚ) : ℝ)
        ≤ ((m : ℝ≥0∞) + 1) * ENNReal.ofReal (((ε / 2 : ℚ)) : ℝ) := by
      have h1 := hmpos ε hε
      have h1R : ((2 * C : ℚ) : ℝ) ≤ ((m : ℕ) : ℝ) * ((ε : ℚ) : ℝ) := by
        rw [hm]; exact_mod_cast h1
      have h2 : ((C : ℚ) : ℝ) ≤ (((m : ℕ) : ℝ) + 1) * (((ε / 2 : ℚ)) : ℝ) := by
        push_cast at h1R ⊢
        nlinarith [hεR]
      calc ENNReal.ofReal ((C : ℚ) : ℝ)
          ≤ ENNReal.ofReal ((((m : ℕ) : ℝ) + 1) * (((ε / 2 : ℚ)) : ℝ)) :=
            ENNReal.ofReal_le_ofReal h2
        _ = ((m : ℝ≥0∞) + 1) * ENNReal.ofReal (((ε / 2 : ℚ)) : ℝ) := by
            rw [ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [ENNReal.ofReal_add (by positivity) (by norm_num)]
            simp [ENNReal.ofReal_natCast]
    have hcancel : ((m : ℝ≥0∞) + 1) ≠ 0 := by
      refine fun hc => ?_
      have : (1 : ℝ≥0∞) ≤ (m : ℝ≥0∞) + 1 := le_add_self
      rw [hc] at this
      exact absurd this (by simp)
    have htop' : ((m : ℝ≥0∞) + 1) ≠ ⊤ := by
      exact ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top m, ENNReal.one_ne_top⟩
    exact (ENNReal.mul_le_mul_iff_right hcancel htop').1 (le_trans hCbound hCle)
  · -- the cover catches `α`
    intro ε hε
    set m : ℕ := (2 * C * (ε.den : ℚ)).num.toNat + 1 with hm
    set b : ℕ → ℚ := fun i => a i + (H i + ratPad 1 i) with hb
    obtain ⟨F₀, hF₀sub, hF₀card⟩ := Set.Infinite.exists_subset_card_eq hinf m
    obtain ⟨j, hjS, hjgt0⟩ := Set.Infinite.exists_gt hinf (F₀.sup id)
    have hjgt : ∀ i ∈ F₀, i < j := by
      intro i hi
      have h1 : i ≤ F₀.sup id := Finset.le_sup (f := id) hi
      omega
    have hlt : ∀ i, α ≤ ((a i : ℚ) : ℝ) + ((H i : ℚ) : ℝ) → α < ((b i : ℚ) : ℝ) := by
      intro i hi
      have hp : (0 : ℝ) < ((ratPad 1 i : ℚ) : ℝ) := by exact_mod_cast ratPad_pos one_pos i
      rw [hb]
      push_cast
      linarith
    refine ⟨j, ?_⟩
    have hcast : (((min (b j) (topRat b (a 0) m j) : ℚ)) : ℝ)
        = min ((b j : ℚ) : ℝ) ((topRat b (a 0) m j : ℚ) : ℝ) := by push_cast; ring
    rw [hcast]
    refine Set.mem_Ioo.mpr ⟨rat_lt_of_strictMono_tendsto hmono hlim j, lt_min ?_ ?_⟩
    · exact hlt j hjS
    · refine lt_topRat (F := F₀) ?_ (le_of_eq hF₀card.symm) (fun i hi => ⟨hjgt i hi, ?_⟩)
      · rw [← Finset.card_pos, hF₀card, hm]
        omega
      · exact hlt i (hF₀sub hi)

/-- **SUV p. 162, the observation after Theorem 106.** The randomness of the sum of
a computable series of positive rationals cannot change if all summands are changed
by an `O(1)`-factor.

The comparison is the genuine two-sided `O(1)`-factor of the source remark: a single
constant `C > 0` with `C⁻¹ rᵢ ≤ r'ᵢ ≤ C rᵢ` for all `i`.  The one-sided form
`c rᵢ ≤ r'ᵢ ≤ c⁻¹ rᵢ` with an unconstrained `c > 0` is vacuous for `c > 1`, so it
does not express the remark. -/
theorem isMartinLofRandomReal_sum_invariant_of_const_mul
    {r r' : ℕ → ℚ} {α α' : ℝ}
    (hr : Computable r) (hr' : Computable r') (hpos : ∀ i, 0 < r i)
    (hcmp : ∃ C : ℚ, 0 < C ∧ ∀ i, C⁻¹ * r i ≤ r' i ∧ r' i ≤ C * r i)
    (hα : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (r i : ℝ)) Filter.atTop (nhds α))
    (hα' : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (r' i : ℝ)) Filter.atTop (nhds α')) :
    IsMartinLofRandomReal α ↔ IsMartinLofRandomReal α' := by
  obtain ⟨C, hC, hcmp'⟩ := hcmp
  have hCinv : (0 : ℚ) < C⁻¹ := inv_pos.2 hC
  have hr'pos : ∀ i, 0 < r' i := by
    intro i
    exact lt_of_lt_of_le (mul_pos hCinv (hpos i)) (hcmp' i).1
  have hbound : ∀ i, r i ≤ C * r' i := by
    intro i
    have h1 := (hcmp' i).1
    have h2 : C * (C⁻¹ * r i) ≤ C * r' i := by
      exact mul_le_mul_of_nonneg_left h1 hC.le
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC), one_mul] at h2
    exact h2
  -- lower semicomputability of the two sums and of their rational multiples
  have hlscα : IsLowerSemicomputableReal α :=
    isLowerSemicomputableReal_of_series hr (fun i => (hpos i).le) hα
  have hlscα' : IsLowerSemicomputableReal α' :=
    isLowerSemicomputableReal_of_series hr' (fun i => (hr'pos i).le) hα'
  -- the two scaled series
  have hscale : ∀ {s : ℕ → ℚ} {x : ℝ},
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, ((s i : ℚ) : ℝ)) Filter.atTop (nhds x) →
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (((C * s i : ℚ)) : ℝ))
        Filter.atTop (nhds ((C : ℝ) * x)) := by
    intro s x hs
    have hcast : (fun n : ℕ => ∑ i ∈ Finset.range n, (((C * s i : ℚ)) : ℝ))
        = fun n : ℕ => (C : ℝ) * ∑ i ∈ Finset.range n, ((s i : ℚ) : ℝ) := by
      funext n
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by push_cast; ring)
    rw [hcast]
    exact hs.const_mul (C : ℝ)
  have hmulc : Computable (fun i => C * r i) :=
    Computable₂.comp computable₂_ratMul (Computable.const C) hr
  have hmulc' : Computable (fun i => C * r' i) :=
    Computable₂.comp computable₂_ratMul (Computable.const C) hr'
  have hdom1 : SolovayDominates α' ((C : ℝ) * α) :=
    solovayDominates_of_series_le hr' hmulc (fun i _ => (hr'pos i).le)
      (fun i _ => (mul_pos hC (hpos i)).le) (fun i _ => (hcmp' i).2) hα' (hscale hα)
  have hdom2 : SolovayDominates α ((C : ℝ) * α') :=
    solovayDominates_of_series_le hr hmulc' (fun i _ => (hpos i).le)
      (fun i _ => (mul_pos hC (hr'pos i)).le) (fun i _ => hbound i) hα (hscale hα')
  constructor
  · intro hrand
    have h1 : IsMartinLofRandomReal ((C : ℝ) * α') :=
      isMartinLofRandomReal_of_solovayDominates hlscα (hlscα'.rat_mul hC.le) hdom2 hrand
    exact (isMartinLofRandomReal_rat_mul hC α').1 h1
  · intro hrand
    have h1 : IsMartinLofRandomReal ((C : ℝ) * α) :=
      isMartinLofRandomReal_of_solovayDominates hlscα' (hlscα.rat_mul hC.le) hdom1 hrand
    exact (isMartinLofRandomReal_rat_mul hC α).1 h1

/-! ### Theorem 108 -/

/-- Uniform lower semicomputability of a family `h : ℚ → ℕ → ℝ≥0∞` of nonnegative
reals: a computable monotone dyadic approximation from below, uniform in the
rational parameter and the index. This renders "for every rational `ε > 0` one can
effectively find a lower semicomputable sequence `hᵢ`" (SUV p. 163). -/
def IsLSCFamily (h : ℚ → ℕ → ℝ≥0∞) : Prop :=
  ∃ approx : ℕ → ℚ → ℕ → ℕ,
    (∀ s ε i, dyadicValue (approx s ε i) s ≤ dyadicValue (approx (s + 1) ε i) (s + 1)) ∧
    (∀ ε i, ⨆ s, dyadicValue (approx s ε i) s = h ε i) ∧
    Computable (fun p : ℕ × ℚ × ℕ => approx p.1 p.2.1 p.2.2)

/-- The monotone hypothesis suffices; the strict form is derived from it.  This
is the "painters" argument of the source, run by `Omega/Painter.lean`: portion `i` of paint
starts at `aᵢ` or at the right end of the already painted region, whichever is further
right, so the emitted intervals are disjoint and the total length is `∑ hᵢ` by construction.
`Omega/PaintLsc.lean` supplies the increments that make the *lower semicomputable* `hᵢ`
usable, and `Omega/PaintCover.lean` the fact that the index `i` of the hypothesis need not
be computable from `ε`.  SUV Theorem 108 (Section 5.7, p. 163), monotone form. -/
theorem not_isMartinLofRandomReal_of_lscTailCover_of_monotone
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : Monotone a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    {h : ℚ → ℕ → ℝ≥0∞} (hlsc : IsLSCFamily h)
    (hsmall : ∀ ε : ℚ, 0 < ε → (∑' i, h ε i) < ENNReal.ofReal (ε : ℝ))
    (hcover : ∀ ε : ℚ, 0 < ε → ∃ i, α ≤ (a i : ℝ) + (∑' k, h ε (i + k)).toReal) :
    ¬ IsMartinLofRandomReal α := by
  classical
  obtain ⟨approx, hstep, hsup, happrox⟩ := hlsc
  refine not_isMartinLofRandomReal_of_lscPaint ha hmono hlim hstep hsup happrox
    (fun ε hε => (hsmall ε hε).le) (fun ε hε => ?_)
  obtain ⟨i₀, hi₀⟩ := hcover ε hε
  refine ⟨i₀, ?_⟩
  have hshift : (∑' i : ℕ, (if i₀ ≤ i then h ε i else 0)) = ∑' k, h ε (i₀ + k) := by
    refine tsum_shift_nat i₀ (fun i hi => if_neg (by omega)) (fun m => ?_)
    rw [if_pos (Nat.le_add_left i₀ m), Nat.add_comm]
  rw [hshift]
  have hle : (∑' k, h ε (i₀ + k)) ≤ ∑' i, h ε i := by
    rw [← hshift]
    refine ENNReal.tsum_le_tsum (fun i => ?_)
    by_cases hc : i₀ ≤ i
    · rw [if_pos hc]
    · rw [if_neg hc]
      exact zero_le _
  have hne : (∑' k, h ε (i₀ + k)) ≠ ⊤ := (lt_of_le_of_lt hle (hsmall ε hε)).ne_top
  have hlt : α - ((a i₀ : ℚ) : ℝ) ≤ (∑' k, h ε (i₀ + k)).toReal := by linarith [hi₀]
  calc ENNReal.ofReal (α - ((a i₀ : ℚ) : ℝ))
      ≤ ENNReal.ofReal ((∑' k, h ε (i₀ + k)).toReal) := ENNReal.ofReal_le_ofReal hlt
    _ = ∑' k, h ε (i₀ + k) := ENNReal.ofReal_toReal hne

/-- Let `aᵢ` be an increasing computable sequence of rationals converging to `α`. Assume that
for every rational `ε > 0` one can effectively find a lower semicomputable sequence `hᵢ` of
nonnegative reals such that `∑ hᵢ < ε` and `α ≤ aᵢ + hᵢ + hᵢ₊₁ + ⋯` for some `i`. Then `α`
is not random. The condition is stated with the *tail* of the series, which is the point of
the theorem (the "painters" argument of the source proof).  SUV Theorem 108 (Section 5.7, p.
163). -/
theorem not_isMartinLofRandomReal_of_lscTailCover
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : StrictMono a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    {h : ℚ → ℕ → ℝ≥0∞} (hlsc : IsLSCFamily h)
    (hsmall : ∀ ε : ℚ, 0 < ε → (∑' i, h ε i) < ENNReal.ofReal (ε : ℝ))
    (hcover : ∀ ε : ℚ, 0 < ε → ∃ i, α ≤ (a i : ℝ) + (∑' k, h ε (i + k)).toReal) :
    ¬ IsMartinLofRandomReal α :=
  not_isMartinLofRandomReal_of_lscTailCover_of_monotone ha hmono.monotone hlim hlsc hsmall hcover

/-! ### Theorem 109 -/

/-- A uniformly enumerable family of sets of indices: one computable enumerator
producing, for every rational parameter `ε`, the members of `W ε`. -/
def IsUniformlyREFamily (W : ℚ → Set ℕ) : Prop :=
  ∃ e : ℚ → ℕ → Option ℕ, Computable₂ e ∧ ∀ ε n, n ∈ W ε ↔ ∃ k, e ε k = some n

/-- The indices whose series block `[s i, s (i+1)]` is swallowed by a single interval of the
cover for the halved budget `ε / 2`. -/
def coveredBlocks (cover : ℚ → ℕ → Option (ℚ × ℚ)) (s : ℕ → ℚ) (ε : ℚ) : Set ℕ :=
  {i | ∃ k, coverInside cover (ε / 2, k) (s i) (s (i + 1)) = true}

/-- The covered blocks of a computable partial-sum sequence against a computable cover form a
uniformly enumerable family: the enumerator unpairs its input into a block index and a cover
index and reports the block when the containment test fires. -/
lemma isUniformlyREFamily_coveredBlocks {cover : ℚ → ℕ → Option (ℚ × ℚ)}
    (hcov : Computable₂ cover) {s : ℕ → ℚ} (hs : Computable s) :
    IsUniformlyREFamily (coveredBlocks cover s) := by
  refine ⟨fun ε n =>
    cond (coverInside cover (ε / 2, (Nat.unpair n).2) (s (Nat.unpair n).1)
      (s ((Nat.unpair n).1 + 1))) (some (Nat.unpair n).1) none, ?_, ?_⟩
  · have hhalf : Computable (fun p : ℚ × ℕ => p.1 / 2) :=
      (computable_ratDivConst (c := 2) (by norm_num)).comp Computable.fst
    have hi : Computable (fun p : ℚ × ℕ => (Nat.unpair p.2).1) :=
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have hk : Computable (fun p : ℚ × ℕ => (Nat.unpair p.2).2) :=
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have hin : Computable (fun p : ℚ × ℕ =>
        coverInside cover (p.1 / 2, (Nat.unpair p.2).2) (s (Nat.unpair p.2).1)
          (s ((Nat.unpair p.2).1 + 1))) :=
      computable_coverInside_comp cover hcov (Computable.pair hhalf hk)
        (hs.comp hi) (hs.comp (Primrec.succ.to_comp.comp hi))
    exact Computable.cond hin (Computable.option_some.comp hi) (Computable.const none)
  · intro ε n
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨Nat.pair n k, ?_⟩
      simp only [Nat.unpair_pair, hk, cond_true]
    · rintro ⟨m, hm⟩
      have hm' : (cond (coverInside cover (ε / 2, (Nat.unpair m).2) (s (Nat.unpair m).1)
          (s ((Nat.unpair m).1 + 1))) (some (Nat.unpair m).1) none : Option ℕ) = some n := hm
      rcases hb : coverInside cover (ε / 2, (Nat.unpair m).2) (s (Nat.unpair m).1)
          (s ((Nat.unpair m).1 + 1)) with _ | _
      · rw [hb, cond_false] at hm'
        exact absurd hm' (by simp)
      · rw [hb, cond_true] at hm'
        have hn : (Nat.unpair m).1 = n := Option.some.inj hm'
        exact ⟨(Nat.unpair m).2, hn ▸ hb⟩

/-- The mass the series puts on its covered blocks is below the budget: the blocks are pairwise
disjoint intervals of length `r i` sitting inside the cover, so their total volume is at most
the total length `ε / 2` of the cover. -/
lemma tsum_coveredBlocks_lt {r s : ℕ → ℚ} {cover : ℚ → ℕ → Option (ℚ × ℚ)} {ε : ℚ}
    (hε : 0 < ε) (hsucc : ∀ n, s (n + 1) = s n + r n) (hsmono : Monotone s)
    (hlen : ∑' k, (cover (ε / 2) k).elim 0 ratIntervalLength ≤
      ENNReal.ofReal (((ε / 2 : ℚ)) : ℝ)) :
    (∑' i : (coveredBlocks cover s ε : Set ℕ), ENNReal.ofReal ((r (i : ℕ) : ℝ))) <
      ENNReal.ofReal ((ε : ℚ) : ℝ) := by
  classical
  set A : ℕ → Set ℝ := fun i =>
    if i ∈ coveredBlocks cover s ε then
      Set.Ioo ((s i : ℚ) : ℝ) ((s (i + 1) : ℚ) : ℝ)
    else ∅ with hAdef
  have hAsub : ∀ i, A i ⊆ Set.Ioo ((s i : ℚ) : ℝ) ((s (i + 1) : ℚ) : ℝ) := by
    intro i
    simp only [hAdef]
    split_ifs
    · exact Set.Subset.rfl
    · exact Set.empty_subset _
  have hAmeas : ∀ i, MeasurableSet (A i) := by
    intro i
    simp only [hAdef]
    split_ifs
    · exact measurableSet_Ioo
    · exact MeasurableSet.empty
  have hAvol : ∀ i, MeasureTheory.volume (A i)
      = if i ∈ coveredBlocks cover s ε then ENNReal.ofReal ((r i : ℚ) : ℝ) else 0 := by
    intro i
    simp only [hAdef]
    split_ifs with hi
    · rw [Real.volume_Ioo]
      congr 1
      rw [hsucc i]
      push_cast
      ring
    · exact MeasureTheory.measure_empty
  have hAdisj : Pairwise (Function.onFun Disjoint A) := by
    have key : ∀ i j : ℕ, i < j → Disjoint (A i) (A j) := by
      intro i j hij
      refine Set.disjoint_of_subset (hAsub i) (hAsub j) ?_
      rw [Set.disjoint_left]
      intro x hx hx'
      have h1 : x < ((s (i + 1) : ℚ) : ℝ) := hx.2
      have h2 : ((s j : ℚ) : ℝ) < x := hx'.1
      have h3 : ((s (i + 1) : ℚ) : ℝ) ≤ ((s j : ℚ) : ℝ) := by
        exact_mod_cast hsmono (by omega : i + 1 ≤ j)
      linarith
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact key i j hlt
    · exact (key j i hgt).symm
  have hAcov : (⋃ i, A i) ⊆ ⋃ k, (cover (ε / 2) k).elim ∅ ratInterval := by
    refine Set.iUnion_subset (fun i => ?_)
    simp only [hAdef]
    split_ifs with hi
    · obtain ⟨k, hk⟩ := hi
      obtain ⟨h1, h2⟩ := coverInside_spec cover hk
      have hne : (covPair cover (ε / 2, k)).1 < (covPair cover (ε / 2, k)).2 :=
        lt_of_lt_of_le h1 (le_trans (hsmono (Nat.le_succ i)) h2.le)
      have hsome : cover (ε / 2) k = some (covPair cover (ε / 2, k)) :=
        cover_eq_some_of_lt cover hne
      refine Set.subset_iUnion_of_subset k ?_
      rw [hsome]
      rintro x ⟨hx1, hx2⟩
      refine ⟨?_, ?_⟩
      · have : (((covPair cover (ε / 2, k)).1 : ℚ) : ℝ) < ((s i : ℚ) : ℝ) := by
          exact_mod_cast h1
        linarith
      · have : (((s (i + 1) : ℚ)) : ℝ) < (((covPair cover (ε / 2, k)).2 : ℚ) : ℝ) := by
          exact_mod_cast h2
        linarith
    · exact Set.empty_subset _
  have hcovvol : ∀ k, MeasureTheory.volume ((cover (ε / 2) k).elim ∅ ratInterval)
      = (cover (ε / 2) k).elim 0 ratIntervalLength := by
    intro k
    rcases Option.eq_none_or_eq_some (cover (ε / 2) k) with hn | ⟨I, hI⟩
    · rw [hn]
      exact MeasureTheory.measure_empty
    · rw [hI]
      exact Real.volume_Ioo
  have hstep : (∑' i : (coveredBlocks cover s ε : Set ℕ), ENNReal.ofReal ((r (i : ℕ) : ℝ)))
      = ∑' i, MeasureTheory.volume (A i) := by
    rw [tsum_subtype (coveredBlocks cover s ε) (fun j : ℕ => ENNReal.ofReal ((r j : ℚ) : ℝ))]
    refine tsum_congr (fun i => ?_)
    rw [hAvol i, Set.indicator_apply]
  have hεR : (0 : ℝ) < ((ε : ℚ) : ℝ) := by exact_mod_cast hε
  calc (∑' i : (coveredBlocks cover s ε : Set ℕ), ENNReal.ofReal ((r (i : ℕ) : ℝ)))
      = ∑' i, MeasureTheory.volume (A i) := hstep
    _ = MeasureTheory.volume (⋃ i, A i) := (MeasureTheory.measure_iUnion hAdisj hAmeas).symm
    _ ≤ MeasureTheory.volume (⋃ k, (cover (ε / 2) k).elim ∅ ratInterval) :=
        MeasureTheory.measure_mono hAcov
    _ ≤ ∑' k, MeasureTheory.volume ((cover (ε / 2) k).elim ∅ ratInterval) :=
        MeasureTheory.measure_iUnion_le _
    _ = ∑' k, (cover (ε / 2) k).elim 0 ratIntervalLength := tsum_congr hcovvol
    _ ≤ ENNReal.ofReal (((ε / 2 : ℚ)) : ℝ) := hlen
    _ < ENNReal.ofReal ((ε : ℚ) : ℝ) := by
        rw [ENNReal.ofReal_lt_ofReal_iff hεR]
        push_cast
        linarith

/-- Only finitely many blocks escape the cover: the limit `α` lies in some interval of the
cover, and from the first partial sum inside that interval on, every block is swallowed by
it. -/
lemma finite_not_mem_coveredBlocks {s : ℕ → ℚ} {cover : ℚ → ℕ → Option (ℚ × ℚ)} {ε : ℚ}
    {α : ℝ} (hsmono : Monotone s)
    (hslim : Filter.Tendsto (fun n => ((s n : ℚ) : ℝ)) Filter.atTop (nhds α))
    (hsle : ∀ n, ((s n : ℚ) : ℝ) ≤ α)
    (hαcov : α ∈ ⋃ k, (cover (ε / 2) k).elim ∅ ratInterval) :
    {i : ℕ | i ∉ coveredBlocks cover s ε}.Finite := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hαcov
  rcases Option.eq_none_or_eq_some (cover (ε / 2) k) with hn | ⟨I, hI⟩
  · rw [hn] at hk
    exact absurd hk (by simp)
  rw [hI] at hk
  have hkI : α ∈ Set.Ioo ((I.1 : ℚ) : ℝ) ((I.2 : ℚ) : ℝ) := hk
  have hIpair : covPair cover (ε / 2, k) = I := by simp [covPair, hI]
  have hexN : ∃ N, ((I.1 : ℚ) : ℝ) < ((s N : ℚ) : ℝ) := by
    by_contra hc
    push_neg at hc
    have hle : α ≤ ((I.1 : ℚ) : ℝ) := le_of_tendsto' hslim hc
    linarith [hkI.1]
  obtain ⟨N, hN⟩ := hexN
  refine Set.Finite.subset (Set.finite_lt_nat N) (fun i hi => ?_)
  rcases Nat.lt_or_ge i N with hlt | hge
  · exact hlt
  exfalso
  refine hi ⟨k, coverInside_of cover ?_ ?_⟩
  · rw [hIpair]
    have h1 : ((s N : ℚ) : ℝ) ≤ ((s i : ℚ) : ℝ) := by
      exact_mod_cast hsmono hge
    have h2 : ((I.1 : ℚ) : ℝ) < ((s i : ℚ) : ℝ) := by linarith
    exact_mod_cast h2
  · rw [hIpair]
    have h2 : ((s (i + 1) : ℚ) : ℝ) < ((I.2 : ℚ) : ℝ) :=
      lt_of_le_of_lt (hsle (i + 1)) hkI.2
    exact_mod_cast h2

/-- If the sum `α` of a computable series `∑ rᵢ` of nonnegative rationals is not random, then
for every `ε > 0` one can effectively produce an enumerable set `W ⊆ ℕ` of indices with
`∑_{i ∈ W} rᵢ < ε` and `W` co-finite.  SUV Theorem 109 (Section 5.7, p. 164), forward
direction. -/
theorem exists_smallMassREFamily_of_not_isMartinLofRandomReal
    {r : ℕ → ℚ} {α : ℝ} (hr : Computable r) (hr0 : ∀ i, 0 ≤ r i)
    (hsum : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (r i : ℝ)) Filter.atTop (nhds α))
    (h : ¬ IsMartinLofRandomReal α) :
    ∃ W : ℚ → Set ℕ, IsUniformlyREFamily W ∧ ∀ ε : ℚ, 0 < ε →
      (∑' i : (W ε : Set ℕ), ENNReal.ofReal ((r (i : ℕ) : ℝ))) < ENNReal.ofReal (ε : ℝ) ∧
      {i : ℕ | i ∉ W ε}.Finite := by
  classical
  rw [IsMartinLofRandomReal] at h
  push_neg at h
  obtain ⟨X, hX, hαX⟩ := h
  obtain ⟨cover, hcov, hspec⟩ := hX
  set s : ℕ → ℚ := ratRangeSum r with hsdef
  have hsucc : ∀ n, s (n + 1) = s n + r n := by
    intro n; simp only [hsdef, ratRangeSum]
  have hscast : ∀ n, ((s n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, ((r i : ℚ) : ℝ) := by
    intro n
    simp only [hsdef, ratRangeSum_eq]
    push_cast
    ring
  have hsmono : Monotone s :=
    monotone_nat_of_le_succ (fun n => by rw [hsucc n]; linarith [hr0 n])
  have hslim : Filter.Tendsto (fun n => ((s n : ℚ) : ℝ)) Filter.atTop (nhds α) := by
    have hfun : (fun n => ((s n : ℚ) : ℝ))
        = fun n => ∑ i ∈ Finset.range n, ((r i : ℚ) : ℝ) := funext hscast
    rw [hfun]; exact hsum
  have hsle : ∀ n, ((s n : ℚ) : ℝ) ≤ α := rat_le_of_monotone_tendsto hsmono hslim
  refine ⟨coveredBlocks cover s,
    isUniformlyREFamily_coveredBlocks hcov (computable_ratRangeSum hr), fun ε hε => ?_⟩
  have hε2 : (0 : ℚ) < ε / 2 := by positivity
  obtain ⟨hsub, hlen⟩ := hspec (ε / 2) hε2
  exact ⟨tsum_coveredBlocks_lt hε hsucc hsmono hlen,
    finite_not_mem_coveredBlocks hsmono hslim hsle (hsub hαX)⟩

end Kolmogorov
