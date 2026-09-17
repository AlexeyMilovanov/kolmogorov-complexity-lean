/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.PredictCover

/-!
# A lower semicomputable ML-random real (SUV p. 161, Problem 86)

SUV's §5.7.2 remarks that "one can prove the existence of a lower semicomputable random
real without references to `Ω` (Problem 86)".  This module does exactly that, using the
universal cover `covEnum` of `Omega/UniversalCover.lean`.

Let `U = ⋃ₙ ratInterval (covEnum 1 n)`, an effectively open set of total length at most
`1/2` that contains every effectively null set.  The **leftmost point of the complement**
of `U` in `[0, ∞)` is lower semicomputable: the "covered initial segment"

  `L 0 = 0`,  `L (n+1) = max (L n) (max_{k ≤ n} {rₖ : lₖ < L n})`

is a computable non-decreasing sequence of rationals, `[0, L n) ⊆ U` for every `n`, and
its supremum `x₀` is not in `U` — if it were, the interval containing it would be reached
by the recursion and would push `L` past `x₀`.  Since `U` contains every effectively null
set, `x₀` is ML-random; and `x₀ ≤ 1/2` because `[0, x₀) ⊆ U`.

Note that `x₀` is *not* rational, and that the recursion does start moving: every rational
lies in some effectively null set, hence in `U`, so in particular `0 ∈ U`.

Everything here is proved; the module renders no statement of the source.
-/

namespace Kolmogorov


open ComputableReals
open ENNReal MeasureTheory

/-! ### The endpoints of the universal cover at budget `1` -/

/-- The left endpoint of the `k`-th interval of the universal cover at budget `1`. -/
def covL (k : ℕ) : ℚ := (covPair covEnum (1, k)).1

/-- The right endpoint of the `k`-th interval of the universal cover at budget `1`. -/
def covR (k : ℕ) : ℚ := (covPair covEnum (1, k)).2

/-- The left endpoints of the universal cover at budget one are computable. -/
theorem computable_covL : Computable covL :=
  Computable.fst.comp ((computable_covPair covEnum computable₂_covEnum).comp
    (Computable.pair (Computable.const 1) Computable.id))

/-- The right endpoints of the universal cover at budget one are computable. -/
theorem computable_covR : Computable covR :=
  Computable.snd.comp ((computable_covPair covEnum computable₂_covEnum).comp
    (Computable.pair (Computable.const 1) Computable.id))

/-- A nondegenerate pair of endpoints comes from a present interval of the universal cover. -/
theorem covEnum_eq_some {k : ℕ} (h : covL k < covR k) :
    covEnum 1 k = some (covL k, covR k) := by
  have h2 : (covPair covEnum (1, k)).1 < (covPair covEnum (1, k)).2 := h
  have := cover_eq_some_of_lt covEnum h2
  simpa [covL, covR] using this

/-! ### The covered initial segment -/

/-- One extension round: the largest right endpoint among the first `m + 1` intervals
whose left endpoint already lies inside the covered segment `[0, x)`. -/
def extStep (x : ℚ) : ℕ → ℚ
  | 0 => cond (ratLtPair (covL 0, x)) (max x (covR 0)) x
  | m + 1 => cond (ratLtPair (covL (m + 1), x))
      (max (extStep x m) (covR (m + 1))) (extStep x m)

/-- The covered initial segment after `n` rounds. -/
def leftSeg : ℕ → ℚ
  | 0 => 0
  | n + 1 => extStep (leftSeg n) n

/-- An extension round never moves the covered segment to the left. -/
theorem le_extStep (x : ℚ) : ∀ m, x ≤ extStep x m := by
  intro m
  induction m with
  | zero =>
      rw [extStep]
      cases ratLtPair (covL 0, x) with
      | false => exact le_rfl
      | true => exact le_max_left _ _
  | succ m ih =>
      rw [extStep]
      cases ratLtPair (covL (m + 1), x) with
      | false => exact ih
      | true => exact le_trans ih (le_max_left _ _)

/-- The extension is either trivial or one of the right endpoints reached from `x`. -/
theorem extStep_cases (x : ℚ) : ∀ m,
    extStep x m = x ∨ ∃ k, k ≤ m ∧ covL k < x ∧ extStep x m = covR k := by
  intro m
  induction m with
  | zero =>
      rw [extStep]
      cases hb : ratLtPair (covL 0, x) with
      | false => exact Or.inl rfl
      | true =>
          have hlt : covL 0 < x := by
            rw [ratLtPair, decide_eq_true_eq] at hb; exact hb
          rcases max_cases x (covR 0) with ⟨he, _⟩ | ⟨he, _⟩
          · exact Or.inl he
          · exact Or.inr ⟨0, le_rfl, hlt, he⟩
  | succ m ih =>
      rw [extStep]
      cases hb : ratLtPair (covL (m + 1), x) with
      | false =>
          rcases ih with h | ⟨k, hk, hlt, he⟩
          · exact Or.inl h
          · exact Or.inr ⟨k, Nat.le_succ_of_le hk, hlt, he⟩
      | true =>
          have hlt : covL (m + 1) < x := by
            rw [ratLtPair, decide_eq_true_eq] at hb; exact hb
          rcases max_cases (extStep x m) (covR (m + 1)) with ⟨he, _⟩ | ⟨he, _⟩
          · rw [he]
            rcases ih with h | ⟨k, hk, hlt2, he2⟩
            · exact Or.inl h
            · exact Or.inr ⟨k, Nat.le_succ_of_le hk, hlt2, he2⟩
          · exact Or.inr ⟨m + 1, le_rfl, hlt, he⟩

/-- Every interval reachable from `x` is inside the extension. -/
theorem covR_le_extStep {x : ℚ} {k m : ℕ} (hk : k ≤ m) (hlt : covL k < x) :
    covR k ≤ extStep x m := by
  induction m with
  | zero =>
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      rw [extStep, ratLtPair, decide_eq_true_eq.mpr hlt, cond_true]
      exact le_max_right _ _
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hlt2 | hge
      · have h := ih (Nat.lt_succ_iff.mp hlt2)
        rw [extStep]
        cases ratLtPair (covL (m + 1), x) with
        | false => exact h
        | true => exact le_trans h (le_max_left _ _)
      · have hkeq : k = m + 1 := le_antisymm hk hge
        subst hkeq
        rw [extStep, ratLtPair, decide_eq_true_eq.mpr hlt, cond_true]
        exact le_max_right _ _

/-- The covered initial segment grows with the number of rounds. -/
theorem monotone_leftSeg : Monotone leftSeg := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  rw [leftSeg]
  exact le_extStep _ n

/-- The covered initial segment is nonnegative. -/
theorem leftSeg_nonneg (n : ℕ) : 0 ≤ leftSeg n := by
  have h := monotone_leftSeg (Nat.zero_le n)
  simpa [leftSeg] using h

/-! ### The covered segment really is covered -/

/-- The universal cover at budget `1`, as a set of reals. -/
def covSet : Set ℝ := ⋃ n, (covEnum 1 n).elim ∅ ratInterval

/-- Every nonnegative real below the covered initial segment is covered. -/
theorem mem_covSet_of_lt_leftSeg : ∀ (n : ℕ) (y : ℝ), 0 ≤ y →
    y < ((leftSeg n : ℚ) : ℝ) → y ∈ covSet := by
  intro n
  induction n with
  | zero =>
      intro y hy hlt
      simp only [leftSeg] at hlt
      exact absurd hlt (by push_cast; linarith)
  | succ n ih =>
      intro y hy hlt
      rw [leftSeg] at hlt
      rcases extStep_cases (leftSeg n) n with h | ⟨k, hk, hklt, he⟩
      · exact ih y hy (by rwa [h] at hlt)
      · rcases lt_or_ge y ((leftSeg n : ℚ) : ℝ) with hy2 | hy2
        · exact ih y hy hy2
        · rw [he] at hlt
          have h1 : ((covL k : ℚ) : ℝ) < ((leftSeg n : ℚ) : ℝ) := by exact_mod_cast hklt
          have hlr : covL k < covR k := by
            have : ((covL k : ℚ) : ℝ) < ((covR k : ℚ) : ℝ) := by linarith
            exact_mod_cast this
          refine Set.mem_iUnion.mpr ⟨k, ?_⟩
          rw [covEnum_eq_some hlr]
          exact Set.mem_Ioo.mpr ⟨by linarith, hlt⟩

/-! ### The measure bound -/

/-- The universal cover at budget one has Lebesgue measure at most one half. -/
theorem volume_covSet_le : volume covSet ≤ ENNReal.ofReal ((1 : ℝ) / 2) := by
  have h1 : volume covSet ≤ ∑' n, volume ((covEnum 1 n).elim ∅ ratInterval) :=
    measure_iUnion_le _
  have h2 : ∀ n, volume ((covEnum 1 n).elim ∅ ratInterval)
      = (covEnum 1 n).elim 0 ratIntervalLength := by
    intro n
    rcases Option.eq_none_or_eq_some (covEnum 1 n) with hn | ⟨I, hI⟩
    · rw [hn]; exact measure_empty
    · rw [hI]; exact Real.volume_Ioo
  have h3 : ∀ n, (covEnum 1 n).elim 0 ratIntervalLength
      = ENNReal.ofReal ((covLen (covEnum 1 n) : ℚ) : ℝ) := fun n => (ofReal_covLen_eq _).symm
  have h4 : (∑' n, ENNReal.ofReal ((covLen (covEnum 1 n) : ℚ) : ℝ))
      ≤ ENNReal.ofReal (((1 : ℚ) : ℝ) / 2) := by
    refine le_trans (tsum_covLen_covEnum_le (by norm_num : (0 : ℚ) < 1)) ?_
    exact le_of_eq (tsum_ofReal_covBudget (by norm_num : (0 : ℚ) < 1))
  calc volume covSet ≤ ∑' n, volume ((covEnum 1 n).elim ∅ ratInterval) := h1
    _ = ∑' n, ENNReal.ofReal ((covLen (covEnum 1 n) : ℚ) : ℝ) :=
        tsum_congr (fun n => (h2 n).trans (h3 n))
    _ ≤ ENNReal.ofReal (((1 : ℚ) : ℝ) / 2) := h4
    _ = ENNReal.ofReal ((1 : ℝ) / 2) := by norm_num

/-- The covered initial segment never passes one half. -/
theorem leftSeg_le_half (n : ℕ) : ((leftSeg n : ℚ) : ℝ) ≤ 1 / 2 := by
  have hsub : Set.Ico (0 : ℝ) ((leftSeg n : ℚ) : ℝ) ⊆ covSet := by
    intro y hy
    exact mem_covSet_of_lt_leftSeg n y hy.1 hy.2
  have h1 : volume (Set.Ico (0 : ℝ) ((leftSeg n : ℚ) : ℝ)) ≤ volume covSet :=
    measure_mono hsub
  rw [Real.volume_Ico, sub_zero] at h1
  have h2 : ENNReal.ofReal ((leftSeg n : ℚ) : ℝ) ≤ ENNReal.ofReal ((1 : ℝ) / 2) :=
    le_trans h1 volume_covSet_le
  have h3 : (0 : ℝ) ≤ ((leftSeg n : ℚ) : ℝ) := by exact_mod_cast leftSeg_nonneg n
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h2

/-! ### The leftmost point -/

/-- The leftmost point of the complement of the universal cover. -/
noncomputable def leftmostReal : ℝ := ⨆ n, ((leftSeg n : ℚ) : ℝ)

/-- The covered initial segments are bounded above, so their supremum exists. -/
theorem bddAbove_leftSeg : BddAbove (Set.range (fun n => ((leftSeg n : ℚ) : ℝ))) := by
  refine ⟨1 / 2, ?_⟩
  rintro y ⟨n, rfl⟩
  exact leftSeg_le_half n

/-- Every covered initial segment is at most the leftmost uncovered real. -/
theorem leftSeg_le_leftmostReal (n : ℕ) : ((leftSeg n : ℚ) : ℝ) ≤ leftmostReal :=
  le_ciSup bddAbove_leftSeg n

/-- The leftmost uncovered real is nonnegative. -/
theorem leftmostReal_nonneg : 0 ≤ leftmostReal := by
  have h := leftSeg_le_leftmostReal 0
  simpa [leftSeg] using h

/-- The leftmost uncovered real is lower semicomputable. -/
theorem isLowerSemicomputableReal_leftmostReal :
    IsLowerSemicomputableReal leftmostReal := by
  refine ⟨leftSeg, ?_, monotone_leftSeg, ?_⟩
  · -- computability of the recursion
    have hcL : Computable (fun z : ℚ × ℕ => covL z.2) := computable_covL.comp Computable.snd
    have hcR : Computable (fun z : ℚ × ℕ => covR z.2) := computable_covR.comp Computable.snd
    have hext : Computable (fun z : ℚ × ℕ => extStep z.1 z.2) := by
      have hbase : Computable (fun z : ℚ × ℕ =>
          cond (ratLtPair (covL 0, z.1)) (max z.1 (covR 0)) z.1) := by
        have hb := computable_ratLtPair.comp
          (Computable.pair (Computable.const (covL 0))
            (Computable.fst : Computable (fun z : ℚ × ℕ => z.1)))
        have hm := Computable₂.comp computable₂_ratMax
          (Computable.fst : Computable (fun z : ℚ × ℕ => z.1))
          (Computable.const (covR 0))
        exact Computable.cond hb hm Computable.fst
      have hstep : Computable₂ (fun (z : ℚ × ℕ) (r : ℕ × ℚ) =>
          cond (ratLtPair (covL (r.1 + 1), z.1)) (max r.2 (covR (r.1 + 1))) r.2) := by
        have hsucc : Computable (fun v : (ℚ × ℕ) × ℕ × ℚ => v.2.1 + 1) :=
          Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)
        have hb := computable_ratLtPair.comp
          (Computable.pair (computable_covL.comp hsucc)
            (Computable.fst.comp (Computable.fst : Computable
              (fun v : (ℚ × ℕ) × ℕ × ℚ => v.1))))
        have hm := Computable₂.comp computable₂_ratMax
          (Computable.snd.comp (Computable.snd : Computable
            (fun v : (ℚ × ℕ) × ℕ × ℚ => v.2)))
          (computable_covR.comp hsucc)
        have h := Computable.cond hb hm
          (Computable.snd.comp (Computable.snd : Computable
            (fun v : (ℚ × ℕ) × ℕ × ℚ => v.2)))
        exact h
      have hrec := Computable.nat_rec (σ := ℚ) Computable.snd hbase hstep
      refine hrec.of_eq (fun z => ?_)
      obtain ⟨x, m⟩ := z
      have key : ∀ j : ℕ, (Nat.rec (motive := fun _ => ℚ)
          (cond (ratLtPair (covL 0, x)) (max x (covR 0)) x)
          (fun y IH => cond (ratLtPair (covL (y + 1), x)) (max IH (covR (y + 1))) IH) j)
          = extStep x j := by
        intro j
        induction j with
        | zero => rfl
        | succ j ih =>
            rw [extStep]
            exact congrArg (fun X : ℚ =>
              cond (ratLtPair (covL (j + 1), x)) (max X (covR (j + 1))) X) ih
      exact key m
    have hstep2 : Computable₂ (fun (_ : ℕ) (r : ℕ × ℚ) => extStep r.2 r.1) := by
      have h := hext.comp (Computable.pair
        (Computable.snd.comp (Computable.snd : Computable (fun v : ℕ × ℕ × ℚ => v.2)))
        (Computable.fst.comp (Computable.snd : Computable (fun v : ℕ × ℕ × ℚ => v.2))))
      exact h
    have hrec := Computable.nat_rec (σ := ℚ) Computable.id (Computable.const 0) hstep2
    refine hrec.of_eq (fun n => ?_)
    have key : ∀ j : ℕ, (Nat.rec (motive := fun _ => ℚ) 0
        (fun y IH => extStep IH y) j) = leftSeg j := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
          rw [leftSeg]
          exact congrArg (fun X : ℚ => extStep X j) ih
    exact key n
  · exact tendsto_atTop_ciSup (fun i j hij => by
      have h : ((leftSeg i : ℚ) : ℝ) ≤ ((leftSeg j : ℚ) : ℝ) := by
        exact_mod_cast monotone_leftSeg hij
      exact h) bddAbove_leftSeg

/-- The leftmost uncovered real is indeed not covered by the universal cover at budget one. -/
theorem not_mem_covSet_leftmostReal : leftmostReal ∉ covSet := by
  intro hmem
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
  rcases Option.eq_none_or_eq_some (covEnum 1 k) with hn | ⟨I, hI⟩
  · rw [hn] at hk; exact absurd hk (by simp)
  rw [hI] at hk
  have hkI : leftmostReal ∈ Set.Ioo ((I.1 : ℚ) : ℝ) ((I.2 : ℚ) : ℝ) := hk
  have hIpair : covPair covEnum (1, k) = I := by simp [covPair, hI]
  have hL : covL k = I.1 := by rw [covL, hIpair]
  have hR : covR k = I.2 := by rw [covR, hIpair]
  -- the recursion reaches the interval
  have hex : ∃ n, ((covL k : ℚ) : ℝ) < ((leftSeg n : ℚ) : ℝ) := by
    by_contra hcon
    push Not at hcon
    have hle : leftmostReal ≤ ((covL k : ℚ) : ℝ) := ciSup_le hcon
    rw [hL] at hle
    exact absurd hkI.1 (by linarith)
  obtain ⟨n, hn⟩ := hex
  have hnq : covL k < leftSeg (max n k) := by
    have h1 : ((leftSeg n : ℚ) : ℝ) ≤ ((leftSeg (max n k) : ℚ) : ℝ) := by
      exact_mod_cast monotone_leftSeg (le_max_left n k)
    have : ((covL k : ℚ) : ℝ) < ((leftSeg (max n k) : ℚ) : ℝ) := by linarith
    exact_mod_cast this
  have hstep : covR k ≤ leftSeg (max n k + 1) := by
    rw [leftSeg]
    exact covR_le_extStep (le_max_right n k) hnq
  have hfin : ((covR k : ℚ) : ℝ) ≤ leftmostReal := by
    refine le_trans ?_ (leftSeg_le_leftmostReal (max n k + 1))
    exact_mod_cast hstep
  rw [hR] at hfin
  exact absurd hkI.2 (by linarith)

/-- **SUV p. 161 (Problem 86).** There is a lower semicomputable ML-random real. -/
theorem exists_isLowerSemicomputableReal_isMartinLofRandomReal :
    ∃ x : ℝ, IsLowerSemicomputableReal x ∧ IsMartinLofRandomReal x := by
  refine ⟨leftmostReal, isLowerSemicomputableReal_leftmostReal, ?_⟩
  rintro Y ⟨c, hc, hspec⟩ hy
  refine not_mem_covSet_leftmostReal ?_
  have hlen : ∀ δ : ℚ, 0 < δ →
      (∑' i, ENNReal.ofReal ((covLen (c δ i) : ℚ) : ℝ)) ≤ ENNReal.ofReal ((δ : ℚ) : ℝ) := by
    intro δ hδ
    have h3 : (∑' i, ENNReal.ofReal ((covLen (c δ i) : ℚ) : ℝ))
        = ∑' i, (c δ i).elim 0 ratIntervalLength :=
      tsum_congr (fun i => ofReal_covLen_eq _)
    rw [h3]
    exact (hspec δ hδ).2
  obtain ⟨δ, hδ, hall⟩ := exists_code_covEnum hc hlen (by norm_num : (0 : ℚ) < 1)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ((hspec δ hδ).1 hy)
  obtain ⟨n, hn⟩ := hall i
  exact Set.mem_iUnion.mpr ⟨n, by rw [hn]; exact hi⟩

end Kolmogorov
