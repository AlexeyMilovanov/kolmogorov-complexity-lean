/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.Painter
import KolmogorovMathlib.MonotoneComplexity.Omega.PredictCover

/-!
# The painter cover of SUV Theorem 108 (p. 163)

`Omega/Painter.lean` runs the painting process; this module assembles it into the actual
cover, in the form both SUV Theorem 108 and SUV Theorem 109 (reverse direction) need.

The input is a computable family of **rational increments** `u ε i s ≥ 0`: the paint
attached to index `i` arrives in the portions `u ε i 0, u ε i 1, …`, so that the total
paint attached to `i` is `∑ₛ u ε i s`.  Splitting the paint into rational increments is
what makes the lower semicomputable `hᵢ` of Theorem 108 usable: the painter never has to
know `hᵢ` exactly, it only has to be told about each increase when it happens.

The portions are then indexed by a single natural number through `Nat.unpair`: portion `n`
carries `u ε n.unpair.1 n.unpair.2` units of paint and starts at `a n.unpair.1`.  This is
the point of the accounting function of `add_sum_le_max_paintEnd`: the cover contains a
portion for *every* index `i`, while the estimate that shows `α` is covered uses only the
portions with `i ≥ i₀`, and `i₀` — the index supplied by the source's hypothesis — is not
computable from the budget.

No statement of the source is rendered in this file.
-/

namespace Kolmogorov

open ENNReal

/-- A sum over `ℕ` of a family read through `Nat.unpair` is the iterated sum. -/
theorem tsum_unpair_ennreal (f : ℕ → ℕ → ℝ≥0∞) :
    (∑' n : ℕ, f n.unpair.1 n.unpair.2) = ∑' i, ∑' s, f i s := by
  rw [← Nat.pairEquiv.tsum_eq (fun n : ℕ => f n.unpair.1 n.unpair.2)]
  have h : (fun p : ℕ × ℕ => f (Nat.pairEquiv p).unpair.1 (Nat.pairEquiv p).unpair.2)
      = fun p : ℕ × ℕ => f p.1 p.2 := by
    funext p
    simp [Nat.pairEquiv, Function.uncurry]
  rw [h]
  exact ENNReal.tsum_prod (f := f)

/-- **The painter cover.**  If for every rational budget `ε > 0` one can compute
nonnegative rational increments `u ε i s` whose total mass is less than `ε`, and if the
paint attached to the indices `i ≥ i₀` already carries the monotone computable sequence
`a` from `a i₀` up to `α`, then `α` is not ML-random.

The index `i₀` is allowed to depend on `ε` in a completely non-effective way — it appears
only in the *proof* that the cover catches `α`, never in the cover itself. -/
theorem not_isMartinLofRandomReal_of_paint
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : Monotone a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    {u : ℚ → ℕ → ℕ → ℚ}
    (hu : Computable (fun p : ℚ × ℕ × ℕ => u p.1 p.2.1 p.2.2))
    (hu0 : ∀ ε i s, 0 ≤ u ε i s)
    (hsmall : ∀ ε : ℚ, 0 < ε →
      (∑' i, ∑' s, ENNReal.ofReal ((u ε i s : ℚ) : ℝ)) ≤ ENNReal.ofReal ((ε : ℚ) : ℝ))
    (hcover : ∀ ε : ℚ, 0 < ε → ∃ i₀ : ℕ,
      ENNReal.ofReal (α - ((a i₀ : ℚ) : ℝ))
        ≤ ∑' i : ℕ, (if i₀ ≤ i then ∑' s, ENNReal.ofReal ((u ε i s : ℚ) : ℝ) else 0)) :
    ¬ IsMartinLofRandomReal α := by
  classical
  -- the paint of portion `n`, its starting point, and the padding
  set B : ℚ → ℕ → ℚ := fun ε n => u (ε / 2) n.unpair.1 n.unpair.2 with hBdef
  set D : ℚ → ℕ → ℚ := fun ε n => ratPad (ε / 4) n with hDdef
  set P : ℚ → ℕ → ℚ := fun _ n => a n.unpair.1 with hPdef
  have hBval : ∀ ε n, B ε n = u (ε / 2) n.unpair.1 n.unpair.2 := fun _ _ => rfl
  have hDval : ∀ ε n, D ε n = ratPad (ε / 4) n := fun _ _ => rfl
  have hPval : ∀ ε n, P ε n = a n.unpair.1 := fun _ _ => rfl
  have hB0 : ∀ ε n, 0 ≤ B ε n := fun ε n => hu0 _ _ _
  have hDpos : ∀ {ε : ℚ}, 0 < ε → ∀ n, 0 < D ε n := by
    intro ε hε n
    simp only [hDval]
    exact ratPad_pos (by linarith) n
  have hPle : ∀ ε n, ((P ε n : ℚ) : ℝ) ≤ α := by
    intro ε n
    simp only [hPval]
    exact rat_le_of_monotone_tendsto hmono hlim _
  refine not_isMartinLofRandomReal_of_ratIntervals
    (C := fun ε n => (paintStart (P ε) (fun k => B ε k + D ε k) n - D ε n,
      paintEnd (P ε) (fun k => B ε k + D ε k) n)) ?_ ?_ ?_
  · -- computability of the cover
    have hp2 : Computable₂ P := by
      have h1 : Computable (fun q : ℚ × ℕ => q.2.unpair.1) :=
        (Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd
      exact (ha.comp h1).of_eq (fun q => rfl)
    have hb2 : Computable₂ B := by
      have h1 : Computable (fun q : ℚ × ℕ => q.1 / 2) :=
        (computable_ratDivConst (c := 2) (by norm_num)).comp Computable.fst
      have h2 : Computable (fun q : ℚ × ℕ => q.2.unpair.1) :=
        (Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd
      have h3 : Computable (fun q : ℚ × ℕ => q.2.unpair.2) :=
        (Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.snd
      exact (hu.comp (h1.pair (h2.pair h3))).of_eq (fun q => rfl)
    have hd2 : Computable₂ D := by
      have h1 : Computable (fun q : ℚ × ℕ => q.1 / 4) :=
        (computable_ratDivConst (c := 4) (by norm_num)).comp Computable.fst
      exact (computable₂_ratPad.comp h1 Computable.snd).of_eq (fun q => rfl)
    have hg2 : Computable₂ (fun ε n => B ε n + D ε n) :=
      Computable₂.comp computable₂_ratAdd hb2 hd2
    have hstart := computable_paintStartP (σ := ℚ) hp2 hg2
    have hend := computable_paintEndP (σ := ℚ) hp2 hg2
    have hend' : Computable (fun q : ℚ × ℕ =>
        paintEnd (P q.1) (fun k => B q.1 k + D q.1 k) q.2) :=
      hend.of_eq (fun q => paintEndP_eq _ _ q.1 q.2)
    have hsub : Computable (fun q : ℚ × ℕ =>
        paintStart (P q.1) (fun k => B q.1 k + D q.1 k) q.2 - D q.1 q.2) :=
      Computable₂.comp computable₂_ratSub hstart hd2
    exact hsub.pair hend'
  · -- total length
    intro ε hε
    have hε2 : (0 : ℚ) < ε / 2 := by linarith
    have hε4 : (0 : ℚ) < ε / 4 := by linarith
    have hterm : ∀ n, ratIntervalLength (paintStart (P ε) (fun k => B ε k + D ε k) n - D ε n,
        paintEnd (P ε) (fun k => B ε k + D ε k) n)
        = ENNReal.ofReal ((B ε n : ℚ) : ℝ)
          + (ENNReal.ofReal ((D ε n : ℚ) : ℝ) + ENNReal.ofReal ((D ε n : ℚ) : ℝ)) :=
      fun n => ratIntervalLength_paint (P ε) (B ε) (D ε) (hB0 ε n) (hDpos hε n).le
    rw [tsum_congr hterm, ENNReal.tsum_add, ENNReal.tsum_add]
    have hd : (∑' n, ENNReal.ofReal ((D ε n : ℚ) : ℝ)) = ENNReal.ofReal (((ε / 8 : ℚ)) : ℝ) := by
      have h := tsum_ofReal_ratPad (ε := ε / 4) hε4
      rw [show (fun n : ℕ => ENNReal.ofReal ((D ε n : ℚ) : ℝ))
          = fun n : ℕ => ENNReal.ofReal ((ratPad (ε / 4) n : ℚ) : ℝ) from rfl]
      rw [h]
      congr 1
      push_cast
      ring
    have hb : (∑' n, ENNReal.ofReal ((B ε n : ℚ) : ℝ))
        = ∑' i, ∑' s, ENNReal.ofReal ((u (ε / 2) i s : ℚ) : ℝ) :=
      tsum_unpair_ennreal (fun i s => ENNReal.ofReal ((u (ε / 2) i s : ℚ) : ℝ))
    rw [hb, hd]
    have h1 : (∑' i, ∑' s, ENNReal.ofReal ((u (ε / 2) i s : ℚ) : ℝ))
        ≤ ENNReal.ofReal (((ε / 2 : ℚ)) : ℝ) := hsmall _ hε2
    have h2 : ENNReal.ofReal (((ε / 2 : ℚ)) : ℝ) + (ENNReal.ofReal (((ε / 8 : ℚ)) : ℝ)
        + ENNReal.ofReal (((ε / 8 : ℚ)) : ℝ)) ≤ ENNReal.ofReal ((ε : ℚ) : ℝ) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hεR : (0 : ℝ) < ((ε : ℚ) : ℝ) := by exact_mod_cast hε
      push_cast
      linarith
    exact le_trans (add_le_add h1 le_rfl) h2
  · -- the cover catches `α`
    intro ε hε
    have hε2 : (0 : ℚ) < ε / 2 := by linarith
    obtain ⟨i₀, hi₀⟩ := hcover (ε / 2) hε2
    set acc : ℕ → ℚ := fun n => if i₀ ≤ n.unpair.1 then B ε n else 0 with haccdef
    have haccval : ∀ n, acc n = if i₀ ≤ n.unpair.1 then B ε n else 0 := fun _ => rfl
    have hacc0 : ∀ n, 0 ≤ acc n := by
      intro n
      simp only [haccval]
      by_cases h : i₀ ≤ n.unpair.1
      · simp only [if_pos h]; exact hB0 ε n
      · simp only [if_neg h]
        exact le_rfl
    have haccle : ∀ n, acc n ≤ B ε n := by
      intro n
      simp only [haccval]
      by_cases h : i₀ ≤ n.unpair.1
      · simp only [if_pos h]
        exact le_rfl
      · simp only [if_neg h]; exact hB0 ε n
    have hstart : ∀ n, 0 < acc n → a i₀ ≤ P ε n := by
      intro n hn
      simp only [hPval]
      refine hmono ?_
      by_contra hcon
      simp only [haccval, if_neg hcon] at hn
      exact absurd hn (lt_irrefl 0)
    have hn₀ : a i₀ ≤ P ε (Nat.pair i₀ 0) := by
      simp only [hPval, Nat.unpair_pair]
      exact le_rfl
    have hsum : ENNReal.ofReal (α - ((a i₀ : ℚ) : ℝ))
        ≤ ∑' n, ENNReal.ofReal ((acc n : ℚ) : ℝ) := by
      refine le_trans hi₀ (le_of_eq ?_)
      have hkey : (∑' n, ENNReal.ofReal ((acc n : ℚ) : ℝ))
          = ∑' i, ∑' s, (if i₀ ≤ i then ENNReal.ofReal ((u (ε / 2) i s : ℚ) : ℝ) else 0) := by
        rw [← tsum_unpair_ennreal
          (fun i s => if i₀ ≤ i then ENNReal.ofReal ((u (ε / 2) i s : ℚ) : ℝ) else 0)]
        refine tsum_congr (fun n => ?_)
        simp only [haccval]
        by_cases h : i₀ ≤ n.unpair.1
        · simp only [if_pos h, hBval]
        · simp only [if_neg h]
          simp
      rw [hkey]
      refine (tsum_congr (fun i => ?_)).symm
      by_cases h : i₀ ≤ i
      · simp only [if_pos h]
      · simp only [if_neg h]
        rw [tsum_zero]
    have hcα : ((a i₀ : ℚ) : ℝ) ≤ α := rat_le_of_monotone_tendsto hmono hlim i₀
    exact exists_mem_ratInterval_paint (n₀ := Nat.pair i₀ 0) (hB0 ε) (hDpos hε) hacc0 haccle
      (hPle ε) hcα hstart hn₀ hsum

end Kolmogorov
