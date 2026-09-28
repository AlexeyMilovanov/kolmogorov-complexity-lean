/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.PaintCover

/-!
# The painter cover for a lower semicomputable family (SUV Theorem 108, p. 163)

`Omega/PaintCover.lean` runs the painters on a computable family of rational increments.
This module produces those increments from a *lower semicomputable* family: the dyadic
approximation `dyadicValue (approx s ε i) s` of `h ε i` increases with the stage `s`, and
its increments `increments (fun s => approx s ε i / 2^s)` are computable nonnegative
rationals summing to `h ε i`.

This is the "incremental paint" that Theorem 108 needs: the painter is never told the
value of `hᵢ`, only about each increase of the approximation, and it charges each increase
separately.  Because a portion of paint always starts at `max (aᵢ, right end so far)`,
paying for the increases separately costs exactly `∑ᵢ hᵢ` and not `∑ₛ ∑ᵢ (stage-s value)`.

No statement of the source is rendered in this file.
-/

namespace Kolmogorov

open ENNReal

/-! ### Rational dyadics -/

/-- The rational number `n / 2 ^ s`, whose `ℝ≥0∞`-value is `dyadicValue n s`. -/
def ratDyadicVal (n s : ℕ) : ℚ := (n : ℚ) / 2 ^ s

/-- The dyadic rational `n / 2 ^ s` is nonnegative. -/
theorem ratDyadicVal_nonneg (n s : ℕ) : 0 ≤ ratDyadicVal n s := by
  rw [ratDyadicVal]
  positivity

/-- The extended-nonnegative value of `n / 2 ^ s` is `dyadicValue n s`. -/
theorem ofReal_ratDyadicVal (n s : ℕ) :
    ENNReal.ofReal ((ratDyadicVal n s : ℚ) : ℝ) = dyadicValue n s := by
  rw [← ofReal_toReal_dyadicValue n s]
  congr 1
  rw [ratDyadicVal]
  push_cast
  ring

/-- The dyadic rational `n / 2 ^ s` is computable in both arguments. -/
theorem computable₂_ratDyadicVal : Computable₂ ratDyadicVal := by
  have hden : Computable (fun p : ℕ × ℕ => (1 : ℚ) / 2 ^ p.2) := by
    have hnat : Primrec (fun n : ℕ => 2 ^ n) :=
      (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id
    refine computable_of_num_den (N := fun _ : ℕ × ℕ => (1 : ℤ))
      (D := fun p : ℕ × ℕ => 2 ^ p.2) (Computable.const 1)
      (hnat.to_comp.comp Computable.snd) (fun _ => by positivity) (fun p => ?_)
    push_cast
    ring
  have hnum : Computable (fun p : ℕ × ℕ => ((p.1 : ℕ) : ℚ)) :=
    computable_nat_to_rat.comp Computable.fst
  refine (Computable₂.comp computable₂_ratMul hnum hden).of_eq (fun p => ?_)
  rw [ratDyadicVal]
  ring

attribute [irreducible] ratDyadicVal

/-! ### Painting from monotone rational stage values -/

/-- The paint attached to the index `p.2` at parameter `p.1`, read off from a
nondecreasing sequence of rational stage values: the increments of that sequence.  Only
the *increase* of the stage value is charged, so the painter is told about the growth of
a lower semicomputable quantity without ever being told the quantity. -/
def stagePaint (v : ℚ × ℕ → ℕ → ℚ) (p : ℚ × ℕ) : ℕ → ℚ := increments (v p)

/-- The increments painted at each stage of a non-decreasing approximation are nonnegative. -/
theorem stagePaint_nonneg {v : ℚ × ℕ → ℕ → ℚ} (h0 : ∀ p, 0 ≤ v p 0)
    (hmono : ∀ p s, v p s ≤ v p (s + 1)) (p : ℚ × ℕ) (s : ℕ) : 0 ≤ stagePaint v p s := by
  cases s with
  | zero =>
      rw [stagePaint, increments_zero]
      exact h0 p
  | succ t =>
      rw [stagePaint, increments_succ, sub_nonneg]
      exact hmono p t

/-- The paint attached to one index adds up to the supremum of the stage values. -/
theorem tsum_stagePaint {v : ℚ × ℕ → ℕ → ℚ} (h0 : ∀ p, 0 ≤ v p 0)
    (hmono : ∀ p s, v p s ≤ v p (s + 1)) (p : ℚ × ℕ) :
    (∑' s, ENNReal.ofReal ((stagePaint v p s : ℚ) : ℝ))
      = ⨆ s, ENNReal.ofReal ((v p s : ℚ) : ℝ) := by
  have hpart : ∀ T : ℕ,
      ∑ s ∈ Finset.range (T + 1), ENNReal.ofReal ((stagePaint v p s : ℚ) : ℝ)
        = ENNReal.ofReal ((v p T : ℚ) : ℝ) := by
    intro T
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun s _ => by exact_mod_cast stagePaint_nonneg h0 hmono p s)]
    congr 1
    have hq : ∑ s ∈ Finset.range (T + 1), stagePaint v p s = v p T :=
      sum_range_increments (v p) T
    rw [← hq]
    push_cast
    ring
  rw [ENNReal.tsum_eq_iSup_nat]
  refine le_antisymm (iSup_le (fun S => ?_)) (iSup_le (fun s => ?_))
  · cases S with
    | zero => simp
    | succ T =>
        rw [hpart T]
        exact le_iSup (fun t => ENNReal.ofReal ((v p t : ℚ) : ℝ)) T
  · rw [← hpart s]
    exact le_iSup
      (fun S => ∑ t ∈ Finset.range S, ENNReal.ofReal ((stagePaint v p t : ℚ) : ℝ)) (s + 1)

/-- The stage increments of a computable approximation are computable. -/
theorem computable_stagePaint {v : ℚ × ℕ → ℕ → ℚ}
    (hv : Computable (fun z : (ℚ × ℕ) × ℕ => v z.1 z.2)) :
    Computable (fun q : ℚ × ℕ × ℕ => stagePaint v (q.1, q.2.1) q.2.2) := by
  -- every composition below is elaborated *without* an expected type (trap 3)
  have hbase0 := hv.comp
    ((Computable.fst : Computable (fun z : (ℚ × ℕ) × ℕ => z.1)).pair (Computable.const 0))
  have hbase : Computable (fun z : (ℚ × ℕ) × ℕ => v z.1 0) := hbase0.of_eq (fun z => rfl)
  have hp1 : Computable (fun w : ((ℚ × ℕ) × ℕ) × ℕ => (w.1.1, w.2 + 1)) :=
    (Computable.fst.comp Computable.fst).pair (Primrec.succ.to_comp.comp Computable.snd)
  have hp2 : Computable (fun w : ((ℚ × ℕ) × ℕ) × ℕ => (w.1.1, w.2)) :=
    (Computable.fst.comp Computable.fst).pair Computable.snd
  have hs1 := hv.comp hp1
  have hs2 := hv.comp hp2
  have hstep0 := Computable₂.comp computable₂_ratSub hs1 hs2
  have hstep2 : Computable₂ (fun (z : (ℚ × ℕ) × ℕ) (j : ℕ) => v z.1 (j + 1) - v z.1 j) :=
    hstep0.of_eq (fun w => rfl)
  have hcases := Computable.nat_casesOn
    (Computable.snd : Computable (fun z : (ℚ × ℕ) × ℕ => z.2)) hbase hstep2
  have hinc : Computable (fun z : (ℚ × ℕ) × ℕ => increments (v z.1) z.2) := by
    refine hcases.of_eq (fun z => ?_)
    obtain ⟨q, n⟩ := z
    cases n with
    | zero => rfl
    | succ n => rfl
  have hre2 : Computable (fun q : ℚ × ℕ × ℕ => ((q.1, q.2.1), q.2.2)) :=
    (Computable.fst.pair (Computable.fst.comp Computable.snd)).pair
      (Computable.snd.comp Computable.snd)
  have hfin := hinc.comp hre2
  exact hfin.of_eq (fun q => rfl)

/-- **The painter cover from monotone rational stage values.**  `v (ε, i) s` is the
stage-`s` rational approximation of the paint attached to index `i`; `hsmall` bounds the
total paint by the budget, and `hcov` says that the paint of the indices `i ≥ i₀` carries
`a` from `a i₀` up to `α`.  The index `i₀` may depend on `ε` non-effectively. -/
theorem not_isMartinLofRandomReal_of_stagePaint
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : Monotone a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    {v : ℚ × ℕ → ℕ → ℚ} (hv : Computable (fun z : (ℚ × ℕ) × ℕ => v z.1 z.2))
    (h0 : ∀ p, 0 ≤ v p 0) (hvmono : ∀ p s, v p s ≤ v p (s + 1))
    (hsmall : ∀ ε : ℚ, 0 < ε →
      (∑' i, ⨆ s, ENNReal.ofReal ((v (ε, i) s : ℚ) : ℝ)) ≤ ENNReal.ofReal ((ε : ℚ) : ℝ))
    (hcov : ∀ ε : ℚ, 0 < ε → ∃ i₀ : ℕ, ENNReal.ofReal (α - ((a i₀ : ℚ) : ℝ))
      ≤ ∑' i : ℕ, (if i₀ ≤ i then ⨆ s, ENNReal.ofReal ((v (ε, i) s : ℚ) : ℝ) else 0)) :
    ¬ IsMartinLofRandomReal α := by
  classical
  refine not_isMartinLofRandomReal_of_paint ha hmono hlim
    (u := fun ε i => stagePaint v (ε, i)) (computable_stagePaint hv)
    (fun ε i s => stagePaint_nonneg h0 hvmono (ε, i) s) (fun ε hε => ?_) (fun ε hε => ?_)
  · rw [tsum_congr (fun i => tsum_stagePaint h0 hvmono (ε, i))]
    exact hsmall ε hε
  · obtain ⟨i₀, hi₀⟩ := hcov ε hε
    refine ⟨i₀, le_trans hi₀ (le_of_eq (tsum_congr (fun i => ?_)))⟩
    by_cases hle : i₀ ≤ i
    · rw [if_pos hle, if_pos hle, tsum_stagePaint h0 hvmono (ε, i)]
    · rw [if_neg hle, if_neg hle]

/-! ### The lower semicomputable family -/

/-- The stage-`s` rational value of the approximation of `h ε i`. -/
def lscFamilyVal (approx : ℕ → ℚ → ℕ → ℕ) (p : ℚ × ℕ) (s : ℕ) : ℚ :=
  ratDyadicVal (approx s p.1 p.2) s

/-- The stage values of a computable family of approximations are computable. -/
theorem computable_lscFamilyVal {approx : ℕ → ℚ → ℕ → ℕ}
    (happrox : Computable (fun p : ℕ × ℚ × ℕ => approx p.1 p.2.1 p.2.2)) :
    Computable (fun z : (ℚ × ℕ) × ℕ => lscFamilyVal approx z.1 z.2) := by
  have hre1 : Computable (fun z : (ℚ × ℕ) × ℕ => (z.2, z.1.1, z.1.2)) :=
    Computable.snd.pair ((Computable.fst.comp Computable.fst).pair
      (Computable.snd.comp Computable.fst))
  have hap := happrox.comp hre1
  have hval0 := Computable₂.comp computable₂_ratDyadicVal hap
    (Computable.snd : Computable (fun z : (ℚ × ℕ) × ℕ => z.2))
  exact hval0.of_eq (fun z => rfl)

/-- The stage values of the family are nonnegative. -/
theorem lscFamilyVal_nonneg (approx : ℕ → ℚ → ℕ → ℕ) (p : ℚ × ℕ) (s : ℕ) :
    0 ≤ lscFamilyVal approx p s := ratDyadicVal_nonneg _ _

/-- The stage values of the family are non-decreasing in the stage. -/
theorem lscFamilyVal_mono {approx : ℕ → ℚ → ℕ → ℕ}
    (hstep : ∀ s ε i, dyadicValue (approx s ε i) s ≤ dyadicValue (approx (s + 1) ε i) (s + 1))
    (p : ℚ × ℕ) (s : ℕ) : lscFamilyVal approx p s ≤ lscFamilyVal approx p (s + 1) := by
  have hR : ENNReal.ofReal ((lscFamilyVal approx p s : ℚ) : ℝ)
      ≤ ENNReal.ofReal ((lscFamilyVal approx p (s + 1) : ℚ) : ℝ) := by
    rw [lscFamilyVal, lscFamilyVal, ofReal_ratDyadicVal, ofReal_ratDyadicVal]
    exact hstep s p.1 p.2
  have hR2 : ((lscFamilyVal approx p s : ℚ) : ℝ)
      ≤ ((lscFamilyVal approx p (s + 1) : ℚ) : ℝ) := by
    refine (ENNReal.ofReal_le_ofReal_iff ?_).1 hR
    exact_mod_cast lscFamilyVal_nonneg approx p (s + 1)
  exact_mod_cast hR2

/-- The stage values of the family converge to the value of the function they approximate. -/
theorem iSup_ofReal_lscFamilyVal {approx : ℕ → ℚ → ℕ → ℕ} {h : ℚ → ℕ → ℝ≥0∞}
    (hsup : ∀ ε i, ⨆ s, dyadicValue (approx s ε i) s = h ε i) (ε : ℚ) (i : ℕ) :
    (⨆ s, ENNReal.ofReal ((lscFamilyVal approx (ε, i) s : ℚ) : ℝ)) = h ε i := by
  rw [← hsup ε i]
  exact iSup_congr (fun s => by rw [lscFamilyVal, ofReal_ratDyadicVal])

/-- **The painter cover of SUV Theorem 108.**  `approx` is the dyadic approximation datum
of a uniformly lower semicomputable family `h`; `hsmall` bounds the total mass of the
family; `hcov` says that the tail of the family from some index `i₀` on already reaches
from `a i₀` up to `α`.  Then `α` is not ML-random.  As in
`not_isMartinLofRandomReal_of_stagePaint`, `i₀` may depend on `ε` non-effectively. -/
theorem not_isMartinLofRandomReal_of_lscPaint
    {a : ℕ → ℚ} {α : ℝ} (ha : Computable a) (hmono : Monotone a)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds α))
    {approx : ℕ → ℚ → ℕ → ℕ} {h : ℚ → ℕ → ℝ≥0∞}
    (hstep : ∀ s ε i, dyadicValue (approx s ε i) s ≤ dyadicValue (approx (s + 1) ε i) (s + 1))
    (hsup : ∀ ε i, ⨆ s, dyadicValue (approx s ε i) s = h ε i)
    (happrox : Computable (fun p : ℕ × ℚ × ℕ => approx p.1 p.2.1 p.2.2))
    (hsmall : ∀ ε : ℚ, 0 < ε → (∑' i, h ε i) ≤ ENNReal.ofReal ((ε : ℚ) : ℝ))
    (hcov : ∀ ε : ℚ, 0 < ε → ∃ i₀ : ℕ,
      ENNReal.ofReal (α - ((a i₀ : ℚ) : ℝ)) ≤ ∑' i : ℕ, (if i₀ ≤ i then h ε i else 0)) :
    ¬ IsMartinLofRandomReal α := by
  classical
  refine not_isMartinLofRandomReal_of_stagePaint ha hmono hlim
    (v := lscFamilyVal approx) (computable_lscFamilyVal happrox)
    (fun p => lscFamilyVal_nonneg approx p 0) (lscFamilyVal_mono hstep)
    (fun ε hε => ?_) (fun ε hε => ?_)
  · rw [tsum_congr (fun i => iSup_ofReal_lscFamilyVal hsup ε i)]
    exact hsmall ε hε
  · obtain ⟨i₀, hi₀⟩ := hcov ε hε
    refine ⟨i₀, le_trans hi₀ (le_of_eq (tsum_congr (fun i => ?_)))⟩
    by_cases hle : i₀ ≤ i
    · rw [if_pos hle, if_pos hle, iSup_ofReal_lscFamilyVal hsup ε i]
    · rw [if_neg hle, if_neg hle]

end Kolmogorov
