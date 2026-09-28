/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic.DiracSemimeasure
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic

/-!
# `Ω` dominates every lower semicomputable real (SUV Theorem 103, p. 160)

This module proves the analytic core of the "vice versa" direction of SUV Theorem 103:
*every* lower semicomputable real `γ` satisfies `γ ≼_K Ω` for some rational `K > 0`.

The argument is the source's: write `γ` as the sum of a computable series of nonnegative
rationals, scale it by a rational `C` above its sum so that it becomes a lower
semicomputable semimeasure on `ℕ`, use the maximality of `m` to get a constant, and then
observe that `K·Ω − γ` is the sum of the *nonnegative* series `K·m(i) − vᵢ`, which is
lower semicomputable because its stage-`s` partial sums `∑_{i<s} max 0 (K·mₛ(i) − vᵢ)`
are computable, non-decreasing rationals converging to it.

Everything here is proved; the module renders no statement of the source.
-/

namespace Kolmogorov


open ComputableReals
open ENNReal

/-! ### A diagonal partial sum -/

/-- `∑_{i < n} P s i`, in the shape `Computable.nat_rec` accepts, with the stage `s` as
the recursion parameter (so that the diagonal `s ↦ ∑_{i < s} P s i` is computable). -/
def ratStageSum (P : ℕ → ℕ → ℚ) (s : ℕ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => ratStageSum P s n + P s n

/-- The recursive stage sum agrees with the sum over `Finset.range`. -/
theorem ratStageSum_eq (P : ℕ → ℕ → ℚ) (s n : ℕ) :
    ratStageSum P s n = ∑ i ∈ Finset.range n, P s i := by
  induction n with
  | zero => simp [ratStageSum]
  | succ n ih => rw [ratStageSum, ih, Finset.sum_range_succ]

/-- The diagonal stage sum of a computable family is computable. -/
theorem computable_ratStageSum_diag {P : ℕ → ℕ → ℚ} (hP : Computable₂ P) :
    Computable (fun s : ℕ => ratStageSum P s s) := by
  have hstep : Computable₂ (fun (s : ℕ) (r : ℕ × ℚ) => r.2 + P s r.1) := by
    have h1 : Computable (fun z : ℕ × ℕ × ℚ => z.2.2) := Computable.snd.comp Computable.snd
    have h2 : Computable (fun z : ℕ × ℕ × ℚ => P z.1 z.2.1) :=
      hP.comp Computable.fst (Computable.fst.comp Computable.snd)
    exact Computable₂.comp computable₂_ratAdd h1 h2
  have hrec := Computable.nat_rec (σ := ℚ) Computable.id (Computable.const 0) hstep
  refine hrec.of_eq (fun s => ?_)
  have key : ∀ n : ℕ, (Nat.rec (motive := fun _ => ℚ) 0
      (fun y IH => IH + P s y) n) = ratStageSum P s n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [ratStageSum]
        exact congrArg (fun x : ℚ => x + P s n) ih
  exact key s

/-! ### A computable series of nonnegative rationals is a semimeasure -/

/-- A computable family of nonnegative rationals with total mass at most `1` is a lower
semicomputable semimeasure on `ℕ`.  The dyadic approximation is the constant-in-`s`
family `⌊q·2^s⌋`. -/
theorem isLowerSemicomputableSemimeasureNat_ofRat {q : ℕ → ℚ} (hq : Computable q)
    (hsum : (∑' i, ENNReal.ofReal ((q i : ℚ) : ℝ)) ≤ 1) :
    IsLowerSemicomputableSemimeasureNat (fun i => ENNReal.ofReal ((q i : ℚ) : ℝ)) := by
  constructor
  · change (∑' x : BitString, ENNReal.ofReal ((q (bitStringToNat x) : ℚ) : ℝ)) ≤ 1
    refine le_of_eq_of_le ?_ hsum
    exact tsum_comp_bitStringToNat (fun i => ENNReal.ofReal ((q i : ℚ) : ℝ))
  · refine ⟨fun s x _ => ratDyadicFloor (q (bitStringToNat x)) s, ?_, ?_, ?_⟩
    · intro s x _
      exact dyadicValue_ratDyadicFloor_mono_of_le (le_refl (q (bitStringToNat x))) s
    · intro x _
      have h := iSup_ratDyadicFloor_of_monotone
        (f := fun _ : ℕ => q (bitStringToNat x)) monotone_const
      have hdy : ∀ s : ℕ, dyadicValue (ratDyadicFloor (q (bitStringToNat x)) s) s
          = (ratDyadicFloor (q (bitStringToNat x)) s : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s := by
        intro s; rw [dyadicValue]
      rw [iSup_congr hdy, h, ciSup_const]
    · have hbts : Computable (fun p : ℕ × BitString × BitString =>
          q (bitStringToNat p.2.1)) :=
        hq.comp (primrec_bitStringToNat.to_comp.comp (Computable.fst.comp Computable.snd))
      exact computable_ratDyadicFloor.comp hbts Computable.fst

/-! ### `Ω` dominates every lower semicomputable real -/

/-- Increments of a lower approximation sequence form a computable non-negative series
summing to `γ - a.seq 0`. -/
private theorem lowerApprox_diff_tsum {γ : ℝ} (a : LowerApprox γ) :
    let v : ℕ → ℚ := fun i => a.seq (i + 1) - a.seq i
    Computable v ∧ (∀ i, 0 ≤ v i) ∧ Summable (fun i => ((v i : ℚ) : ℝ)) ∧
      ∑' i, ((v i : ℚ) : ℝ) = γ - ((a.seq 0 : ℚ) : ℝ) := by
  intro v
  have hvc : Computable v :=
    Computable₂.comp computable₂_ratSub (a.isComputable.comp Primrec.succ.to_comp)
      a.isComputable
  have hv0 : ∀ i, 0 ≤ v i := by
    intro i
    simp only [v, sub_nonneg]
    exact a.isStrictMono.monotone (Nat.le_succ i)
  have hvsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, v i = a.seq n - a.seq 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; simp only [v]; ring
  have hvlim : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, ((v i : ℚ) : ℝ))
      Filter.atTop (nhds (γ - ((a.seq 0 : ℚ) : ℝ))) := by
    have hcast : (fun n => ∑ i ∈ Finset.range n, ((v i : ℚ) : ℝ))
        = fun n => ((a.seq n : ℚ) : ℝ) - ((a.seq 0 : ℚ) : ℝ) := by
      funext n
      have hc1 : (((∑ i ∈ Finset.range n, v i : ℚ)) : ℝ)
          = ∑ i ∈ Finset.range n, ((v i : ℚ) : ℝ) := by push_cast; ring
      rw [← hc1, hvsum n]
      push_cast
      ring
    rw [hcast]
    exact a.tendsto.sub tendsto_const_nhds
  have hvmono : Monotone (fun n => ∑ i ∈ Finset.range n, ((v i : ℚ) : ℝ)) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rw [Finset.sum_range_succ]
    have : (0 : ℝ) ≤ ((v n : ℚ) : ℝ) := by exact_mod_cast hv0 n
    linarith
  have hvpartial : ∀ n, ∑ i ∈ Finset.range n, ((v i : ℚ) : ℝ) ≤ γ - ((a.seq 0 : ℚ) : ℝ) :=
    fun n => hvmono.ge_of_tendsto hvlim n
  have hvsummable : Summable (fun i => ((v i : ℚ) : ℝ)) :=
    summable_of_sum_range_le (fun i => by exact_mod_cast hv0 i) hvpartial
  have hvtsum : ∑' i, ((v i : ℚ) : ℝ) = γ - ((a.seq 0 : ℚ) : ℝ) :=
    tendsto_nhds_unique hvsummable.hasSum.tendsto_sum_nat hvlim
  exact ⟨hvc, hv0, hvsummable, hvtsum⟩

/-- Universal semimeasure domination yields a rational multiplier `K > 0` bounding
`v n` by `K * (m n).toReal`. -/
private theorem exists_rat_mul_ge_of_dominates {m : ℕ → ℝ≥0∞} (hmtop : ∀ n, m n ≠ ⊤)
    {v : ℕ → ℚ} (hv0 : ∀ i, 0 ≤ v i) {C : ℚ} (hCpos : 0 < C) {c : ℝ≥0∞} (hcpos : 0 < c)
    (hdom : ∀ n, c * ENNReal.ofReal ((v n / C : ℚ) : ℝ) ≤ m n) :
    ∃ K : ℚ, 0 < K ∧ ∀ n, ((v n : ℚ) : ℝ) ≤ ((K : ℚ) : ℝ) * (m n).toReal := by
  set c' : ℝ≥0∞ := min c 1 with hc'def
  have hc'pos : 0 < c' := lt_min hcpos one_pos
  have hc'top : c' ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (min_le_right c 1)
  have hdom' : ∀ n, c' * ENNReal.ofReal ((v n / C : ℚ) : ℝ) ≤ m n := by
    intro n
    exact le_trans (mul_le_mul_left (min_le_left c 1) _) (hdom n)
  have hCposR : (0 : ℝ) < ((C : ℚ) : ℝ) := by exact_mod_cast hCpos
  have hstep : ∀ n, ENNReal.ofReal ((v n : ℚ) : ℝ) * c'
      ≤ ENNReal.ofReal ((C : ℚ) : ℝ) * m n := by
    intro n
    have hsplit : ENNReal.ofReal ((v n : ℚ) : ℝ)
        = ENNReal.ofReal ((C : ℚ) : ℝ) * ENNReal.ofReal ((v n / C : ℚ) : ℝ) := by
      rw [← ENNReal.ofReal_mul hCposR.le]
      congr 1
      push_cast
      field_simp
    rw [hsplit]
    calc ENNReal.ofReal ((C : ℚ) : ℝ) * ENNReal.ofReal ((v n / C : ℚ) : ℝ) * c'
        = ENNReal.ofReal ((C : ℚ) : ℝ) * (c' * ENNReal.ofReal ((v n / C : ℚ) : ℝ)) := by ring
      _ ≤ ENNReal.ofReal ((C : ℚ) : ℝ) * m n := mul_le_mul_right (hdom' n) _
  have hc'R : (0 : ℝ) < c'.toReal := ENNReal.toReal_pos hc'pos.ne' hc'top
  have hreal : ∀ n, ((v n : ℚ) : ℝ) * c'.toReal ≤ ((C : ℚ) : ℝ) * (m n).toReal := by
    intro n
    have h1 := hstep n
    have hL : (ENNReal.ofReal ((v n : ℚ) : ℝ) * c').toReal
        = ((v n : ℚ) : ℝ) * c'.toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by exact_mod_cast hv0 n)]
    have hR : (ENNReal.ofReal ((C : ℚ) : ℝ) * m n).toReal
        = ((C : ℚ) : ℝ) * (m n).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCposR.le]
    have hne1 : ENNReal.ofReal ((v n : ℚ) : ℝ) * c' ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc'top
    have hne2 : ENNReal.ofReal ((C : ℚ) : ℝ) * m n ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmtop n)
    have := (ENNReal.toReal_le_toReal hne1 hne2).2 h1
    rwa [hL, hR] at this
  obtain ⟨K, hKgt⟩ := exists_rat_gt (((C : ℚ) : ℝ) / c'.toReal)
  have hKpos : (0 : ℚ) < K := by
    have h1 : (0 : ℝ) < ((C : ℚ) : ℝ) / c'.toReal := div_pos hCposR hc'R
    have : (0 : ℝ) < ((K : ℚ) : ℝ) := lt_trans h1 hKgt
    exact_mod_cast this
  have hKle : ∀ n, ((v n : ℚ) : ℝ) ≤ ((K : ℚ) : ℝ) * (m n).toReal := by
    intro n
    have h1 := hreal n
    have h2 : ((v n : ℚ) : ℝ) ≤ (((C : ℚ) : ℝ) / c'.toReal) * (m n).toReal := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc'R]
      linarith
    have h3 : (((C : ℚ) : ℝ) / c'.toReal) * (m n).toReal
        ≤ ((K : ℚ) : ℝ) * (m n).toReal := by
      refine mul_le_mul_of_nonneg_right hKgt.le ENNReal.toReal_nonneg
    linarith
  exact ⟨K, hKpos, hKle⟩

/-- The dyadic rational stage approximation function `w s i = (g s i : ℚ) / 2 ^ s` is
`Computable₂`. -/
private theorem dyadic_stage_approx_computable {A : ℕ → BitString → BitString → ℕ}
    (hA : Computable (fun p : ℕ × BitString × BitString => A p.1 p.2.1 p.2.2)) :
    Computable₂ (fun s i => ((A s (natToBitString i) [] : ℚ) / 2 ^ s)) := by
  have hgc : Computable (fun p : ℕ × ℕ => A p.1 (natToBitString p.2) []) :=
    hA.comp (Computable.pair Computable.fst
      (Computable.pair (computable_natToBitString.comp Computable.snd) (Computable.const [])))
  refine computable_of_num_den
    (N := fun p : ℕ × ℕ => ((A p.1 (natToBitString p.2) [] : ℕ) : ℤ))
    (D := fun p : ℕ × ℕ => 2 ^ p.1)
    (ComputableReals.primrec_natCastInt.to_comp.comp hgc)
    (((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.fst).to_comp)
    (fun _ => by positivity) (fun _ => ?_)
  push_cast
  ring

/-- The dyadic stage approximations `(g s i : ℚ) / 2 ^ s` tend to `(m i).toReal`
as `s → ∞`. -/
private theorem dyadic_stage_approx_tendsto {m : ℕ → ℝ≥0∞} (hmtop : ∀ n, m n ≠ ⊤)
    (g : ℕ → ℕ → ℕ) (hmn : ∀ n, ⨆ s, dyadicValue (g s n) s = m n)
    (hgmono : ∀ n, Monotone (fun s => dyadicValue (g s n) s))
    (hgle : ∀ s n, dyadicValue (g s n) s ≤ m n) (i : ℕ) :
    Filter.Tendsto (fun s => (((g s i : ℚ) / 2 ^ s : ℚ) : ℝ)) Filter.atTop
      (nhds ((m i).toReal)) := by
  have hwcast : ∀ s, (((g s i : ℚ) / 2 ^ s : ℚ) : ℝ) = (dyadicValue (g s i) s).toReal := by
    intro s
    rw [toReal_dyadicValue]
    push_cast
    ring
  have hw0 : ∀ s, (0 : ℚ) ≤ (g s i : ℚ) / 2 ^ s := fun _ => by positivity
  have hwle : ∀ s, (((g s i : ℚ) / 2 ^ s : ℚ) : ℝ) ≤ (m i).toReal := by
    intro s
    rw [hwcast]
    exact ENNReal.toReal_mono (hmtop i) (hgle s i)
  have hmonoR : Monotone (fun s => (((g s i : ℚ) / 2 ^ s : ℚ) : ℝ)) := by
    intro s u hsu
    change (((g s i : ℚ) / 2 ^ s : ℚ) : ℝ) ≤ (((g u i : ℚ) / 2 ^ u : ℚ) : ℝ)
    rw [hwcast s, hwcast u]
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top (hmtop i) (hgle u i)) (hgmono i hsu)
  have hbdd : BddAbove (Set.range (fun s => (((g s i : ℚ) / 2 ^ s : ℚ) : ℝ))) := by
    refine ⟨(m i).toReal, ?_⟩
    rintro y ⟨s, rfl⟩
    exact hwle s
  have htend := tendsto_atTop_ciSup hmonoR hbdd
  have hsup : (⨆ s, (((g s i : ℚ) / 2 ^ s : ℚ) : ℝ)) = (m i).toReal := by
    refine le_antisymm (ciSup_le (fun s => hwle s)) ?_
    by_contra hcon
    push_neg at hcon
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hcon
    have h0 : (0 : ℝ) ≤ ⨆ s, (((g s i : ℚ) / 2 ^ s : ℚ) : ℝ) := by
      refine le_trans ?_ (le_ciSup hbdd 0)
      exact_mod_cast hw0 0
    have hr0 : (0 : ℝ) ≤ ((r : ℚ) : ℝ) := le_trans h0 hr1.le
    have hlt : ENNReal.ofReal ((r : ℚ) : ℝ) < m i := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal hr0 (hmtop i)]
      exact hr2
    rw [← hmn i] at hlt
    obtain ⟨s, hs⟩ := lt_iSup_iff.mp hlt
    have hfin : dyadicValue (g s i) s ≠ ⊤ := ne_top_of_le_ne_top (hmtop i) (hgle s i)
    have hrs : ((r : ℚ) : ℝ) < (((g s i : ℚ) / 2 ^ s : ℚ) : ℝ) := by
      rw [hwcast, ← ENNReal.ofReal_lt_iff_lt_toReal hr0 hfin]
      exact hs
    have hle2 : (((g s i : ℚ) / 2 ^ s : ℚ) : ℝ) ≤ ⨆ t, (((g t i : ℚ) / 2 ^ t : ℚ) : ℝ) :=
      le_ciSup hbdd s
    linarith
  rwa [hsup] at htend

/-- The diagonal stage sums of a non-decreasing family of non-negative rational sequences
converging point-wise to a summable real sequence tend to the sum of the series. -/
private theorem tendsto_ratStageSum_diag {P : ℕ → ℕ → ℚ} {t : ℕ → ℝ}
    (hP0 : ∀ s i, 0 ≤ P s i) (ht0 : ∀ i, 0 ≤ t i)
    (hPmono : ∀ i, Monotone (fun s => P s i))
    (hPle : ∀ s i, ((P s i : ℚ) : ℝ) ≤ t i)
    (hPtend : ∀ i, Filter.Tendsto (fun s => ((P s i : ℚ) : ℝ)) Filter.atTop (nhds (t i)))
    (htsummable : Summable t) :
    Filter.Tendsto (fun s => ((ratStageSum P s s : ℚ) : ℝ)) Filter.atTop (nhds (∑' i, t i)) := by
  have hGval : ∀ s, ratStageSum P s s = ∑ i ∈ Finset.range s, P s i := fun s => ratStageSum_eq P s s
  have hGmono : Monotone (fun s => ratStageSum P s s) := by
    refine monotone_nat_of_le_succ (fun s => ?_)
    rw [hGval, hGval, Finset.sum_range_succ]
    have h1 : ∑ i ∈ Finset.range s, P s i ≤ ∑ i ∈ Finset.range s, P (s + 1) i :=
      Finset.sum_le_sum (fun i _ => hPmono i (Nat.le_succ s))
    linarith [hP0 (s + 1) s]
  have hGleR : ∀ s, ((ratStageSum P s s : ℚ) : ℝ) ≤ ∑' i, t i := by
    intro s
    have hcast : (((∑ i ∈ Finset.range s, P s i : ℚ)) : ℝ)
        = ∑ i ∈ Finset.range s, ((P s i : ℚ) : ℝ) := by push_cast; ring
    rw [hGval, hcast]
    refine le_trans (Finset.sum_le_sum (fun i _ => hPle s i)) ?_
    exact htsummable.sum_le_tsum _ (fun i _ => ht0 i)
  have hmonoR : Monotone (fun s => ((ratStageSum P s s : ℚ) : ℝ)) := by
    intro s s' hss'
    have hm2 : ((ratStageSum P s s : ℚ) : ℝ) ≤ ((ratStageSum P s' s' : ℚ) : ℝ) := by
      exact_mod_cast hGmono hss'
    exact hm2
  have hbdd : BddAbove (Set.range (fun s => ((ratStageSum P s s : ℚ) : ℝ))) := by
    refine ⟨∑' i, t i, ?_⟩
    rintro y ⟨s, rfl⟩
    exact hGleR s
  have htend := tendsto_atTop_ciSup hmonoR hbdd
  have hsup : (⨆ s, ((ratStageSum P s s : ℚ) : ℝ)) = ∑' i, t i := by
    refine le_antisymm (ciSup_le hGleR) ?_
    have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range N, t i ≤ ⨆ s, ((ratStageSum P s s : ℚ) : ℝ) := by
      intro N
      have hfin : Filter.Tendsto (fun s => ∑ i ∈ Finset.range N, ((P s i : ℚ) : ℝ))
          Filter.atTop (nhds (∑ i ∈ Finset.range N, t i)) :=
        tendsto_finset_sum _ (fun i _ => hPtend i)
      refine le_of_tendsto hfin ?_
      filter_upwards [Filter.eventually_ge_atTop N] with s hs
      have hsub : Finset.range N ⊆ Finset.range s := fun x hx =>
        Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hs)
      have h1 : ∑ i ∈ Finset.range N, ((P s i : ℚ) : ℝ)
          ≤ ∑ i ∈ Finset.range s, ((P s i : ℚ) : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => ?_)
        exact_mod_cast hP0 s i
      have hcast : (((∑ i ∈ Finset.range s, P s i : ℚ)) : ℝ)
          = ∑ i ∈ Finset.range s, ((P s i : ℚ) : ℝ) := by push_cast; ring
      have h2 : ((ratStageSum P s s : ℚ) : ℝ) ≤ ⨆ u, ((ratStageSum P u u : ℚ) : ℝ) :=
        le_ciSup hbdd s
      rw [hGval, hcast] at h2
      linarith
    have hlim : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, t i) Filter.atTop
        (nhds (∑' i, t i)) := htsummable.hasSum.tendsto_sum_nat
    exact le_of_tendsto hlim (Filter.Eventually.of_forall hpart)
  rwa [hsup] at htend

/-- **SUV p. 160, the analytic core of Theorem 103's "vice versa" direction.**  For every
lower semicomputable real `γ` there is a positive rational `K` with `K·Ω − γ` lower
semicomputable, i.e. `γ ≼_K Ω`. -/
theorem exists_rat_isLowerSemicomputableReal_mul_omega_sub {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {γ : ℝ} (hγ : IsLowerSemicomputableReal γ) :
    ∃ K : ℚ, 0 < K ∧ IsLowerSemicomputableReal ((K : ℝ) * omegaReal m - γ) := by
  classical
  obtain ⟨a⟩ := exists_lowerApprox_of_isLowerSemicomputableReal hγ
  set v : ℕ → ℚ := fun i => a.seq (i + 1) - a.seq i with hvdef
  obtain ⟨hvc, hv0, hvsummable, hvtsum⟩ := lowerApprox_diff_tsum a
  set γ' : ℝ := γ - ((a.seq 0 : ℚ) : ℝ) with hγ'def
  have hγ'nonneg : 0 ≤ γ' := by
    have h := a.seq_lt 0
    rw [hγ'def]
    linarith
  obtain ⟨C, hCgt⟩ := exists_rat_gt γ'
  have hCposR : (0 : ℝ) < ((C : ℚ) : ℝ) := lt_of_le_of_lt hγ'nonneg hCgt
  have hCpos : (0 : ℚ) < C := by exact_mod_cast hCposR
  set qq : ℕ → ℚ := fun i => v i / C with hqqdef
  have hqqc : Computable qq := (computable_ratDivConst hCpos).comp hvc
  have hqq0 : ∀ i, 0 ≤ qq i := fun i => div_nonneg (hv0 i) hCpos.le
  have hqqsummable : Summable (fun i => ((qq i : ℚ) : ℝ)) := by
    have : (fun i => ((qq i : ℚ) : ℝ)) = fun i => ((v i : ℚ) : ℝ) / ((C : ℚ) : ℝ) := by
      funext i; simp only [hqqdef]; push_cast; ring
    rw [this]
    exact hvsummable.div_const _
  have hqqsum : (∑' i, ENNReal.ofReal ((qq i : ℚ) : ℝ)) ≤ 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by exact_mod_cast hqq0 i) hqqsummable]
    have hval : ∑' i, ((qq i : ℚ) : ℝ) = γ' / ((C : ℚ) : ℝ) := by
      have hfun : (fun i => ((qq i : ℚ) : ℝ)) = fun i => ((v i : ℚ) : ℝ) / ((C : ℚ) : ℝ) := by
        funext i; simp only [hqqdef]; push_cast; ring
      rw [hfun, tsum_div_const, hvtsum]
    rw [hval]
    refine ENNReal.ofReal_le_one.mpr ?_
    rw [div_le_one hCposR]
    exact hCgt.le
  obtain ⟨c, hc, hdom⟩ := hm.dominates (isLowerSemicomputableSemimeasureNat_ofRat hqqc hqqsum)
  have hmtop : ∀ n, m n ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top one_ne_top (le_trans (ENNReal.le_tsum n) hm.tsum_le_one)
  obtain ⟨K, hKpos, hKle⟩ := exists_rat_mul_ge_of_dominates hmtop hv0 hCpos hc hdom
  obtain ⟨A, Amono, Asup, Acomp⟩ := hm.isLowerSemicomputableSemimeasureNat.2
  set g : ℕ → ℕ → ℕ := fun s n => A s (natToBitString n) [] with hgdef
  have hmn : ∀ n : ℕ, ⨆ s, dyadicValue (g s n) s = m n := fun n => by
    simpa [hgdef] using Asup (natToBitString n) []
  have hgle : ∀ s n, dyadicValue (g s n) s ≤ m n := fun s n => by
    rw [← hmn n]
    exact le_iSup (fun t => dyadicValue (g t n) t) s
  have hgmono : ∀ n, Monotone (fun s => dyadicValue (g s n) s) := fun n =>
    monotone_nat_of_le_succ (fun s => Amono s (natToBitString n) [])
  set w : ℕ → ℕ → ℚ := fun s i => (g s i : ℚ) / 2 ^ s with hwdef
  have hwc : Computable₂ w := dyadic_stage_approx_computable Acomp
  have hwcast : ∀ s i, ((w s i : ℚ) : ℝ) = (dyadicValue (g s i) s).toReal := fun s i => by
    rw [toReal_dyadicValue]
    simp only [hwdef]
    push_cast
    ring
  have hw0 : ∀ s i, (0 : ℚ) ≤ w s i := fun s i => by positivity
  have hwle : ∀ s i, ((w s i : ℚ) : ℝ) ≤ (m i).toReal := fun s i => by
    rw [hwcast]
    exact ENNReal.toReal_mono (hmtop i) (hgle s i)
  have hwmono : ∀ i, Monotone (fun s => w s i) := by
    intro i s t hst
    have h : ((w s i : ℚ) : ℝ) ≤ ((w t i : ℚ) : ℝ) := by
      rw [hwcast, hwcast]
      exact ENNReal.toReal_mono (ne_top_of_le_ne_top (hmtop i) (hgle t i)) (hgmono i hst)
    exact_mod_cast h
  have hwtend : ∀ i, Filter.Tendsto (fun s => ((w s i : ℚ) : ℝ)) Filter.atTop
      (nhds ((m i).toReal)) := dyadic_stage_approx_tendsto hmtop g hmn hgmono hgle
  set t : ℕ → ℝ := fun i => ((K : ℚ) : ℝ) * (m i).toReal - ((v i : ℚ) : ℝ) with htdef
  have ht0 : ∀ i, 0 ≤ t i := fun i => by simp only [htdef, sub_nonneg]; exact hKle i
  have hmsummable : Summable (fun i => (m i).toReal) :=
    ENNReal.summable_toReal (omegaSum_ne_top hm)
  have hmtsum : ∑' i, (m i).toReal = omegaReal m := by
    rw [omegaReal, omegaSum]
    exact (ENNReal.tsum_toReal_eq (fun i => hmtop i)).symm
  have htsummable : Summable t := (hmsummable.mul_left _).sub hvsummable
  have httsum : ∑' i, t i = ((K : ℚ) : ℝ) * omegaReal m - γ' := by
    have h := (hmsummable.hasSum.mul_left ((K : ℚ) : ℝ)).sub hvsummable.hasSum
    rw [hmtsum, hvtsum] at h
    exact h.tsum_eq
  set P : ℕ → ℕ → ℚ := fun s i => max 0 (K * w s i - v i) with hPdef
  have hPc : Computable₂ P := by
    have hsub := Computable₂.comp computable₂_ratSub
      (Computable₂.comp computable₂_ratMul (Computable.const K) hwc)
      (hvc.comp (Computable.snd : Computable (fun z : ℕ × ℕ => z.2)))
    have h := Computable₂.comp computable₂_ratMax
      (Computable.const (0 : ℚ) : Computable (fun _ : ℕ × ℕ => (0 : ℚ))) hsub
    exact h
  have hP0 : ∀ s i, (0 : ℚ) ≤ P s i := fun s i => le_max_left _ _
  have hPmono : ∀ i, Monotone (fun s => P s i) := by
    intro i s s' hss'
    simp only [hPdef]
    refine max_le_max le_rfl ?_
    have := hwmono i hss'
    nlinarith [hKpos.le, this]
  have hPle : ∀ s i, ((P s i : ℚ) : ℝ) ≤ t i := by
    intro s i
    simp only [hPdef, htdef]
    push_cast
    refine max_le (by linarith [hKle i]) ?_
    have h1 : ((K : ℚ) : ℝ) * ((w s i : ℚ) : ℝ) ≤ ((K : ℚ) : ℝ) * (m i).toReal :=
      mul_le_mul_of_nonneg_left (hwle s i) (by exact_mod_cast hKpos.le)
    linarith
  have hPtend : ∀ i, Filter.Tendsto (fun s => ((P s i : ℚ) : ℝ)) Filter.atTop (nhds (t i)) := by
    intro i
    have hfun : (fun s => ((P s i : ℚ) : ℝ))
        = fun s => max 0 (((K : ℚ) : ℝ) * ((w s i : ℚ) : ℝ) - ((v i : ℚ) : ℝ)) := by
      funext s; simp only [hPdef]; push_cast; ring
    rw [hfun]
    have hin : Filter.Tendsto
        (fun s => ((K : ℚ) : ℝ) * ((w s i : ℚ) : ℝ) - ((v i : ℚ) : ℝ)) Filter.atTop
        (nhds (((K : ℚ) : ℝ) * (m i).toReal - ((v i : ℚ) : ℝ))) :=
      ((hwtend i).const_mul _).sub tendsto_const_nhds
    have h := (tendsto_const_nhds (x := (0 : ℝ)) (f := Filter.atTop (α := ℕ))).max hin
    have hval : max (0 : ℝ) (((K : ℚ) : ℝ) * (m i).toReal - ((v i : ℚ) : ℝ)) = t i :=
      max_eq_right (ht0 i)
    rwa [hval] at h
  set G : ℕ → ℚ := fun s => ratStageSum P s s with hGdef
  have hGc : Computable G := computable_ratStageSum_diag hPc
  have hGmono : Monotone G := by
    have hGval : ∀ s, G s = ∑ i ∈ Finset.range s, P s i := fun s => ratStageSum_eq P s s
    refine monotone_nat_of_le_succ (fun s => ?_)
    rw [hGval, hGval, Finset.sum_range_succ]
    have h1 : ∑ i ∈ Finset.range s, P s i ≤ ∑ i ∈ Finset.range s, P (s + 1) i :=
      Finset.sum_le_sum (fun i _ => hPmono i (Nat.le_succ s))
    linarith [hP0 (s + 1) s]
  have hGtend : Filter.Tendsto (fun s => ((G s : ℚ) : ℝ)) Filter.atTop (nhds (∑' i, t i)) :=
    tendsto_ratStageSum_diag hP0 ht0 hPmono hPle hPtend htsummable
  refine ⟨K, hKpos, ?_⟩
  have hlsc : IsLowerSemicomputableReal (((K : ℚ) : ℝ) * omegaReal m - γ') := ⟨G, hGc, hGmono, by
    rw [← httsum]
    exact hGtend⟩
  have hshift := hlsc.add_rat (-(a.seq 0))
  have hval : ((K : ℚ) : ℝ) * omegaReal m - γ' + ((-(a.seq 0) : ℚ) : ℝ)
      = ((K : ℚ) : ℝ) * omegaReal m - γ := by
    simp only [hγ'def]
    push_cast
    ring
  rwa [hval] at hshift

end Kolmogorov
