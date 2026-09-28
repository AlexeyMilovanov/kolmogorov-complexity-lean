



/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.ArithmeticStreamMap
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic

/-!
# The endpoints of the intervals `π_x` are not random (SUV Theorem 121, obligation (a))

SUV's proof of Theorem 121 (§5.9.1, pp. 176-177) reads a sequence `ω` as the real
number `r(ω)` that is the common point of the intervals `π_{(ω)_n}`, and disposes
of the non-injectivity of `ω ↦ r(ω)` with the parenthetical remark

> "Note that the endpoints of the segments, as well as corresponding sequences
> `x000⋯` and `x111⋯`, are not random." (p. 177)

This module proves that remark, in the form needed by
`exists_infinite_invArithMap` of `Dimension/ArithmeticStreamMap.lean`: for a
`μ`-random `w` the real `measureReal μ w` is **not a dyadic rational**, hence
`invArithMap μ` is total at `w`.

## The test

For a dyadic rational `q` the bad sequences are those whose intervals
`π_{(w)_n}` shrink onto `q`.  The cover used here is, for each level `c`,

  `U c = {w | some prefix x of w has π_x ⊆ (q - 2^{-n}, q + 2^{-n})}`,  `n = m+c+1`,

which is an *open* condition on the two endpoints of `π_x`, hence enumerable for
a computable measure by the same stage argument that makes `invArithGraph`
enumerable.  Its mass is at most the length `2·2^{-n} = 2^{-(m+c)}` of the window:
the intervals `π_x` over the prefix-minimal `x` in the cover are pairwise
disjoint subintervals of the window, so their total length -- which is their
total `μ`-mass -- is at most the window's length.  That is the whole proof; no
`König`-style compactness and no case analysis on degenerate cells is needed.

To keep every numerator a natural number the window is described in the shifted
coordinate `treeLeftEnd + 1 ∈ [1,2]`, so that `q = 0` needs no special treatment.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ## The strings whose interval sits strictly inside a dyadic window -/

/-- The strings `x` whose closed interval `π_x`, shifted by `1`, lies strictly
inside the open dyadic interval `(A/2^n, B/2^n)`.  The shift keeps all numerators
natural: `treeLeftEnd + 1` ranges over `[1,2]`. -/
def treeGapSet (μ : Measure CantorSeq) (A B n : ℕ) : Set BitString :=
  {x | (A : ℝ) / 2 ^ n < treeLeftEnd (cantorMass μ) x + 1 ∧
    treeLeftEnd (cantorMass μ) x + 1 + (cantorMass μ x).toReal < (B : ℝ) / 2 ^ n}

/-- A string in the gap set has its tree interval inside the corresponding open dyadic gap. -/
lemma treeIco_subset_Ioo_of_mem_treeGapSet {μ : Measure CantorSeq} {A B n : ℕ} {x : BitString}
    (hx : x ∈ treeGapSet μ A B n) :
    treeIco (cantorMass μ) x ⊆ Set.Ioo ((A : ℝ) / 2 ^ n - 1) ((B : ℝ) / 2 ^ n - 1) := by
  obtain ⟨h1, h2⟩ := hx
  intro r hr
  rw [treeIco, Set.mem_Ico] at hr
  exact ⟨by linarith [hr.1], by linarith [hr.2]⟩

/-- The tree interval of `x` has Lebesgue measure the cylinder mass of `x`. -/
lemma volume_treeIco_cantorMass (μ : Measure CantorSeq) [IsFiniteMeasure μ] (x : BitString) :
    volume (treeIco (cantorMass μ) x) = cantorMass μ x := by
  rw [treeIco, Real.volume_Ico, add_sub_cancel_left]
  exact ENNReal.ofReal_toReal (measure_ne_top μ _)

/-- Tree intervals start at a nonnegative point. -/
lemma treeLeftEnd_nonneg (a : BitString → ℝ≥0∞) (x : BitString) : 0 ≤ treeLeftEnd a x := by
  refine Finset.sum_nonneg fun i _ => ?_
  split
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

/-- Tree intervals end at or before one. -/
lemma treeRightEnd_le_one {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a)
    (x : BitString) : treeLeftEnd a x + (a x).toReal ≤ 1 := by
  have hmem : treeLeftEnd a x + (a x).toReal ∈ treeIcc a x :=
    Set.right_mem_Icc.2 (le_add_of_nonneg_right ENNReal.toReal_nonneg)
  have hsub := treeIcc_prefix_subset ha (List.nil_prefix (l := x)) hmem
  simpa [treeIcc, ha.1] using (Set.mem_Icc.1 hsub).2

/-- For a probability measure the tree intervals stay inside the unit interval. -/
lemma treeRightEnd_cantorMass_le_one (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (x : BitString) :
    treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal ≤ 1 :=
  treeRightEnd_le_one (isContinuousTreeSemimeasure_cantorMass μ) x

/-- The total mass of a prefix-free family of strings whose intervals all lie in
a fixed set of reals is at most the Lebesgue measure of that set. -/
lemma tsum_cantorMass_le_volume_of_antichain (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (T : Set BitString) (hanti : ∀ y ∈ T, ∀ z ∈ T, y <+: z → y = z) (A : Set ℝ)
    (hsub : ∀ x ∈ T, treeIco (cantorMass μ) x ⊆ A) :
    ∑' x : T, cantorMass μ (x : BitString) ≤ volume A := by
  have hdisj : Pairwise (Function.onFun Disjoint
      fun x : T => treeIco (cantorMass μ) (x : BitString)) := by
    intro y z hyz
    rw [Function.onFun, Set.disjoint_left]
    intro r hry hrz
    refine hyz ?_
    rcases prefix_or_prefix_of_mem_treeIco (isContinuousTreeSemimeasure_cantorMass μ) hry hrz
      with h | h
    · exact Subtype.ext (hanti _ y.2 _ z.2 h)
    · exact Subtype.ext (hanti _ z.2 _ y.2 h).symm
  calc ∑' x : T, cantorMass μ (x : BitString)
      = ∑' x : T, volume (treeIco (cantorMass μ) (x : BitString)) :=
        tsum_congr fun x => (volume_treeIco_cantorMass μ _).symm
    _ = volume (⋃ x : T, treeIco (cantorMass μ) (x : BitString)) :=
        (measure_iUnion hdisj fun _ => measurableSet_Ico).symm
    _ ≤ volume A := measure_mono (Set.iUnion_subset fun x => hsub x x.2)

/-- The total mass of a prefix-free family of strings whose intervals lie in a
fixed window is at most the length of the window. -/
lemma tsum_cantorMass_le_of_antichain (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (T : Set BitString) (hanti : ∀ y ∈ T, ∀ z ∈ T, y <+: z → y = z) {c d : ℝ}
    (hsub : ∀ x ∈ T, treeIco (cantorMass μ) x ⊆ Set.Ioo c d) :
    ∑' x : T, cantorMass μ (x : BitString) ≤ ENNReal.ofReal (d - c) := by
  rw [← Real.volume_Ioo (a := c) (b := d)]
  exact tsum_cantorMass_le_volume_of_antichain μ T hanti _ hsub

/-- The half-open variant, which is what a one-sided bound `[0, a)` or `(b, 1]`
needs. -/
lemma tsum_cantorMass_le_of_antichain_Ico (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (T : Set BitString) (hanti : ∀ y ∈ T, ∀ z ∈ T, y <+: z → y = z) {c d : ℝ}
    (hsub : ∀ x ∈ T, treeIco (cantorMass μ) x ⊆ Set.Ico c d) :
    ∑' x : T, cantorMass μ (x : BitString) ≤ ENNReal.ofReal (d - c) := by
  rw [← Real.volume_Ico (a := c) (b := d)]
  exact tsum_cantorMass_le_volume_of_antichain μ T hanti _ hsub

/-- **The mass of the window cover.**  The set of sequences having a prefix whose
interval lies inside the window `(A/2^n, B/2^n)` has `μ`-mass at most the
window's length. -/
theorem measure_prefixHitSet_treeGapSet_le (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (A B n : ℕ) :
    μ (prefixHitSet (treeGapSet μ A B n))
      ≤ ENNReal.ofReal ((B : ℝ) / 2 ^ n - (A : ℝ) / 2 ^ n) := by
  refine le_trans (measure_prefixHitSet_le_tsum_minimalPrefixElements μ _) ?_
  have h := tsum_cantorMass_le_of_antichain μ (minimalPrefixElements (treeGapSet μ A B n))
    (minimalPrefixElements_antichain _) (c := (A : ℝ) / 2 ^ n - 1) (d := (B : ℝ) / 2 ^ n - 1)
    (fun x hx => treeIco_subset_Ioo_of_mem_treeGapSet (minimalPrefixElements_subset _ hx))
  have heq : ((B : ℝ) / 2 ^ n - 1) - ((A : ℝ) / 2 ^ n - 1)
      = (B : ℝ) / 2 ^ n - (A : ℝ) / 2 ^ n := by ring
  rwa [heq] at h

/-! ## Enumerability of the window relation -/

/-- Arithmetic core: strict containment of `[L, L+M]` in `(A/2^n, B/2^n)` is
witnessed at a finite stage of any approximation with the stated error bounds.
This is `dyadic_interval_iff_exists_stage_core` with the two numerators allowed
to differ by more than one. -/
lemma dyadic_pair_iff_exists_stage_core (N A B n : ℕ) (L M : ℝ) (LA Ap : ℕ → ℕ)
    (hA : ∀ s, |(LA s : ℝ) - 2 ^ s * L| ≤ (N : ℝ))
    (hB : ∀ s, |((LA s : ℝ) + (Ap s : ℝ)) - 2 ^ s * (L + M)| ≤ (N : ℝ) + 1) :
    ((A : ℝ) / 2 ^ n < L ∧ L + M < (B : ℝ) / 2 ^ n) ↔
      ∃ s, n ≤ s ∧ A * 2 ^ (s - n) + N < LA s ∧
        LA s + Ap s + N + 1 < B * 2 ^ (s - n) := by
  have hpowsplit : ∀ s : ℕ, n ≤ s → (2 : ℝ) ^ s = 2 ^ (s - n) * 2 ^ n := by
    intro s hs
    rw [← pow_add]
    congr 1
    omega
  have hPL : ∀ s : ℕ, n ≤ s → (2 : ℝ) ^ s * ((A : ℝ) / 2 ^ n) = (A : ℝ) * 2 ^ (s - n) := by
    intro s hs
    rw [hpowsplit s hs]
    field_simp
  have hPR : ∀ s : ℕ, n ≤ s → (2 : ℝ) ^ s * ((B : ℝ) / 2 ^ n) = (B : ℝ) * 2 ^ (s - n) := by
    intro s hs
    rw [hpowsplit s hs]
    field_simp
  constructor
  · rintro ⟨h1, h2⟩
    set δ : ℝ := min (L - (A : ℝ) / 2 ^ n) ((B : ℝ) / 2 ^ n - (L + M)) with hδ
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    obtain ⟨m, hm⟩ := exists_nat_gt ((2 * (N : ℝ) + 2) / δ)
    have hmlt : (m : ℝ) ≤ 2 ^ m := by
      have hmm : m < 2 ^ m := Nat.lt_two_pow_self
      exact_mod_cast hmm.le
    set s : ℕ := max m n with hsdef
    have hsn : n ≤ s := le_max_right _ _
    have hpow : (2 : ℝ) ^ m ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
    have hApos : (0 : ℝ) < 2 ^ s := by positivity
    have hbig : 2 * (N : ℝ) + 2 < δ * 2 ^ s := by
      have h0 : (2 * (N : ℝ) + 2) / δ < 2 ^ s := lt_of_lt_of_le hm (le_trans hmlt hpow)
      calc 2 * (N : ℝ) + 2 = ((2 * (N : ℝ) + 2) / δ) * δ := by field_simp
        _ < 2 ^ s * δ := mul_lt_mul_of_pos_right h0 hδpos
        _ = δ * 2 ^ s := mul_comm _ _
    have hδ1 : δ ≤ L - (A : ℝ) / 2 ^ n := min_le_left _ _
    have hδ2 : δ ≤ (B : ℝ) / 2 ^ n - (L + M) := min_le_right _ _
    have hPLs := hPL s hsn
    have hPRs := hPR s hsn
    have hL1 : (A : ℝ) * 2 ^ (s - n) + δ * 2 ^ s ≤ 2 ^ s * L := by
      have hmul : δ * 2 ^ s ≤ (L - (A : ℝ) / 2 ^ n) * 2 ^ s :=
        mul_le_mul_of_nonneg_right hδ1 hApos.le
      have hexp : (L - (A : ℝ) / 2 ^ n) * 2 ^ s = 2 ^ s * L - (A : ℝ) * 2 ^ (s - n) := by
        rw [sub_mul, ← hPLs]; ring
      rw [hexp] at hmul
      linarith
    have hL2 : (2 : ℝ) ^ s * (L + M) ≤ (B : ℝ) * 2 ^ (s - n) - δ * 2 ^ s := by
      have hmul : δ * 2 ^ s ≤ ((B : ℝ) / 2 ^ n - (L + M)) * 2 ^ s :=
        mul_le_mul_of_nonneg_right hδ2 hApos.le
      have hexp : ((B : ℝ) / 2 ^ n - (L + M)) * 2 ^ s
          = (B : ℝ) * 2 ^ (s - n) - 2 ^ s * (L + M) := by
        rw [sub_mul, ← hPRs]; ring
      rw [hexp] at hmul
      linarith
    have hLA := hA s
    have hAB := hB s
    rw [abs_le] at hLA hAB
    refine ⟨s, hsn, ?_, ?_⟩
    · have hreal : ((A * 2 ^ (s - n) + N : ℕ) : ℝ) < ((LA s : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hreal
    · have hreal : ((LA s + Ap s + N + 1 : ℕ) : ℝ) < ((B * 2 ^ (s - n) : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hreal
  · rintro ⟨s, hsn, C1, C2⟩
    have hpos : (0 : ℝ) < 2 ^ s := by positivity
    have hC1 : (A : ℝ) * 2 ^ (s - n) + (N : ℝ) < (LA s : ℝ) := by exact_mod_cast C1
    have hC2 : (LA s : ℝ) + (Ap s : ℝ) + (N : ℝ) + 1 < (B : ℝ) * 2 ^ (s - n) := by
      exact_mod_cast C2
    have hLA := hA s
    have hAB := hB s
    rw [abs_le] at hLA hAB
    constructor
    · have h1 : (2 : ℝ) ^ s * ((A : ℝ) / 2 ^ n) < 2 ^ s * L := by
        rw [hPL s hsn]; linarith
      exact lt_of_mul_lt_mul_left h1 hpos.le
    · have h2 : (2 : ℝ) ^ s * (L + M) < 2 ^ s * ((B : ℝ) / 2 ^ n) := by
        rw [hPR s hsn]; linarith
      exact lt_of_mul_lt_mul_left h2 hpos.le

/-- The stage test of the window relation. -/
def treeGapStage (a : BitString → ℕ → ℕ) (A B n s : ℕ) (x : BitString) : Bool :=
  if s < n then false else
  let l_approx := treeLeftEndApprox a x s + 2 ^ s
  (A * 2 ^ (s - n) + x.length < l_approx) ∧ (l_approx + a x s + x.length + 1 < B * 2 ^ (s - n))

/-- With two-sided approximations of the masses, membership of the gap set is the union of its
stage tests. -/
lemma mem_treeGapSet_iff_exists_stage (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (a : BitString → ℕ → ℕ)
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (A B n : ℕ) (x : BitString) :
    x ∈ treeGapSet μ A B n ↔ ∃ s : ℕ, treeGapStage a A B n s x := by
  have hstage : ∀ s : ℕ, n ≤ s → (treeGapStage a A B n s x = true ↔
      (A * 2 ^ (s - n) + x.length < treeLeftEndApprox a x s + 2 ^ s ∧
        treeLeftEndApprox a x s + 2 ^ s + a x s + x.length + 1 < B * 2 ^ (s - n))) := by
    intro s hs
    simp [treeGapStage, Nat.not_lt.mpr hs, Nat.add_assoc]
  have hA : ∀ s : ℕ, |((treeLeftEndApprox a x s + 2 ^ s : ℕ) : ℝ)
      - 2 ^ s * (treeLeftEnd (cantorMass μ) x + 1)| ≤ (x.length : ℝ) := by
    intro s
    have h1 := abs_treeLeftEndApprox_sub_le μ ha x s
    have hrw : ((treeLeftEndApprox a x s + 2 ^ s : ℕ) : ℝ)
        - 2 ^ s * (treeLeftEnd (cantorMass μ) x + 1)
        = (treeLeftEndApprox a x s : ℝ) - 2 ^ s * treeLeftEnd (cantorMass μ) x := by
      push_cast
      ring
    rw [hrw]
    exact h1
  have hB : ∀ s : ℕ, |(((treeLeftEndApprox a x s + 2 ^ s : ℕ) : ℝ) + (a x s : ℝ))
      - 2 ^ s * ((treeLeftEnd (cantorMass μ) x + 1) + (cantorMass μ x).toReal)|
      ≤ (x.length : ℝ) + 1 := by
    intro s
    have h1 := abs_treeLeftEndApprox_sub_le μ ha x s
    have h2 := abs_approx_sub_le_one μ ha x s
    have hrw : (((treeLeftEndApprox a x s + 2 ^ s : ℕ) : ℝ) + (a x s : ℝ))
        - 2 ^ s * ((treeLeftEnd (cantorMass μ) x + 1) + (cantorMass μ x).toReal)
        = ((treeLeftEndApprox a x s : ℝ) - 2 ^ s * treeLeftEnd (cantorMass μ) x)
          + ((a x s : ℝ) - 2 ^ s * (cantorMass μ x).toReal) := by
      push_cast
      ring
    rw [hrw]
    exact le_trans (abs_add_le _ _) (by linarith)
  rw [treeGapSet, Set.mem_setOf_eq,
    dyadic_pair_iff_exists_stage_core x.length A B n
      (treeLeftEnd (cantorMass μ) x + 1) ((cantorMass μ x).toReal)
      (fun s => treeLeftEndApprox a x s + 2 ^ s) (fun s => a x s) hA hB]
  constructor
  · rintro ⟨s, hsn, C1, C2⟩
    exact ⟨s, (hstage s hsn).mpr ⟨C1, C2⟩⟩
  · rintro ⟨s, hstg⟩
    have hsn : n ≤ s := by
      by_contra hc
      push_neg at hc
      simp [treeGapStage, hc] at hstg
    obtain ⟨C1, C2⟩ := (hstage s hsn).mp hstg
    exact ⟨s, hsn, C1, C2⟩

/-- The stage test of the gap set is computable. -/
lemma computable_treeGapStage {a : BitString → ℕ → ℕ} (ha : Computable₂ a)
    {A B n : ℕ → ℕ} (hAc : Computable A) (hBc : Computable B) (hnc : Computable n) :
    Computable (fun r : (ℕ × BitString) × ℕ =>
      treeGapStage a (A r.1.1) (B r.1.1) (n r.1.1) r.2 r.1.2) := by
  have hc : Computable (fun r : (ℕ × BitString) × ℕ => r.1.1) :=
    Computable.fst.comp Computable.fst
  have hx : Computable (fun r : (ℕ × BitString) × ℕ => r.1.2) :=
    Computable.snd.comp Computable.fst
  have hs : Computable (fun r : (ℕ × BitString) × ℕ => r.2) := Computable.snd
  have hA : Computable (fun r : (ℕ × BitString) × ℕ => A r.1.1) := hAc.comp hc
  have hB : Computable (fun r : (ℕ × BitString) × ℕ => B r.1.1) := hBc.comp hc
  have hn : Computable (fun r : (ℕ × BitString) × ℕ => n r.1.1) := hnc.comp hc
  have hxlen : Computable (fun r : (ℕ × BitString) × ℕ => r.1.2.length) :=
    Computable.list_length.comp hx
  have hlt : Computable₂ (fun m n : ℕ => decide (m < n)) := primrec_decide_nat_lt.to_comp
  have hshort : Computable (fun r : (ℕ × BitString) × ℕ => decide (r.2 < n r.1.1)) :=
    hlt.comp hs hn
  have hpow : Computable (fun r : (ℕ × BitString) × ℕ => 2 ^ (r.2 - n r.1.1)) :=
    primrec_two_pow_aux.to_comp.comp (Primrec.nat_sub.to_comp.comp hs hn)
  have hpow2 : Computable (fun r : (ℕ × BitString) × ℕ => 2 ^ r.2) :=
    primrec_two_pow_aux.to_comp.comp hs
  have hAL : Computable (fun r : (ℕ × BitString) × ℕ => A r.1.1 * 2 ^ (r.2 - n r.1.1)) :=
    Primrec.nat_mul.to_comp.comp hA hpow
  have hBR : Computable (fun r : (ℕ × BitString) × ℕ => B r.1.1 * 2 ^ (r.2 - n r.1.1)) :=
    Primrec.nat_mul.to_comp.comp hB hpow
  have hla0 : Computable (fun r : (ℕ × BitString) × ℕ =>
      treeLeftEndApprox a r.1.2 r.2) := (computable_treeLeftEndApprox ha).comp hx hs
  have hla : Computable (fun r : (ℕ × BitString) × ℕ =>
      treeLeftEndApprox a r.1.2 r.2 + 2 ^ r.2) := Primrec.nat_add.to_comp.comp hla0 hpow2
  have hax : Computable (fun r : (ℕ × BitString) × ℕ => a r.1.2 r.2) := ha.comp hx hs
  have hc1 := hlt.comp (Primrec.nat_add.to_comp.comp hAL hxlen) hla
  have hc2 := hlt.comp
    (Primrec.succ.to_comp.comp (Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp hla hax) hxlen)) hBR
  have hbody := Primrec.and.to_comp.comp hc1 hc2
  refine ((Computable.cond hshort (Computable.const false) hbody)).of_eq ?_
  rintro ⟨⟨c, x⟩, s⟩
  simp only [treeGapStage]
  by_cases h : s < n c
  · simp [h]
  · simp [h, Nat.add_assoc]

/-- **The window relation is enumerable**, uniformly along any computable choice
of the three numeric parameters, for a computable probability measure. -/
theorem isRE_treeGapSet (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (hμ : IsComputableMeasure μ) {A B n : ℕ → ℕ} (hAc : Computable A) (hBc : Computable B)
    (hnc : Computable n) :
    IsRE (fun q : ℕ × BitString => q.2 ∈ treeGapSet μ (A q.1) (B q.1) (n q.1)) := by
  obtain ⟨a, ha_comp, ha⟩ := hμ
  have hstage : IsRE (fun r : (ℕ × BitString) × ℕ =>
      treeGapStage a (A r.1.1) (B r.1.1) (n r.1.1) r.2 r.1.2 = true) :=
    isRE_of_computable_bool _ (fun r => treeGapStage a (A r.1.1) (B r.1.1) (n r.1.1) r.2 r.1.2)
      (fun _ => Iff.rfl) (computable_treeGapStage ha_comp hAc hBc hnc)
  have hex : IsRE (fun q : ℕ × BitString => ∃ s : ℕ,
      treeGapStage a (A q.1) (B q.1) (n q.1) s q.2 = true) :=
    IsRE.exists_encodable (R := fun (q : ℕ × BitString) (s : ℕ) =>
      treeGapStage a (A q.1) (B q.1) (n q.1) s q.2 = true) hstage
  exact hex.of_iff fun q =>
    (mem_treeGapSet_iff_exists_stage μ a ha (A q.1) (B q.1) (n q.1) q.2).symm

/-! ## A random sequence's real is not dyadic -/

/-- The extended-nonnegative value of one half is one half. -/
lemma ofReal_inv_two : ENNReal.ofReal ((2 : ℝ)⁻¹) = (2 : ℝ≥0∞)⁻¹ := by
  rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- The extended-nonnegative value of `2 ^ -j` is `2 ^ -j`. -/
lemma ofReal_inv_two_pow (j : ℕ) : ENNReal.ofReal (((2 : ℝ)⁻¹) ^ j) = (2 : ℝ≥0∞)⁻¹ ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, pow_succ, ← ih, ← ofReal_inv_two,
        ← ENNReal.ofReal_mul (by positivity)]

/-- The arithmetic-coding real of a sequence is nonnegative. -/
lemma measureReal_nonneg (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (w : CantorSeq) :
    0 ≤ measureReal μ w := by
  have hb : BddAbove (Set.range fun n => treeLeftEnd (cantorMass μ) (cantorPrefix w n)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact treeLeftEnd_cantorMass_le_one μ _
  have h := le_ciSup hb 0
  simpa [measureReal, cantorPrefix] using h

/-- The arithmetic-coding real of a sequence is at most one. -/
lemma measureReal_le_one (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (w : CantorSeq) :
    measureReal μ w ≤ 1 :=
  ciSup_le fun _ => treeLeftEnd_cantorMass_le_one μ _

/-! ## A random sequence denotes no computable real

Both endpoint statements the source needs -- and, on either side of the
correspondence, both endpoints of every interval `π_x` -- are instances of one
lemma: if a real `E` has a computable sequence of dyadic approximations with a
*uniform* error bound, then no `ν`-random sequence denotes it.  The test is the
window family `treeGapSet ν` centred on the approximation. -/

/-- **The sequences denoting a computable real form an effectively null set.**
`app s` is a numerator whose value `app s / 2^s` approximates `E` to within
`M · 2^{-s}`, uniformly in `s`.  The cover at level `c` is the window family
`treeGapSet ν` centred on that approximation. -/
theorem isEffectivelyNull_setOf_measureReal_eq (ν : Measure CantorSeq)
    [IsProbabilityMeasure ν] (hν : IsComputableMeasure ν) (haν : ∀ u : CantorSeq, ν {u} = 0)
    (E : ℝ) (M : ℕ) (app : ℕ → ℕ) (happ : Computable app)
    (herr : ∀ s, |(app s : ℝ) - 2 ^ s * E| ≤ (M : ℝ)) :
    IsEffectivelyNull ν {w : CantorSeq | measureReal ν w = E} := by
  set sf : ℕ → ℕ := fun c => c + (2 * M + 2) with hsf
  set LAf : ℕ → ℕ := fun c => app (sf c) + 2 ^ sf c with hLAf
  set Af : ℕ → ℕ := fun c => LAf c - (M + 1) with hAf
  set Bf : ℕ → ℕ := fun c => LAf c + (M + 1) with hBf
  set S : ℕ → Set BitString := fun c => treeGapSet ν (Af c) (Bf c) (sf c) with hS
  have hsfv : ∀ c, sf c = c + (2 * M + 2) := fun _ => rfl
  have hLAfv : ∀ c, LAf c = app (sf c) + 2 ^ sf c := fun _ => rfl
  have hAfv : ∀ c, Af c = LAf c - (M + 1) := fun _ => rfl
  have hBfv : ∀ c, Bf c = LAf c + (M + 1) := fun _ => rfl
  have hNs : ∀ c, M + 1 ≤ LAf c := by
    intro c
    have h1 : M < 2 ^ M := Nat.lt_two_pow_self
    have hMle : M ≤ sf c := by rw [hsfv]; omega
    have h2 : (2 : ℕ) ^ M ≤ 2 ^ sf c := Nat.pow_le_pow_right (by norm_num) hMle
    rw [hLAfv]
    omega
  have hcastA : ∀ c, ((Af c : ℕ) : ℝ) = (app (sf c) : ℝ) + 2 ^ sf c - ((M : ℝ) + 1) := by
    intro c
    rw [hAfv, Nat.cast_sub (hNs c), hLAfv]
    push_cast
    ring
  have hcastB : ∀ c, ((Bf c : ℕ) : ℝ) = (app (sf c) : ℝ) + 2 ^ sf c + ((M : ℝ) + 1) := by
    intro c
    rw [hBfv, hLAfv]
    push_cast
    ring
  have hsfc : Computable sf :=
    Primrec.nat_add.to_comp.comp Computable.id (Computable.const (2 * M + 2))
  have hLAfc : Computable LAf :=
    Primrec.nat_add.to_comp.comp (happ.comp hsfc) (primrec_two_pow_aux.to_comp.comp hsfc)
  have hAfc : Computable Af := Primrec.nat_sub.to_comp.comp hLAfc (Computable.const (M + 1))
  have hBfc : Computable Bf := Primrec.nat_add.to_comp.comp hLAfc (Computable.const (M + 1))
  have hSRE : IsRE (fun q : ℕ × BitString => q.2 ∈ S q.1) :=
    isRE_treeGapSet ν hν hAfc hBfc hsfc
  have hmass : ∀ c : ℕ, ν (prefixHitSet (S c)) ≤ (2 : ℝ≥0∞)⁻¹ ^ c := by
    intro c
    refine le_trans (measure_prefixHitSet_treeGapSet_le ν _ _ _) ?_
    have hdiff : ((Bf c : ℕ) : ℝ) / 2 ^ sf c - ((Af c : ℕ) : ℝ) / 2 ^ sf c
        = (2 * (M : ℝ) + 2) / 2 ^ sf c := by
      rw [div_sub_div_same, hcastA c, hcastB c]
      ring
    have hsplit : ((2 : ℝ)) ^ sf c = 2 ^ c * 2 ^ (2 * M + 2) := by
      rw [hsfv, ← pow_add]
    have hle : (2 * (M : ℝ) + 2) / 2 ^ sf c ≤ ((2 : ℝ)⁻¹) ^ c := by
      have h1 : (2 * M + 2 : ℕ) < 2 ^ (2 * M + 2) := Nat.lt_two_pow_self
      have h1' : (2 * (M : ℝ) + 2) ≤ 2 ^ (2 * M + 2) := by exact_mod_cast h1.le
      rw [hsplit, inv_pow, div_le_iff₀ (by positivity)]
      have hrw : ((2 : ℝ) ^ c)⁻¹ * (2 ^ c * 2 ^ (2 * M + 2)) = 2 ^ (2 * M + 2) := by
        field_simp
      rw [hrw]
      exact h1'
    rw [hdiff, ← ofReal_inv_two_pow]
    exact ENNReal.ofReal_le_ofReal hle
  have hmem : ∀ c : ℕ, {w : CantorSeq | measureReal ν w = E} ⊆ prefixHitSet (S c) := by
    intro c w hcon
    have hL := tendsto_treeLeftEnd_measureReal ν w
    have hR := tendsto_treeRightEnd_measureReal ν (haν w)
    have habs := herr (sf c)
    rw [abs_le] at habs
    have hpow : (0 : ℝ) < 2 ^ sf c := by positivity
    have hAlt : ((Af c : ℕ) : ℝ) / 2 ^ sf c < measureReal ν w + 1 := by
      rw [hcastA c, div_lt_iff₀ hpow, hcon]
      nlinarith [habs.2]
    have hBgt : measureReal ν w + 1 < ((Bf c : ℕ) : ℝ) / 2 ^ sf c := by
      rw [hcastB c, lt_div_iff₀ hpow, hcon]
      nlinarith [habs.1]
    have e1 : ∀ᶠ j in Filter.atTop, ((Af c : ℕ) : ℝ) / 2 ^ sf c - 1
        < treeLeftEnd (cantorMass ν) (cantorPrefix w j) :=
      hL.eventually (eventually_gt_nhds (by linarith))
    have e2 : ∀ᶠ j in Filter.atTop, treeLeftEnd (cantorMass ν) (cantorPrefix w j)
        + (cantorMass ν (cantorPrefix w j)).toReal < ((Bf c : ℕ) : ℝ) / 2 ^ sf c - 1 :=
      hR.eventually (eventually_lt_nhds (by linarith))
    obtain ⟨j, hj1, hj2⟩ := (e1.and e2).exists
    refine ⟨j, ?_⟩
    have hgoal : cantorPrefix w j ∈ treeGapSet ν (Af c) (Bf c) (sf c) := by
      rw [treeGapSet, Set.mem_setOf_eq]
      constructor
      · linarith
      · linarith
    exact hgoal
  have htest := isMartinLofTest_prefixHitSet (μ := ν) hSRE hmass
  exact ⟨fun c => prefixHitSet (S c), htest.1,
    fun w hw => Set.mem_iInter.2 fun c => hmem c hw, htest.2⟩

/-- **A `ν`-random sequence denotes no computable real.**  The pointwise reading
of `isEffectivelyNull_setOf_measureReal_eq`. -/
theorem measureReal_ne_of_computable_approx (ν : Measure CantorSeq) [IsProbabilityMeasure ν]
    (hν : IsComputableMeasure ν) (haν : ∀ u : CantorSeq, ν {u} = 0)
    (E : ℝ) (M : ℕ) (app : ℕ → ℕ) (happ : Computable app)
    (herr : ∀ s, |(app s : ℝ) - 2 ^ s * E| ≤ (M : ℝ))
    {w : CantorSeq} (hw : IsMartinLofRandom ν w) :
    measureReal ν w ≠ E := by
  intro hcon
  obtain ⟨U, hU1, hU2, hU3⟩ :=
    isEffectivelyNull_setOf_measureReal_eq ν hν haν E M app happ herr
  exact hw U ⟨hU1, hU3⟩ (hU2 hcon)

end Kolmogorov
