/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity

/-!
# Domination of lower semicomputable sub-semimeasures

A *sub-semimeasure* on the binary tree is a function `f : BitString → ℝ≥0∞` whose root
value is at most one and which is superadditive along the two children,
`f (x ++ [false]) + f (x ++ [true]) ≤ f x`.  Such a function need not be a continuous
tree semimeasure in the sense of `IsContinuousTreeSemimeasure`, which normalises the root
value to exactly one, and the missing mass `1 - f []` is in general not computable.

`rootNormalize f`, which raises the root value to one and leaves the rest untouched, repairs
this defect without disturbing lower semicomputability.  Consequently the universal
continuous semimeasure dominates every lower semicomputable sub-semimeasure
(`exists_const_mul_universalContinuousSemimeasure_ge`).

The file also provides `isLSC_tsum_nsmul_of_uniform`, which builds a lower semicomputable
function as an infinite sum `∑' m, wt m * b m x` of a uniformly lower semicomputable family
with natural-number weights.
-/

namespace Kolmogorov

open scoped ENNReal
open ENNReal

/-- Raise the root value of `f` to one, leaving all other values untouched. -/
noncomputable def rootNormalize (f : BitString → ℝ≥0∞) : BitString → ℝ≥0∞ :=
  fun x => if x = [] then 1 else f x

/-- Normalising the root mass to `1` only increases the mass of every node. -/
lemma self_le_rootNormalize {f : BitString → ℝ≥0∞} (hroot : f [] ≤ 1) (x : BitString) :
    f x ≤ rootNormalize f x := by
  unfold rootNormalize
  split_ifs with hx
  · rw [hx]; exact hroot
  · exact le_rfl

/-- A coherent mass assignment with root mass at most `1` becomes a continuous tree semimeasure
after
root normalisation. -/
lemma isContinuousTreeSemimeasure_rootNormalize {f : BitString → ℝ≥0∞}
    (hcoh : ∀ x, f (x ++ [false]) + f (x ++ [true]) ≤ f x) (hroot : f [] ≤ 1) :
    IsContinuousTreeSemimeasure (rootNormalize f) := by
  refine ⟨by simp [rootNormalize], ?_⟩
  intro x
  by_cases hx : x = []
  · subst hx
    have h := hcoh []
    simp only [List.nil_append] at h
    simp only [rootNormalize]
    exact le_trans h hroot
  · have hf : ¬ (x ++ [false] : BitString) = [] := by simp
    have ht : ¬ (x ++ [true] : BitString) = [] := by simp
    simp only [rootNormalize, if_neg hf, if_neg ht, if_neg hx]
    exact hcoh x

/-- Root normalisation preserves lower semicomputability. -/
lemma isLSC_rootNormalize {f : BitString → ℝ≥0∞} (hlsc : IsLSC fun x _ => f x) :
    IsLSC fun x _ => rootNormalize f x := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hlsc
  refine ⟨fun s out ctx => if out = [] then 2 ^ s else approx s out ctx, ?_, ?_, ?_⟩
  · intro s out ctx
    by_cases h : out = []
    · simp only [if_pos h, dyadicValue_two_pow_self, le_refl]
    · simp only [if_neg h]
      exact hmono s out ctx
  · intro out ctx
    by_cases h : out = []
    · simp only [if_pos h, dyadicValue_two_pow_self, rootNormalize, iSup_const]
    · simp only [if_neg h, rootNormalize]
      exact hsup out ctx
  · have hpred : Computable (fun p : ℕ × BitString × BitString => (p.2.1.length == 0)) :=
      (Primrec.beq.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const 0)).to_comp
    have hpow : Computable (fun p : ℕ × BitString × BitString => 2 ^ p.1) :=
      (primrec_two_pow_aux.comp Primrec.fst).to_comp
    exact (Computable.cond hpred hpow hcomp).of_eq (fun p => by
      rcases p.2.1 with _ | ⟨a, l⟩ <;> simp)

/-- **Domination of lower semicomputable sub-semimeasures.** If `f` is lower semicomputable,
superadditive along children and has root value at most one, then the universal continuous
semimeasure dominates `f` up to a finite multiplicative constant. -/
theorem exists_const_mul_universalContinuousSemimeasure_ge {f : BitString → ℝ≥0∞}
    (hcoh : ∀ x, f (x ++ [false]) + f (x ++ [true]) ≤ f x) (hroot : f [] ≤ 1)
    (hlsc : IsLSC fun x _ => f x) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ x, f x ≤ c * universalContinuousSemimeasure x := by
  obtain ⟨c, hc_top, hc⟩ := universalContinuousSemimeasure_isMaximal (rootNormalize f)
    ⟨isContinuousTreeSemimeasure_rootNormalize hcoh hroot, isLSC_rootNormalize hlsc⟩
  exact ⟨c, hc_top, fun x => le_trans (self_le_rootNormalize hroot x) (hc x)⟩

/-! ### Weighted infinite sums of uniformly lower semicomputable families -/

/-- The staged numerator of a weighted infinite sum: at stage `s` only the first `s`
components contribute. -/
def weightedStage (wt : ℕ → ℕ) (A : ℕ → ℕ → BitString → ℕ) (s : ℕ) (x : BitString) : ℕ :=
  ∑ m ∈ Finset.range s, wt m * A m s x

/-- The weighted stage sum agrees with the accumulator recursion computing it, the form used to
establish computability. -/
lemma weightedStage_eq_rec (wt : ℕ → ℕ) (A : ℕ → ℕ → BitString → ℕ) (k s : ℕ)
    (x : BitString) :
    ∑ m ∈ Finset.range k, wt m * A m s x
      = Nat.rec (motive := fun _ => ℕ) 0 (fun y IH => IH + wt y * A y s x) k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]

/-- For computable weights and computable approximations the weighted stage sum is computable. -/
lemma computable_weightedStage {wt : ℕ → ℕ} {A : ℕ → ℕ → BitString → ℕ}
    (hwt : Computable wt)
    (hA : Computable fun p : ℕ × ℕ × BitString => A p.1 p.2.1 p.2.2) :
    Computable fun p : ℕ × BitString × BitString => weightedStage wt A p.1 p.2.1 := by
  have hwt' : Computable (fun r : (ℕ × BitString × BitString) × ℕ × ℕ => wt r.2.1) :=
    Computable.comp (f := wt) (g := fun r : (ℕ × BitString × BitString) × ℕ × ℕ => r.2.1)
      hwt (Computable.fst.comp Computable.snd)
  have hproj : Computable (fun r : (ℕ × BitString × BitString) × ℕ × ℕ =>
      (r.2.1, r.1.1, r.1.2.1)) :=
    (Computable.fst.comp Computable.snd).pair
      ((Computable.fst.comp Computable.fst).pair
        (Computable.fst.comp (Computable.snd.comp Computable.fst)))
  have hA' : Computable (fun r : (ℕ × BitString × BitString) × ℕ × ℕ =>
      A r.2.1 r.1.1 r.1.2.1) :=
    Computable.comp (f := fun p : ℕ × ℕ × BitString => A p.1 p.2.1 p.2.2)
      (g := fun r : (ℕ × BitString × BitString) × ℕ × ℕ => (r.2.1, r.1.1, r.1.2.1)) hA hproj
  have hmul : Computable (fun r : (ℕ × BitString × BitString) × ℕ × ℕ =>
      wt r.2.1 * A r.2.1 r.1.1 r.1.2.1) :=
    Computable₂.comp (f := fun a b : ℕ => a * b) (Primrec₂.to_comp Primrec.nat_mul) hwt' hA'
  have hadd : Computable (fun r : (ℕ × BitString × BitString) × ℕ × ℕ =>
      r.2.2 + wt r.2.1 * A r.2.1 r.1.1 r.1.2.1) :=
    Computable₂.comp (f := fun a b : ℕ => a + b) (Primrec₂.to_comp Primrec.nat_add)
      (Computable.snd.comp Computable.snd) hmul
  have hrec := Computable.nat_rec (f := fun a : ℕ × BitString × BitString => a.1)
    (g := fun _ : ℕ × BitString × BitString => (0 : ℕ))
    (h := fun (a : ℕ × BitString × BitString) (q : ℕ × ℕ) => q.2 + wt q.1 * A q.1 a.1 a.2.1)
    Computable.fst (Computable.const 0) hadd.to₂
  exact hrec.of_eq (fun p => (weightedStage_eq_rec wt A p.1 p.1 p.2.1).symm)

/-- The dyadic value of the weighted stage sum is the weighted sum of the stage values of the first
`s` components. -/
lemma dyadicValue_weightedStage (wt : ℕ → ℕ) (A : ℕ → ℕ → BitString → ℕ) (s : ℕ)
    (x : BitString) :
    dyadicValue (weightedStage wt A s x) s
      = ∑ m ∈ Finset.range s, (wt m : ℝ≥0∞) * dyadicValue (A m s x) s := by
  unfold dyadicValue weightedStage
  rw [ENNReal.div_eq_inv_mul, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [ENNReal.div_eq_inv_mul, Nat.cast_mul]
  ring

/-- The weighted stage sums increase with the stage. -/
lemma weightedStage_mono {wt : ℕ → ℕ} {A : ℕ → ℕ → BitString → ℕ}
    (hmono : ∀ m s x, dyadicValue (A m s x) s ≤ dyadicValue (A m (s + 1) x) (s + 1))
    (s : ℕ) (x : BitString) :
    dyadicValue (weightedStage wt A s x) s
      ≤ dyadicValue (weightedStage wt A (s + 1) x) (s + 1) := by
  rw [dyadicValue_weightedStage, dyadicValue_weightedStage]
  calc ∑ m ∈ Finset.range s, (wt m : ℝ≥0∞) * dyadicValue (A m s x) s
      ≤ ∑ m ∈ Finset.range s, (wt m : ℝ≥0∞) * dyadicValue (A m (s + 1) x) (s + 1) :=
        Finset.sum_le_sum (fun m _ => mul_le_mul_right (hmono m s x) _)
    _ ≤ ∑ m ∈ Finset.range (s + 1), (wt m : ℝ≥0∞) * dyadicValue (A m (s + 1) x) (s + 1) :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ s))

/-- The weighted stage sums converge upward to the weighted mixture of the approximated
semimeasures. -/
lemma iSup_dyadicValue_weightedStage {b : ℕ → BitString → ℝ≥0∞} {wt : ℕ → ℕ}
    {A : ℕ → ℕ → BitString → ℕ}
    (hmono : ∀ m s x, dyadicValue (A m s x) s ≤ dyadicValue (A m (s + 1) x) (s + 1))
    (hsup : ∀ m x, ⨆ s, dyadicValue (A m s x) s = b m x) (x : BitString) :
    ⨆ s, dyadicValue (weightedStage wt A s x) s = ∑' m, (wt m : ℝ≥0∞) * b m x := by
  have hd_mono : ∀ m, Monotone (fun s => dyadicValue (A m s x) s) := by
    intro m s₁ s₂ h
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hmono m _ x)
  refine le_antisymm ?_ ?_
  · refine iSup_le (fun s => ?_)
    rw [dyadicValue_weightedStage]
    calc ∑ m ∈ Finset.range s, (wt m : ℝ≥0∞) * dyadicValue (A m s x) s
        ≤ ∑ m ∈ Finset.range s, (wt m : ℝ≥0∞) * b m x := by
          refine Finset.sum_le_sum (fun m _ => mul_le_mul_right ?_ _)
          rw [← hsup m x]
          exact le_iSup (fun t => dyadicValue (A m t x) t) s
      _ ≤ ∑' m, (wt m : ℝ≥0∞) * b m x := ENNReal.sum_le_tsum (Finset.range s)
  · rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le (fun N => ?_)
    have hswap : ∑ m ∈ Finset.range N, (wt m : ℝ≥0∞) * b m x
        = ⨆ s, ∑ m ∈ Finset.range N, (wt m : ℝ≥0∞) * dyadicValue (A m s x) s := by
      have hb : ∀ m, (wt m : ℝ≥0∞) * b m x
          = ⨆ s, (wt m : ℝ≥0∞) * dyadicValue (A m s x) s := by
        intro m
        rw [← hsup m x, ENNReal.mul_iSup]
      simp_rw [hb]
      exact ENNReal.finsetSum_iSup (fun s₁ s₂ => ⟨max s₁ s₂, fun m =>
        ⟨mul_le_mul_right (hd_mono m (le_max_left s₁ s₂)) _,
          mul_le_mul_right (hd_mono m (le_max_right s₁ s₂)) _⟩⟩)
    rw [hswap]
    refine iSup_le (fun s => ?_)
    refine le_trans ?_ (le_iSup (fun t => dyadicValue (weightedStage wt A t x) t) (max N s))
    rw [dyadicValue_weightedStage]
    calc ∑ m ∈ Finset.range N, (wt m : ℝ≥0∞) * dyadicValue (A m s x) s
        ≤ ∑ m ∈ Finset.range N, (wt m : ℝ≥0∞)
            * dyadicValue (A m (max N s) x) (max N s) :=
          Finset.sum_le_sum (fun m _ => mul_le_mul_right (hd_mono m (le_max_right N s)) _)
      _ ≤ ∑ m ∈ Finset.range (max N s), (wt m : ℝ≥0∞)
            * dyadicValue (A m (max N s) x) (max N s) :=
          Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_left N s))

/-- A weighted infinite sum of a uniformly lower semicomputable family of functions is
lower semicomputable. -/
theorem isLSC_tsum_nsmul_of_uniform {b : ℕ → BitString → ℝ≥0∞} {wt : ℕ → ℕ}
    {A : ℕ → ℕ → BitString → ℕ} (hwt : Computable wt)
    (hmono : ∀ m s x, dyadicValue (A m s x) s ≤ dyadicValue (A m (s + 1) x) (s + 1))
    (hsup : ∀ m x, ⨆ s, dyadicValue (A m s x) s = b m x)
    (hA : Computable fun p : ℕ × ℕ × BitString => A p.1 p.2.1 p.2.2) :
    IsLSC fun x _ => ∑' m, (wt m : ℝ≥0∞) * b m x := by
  refine ⟨fun s out _ => weightedStage wt A s out, ?_, ?_, ?_⟩
  · intro s out _
    exact weightedStage_mono (wt := wt) hmono s out
  · intro out _
    exact iSup_dyadicValue_weightedStage (wt := wt) hmono hsup out
  · exact computable_weightedStage hwt hA

end Kolmogorov
