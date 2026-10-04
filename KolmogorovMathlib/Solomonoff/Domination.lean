/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.Solomonoff.Domination.IndexedMeasures
import KolmogorovMathlib.Solomonoff.Domination.KPNatUpper

/-!
# The a priori probability dominates every computable measure

Solomonoff's theorem rests on one property of the a priori probability `M`: it dominates every
computable probability measure `μ` up to a multiplicative constant, `c · μ(x) ≤ M(x)`, and the
constant can be taken to be `2^{-K(μ)-O(1)}`.

### Outline

* `exists_pos_mul_cantorMass_le_universal` (target DOM, existence form): some `c > 0` works for
  each computable `μ`. The cylinder masses of `μ` form a lower semicomputable continuous
  semimeasure (`isLowerSemicomputableContinuousSemimeasure_of_isComputableMeasure`, SUV
  Theorem 77(a)), which `M` dominates by maximality (`universalContinuousSemimeasure_isMaximal`,
  SUV Theorem 78);
* `exists_const_two_pow_KPNat_mul_cantorMass_le_universal`: one constant `C`, fixed before `μ`,
  such that every index `e` of `μ` gives `2^{-(K(e)+C)} · μ(x) ≤ M(x)`. The proof mixes the
  semimeasures read off from all indices with weights `2^{-K(e)}` and applies maximality once;
* `exists_const_two_pow_complexity_mul_cantorMass_le_universal` (target DOM, complexity form):
  the same with `K(e)` replaced by `K(μ) = computableMeasureComplexity U μ`.

The constant `C` depends only on the prefix decompressor `U` (and on the fixed choice of `M`).

The two computability inputs of the mixture live in their own modules: the uniform
sanitization of measure indices into semimeasures in `Solomonoff/Domination/IndexedMeasures.lean`,
and the upper semicomputability of `K(e)` in `Solomonoff/Domination/KPNatUpper.lean`.

Sources: Li–Vitányi (3rd ed.) §4.5 (`M(x) ≥ 2^{-K(μ)} μ(x)` up to a constant factor), Hutter
(2005) §2.4 (universality of `ξ_U`, weights `2^{-K(ν)}`), SUV Theorems 77(a) and 78.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-- **Dominance, existence form.** For every computable probability measure `μ` on Cantor space
there is a constant `c > 0` with `c · μ(Ω_x) ≤ M(x)` for all strings `x`. Item SOL-D-DOM
(target DOM); SUV Theorems 77(a) and 78, Li–Vitányi (3rd ed.) §4.5. -/
theorem exists_pos_mul_cantorMass_le_universal (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (hμ : IsComputableMeasure μ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : BitString, ENNReal.ofReal c * cantorMass μ x ≤ universalContinuousSemimeasure x := by
  have hlsc := isLowerSemicomputableContinuousSemimeasure_of_isComputableMeasure hμ
  obtain ⟨c, hc_top, hca⟩ := universalContinuousSemimeasure_isMaximal (cantorMass μ) hlsc
  have h_root := hca []
  have h_root_mass : cantorMass μ [] = 1 := by
    unfold cantorMass
    rw [cantorCylinder_nil_eq, measure_univ]
  rw [h_root_mass] at h_root
  have hc_ne_zero : c ≠ 0 := by
    rintro rfl
    have h_contra : (1 : ℝ≥0∞) ≤ 0 := by
      calc
        (1 : ℝ≥0∞) ≤ 0 * universalContinuousSemimeasure [] := h_root
        _ = 0 := zero_mul _
    have h_contra2 : (1 : ℝ≥0∞) = 0 := le_antisymm h_contra zero_le
    exact one_ne_zero h_contra2
  have c_real_pos : 0 < c.toReal := ENNReal.toReal_pos hc_ne_zero hc_top
  use (c.toReal)⁻¹
  constructor
  · exact inv_pos.mpr c_real_pos
  · intro x
    have h_x := hca x
    have h_ofReal : ENNReal.ofReal (c.toReal)⁻¹ = c⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos c_real_pos]
      rw [ENNReal.ofReal_toReal hc_top]
    rw [h_ofReal]
    have h_div : cantorMass μ x / c ≤ universalContinuousSemimeasure x :=
      ENNReal.div_le_of_le_mul' h_x
    rw [div_eq_mul_inv, mul_comm] at h_div
    exact h_div

/-- The Kraft sum of the prefix-complexity weights of all numerical indices is at most one. -/
private lemma tsum_complexityWeight_KPNat_le_one (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    (∑' e : ℕ, complexityWeight (KPNat U e)) ≤ 1 := by
  calc
    (∑' e : ℕ, complexityWeight (KPNat U e)) =
        ∑' x : BitString, complexityWeight (KPPlain U x) :=
      tsum_comp_natToBitString (fun x => complexityWeight (KPPlain U x))
    _ ≤ 1 := KPPlain_kraft_sum_le_one U hU.isPrefixDecompressor

/-- The complexity-weighted mixture, normalized to have mass one at the root. -/
private noncomputable def KPNatWeightedTreeMixture (U : Map)
    (ν : ℕ → BitString → ℝ≥0∞) (x : BitString) : ℝ≥0∞ :=
  if x = [] then 1 else ∑' e, complexityWeight (KPNat U e) * ν e x

/-- Kraft's inequality and the component tree inequalities make the normalized weighted mixture a
continuous tree semimeasure. -/
private lemma KPNatWeightedTreeMixture_isContinuousTreeSemimeasure (U : Map)
    (hU : IsOptimalPrefixConditional U) (ν : ℕ → BitString → ℝ≥0∞)
    (hν_cont : ∀ e, IsContinuousTreeSemimeasure (ν e)) :
    IsContinuousTreeSemimeasure (KPNatWeightedTreeMixture U ν) := by
  constructor
  · simp [KPNatWeightedTreeMixture]
  · intro x
    by_cases hx : x = []
    · subst x
      simp only [List.nil_append]
      simp only [KPNatWeightedTreeMixture, List.cons_ne_nil, ↓reduceIte]
      rw [← ENNReal.tsum_add]
      calc
        (∑' e, (complexityWeight (KPNat U e) * ν e [false] +
            complexityWeight (KPNat U e) * ν e [true])) =
            ∑' e, complexityWeight (KPNat U e) * (ν e [false] + ν e [true]) := by
          apply tsum_congr
          intro e
          rw [mul_add]
        _ ≤ ∑' e, complexityWeight (KPNat U e) := by
          apply ENNReal.tsum_le_tsum
          intro e
          calc
            complexityWeight (KPNat U e) * (ν e [false] + ν e [true]) ≤
                complexityWeight (KPNat U e) * ν e [] := by
              gcongr
              exact (hν_cont e).2 []
            _ = complexityWeight (KPNat U e) := by rw [(hν_cont e).1, mul_one]
        _ ≤ 1 := tsum_complexityWeight_KPNat_le_one U hU
    · simp only [KPNatWeightedTreeMixture, hx, ↓reduceIte, List.append_eq_nil_iff,
        List.cons_ne_nil, and_false]
      rw [← ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro e
      rw [← mul_add]
      gcongr
      exact (hν_cont e).2 x

/-- **From an upper-semicomputable `f` to a lower-semicomputable `2^{-f}`.** For an upper
semicomputable integer function `f` with non-increasing computable approximation `g`, the
stage-`s` numerator `2^{s - g s e}` realises the dyadic value `2^{-g s e}`, which increases to
`2^{-f e}`. This is a uniform lower-semicomputable tree family, constant in the string. -/
private lemma isUniformlyLSC_two_pow_neg_of_upperSemicomputable {f : ℕ → ℕ}
    (hf : IsUpperSemicomputableNat f) :
    IsUniformlyLowerSemicomputableTreeFamily (fun e (_ : BitString) => (2 : ℝ≥0∞)⁻¹ ^ f e) := by
  obtain ⟨g, hg_comp, hg_anti, hg_stab⟩ := hf
  have hanti : ∀ e, Antitone (fun s => g s e) := fun e =>
    antitone_nat_of_succ_le (fun s => hg_anti s e)
  have hge : ∀ e s, f e ≤ g s e := by
    intro e s
    obtain ⟨s₀, hs₀⟩ := hg_stab e
    calc f e = g (max s s₀) e := (hs₀ _ (le_max_right _ _)).symm
      _ ≤ g s e := hanti e (le_max_left _ _)
  refine ⟨fun e s _ => if g s e ≤ s then 2 ^ (s - g s e) else 0, ?_, ?_, ?_⟩
  · intro e s _
    by_cases hs : g s e ≤ s
    · have hs1 : g (s + 1) e ≤ s + 1 :=
        le_trans (hanti e (Nat.le_succ s)) (le_trans hs (Nat.le_succ s))
      simp only [hs, hs1, ite_true]
      rw [dyadicValue_two_pow_sub hs, dyadicValue_two_pow_sub hs1]
      exact pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr one_le_two)
        (hanti e (Nat.le_succ s))
    · simp only [hs, ite_false, dyadicValue_zero]
      exact zero_le
  · intro e _
    apply le_antisymm
    · refine iSup_le fun s => ?_
      by_cases hs : g s e ≤ s
      · simp only [hs, ite_true]
        rw [dyadicValue_two_pow_sub hs]
        exact pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr one_le_two) (hge e s)
      · simp only [hs, ite_false, dyadicValue_zero]
        exact zero_le
    · obtain ⟨s₀, hs₀⟩ := hg_stab e
      refine le_trans ?_ (le_iSup _ (max s₀ (f e)))
      have hgs : g (max s₀ (f e)) e = f e := hs₀ _ (le_max_left _ _)
      have hle : g (max s₀ (f e)) e ≤ max s₀ (f e) := by rw [hgs]; exact le_max_right _ _
      simp only [hle, ite_true]
      rw [dyadicValue_two_pow_sub hle, hgs]
  · have hg2 : Computable (fun p : ℕ × ℕ => g p.1 p.2) := hg_comp
    have hs : Computable (fun p : ℕ × ℕ × BitString => p.2.1) :=
      Computable.fst.comp Computable.snd
    have hgse : Computable (fun p : ℕ × ℕ × BitString => g p.2.1 p.1) :=
      hg2.comp (hs.pair Computable.fst)
    have cle : Computable (fun q : ℕ × ℕ => decide (q.1 ≤ q.2)) := by
      obtain ⟨inst, h⟩ := Primrec.nat_le
      exact (h.of_eq (fun p => by rw [Subsingleton.elim (inst p) (Nat.decLe p.1 p.2)])).to_comp
    have csub : Computable (fun q : ℕ × ℕ => q.1 - q.2) :=
      Primrec.to_comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd)
    have cpow : Computable (fun n : ℕ => 2 ^ n) := Primrec.to_comp primrec_two_pow_aux
    have hcond : Computable (fun p : ℕ × ℕ × BitString => decide (g p.2.1 p.1 ≤ p.2.1)) :=
      cle.comp (hgse.pair hs)
    have hpow : Computable (fun p : ℕ × ℕ × BitString => 2 ^ (p.2.1 - g p.2.1 p.1)) :=
      (cpow.comp (csub.comp (hs.pair hgse))).of_eq fun _ => rfl
    exact (Computable.cond hcond hpow (Computable.const 0)).of_eq
      (fun p => by rw [Bool.cond_decide])

/-- **Product closure of uniform lower-semicomputable tree families.** Running both stage
approximations at the half-stage and multiplying the numerators makes the stage-`S` dyadic value
the product of the two half-stage values, which converges to the product of the limits. -/
private lemma IsUniformlyLowerSemicomputableTreeFamily.mul {f g : ℕ → BitString → ℝ≥0∞}
    (hf : IsUniformlyLowerSemicomputableTreeFamily f)
    (hg : IsUniformlyLowerSemicomputableTreeFamily g) :
    IsUniformlyLowerSemicomputableTreeFamily (fun e x => f e x * g e x) := by
  obtain ⟨qf, hqf_mono, hqf_sup, hqf_comp⟩ := hf
  obtain ⟨qg, hqg_mono, hqg_sup, hqg_comp⟩ := hg
  have dmul : ∀ (m n s p : ℕ),
      dyadicValue m s * dyadicValue n p = dyadicValue (m * n) (s + p) := by
    intro m n s p
    rw [dyadicValue_eq_mul_inv_pow, dyadicValue_eq_mul_inv_pow, dyadicValue_eq_mul_inv_pow,
      pow_add]
    push_cast; ring
  have hF : ∀ e x, Monotone (fun m => dyadicValue (qf e m x) m) := fun e x =>
    monotone_nat_of_le_succ (fun m => hqf_mono e m x)
  have hG : ∀ e x, Monotone (fun m => dyadicValue (qg e m x) m) := fun e x =>
    monotone_nat_of_le_succ (fun m => hqg_mono e m x)
  have hval : ∀ e x T,
      dyadicValue (qf e (T / 2) x * qg e (T / 2) x * 2 ^ (T - 2 * (T / 2))) T
        = dyadicValue (qf e (T / 2) x) (T / 2) * dyadicValue (qg e (T / 2) x) (T / 2) := by
    intro e x T
    set m := T / 2 with hm
    set δ := T - 2 * m with hδ
    have hTmδ : 2 * m + δ = T := by omega
    rw [mul_comm (qf e m x * qg e m x) (2 ^ δ), ← hTmδ, dyadicValue_two_pow_mul_add,
      two_mul m, dmul]
  refine ⟨fun e S x => qf e (S / 2) x * qg e (S / 2) x * 2 ^ (S - 2 * (S / 2)), ?_, ?_, ?_⟩
  · intro e S x
    rw [hval e x S, hval e x (S + 1)]
    exact mul_le_mul' (hF e x (Nat.div_le_div_right (Nat.le_succ S)))
      (hG e x (Nat.div_le_div_right (Nat.le_succ S)))
  · intro e x
    change (⨆ S, dyadicValue (qf e (S / 2) x * qg e (S / 2) x * 2 ^ (S - 2 * (S / 2))) S)
      = f e x * g e x
    simp only [hval e x]
    rw [← hqf_sup e x, ← hqg_sup e x]
    apply le_antisymm
    · exact iSup_le fun S => mul_le_mul'
        (le_iSup (fun m => dyadicValue (qf e m x) m) (S / 2))
        (le_iSup (fun m => dyadicValue (qg e m x) m) (S / 2))
    · rw [ENNReal.iSup_mul]
      refine iSup_le fun m => ?_
      rw [ENNReal.mul_iSup]
      refine iSup_le fun n => ?_
      refine le_trans ?_ (le_iSup
        (fun S => dyadicValue (qf e (S / 2) x) (S / 2) * dyadicValue (qg e (S / 2) x) (S / 2))
        (2 * max m n))
      rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      exact mul_le_mul' (hF e x (le_max_left m n)) (hG e x (le_max_right m n))
  · have cmul : Computable (fun q : ℕ × ℕ => q.1 * q.2) :=
      Primrec.to_comp (Primrec.nat_mul.comp Primrec.fst Primrec.snd)
    have csub : Computable (fun q : ℕ × ℕ => q.1 - q.2) :=
      Primrec.to_comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd)
    have cdiv2 : Computable (fun n : ℕ => n / 2) :=
      Primrec.to_comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
    have cpow : Computable (fun n : ℕ => 2 ^ n) := Primrec.to_comp primrec_two_pow_aux
    have hS : Computable (fun p : ℕ × ℕ × BitString => p.2.1) := Computable.fst.comp Computable.snd
    have hdiv : Computable (fun p : ℕ × ℕ × BitString => p.2.1 / 2) := cdiv2.comp hS
    have hhalf : Computable (fun p : ℕ × ℕ × BitString => (p.1, p.2.1 / 2, p.2.2)) :=
      Computable.fst.pair (hdiv.pair (Computable.snd.comp Computable.snd))
    have hqf' : Computable (fun p : ℕ × ℕ × BitString => qf p.1 (p.2.1 / 2) p.2.2) :=
      (hqf_comp.comp hhalf).of_eq fun _ => rfl
    have hqg' : Computable (fun p : ℕ × ℕ × BitString => qg p.1 (p.2.1 / 2) p.2.2) :=
      (hqg_comp.comp hhalf).of_eq fun _ => rfl
    have hsub : Computable (fun p : ℕ × ℕ × BitString => p.2.1 - 2 * (p.2.1 / 2)) :=
      csub.comp (hS.pair (cmul.comp ((Computable.const 2).pair hdiv)))
    have hδpow : Computable (fun p : ℕ × ℕ × BitString => 2 ^ (p.2.1 - 2 * (p.2.1 / 2))) :=
      cpow.comp hsub
    exact cmul.comp ((cmul.comp (hqf'.pair hqg')).pair hδpow)

/-- **Lower semicomputability of the root-normalised countable sum.** Fold each component's weight
into the fixed dyadic mixture and override the empty string with the constant `1`; the override is
a computable branch, constant in the stage. -/
private lemma isLSC_rootOne_tsum_of_uniform (g : ℕ → BitString → ℝ≥0∞)
    (hg : IsUniformlyLowerSemicomputableTreeFamily g) :
    IsLSC (fun x (_ : BitString) => if x = [] then 1 else ∑' e, g e x) := by
  obtain ⟨q, hq_mono, hq_sup, hq_comp⟩ := hg
  have hcast : ∀ i : ℕ, ((2 ^ (i + 1) : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (i + 1) := by
    intro i; push_cast; ring
  have hval : ∀ i s out, dyadicValue (q i s out * 2 ^ (i + 1)) s
      = (2 : ℝ≥0∞) ^ (i + 1) * dyadicValue (q i s out) s := by
    intro i s out
    rw [mul_comm (q i s out) (2 ^ (i + 1)), dyadicValue_natCast_mul_left, hcast]
  have ha_mono : ∀ (i s : ℕ) (out ctx : BitString),
      dyadicValue ((fun i s out (_ : BitString) => q i s out * 2 ^ (i + 1)) i s out ctx) s
        ≤ dyadicValue ((fun i s out (_ : BitString) => q i s out * 2 ^ (i + 1))
            i (s + 1) out ctx) (s + 1) := by
    intro i s out _
    simp only
    rw [hval, hval]
    exact mul_le_mul' le_rfl (hq_mono i s out)
  have ha_sup : ∀ (i : ℕ) (out ctx : BitString),
      ⨆ s, dyadicValue ((fun i s out (_ : BitString) => q i s out * 2 ^ (i + 1)) i s out ctx) s
        = (fun i out (_ : BitString) => (2 : ℝ≥0∞) ^ (i + 1) * g i out) i out ctx := by
    intro i out _
    simp only [hval]
    rw [← ENNReal.mul_iSup, hq_sup i out]
  have ha_comp : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      (fun i s out (_ : BitString) => q i s out * 2 ^ (i + 1)) p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    have hproj : Computable (fun p : ℕ × ℕ × BitString × BitString => (p.1, p.2.1, p.2.2.1)) :=
      Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))
    have hA := hq_comp.comp hproj
    have hpow : Computable (fun p : ℕ × ℕ × BitString × BitString => (2 ^ (p.1 + 1) : ℕ)) :=
      (primrec_two_pow_aux.comp (Primrec.succ.comp Primrec.fst)).to_comp
    exact Primrec.nat_mul.to_comp.comp hA hpow
  have hA : IsLSC (fun out (_ : BitString) => ∑' e, g e out) := by
    have engine := isLSC_unaryMixture_dyadicWeight_of_uniform
      (fun i out (_ : BitString) => (2 : ℝ≥0∞) ^ (i + 1) * g i out)
      (fun i s out (_ : BitString) => q i s out * 2 ^ (i + 1)) ha_mono ha_sup ha_comp
    have hfun : (fun out (_ : BitString) => ∑' e, g e out)
        = (fun out (_ : BitString) =>
            ∑' i, dyadicWeight i * ((2 : ℝ≥0∞) ^ (i + 1) * g i out)) := by
      funext out _
      refine tsum_congr fun i => ?_
      rw [dyadicWeight, ← mul_assoc, ← mul_pow,
        ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]
    rw [hfun]
    exact engine
  obtain ⟨A, hA_mono, hA_sup, hA_comp⟩ := hA
  refine ⟨fun s x _ => if x = [] then 2 ^ s else A s x [], ?_, ?_, ?_⟩
  · intro s x _
    by_cases hx : x = []
    · subst hx; simp [dyadicValue_two_pow_eq_one]
    · simp only [ite_eq_right hx]; exact hA_mono s x []
  · intro x _
    by_cases hx : x = []
    · subst hx; simp [dyadicValue_two_pow_eq_one]
    · simp only [ite_eq_right hx]; exact hA_sup x []
  · have hpred : Computable (fun p : ℕ × BitString × BitString => decide (p.2.1 = [])) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp
        (Computable.fst.comp Computable.snd) (Computable.const [])
    have hpow2 : Computable (fun p : ℕ × BitString × BitString => (2 : ℕ) ^ p.1) :=
      primrec_two_pow_aux.to_comp.comp Computable.fst
    have hAcomp' : Computable (fun p : ℕ × BitString × BitString => A p.1 p.2.1 []) :=
      hA_comp.comp (Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
        (Computable.const [])))
    exact (Computable.cond hpred hpow2 hAcomp').of_eq
      (fun p => by by_cases h : p.2.1 = [] <;> simp [h])

/-- Upper approximations to `K(e)` and uniform lower approximations to the components enumerate the
complexity-weighted mixture from below. -/
private lemma KPNatWeightedTreeMixture_isLSC (U : Map)
    (hU : IsOptimalPrefixConditional U) (ν : ℕ → BitString → ℝ≥0∞)
    (hν_lsc : IsUniformlyLowerSemicomputableTreeFamily ν) :
    IsLSC (fun x _ => KPNatWeightedTreeMixture U ν x) := by
  have hKtop : ∀ e, KPNat U e ≠ ⊤ := by
    intro e
    obtain ⟨d, hd⟩ := KPPlain_le_length_add_log U hU
    have h_ne : ((natToBitString e).length +
        2 * (Nat.bits (natToBitString e).length).length + (d : ENat) : ENat) ≠ ⊤ :=
      ENat.natCast_ne_top _
    rw [KPNat_def]
    exact ne_top_of_le_ne_top h_ne (hd (natToBitString e))
  have hW : IsUniformlyLowerSemicomputableTreeFamily
      (fun e (_ : BitString) => complexityWeight (KPNat U e)) := by
    have hbridge := isUniformlyLSC_two_pow_neg_of_upperSemicomputable
      (isUpperSemicomputableNat_KPNat_toNat U hU)
    have heq : (fun e (_ : BitString) => (2 : ℝ≥0∞)⁻¹ ^ (KPNat U e).toNat)
        = (fun e (_ : BitString) => complexityWeight (KPNat U e)) := by
      funext e _
      rw [← complexityWeight_coe, ENat.natCast_toNat (hKtop e)]
    rwa [heq] at hbridge
  have hprod := hW.mul hν_lsc
  have hlsc := isLSC_rootOne_tsum_of_uniform _ hprod
  have hfun : (fun x (_ : BitString) => KPNatWeightedTreeMixture U ν x)
      = (fun x (_ : BitString) =>
          if x = [] then (1 : ℝ≥0∞) else ∑' e, complexityWeight (KPNat U e) * ν e x) := by
    funext x _; rw [KPNatWeightedTreeMixture]
  rw [hfun]
  exact hlsc

/-- The weighted mixture contains every component with its prefix-complexity weight. -/
private lemma KPNatWeightedTreeMixture_dominates_component (U : Map)
    (ν : ℕ → BitString → ℝ≥0∞) (hν_cont : ∀ e, IsContinuousTreeSemimeasure (ν e))
    (e : ℕ) (x : BitString) :
    complexityWeight (KPNat U e) * ν e x ≤ KPNatWeightedTreeMixture U ν x := by
  by_cases hx : x = []
  · subst x
    rw [(hν_cont e).1, mul_one]
    simpa [KPNatWeightedTreeMixture] using complexityWeight_le_one (KPNat U e)
  · rw [KPNatWeightedTreeMixture, ite_eq_right hx]
    exact ENNReal.le_tsum (f := fun e => complexityWeight (KPNat U e) * ν e x) e

/-- Applying maximality once to the weighted mixture turns its finite multiplicative loss into a
single additive constant in every prefix-complexity exponent. -/
private lemma exists_const_of_KPNat_weighted_continuousSemimeasure (U : Map)
    (hU : IsOptimalPrefixConditional U) (ν : ℕ → BitString → ℝ≥0∞)
    (ξ : BitString → ℝ≥0∞) (hξ : IsLowerSemicomputableContinuousSemimeasure ξ)
    (hcomponent : ∀ e x, complexityWeight (KPNat U e) * ν e x ≤ ξ x) :
    ∃ C : ℕ, ∀ e x,
      (2 : ℝ≥0∞)⁻¹ ^ ((KPNat U e).toNat + C) * ν e x ≤
        universalContinuousSemimeasure x := by
  obtain ⟨c, hc_top, hc⟩ := universalContinuousSemimeasure_isMaximal ξ hξ
  obtain ⟨C, hC⟩ :=
    pow_unbounded_of_one_lt c.toReal (by norm_num : (1 : ℝ) < 2)
  have hc_pow : c ≤ (2 : ℝ≥0∞) ^ C := by
    rw [← ENNReal.toReal_le_toReal hc_top (ENNReal.pow_ne_top (by norm_num))]
    simpa using hC.le
  have hscale : (2 : ℝ≥0∞)⁻¹ ^ C * c ≤ 1 := by
    calc
      (2 : ℝ≥0∞)⁻¹ ^ C * c ≤ (2 : ℝ≥0∞)⁻¹ ^ C * (2 : ℝ≥0∞) ^ C := by
        gcongr
      _ = 1 := by
        rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  use C
  intro e x
  have hK_top : KPNat U e ≠ ⊤ := by
    obtain ⟨d, hd⟩ := KPPlain_le_length_add_log U hU
    have h_ne : ((natToBitString e).length +
        2 * (Nat.bits (natToBitString e).length).length + (d : ENat) : ENat) ≠ ⊤ := by
      exact ENat.natCast_ne_top _
    rw [KPNat_def]
    exact ne_top_of_le_ne_top h_ne (hd (natToBitString e))
  have hweight : complexityWeight (KPNat U e) =
      (2 : ℝ≥0∞)⁻¹ ^ (KPNat U e).toNat := by
    rw [← complexityWeight_coe, ENat.natCast_toNat hK_top]
  calc
    (2 : ℝ≥0∞)⁻¹ ^ ((KPNat U e).toNat + C) * ν e x =
        (2 : ℝ≥0∞)⁻¹ ^ C * (complexityWeight (KPNat U e) * ν e x) := by
      rw [hweight, pow_add]
      ac_rfl
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ C * ξ x := by gcongr; exact hcomponent e x
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ C * (c * universalContinuousSemimeasure x) := by
      gcongr
      exact hc x
    _ = ((2 : ℝ≥0∞)⁻¹ ^ C * c) * universalContinuousSemimeasure x := by
      rw [mul_assoc]
    _ ≤ 1 * universalContinuousSemimeasure x := by gcongr
    _ = universalContinuousSemimeasure x := one_mul _

/-- **Dominance through an index.** There is a constant `C`, quantified before the measure, such
that for every computable probability measure `μ`, every index `e` of `μ` and every string `x`,
`2^{-(K(e)+C)} · μ(Ω_x) ≤ M(x)`, where `K(e) = KPNat U e`. Item SOL-D-DOM-INDEX;
Li–Vitányi (3rd ed.) §4.5, Hutter (2005) §2.4. -/
theorem exists_const_two_pow_KPNat_mul_cantorMass_le_universal (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (e : ℕ),
      IsComputableMeasureIndex μ e → ∀ x : BitString,
        (2 : ℝ≥0∞)⁻¹ ^ ((KPNat U e).toNat + C) * cantorMass μ x ≤
          universalContinuousSemimeasure x := by
  obtain ⟨ν, hν_cont, hν_lsc, hν_index⟩ :=
    exists_uniform_indexed_continuousSemimeasure
  let ξ := KPNatWeightedTreeMixture U ν
  have hξ : IsLowerSemicomputableContinuousSemimeasure ξ := by
    exact ⟨KPNatWeightedTreeMixture_isContinuousTreeSemimeasure U hU ν hν_cont,
      KPNatWeightedTreeMixture_isLSC U hU ν hν_lsc⟩
  have hcomponent : ∀ e x, complexityWeight (KPNat U e) * ν e x ≤ ξ x :=
    KPNatWeightedTreeMixture_dominates_component U ν hν_cont
  obtain ⟨C, hC⟩ :=
    exists_const_of_KPNat_weighted_continuousSemimeasure U hU ν ξ hξ hcomponent
  use C
  intro μ _ e he x
  rw [← hν_index μ e he]
  exact hC e x

/-- **Dominance, complexity form.** There is a constant `C`, quantified before the measure, such
that every computable probability measure `μ` satisfies `2^{-(K(μ)+C)} · μ(Ω_x) ≤ M(x)` for all
strings `x`, where `K(μ) = computableMeasureComplexity U μ` (finite by
`computableMeasureComplexity_ne_top`). Item SOL-D-DOM-K (target DOM); Li–Vitányi (3rd ed.) §4.5
and the proof of Theorem 5.2.1, Hutter (2005) §2.4. -/
theorem exists_const_two_pow_complexity_mul_cantorMass_le_universal (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (μ : Measure CantorSeq) [IsProbabilityMeasure μ], IsComputableMeasure μ →
      ∀ x : BitString,
        (2 : ℝ≥0∞)⁻¹ ^ ((computableMeasureComplexity U μ).toNat + C) * cantorMass μ x ≤
          universalContinuousSemimeasure x := by
  obtain ⟨C, hC⟩ := exists_const_two_pow_KPNat_mul_cantorMass_le_universal U hU
  use C
  intro μ _ h_comp x
  obtain ⟨e, he_comp, he_eq⟩ := exists_index_KPNat_eq_computableMeasureComplexity U h_comp
  have h_bound := hC μ e he_comp x
  have h_toNat_eq : (KPNat U e).toNat = (computableMeasureComplexity U μ).toNat := by
    rw [he_eq]
  rw [← h_toNat_eq]
  exact h_bound

end Kolmogorov
