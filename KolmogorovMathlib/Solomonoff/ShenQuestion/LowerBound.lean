/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Solomonoff.ShenQuestion.Sanitize
import KolmogorovMathlib.MonotoneComplexity.SubSemimeasureDomination
import KolmogorovMathlib.MonotoneComplexity.SharedCoding

/-!
# The classical (known) half of Shen's question: `f(x) ≥ c · m(x)`

This file proves `exists_pos_mul_le_shenF`: for every lower semicomputable conditional
continuous semimeasure `Q` and every lower semicomputable discrete semimeasure `m` there is
a constant `c ∈ (0, ∞)` with `c · m(x) ≤ f(x)` for all `x`, where `f = shenF M Q` is Shen's
functional for the universal continuous semimeasure `M`.

The proof is the classical mixture argument.  Put on the node `z` of the binary tree the
mass

  `ρ(z) = Σ_{z ⊑ x} m(x) + Σ_{x ⊏ z} m(x) · Q(z ∖ x | x)`,

i.e. every point `x` of the discrete semimeasure ships its mass `m(x)` along the path to
`x` and then spreads it according to `Q(· | x)`.  This is `pathMixture` below, written as a
single sum `∑' x, pathWeight Q m z x` of the per-point contributions `pathWeight`.

* `pathMixture_nil` : `ρ([]) = Σ_x m(x) ≤ 1`;
* `pathMixture_coherent` : `ρ(z0) + ρ(z1) ≤ ρ(z)` — checked *termwise* in `x`;
* `isLSC_pathMixture` : `ρ` is lower semicomputable — via the library engine
  `isLSC_tsum_nsmul_of_uniform`, whose stage numerators `mixStage` are built from the
  stages `ma` of `m` and the sanitized stages `qHat qa` of `Q`.

Hence `ρ` is a lower semicomputable sub-semimeasure, so
`exists_const_mul_universalContinuousSemimeasure_ge` gives `ρ ≤ C · M` with `C ≠ ⊤`.  Since
`m(x) · Q(y | x) ≤ ρ(x y)` by construction, `c = (C + 1)⁻¹` witnesses the claim.
-/

namespace Kolmogorov
namespace Shen

open scoped ENNReal

variable {Q : BitString → BitString → ℝ≥0∞} {m : BitString → ℝ≥0∞}

/-! ### The path mixture -/

/-- The contribution of the point `x` of the discrete semimeasure `m` to the node `z`:
`m x` while `z` is still on the path to `x`, and `m x · Q(z ∖ x | x)` once `x` has been
passed. -/
noncomputable def pathWeight (Q : BitString → BitString → ℝ≥0∞) (m : BitString → ℝ≥0∞)
    (z x : BitString) : ℝ≥0∞ :=
  if z <+: x then m x else if x <+: z then m x * Q (z.drop x.length) x else 0

/-- The **path mixture** `ρ(z) = Σ_{z ⊑ x} m(x) + Σ_{x ⊏ z} m(x) · Q(z ∖ x | x)`. -/
noncomputable def pathMixture (Q : BitString → BitString → ℝ≥0∞) (m : BitString → ℝ≥0∞)
    (z : BitString) : ℝ≥0∞ :=
  ∑' x : BitString, pathWeight Q m z x

/-- The root mass of the path mixture is the total mass of `m`. -/
theorem pathMixture_nil (Q : BitString → BitString → ℝ≥0∞) (m : BitString → ℝ≥0∞) :
    pathMixture Q m [] = ∑' x : BitString, m x := by
  simp [pathMixture, pathWeight]

/-- Termwise coherence of the path mixture. -/
theorem pathWeight_coherent (hQ : IsConditionalContinuousTreeSemimeasure Q)
    (z x : BitString) :
    pathWeight Q m (z ++ [false]) x + pathWeight Q m (z ++ [true]) x ≤ pathWeight Q m z x := by
  by_cases hzx : z <+: x
  · obtain ⟨w, rfl⟩ := hzx
    cases w with
    | nil =>
      simp only [List.append_nil]
      have hnp : ∀ b : Bool, ¬ ((z ++ [b] : BitString) <+: z) := by
        intro b hb
        have := hb.length_le
        simp at this
      have hp : ∀ b : Bool, (z : BitString) <+: z ++ [b] := fun b => List.prefix_append z [b]
      have hdrop : ∀ b : Bool, (z ++ [b]).drop z.length = [b] := by intro b; simp
      have hroot : Q [] z = 1 := (hQ z).1
      have hQ2 : Q ([] ++ [false]) z + Q ([] ++ [true]) z ≤ Q [] z := (hQ z).2 []
      simp only [List.nil_append] at hQ2
      rw [pathWeight, pathWeight, pathWeight, ite_eq_right (hnp false), ite_eq_left (hp false),
        ite_eq_right (hnp true), ite_eq_left (hp true), ite_eq_left (List.prefix_rfl (l := z)),
            hdrop, hdrop]
      calc m z * Q [false] z + m z * Q [true] z
          = m z * (Q [false] z + Q [true] z) := (mul_add _ _ _).symm
        _ ≤ m z * Q [] z := mul_le_mul' le_rfl hQ2
        _ = m z := by rw [hroot, mul_one]
    | cons c w' =>
      have hcat : (z ++ c :: w' : BitString) = (z ++ [c]) ++ w' := by simp
      have hgood : (z ++ [c] : BitString) <+: z ++ c :: w' := by
        rw [hcat]; exact List.prefix_append _ _
      have hbad : ∀ b : Bool, b ≠ c → ¬ ((z ++ [b] : BitString) <+: z ++ c :: w') := by
        intro b hb hpre
        have h2 : ([b] : BitString) <+: c :: w' := (List.prefix_append_right_inj z).mp hpre
        obtain ⟨t, ht⟩ := h2
        rw [List.singleton_append, List.cons.injEq] at ht
        exact hb ht.1
      have hbad2 : ∀ b : Bool, b ≠ c → ¬ ((z ++ c :: w' : BitString) <+: z ++ [b]) := by
        intro b hb hpre
        have h2 : (c :: w' : BitString) <+: [b] := (List.prefix_append_right_inj z).mp hpre
        obtain ⟨t, ht⟩ := h2
        rw [List.cons_append, List.cons.injEq] at ht
        exact hb ht.1.symm
      have hzcw : (z : BitString) <+: z ++ c :: w' := List.prefix_append _ _
      rw [pathWeight, pathWeight, pathWeight, ite_eq_left hzcw]
      cases c with
      | false =>
        rw [ite_eq_left hgood, ite_eq_right (hbad true (by decide)),
            ite_eq_right (hbad2 true (by decide))]
        simp
      | true =>
        rw [ite_eq_right (hbad false (by decide)), ite_eq_right (hbad2 false (by decide)),
            ite_eq_left hgood]
        simp
  · by_cases hxz : x <+: z
    · have hz : ∀ b : Bool, ¬ (z ++ [b] <+: x) := by
        intro b hb
        exact hzx ((List.prefix_append z [b]).trans hb)
      have hx : ∀ b : Bool, x <+: z ++ [b] := fun b => hxz.trans (List.prefix_append z [b])
      have hlen : x.length ≤ z.length := hxz.length_le
      have hdrop : ∀ b : Bool, (z ++ [b]).drop x.length = z.drop x.length ++ [b] :=
        fun b => List.drop_append_of_le_length hlen
      simp only [pathWeight, ite_eq_right (hz false), ite_eq_right (hz true),
          ite_eq_left (hx false),
        ite_eq_left (hx true), ite_eq_right hzx, ite_eq_left hxz, hdrop]
      calc m x * Q (z.drop x.length ++ [false]) x + m x * Q (z.drop x.length ++ [true]) x
          = m x * (Q (z.drop x.length ++ [false]) x + Q (z.drop x.length ++ [true]) x) := by
            rw [mul_add]
        _ ≤ m x * Q (z.drop x.length) x := mul_le_mul' le_rfl ((hQ x).2 _)
    · have hz : ∀ b : Bool, ¬ (z ++ [b] <+: x) := by
        intro b hb
        exact hzx ((List.prefix_append z [b]).trans hb)
      have hx : ∀ b : Bool, ¬ (x <+: z ++ [b]) := by
        intro b hb
        rcases (List.prefix_concat_iff (a := b) (l₁ := x) (l₂ := z)).mp hb with h | h
        · exact hzx (h ▸ List.prefix_append z [b])
        · exact hxz h
      simp only [pathWeight, ite_eq_right (hz false), ite_eq_right (hz true),
          ite_eq_right (hx false),
        ite_eq_right (hx true), ite_eq_right hzx, ite_eq_right hxz, add_zero, le_refl]

/-- The path mixture is coherent: the two children carry at most the parent. -/
theorem pathMixture_coherent (hQ : IsConditionalContinuousTreeSemimeasure Q) (z : BitString) :
    pathMixture Q m (z ++ [false]) + pathMixture Q m (z ++ [true]) ≤ pathMixture Q m z := by
  rw [pathMixture, pathMixture, pathMixture, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun x => pathWeight_coherent hQ z x

/-- The point of the construction: the mixture already carries `m x · Q(y | x)` at `x y`. -/
theorem mul_le_pathMixture (hQ : IsConditionalContinuousTreeSemimeasure Q) (x y : BitString) :
    m x * Q y x ≤ pathMixture Q m (x ++ y) := by
  refine le_trans ?_ (ENNReal.le_tsum (f := pathWeight Q m (x ++ y)) x)
  by_cases h : (x ++ y) <+: x
  · have hy : y = [] := by
      have := h.length_le
      simpa using this
    subst hy
    simp [pathWeight, (hQ x).1]
  · rw [pathWeight, ite_eq_right h, ite_eq_left (List.prefix_append x y)]
    simp

/-! ### Lower semicomputability of the path mixture

The mixture is an infinite sum `∑' n, pathWeight Q m z (natToBitString n)` of *uniformly*
lower semicomputable functions of `z`, so the library engine `isLSC_tsum_nsmul_of_uniform`
applies once we exhibit the stage numerators.  The one subtlety is that the second branch
of `pathWeight` is a *product* of two dyadic stage values; a product of two stage-`k`
values is a stage-`2k` value, so the stage `s` uses the inner stage `k = s / 2` and the
factor `2 ^ (s % 2)` lifts the numerator from level `2 * (s / 2)` to level `s`. -/

section LSC

/-- Stage-`s` numerator of the contribution of the point `natToBitString n` to the node
`z`; the inner stage is `k = s / 2`. -/
def mixStage (ma qa : ℕ → BitString → BitString → ℕ) (n s : ℕ) (z : BitString) : ℕ :=
  if z <+: natToBitString n then
    2 ^ (s % 2) * (ma (s / 2) (natToBitString n) [] * 2 ^ (s / 2))
  else if natToBitString n <+: z then
    2 ^ (s % 2) * (ma (s / 2) (natToBitString n) [] *
      qHat qa (natToBitString n) (s / 2) (z.drop (natToBitString n).length))
  else 0

private lemma dyadicValue_eq_mul_inv_pow (n s : ℕ) :
    dyadicValue n s = (n : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ s := by
  rw [dyadicValue, ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]

private lemma cancel_alg (p q A B ik : ℝ≥0∞) (h : p * q = 1) :
    p * (A * B) * (ik * ik * q) = A * ik * (B * ik) := by
  calc p * (A * B) * (ik * ik * q) = p * q * (A * ik * (B * ik)) := by ring
    _ = A * ik * (B * ik) := by rw [h, one_mul]

private lemma dyadicValue_mul_lift (a b k d : ℕ) :
    dyadicValue (2 ^ d * (a * b)) (k + k + d) = dyadicValue a k * dyadicValue b k := by
  have hp : (2 : ℝ≥0∞) ^ d * ((2 : ℝ≥0∞)⁻¹) ^ d = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (two_ne_zero) (by norm_num), one_pow]
  rw [dyadicValue_eq_mul_inv_pow, dyadicValue_eq_mul_inv_pow, dyadicValue_eq_mul_inv_pow,
    pow_add, pow_add]
  push_cast
  exact cancel_alg _ _ _ _ _ hp

private lemma dv_lift_mul (a b s : ℕ) :
    dyadicValue (2 ^ (s % 2) * (a * b)) s = dyadicValue a (s / 2) * dyadicValue b (s / 2) := by
  obtain ⟨k, d, hd, rfl⟩ : ∃ k d, d < 2 ∧ s = k + k + d :=
    ⟨s / 2, s % 2, by omega, by omega⟩
  have hk : (k + k + d) / 2 = k := by omega
  have hm2 : (k + k + d) % 2 = d := by omega
  rw [hk, hm2]
  exact dyadicValue_mul_lift a b k d

private lemma dv_lift_pow (a s : ℕ) :
    dyadicValue (2 ^ (s % 2) * (a * 2 ^ (s / 2))) s = dyadicValue a (s / 2) := by
  rw [dv_lift_mul, dyadicValue_two_pow_self, mul_one]

/-- The dyadic value of the mixture stage, with `x = natToBitString n`: the stage weight of
`x` at the prefixes of `x`, that weight times the sanitized conditional stage below `x` at the
extensions of `x`, and `0` elsewhere. -/
lemma dyadicValue_mixStage (ma qa : ℕ → BitString → BitString → ℕ) (n s : ℕ) (z : BitString) :
    dyadicValue (mixStage ma qa n s z) s =
      if z <+: natToBitString n then dyadicValue (ma (s / 2) (natToBitString n) []) (s / 2)
      else if natToBitString n <+: z then
        dyadicValue (ma (s / 2) (natToBitString n) []) (s / 2) *
          dyadicValue (qHat qa (natToBitString n) (s / 2)
            (z.drop (natToBitString n).length)) (s / 2)
      else 0 := by
  rw [mixStage]
  split_ifs with h1 h2
  · exact dv_lift_pow _ _
  · exact dv_lift_mul _ _ _
  · simp [dyadicValue]

private lemma iSup_div_two (F : ℕ → ℝ≥0∞) : (⨆ s, F (s / 2)) = ⨆ k, F k := by
  refine le_antisymm (iSup_le fun s => le_iSup F (s / 2)) (iSup_le fun k => ?_)
  have h : 2 * k / 2 = k := by omega
  exact le_trans (le_of_eq (by rw [h])) (le_iSup (fun s => F (s / 2)) (2 * k))

private lemma iSup_mul_iSup_of_mono {f g : ℕ → ℝ≥0∞} (hf : Monotone f) (hg : Monotone g) :
    (⨆ n, f n * g n) = (⨆ n, f n) * (⨆ n, g n) := by
  refine le_antisymm (iSup_le fun n => mul_le_mul' (le_iSup f n) (le_iSup g n)) ?_
  rw [ENNReal.iSup_mul]
  refine iSup_le fun i => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun j => ?_
  exact le_trans (mul_le_mul' (hf (le_max_left i j)) (hg (le_max_right i j)))
    (le_iSup (fun n => f n * g n) (max i j))

private lemma mixStage_mono {ma qa : ℕ → BitString → BitString → ℕ}
    (hqmono : ∀ s out ctx, dyadicValue (qa s out ctx) s ≤ dyadicValue (qa (s + 1) out ctx) (s + 1))
    (hmmono : ∀ s out ctx, dyadicValue (ma s out ctx) s ≤ dyadicValue (ma (s + 1) out ctx) (s + 1))
    (n s : ℕ) (z : BitString) :
    dyadicValue (mixStage ma qa n s z) s ≤ dyadicValue (mixStage ma qa n (s + 1) z) (s + 1) := by
  have hle : s / 2 ≤ (s + 1) / 2 := by omega
  have hmv : Monotone (fun k => dyadicValue (ma k (natToBitString n) []) k) :=
    monotone_nat_of_le_succ fun k => hmmono k _ []
  have hqv : Monotone (fun k =>
      dyadicValue (qHat qa (natToBitString n) k (z.drop (natToBitString n).length)) k) :=
    monotone_nat_of_le_succ fun k => qHat_stage_mono (fun t y u => hqmono t y u) _ k _
  rw [dyadicValue_mixStage, dyadicValue_mixStage]
  split_ifs with h1 h2
  · exact hmv hle
  · exact mul_le_mul' (hmv hle) (hqv hle)
  · exact le_rfl

private lemma iSup_dyadicValue_mixStage
    (hQcont : IsConditionalContinuousTreeSemimeasure Q)
    {qa ma : ℕ → BitString → BitString → ℕ}
    (hqmono : ∀ s out ctx, dyadicValue (qa s out ctx) s ≤ dyadicValue (qa (s + 1) out ctx) (s + 1))
    (hqsup : ∀ out ctx, ⨆ s, dyadicValue (qa s out ctx) s = Q out ctx)
    (hmmono : ∀ s out ctx, dyadicValue (ma s out ctx) s ≤ dyadicValue (ma (s + 1) out ctx) (s + 1))
    (hmsup : ∀ out ctx, ⨆ s, dyadicValue (ma s out ctx) s = m out)
    (n : ℕ) (z : BitString) :
    ⨆ s, dyadicValue (mixStage ma qa n s z) s = pathWeight Q m z (natToBitString n) := by
  have hmvmono : Monotone (fun k => dyadicValue (ma k (natToBitString n) []) k) :=
    monotone_nat_of_le_succ fun k => hmmono k _ []
  have hmvsup : (⨆ k, dyadicValue (ma k (natToBitString n) []) k) = m (natToBitString n) :=
    hmsup _ []
  simp only [dyadicValue_mixStage]
  by_cases h1 : z <+: natToBitString n
  · simp only [ite_eq_left h1, pathWeight]
    exact (iSup_div_two fun k => dyadicValue (ma k (natToBitString n) []) k).trans hmvsup
  · by_cases h2 : natToBitString n <+: z
    · have hqvmono : Monotone (fun k =>
          dyadicValue (qHat qa (natToBitString n) k
            (z.drop (natToBitString n).length)) k) :=
        monotone_nat_of_le_succ fun k => qHat_stage_mono (fun t y u => hqmono t y u) _ k _
      have hqvsup : (⨆ k, dyadicValue (qHat qa (natToBitString n) k
          (z.drop (natToBitString n).length)) k)
          = Q (z.drop (natToBitString n).length) (natToBitString n) :=
        qHat_iSup hQcont (fun t y u => hqmono t y u) (fun y u => hqsup y u) _ _
      simp only [ite_eq_right h1, ite_eq_left h2, pathWeight]
      calc (⨆ s, dyadicValue (ma (s / 2) (natToBitString n) []) (s / 2) *
              dyadicValue (qHat qa (natToBitString n) (s / 2)
                (z.drop (natToBitString n).length)) (s / 2))
          = ⨆ k, dyadicValue (ma k (natToBitString n) []) k *
              dyadicValue (qHat qa (natToBitString n) k
                (z.drop (natToBitString n).length)) k :=
            iSup_div_two (fun k => dyadicValue (ma k (natToBitString n) []) k *
              dyadicValue (qHat qa (natToBitString n) k
                (z.drop (natToBitString n).length)) k)
        _ = (⨆ k, dyadicValue (ma k (natToBitString n) []) k) *
              ⨆ k, dyadicValue (qHat qa (natToBitString n) k
                (z.drop (natToBitString n).length)) k :=
            iSup_mul_iSup_of_mono hmvmono hqvmono
        _ = _ := by rw [hmvsup, hqvsup]
    · simp only [ite_eq_right h1, ite_eq_right h2, pathWeight, iSup_const]

private lemma primrec_prefixDecide {γ : Type*} [Primcodable γ] {f g : γ → BitString}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => decide (f a <+: g a) := by
  obtain ⟨_, h⟩ : PrimrecPred fun a => List.take (f a).length (g a) = f a :=
    Primrec.eq.comp (Primrec.list_take.comp (Primrec.list_length.comp hf) hg) hf
  refine h.of_eq fun a => ?_
  by_cases hh : f a <+: g a
  · have he : List.take (f a).length (g a) = f a := (List.prefix_iff_eq_take.mp hh).symm
    simp [hh, he]
  · have hne : List.take (f a).length (g a) ≠ f a := fun he =>
      hh (List.prefix_iff_eq_take.mpr he.symm)
    simp [hh, hne]

attribute [local irreducible] qHat

attribute [local irreducible] natToBitString mixStage in
private lemma computable_mixStage {ma qa : ℕ → BitString → BitString → ℕ}
    (hma : Computable fun p : ℕ × BitString × BitString => ma p.1 p.2.1 p.2.2)
    (hqa : Computable fun p : ℕ × BitString × BitString => qa p.1 p.2.1 p.2.2) :
    Computable fun p : ℕ × ℕ × BitString => mixStage ma qa p.1 p.2.1 p.2.2 := by
  have hxP : Primrec fun p : ℕ × ℕ × BitString => natToBitString p.1 :=
    primrec_natToBitString.comp Primrec.fst
  have hzP : Primrec fun p : ℕ × ℕ × BitString => p.2.2 := Primrec.snd.comp Primrec.snd
  have hx : Computable fun p : ℕ × ℕ × BitString => natToBitString p.1 := hxP.to_comp
  have hz : Computable fun p : ℕ × ℕ × BitString => p.2.2 := hzP.to_comp
  have hs : Computable fun p : ℕ × ℕ × BitString => p.2.1 := Computable.fst.comp Computable.snd
  have hk : Computable fun p : ℕ × ℕ × BitString => p.2.1 / 2 :=
    Primrec.nat_div.to_comp.comp hs (Computable.const 2)
  have hd : Computable fun p : ℕ × ℕ × BitString => p.2.1 % 2 :=
    Primrec.nat_mod.to_comp.comp hs (Computable.const 2)
  have hpowd : Computable fun p : ℕ × ℕ × BitString => 2 ^ (p.2.1 % 2) :=
    primrec_two_pow_aux.to_comp.comp hd
  have hpowk : Computable fun p : ℕ × ℕ × BitString => 2 ^ (p.2.1 / 2) :=
    primrec_two_pow_aux.to_comp.comp hk
  have hmav : Computable fun p : ℕ × ℕ × BitString =>
      ma (p.2.1 / 2) (natToBitString p.1) [] :=
    hma.comp (hk.pair (hx.pair (Computable.const [])))
  have hlen : Computable fun p : ℕ × ℕ × BitString => (natToBitString p.1).length :=
    Computable.list_length.comp hx
  have hdrop : Computable fun p : ℕ × ℕ × BitString =>
      p.2.2.drop (natToBitString p.1).length :=
    Primrec.list_drop.to_comp.comp hlen hz
  have hqv : Computable fun p : ℕ × ℕ × BitString =>
      qHat qa (natToBitString p.1) (p.2.1 / 2)
        (p.2.2.drop (natToBitString p.1).length) :=
    (qHat_computable hqa).comp (hk.pair (hdrop.pair hx))
  have hbr1 : Computable fun p : ℕ × ℕ × BitString =>
      2 ^ (p.2.1 % 2) * (ma (p.2.1 / 2) (natToBitString p.1) [] * 2 ^ (p.2.1 / 2)) :=
    Primrec.nat_mul.to_comp.comp hpowd (Primrec.nat_mul.to_comp.comp hmav hpowk)
  have hbr2 : Computable fun p : ℕ × ℕ × BitString =>
      2 ^ (p.2.1 % 2) * (ma (p.2.1 / 2) (natToBitString p.1) [] *
        qHat qa (natToBitString p.1) (p.2.1 / 2)
          (p.2.2.drop (natToBitString p.1).length)) :=
    Primrec.nat_mul.to_comp.comp hpowd (Primrec.nat_mul.to_comp.comp hmav hqv)
  have hp1 : Computable fun p : ℕ × ℕ × BitString => decide (p.2.2 <+: natToBitString p.1) :=
    (primrec_prefixDecide hzP hxP).to_comp
  have hp2 : Computable fun p : ℕ × ℕ × BitString => decide (natToBitString p.1 <+: p.2.2) :=
    (primrec_prefixDecide hxP hzP).to_comp
  refine (Computable.cond hp1 hbr1
    (Computable.cond hp2 hbr2 (Computable.const 0))).of_eq fun p => ?_
  rw [mixStage]
  by_cases h1 : p.2.2 <+: natToBitString p.1
  · simp [h1]
  · by_cases h2 : natToBitString p.1 <+: p.2.2 <;> simp [h1, h2]

/-- The path mixture is lower semicomputable. -/
theorem isLSC_pathMixture (hQ : IsLSCConditionalContinuousSemimeasure Q)
    (hm : IsLowerSemicomputableSemimeasure m) :
    IsLSC fun z (_ : BitString) => pathMixture Q m z := by
  obtain ⟨qa, hqmono, hqsup, hqcomp⟩ := hQ.2
  obtain ⟨ma, hmmono, hmsup, hmcomp⟩ := hm.2
  have hmain : IsLSC fun z (_ : BitString) =>
      ∑' n : ℕ, ((1 : ℕ) : ℝ≥0∞) * pathWeight Q m z (natToBitString n) :=
    isLSC_tsum_nsmul_of_uniform (wt := fun _ : ℕ => 1) (A := mixStage ma qa)
      (Computable.const 1) (fun n s z => mixStage_mono hqmono hmmono n s z)
      (fun n z => iSup_dyadicValue_mixStage hQ.1 hqmono hqsup hmmono hmsup n z)
      (computable_mixStage hmcomp hqcomp)
  have heq : (fun z (_ : BitString) =>
      ∑' n : ℕ, ((1 : ℕ) : ℝ≥0∞) * pathWeight Q m z (natToBitString n))
      = fun z (_ : BitString) => pathMixture Q m z := by
    funext z _
    simp only [Nat.cast_one, one_mul]
    exact tsum_comp_natToBitString (pathWeight Q m z)
  rwa [heq] at hmain

end LSC

/-! ### The lower bound -/

/-- **The known half of Shen's question**: `f(x) ≥ c · m(x)` for some `c > 0`
(mixture `ρ(z) = Σ_{z ⊑ x} m(x) + Σ_{x ⊏ z} m(x) Q(z∖x | x)`, then universality of `M`). -/
theorem exists_pos_mul_le_shenF (Q : BitString → BitString → ℝ≥0∞)
    (hQ : IsLSCConditionalContinuousSemimeasure Q)
    (m : BitString → ℝ≥0∞) (hm : IsLowerSemicomputableSemimeasure m) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ x, c * m x ≤ shenF universalContinuousSemimeasure Q x := by
  have hroot : pathMixture Q m [] ≤ 1 := by
    rw [pathMixture_nil]; exact hm.1
  obtain ⟨C, hCtop, hCle⟩ := exists_const_mul_universalContinuousSemimeasure_ge
    (f := pathMixture Q m) (fun z => pathMixture_coherent hQ.1 z) hroot
    (isLSC_pathMixture hQ hm)
  have hne0 : C + 1 ≠ 0 := by simp
  have hnetop : C + 1 ≠ ⊤ := by
    simp only [ne_eq, ENNReal.add_eq_top, not_or]
    exact ⟨hCtop, ENNReal.one_ne_top⟩
  refine ⟨(C + 1)⁻¹, ENNReal.inv_ne_zero.mpr hnetop, ENNReal.inv_ne_top.mpr hne0, fun x => ?_⟩
  refine le_shenF fun y => ?_
  calc (C + 1)⁻¹ * m x * Q y x = (C + 1)⁻¹ * (m x * Q y x) := by rw [mul_assoc]
    _ ≤ (C + 1)⁻¹ * (C * universalContinuousSemimeasure (x ++ y)) :=
        mul_le_mul' le_rfl ((mul_le_pathMixture hQ.1 x y).trans (hCle (x ++ y)))
    _ ≤ (C + 1)⁻¹ * ((C + 1) * universalContinuousSemimeasure (x ++ y)) :=
        mul_le_mul' le_rfl (mul_le_mul' (le_self_add) le_rfl)
    _ = universalContinuousSemimeasure (x ++ y) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne0 hnetop, one_mul]

end Shen
end Kolmogorov
