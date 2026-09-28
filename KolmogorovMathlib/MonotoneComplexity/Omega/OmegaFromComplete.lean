/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic.DiracSemimeasure
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic

/-!
# Rebuilding a maximal semimeasure with a prescribed sum (SUV Theorem 103, p. 160)

This module proves the construction behind the forward direction of SUV Theorem 103:
"Dividing `m` by `c` and then adding `τ` to one of the values, we get a universal
semimeasure with sum `α`."

Given a maximal lower semicomputable semimeasure `m`, a positive integer `c` with
`Ω ≤ c·α ≤ c`, and the lower semicomputability of `c·α − Ω`, the function

  `M n = m n / c + (if n = 0 then (c·α − Ω)/c else 0)`

is again a maximal lower semicomputable semimeasure, and its sum is exactly `α`.  Its
`IsLSC` datum is assembled from the dyadic floors of the rationals `A(s,n)/(2^s·c)`
(monotone by `dyadicValue_ratDyadicFloor_mono_of_le`) and from the dyadic approximation
of `(c·α − Ω)/c` supplied by the proved bridge `isLowerSemicomputableReal_iff_ofReal`.

Everything here is proved; the module renders no statement of the source.
-/

namespace Kolmogorov


open ComputableReals
open ENNReal

/-- Doubling the numerator `a` at level `s` is at most `b` at level `s+1` if their dyadic values
are ordered. -/
private lemma double_le_of_dyadicValue_le (a b s : ℕ)
    (h : dyadicValue a s ≤ dyadicValue b (s + 1)) :
    2 * a ≤ b := by
  rw [dyadicValue, dyadicValue] at h
  have h2 : (a : ℝ) / 2 ^ s ≤ (b : ℝ) / 2 ^ (s + 1) := by
    have hL : ((a : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s).toReal = (a : ℝ) / 2 ^ s := by
      rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
      norm_num
    have hR : ((b : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (s + 1)).toReal = (b : ℝ) / 2 ^ (s + 1) := by
      rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
      norm_num
    have hne1 : ((a : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s) ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)
    have hne2 : ((b : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (s + 1)) ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)
    have := (ENNReal.toReal_le_toReal hne1 hne2).2 h
    rwa [hL, hR] at this
  have hp1 : (0 : ℝ) < 2 ^ (s + 1) := by positivity
  have h3 : (2 : ℝ) * (a : ℝ) ≤ (b : ℝ) := by
    have key : ((a : ℝ) / 2 ^ s) * 2 ^ (s + 1) ≤ ((b : ℝ) / 2 ^ (s + 1)) * 2 ^ (s + 1) :=
      mul_le_mul_of_nonneg_right h2 hp1.le
    rw [div_mul_cancel₀ (b : ℝ) hp1.ne'] at key
    have heq : ((a : ℝ) / 2 ^ s) * 2 ^ (s + 1) = 2 * (a : ℝ) := by
      rw [pow_succ]
      field_simp
    rwa [heq] at key
  exact_mod_cast h3

/-- Scaling a dyadic rational approximation sequence by `c` preserves monotonicity. -/
private lemma scaled_dyadic_rat_mono (A : ℕ → BitString → BitString → ℕ)
    (hAmono2 : ∀ s bs ctx, 2 * A s bs ctx ≤ A (s + 1) bs ctx) (c : ℕ) (s : ℕ) (bs ctx : BitString) :
    ((A s bs ctx : ℚ) / 2 ^ s) / (c : ℚ) ≤ ((A (s + 1) bs ctx : ℚ) / 2 ^ (s + 1)) / (c : ℚ) := by
  have hq : (2 : ℚ) * (A s bs ctx : ℚ) ≤ (A (s + 1) bs ctx : ℚ) := by
    exact_mod_cast hAmono2 s bs ctx
  have h1 : (A s bs ctx : ℚ) / 2 ^ s = (2 * (A s bs ctx : ℚ)) / 2 ^ (s + 1) := by
    rw [pow_succ]
    field_simp
  rw [h1]
  gcongr

/-- The `ENNReal.ofReal` of a scaled rational dyadic approximation equals the dyadic value
divided by `c`. -/
private lemma ofReal_scaled_dyadic_rat_eq (a c s : ℕ) (hc : 0 < c) :
    ENNReal.ofReal (((((a : ℚ) / 2 ^ s) / (c : ℚ)) : ℚ) : ℝ)
      = dyadicValue a s / (c : ℝ≥0∞) := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hcast : (((((a : ℚ) / 2 ^ s) / (c : ℚ)) : ℚ) : ℝ) = ((a : ℝ) / 2 ^ s) / (c : ℝ) := by
    push_cast; ring
  rw [hcast, ENNReal.ofReal_div_of_pos hcR, ENNReal.ofReal_natCast,
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num)]
  norm_num [dyadicValue]

/-- The total mass of the scaled semimeasure plus parameter `τ` equals `α`. -/
private lemma toReal_tsum_rebuilt_semimeasure {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    {α τ : ℝ} {c : ℕ} (hc : 0 < c) (hτ0 : 0 ≤ τ)
    (hτdef : τ = ((c : ℝ) * α - omegaReal m) / (c : ℝ)) :
    (∑' n, (m n / (c : ℝ≥0∞) + (if n = 0 then ENNReal.ofReal τ else 0))).toReal = α := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hcE : (0 : ℝ≥0∞) < (c : ℝ≥0∞) := by exact_mod_cast hc
  have h1 : (∑' n, m n / (c : ℝ≥0∞)) = omegaSum m / (c : ℝ≥0∞) := by
    simp only [ENNReal.div_eq_inv_mul]
    rw [ENNReal.tsum_mul_left, omegaSum]
  have h2 : (∑' n : ℕ, (if n = 0 then ENNReal.ofReal τ else 0)) = ENNReal.ofReal τ := by
    simp
  have htsum : (∑' n, (m n / (c : ℝ≥0∞) + (if n = 0 then ENNReal.ofReal τ else 0)))
      = omegaSum m / (c : ℝ≥0∞) + ENNReal.ofReal τ := by
    rw [ENNReal.tsum_add, h1, h2]
  rw [htsum, ENNReal.toReal_add (ENNReal.div_ne_top (omegaSum_ne_top hm) hcE.ne')
    ENNReal.ofReal_ne_top, ENNReal.toReal_div, ENNReal.toReal_ofReal hτ0,
    ENNReal.toReal_natCast, hτdef, ← omegaReal]
  field_simp
  ring

/-- The rational family `xq` is the stagewise scaling of the enumeration `A` by the factor `c`:
it increases with the stage and its value at stage `s` is the dyadic value of `A` divided
by `c`. -/
private def ScalesBy (xq : ℕ → BitString → BitString → ℚ)
    (A : ℕ → BitString → BitString → ℕ) (c : ℕ) : Prop :=
  (∀ s bs ctx, xq s bs ctx ≤ xq (s + 1) bs ctx) ∧
    ∀ s bs ctx, ENNReal.ofReal ((xq s bs ctx : ℚ) : ℝ)
      = dyadicValue (A s bs ctx) s / (c : ℝ≥0∞)

/-- The supremum over $s$ of the ratDyadicFloor of a scaled sequence equals $m(x)/c$. -/
private lemma iSup_dyadicValue_ratDyadicFloor_scaled {m : ℕ → ℝ≥0∞} {c : ℕ}
    {A : ℕ → BitString → BitString → ℕ}
    (Asup : ∀ bs ctx, (⨆ s, dyadicValue (A s bs ctx) s) = m (bitStringToNat bs))
    (xq : ℕ → BitString → BitString → ℚ) (hxq : ScalesBy xq A c)
    (bs ctx : BitString) :
    (⨆ s, dyadicValue (ratDyadicFloor (xq s bs ctx) s) s) = m (bitStringToNat bs) / (c : ℝ≥0∞) := by
  obtain ⟨hxqmono, hxqval⟩ := hxq
  have hdy : ∀ s : ℕ, dyadicValue (ratDyadicFloor (xq s bs ctx) s) s
      = (ratDyadicFloor (xq s bs ctx) s : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s := fun s => by rw [dyadicValue]
  rw [iSup_congr hdy,
    iSup_ratDyadicFloor_of_monotone (monotone_nat_of_le_succ (hxqmono · bs ctx))]
  rw [iSup_congr (fun s => hxqval s bs ctx), ← ENNReal.iSup_div, Asup bs ctx]

/-- The supremum over `s` of the indicator dyadic sequence equals the indicator of `τ`. -/
private lemma iSup_dyadicValue_indicator {τ : ℝ} (Aτ : ℕ → ℕ)
    (Aτsup : (⨆ s, dyadicValue (Aτ s) s) = ENNReal.ofReal τ) (bs : BitString) :
    (⨆ s, dyadicValue (if bitStringToNat bs = 0 then Aτ s else 0) s)
      = (if bitStringToNat bs = 0 then ENNReal.ofReal τ else 0) := by
  by_cases hb : bitStringToNat bs = 0
  · simp only [hb]
    exact Aτsup
  · simp only [hb]
    simp [dyadicValue_zero]

/-- Computability of the combined dyadic approximation sequence for the rebuilt semimeasure. -/
private lemma computable_rebuilt_semimeasure_approx {c : ℕ} (hc : 0 < c)
    {A : ℕ → BitString → BitString → ℕ} {Aτ : ℕ → ℕ}
    (Acomp : Computable (fun p : ℕ × BitString × BitString => A p.1 p.2.1 p.2.2))
    (Aτcomp : Computable Aτ) :
    Computable (fun p : ℕ × BitString × BitString =>
      ratDyadicFloor (((A p.1 p.2.1 p.2.2 : ℚ) / 2 ^ p.1) / (c : ℚ)) p.1
        + (if bitStringToNat p.2.1 = 0 then Aτ p.1 else 0)) := by
  have hnum : Computable (fun p : ℕ × BitString × BitString =>
      ((A p.1 p.2.1 p.2.2 : ℕ) : ℤ)) :=
    ComputableReals.primrec_natCastInt.to_comp.comp Acomp
  have hden : Computable (fun p : ℕ × BitString × BitString => 2 ^ p.1 * c) :=
    (Primrec.nat_mul.comp
      ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.fst)
      (Primrec.const c)).to_comp
  have hxc : Computable (fun p : ℕ × BitString × BitString =>
      (((A p.1 p.2.1 p.2.2 : ℚ) / 2 ^ p.1) / (c : ℚ))) := by
    refine computable_of_num_den hnum hden (fun p => ?_) (fun p => ?_)
    · have : 0 < 2 ^ p.1 * c := Nat.mul_pos (by positivity) hc
      exact_mod_cast this
    · push_cast
      field_simp
  have hfloor : Computable (fun p : ℕ × BitString × BitString =>
      ratDyadicFloor (((A p.1 p.2.1 p.2.2 : ℚ) / 2 ^ p.1) / (c : ℚ)) p.1) :=
    computable_ratDyadicFloor.comp hxc Computable.fst
  have hbeq : Computable (fun p : ℕ × BitString × BitString =>
      (bitStringToNat p.2.1 == 0)) :=
    Primrec.beq.to_comp.comp
      (primrec_bitStringToNat.to_comp.comp (Computable.fst.comp Computable.snd))
      (Computable.const 0)
  have hsel : Computable (fun p : ℕ × BitString × BitString =>
      cond (bitStringToNat p.2.1 == 0) (Aτ p.1) 0) :=
    Computable.cond hbeq (Aτcomp.comp Computable.fst) (Computable.const 0)
  have hadd : Computable (fun p : ℕ × BitString × BitString =>
      ratDyadicFloor (((A p.1 p.2.1 p.2.2 : ℚ) / 2 ^ p.1) / (c : ℚ)) p.1
        + cond (bitStringToNat p.2.1 == 0) (Aτ p.1) 0) :=
    Primrec.nat_add.to_comp.comp hfloor hsel
  refine hadd.of_eq (fun p => ?_)
  by_cases hb : bitStringToNat p.2.1 = 0
  · simp [hb]
  · simp [hb, beq_eq_false_iff_ne.mpr hb]

/-- **SUV p. 160, the construction of Theorem 103's forward direction.** -/
theorem isOmegaNumber_of_scaled {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    {α : ℝ} {c : ℕ} (hc : 0 < c) (hα1 : α ≤ 1) (_hα0 : 0 ≤ α)
    (hle : omegaReal m ≤ (c : ℝ) * α)
    (hlsc : IsLowerSemicomputableReal ((c : ℝ) * α - omegaReal m)) :
    IsOmegaNumber α := by
  classical
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hcE : (0 : ℝ≥0∞) < (c : ℝ≥0∞) := by exact_mod_cast hc
  have hcEtop : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top c
  -- the extra mass
  set τ : ℝ := ((c : ℝ) * α - omegaReal m) / (c : ℝ) with hτdef
  have hτ0 : 0 ≤ τ := div_nonneg (by linarith) hcR.le
  have hτlsc : IsLowerSemicomputableReal τ := by
    have h := hlsc.rat_mul (c := (1 : ℚ) / (c : ℚ)) (by positivity)
    have hcast : (((1 : ℚ) / (c : ℚ) : ℚ) : ℝ) * ((c : ℝ) * α - omegaReal m) = τ := by
      rw [hτdef]; push_cast; field_simp
    rwa [hcast] at h
  obtain ⟨Aτ, Aτmono, Aτsup, Aτcomp⟩ := (isLowerSemicomputableReal_iff_ofReal hτ0).mp hτlsc
  obtain ⟨A, Amono, Asup, Acomp⟩ := hm.isLowerSemicomputableSemimeasureNat.2
  -- the new semimeasure
  set M : ℕ → ℝ≥0∞ := fun n => m n / (c : ℝ≥0∞) + (if n = 0 then ENNReal.ofReal τ else 0)
    with hMdef
  have htoReal : (∑' n, M n).toReal = α :=
    toReal_tsum_rebuilt_semimeasure hm hc hτ0 hτdef
  have hMle : (∑' n, M n) ≤ 1 := by
    have hsumtop : (∑' n, M n) ≠ ⊤ := by
      rw [hMdef]
      have h1 : (∑' n, m n / (c : ℝ≥0∞)) = omegaSum m / (c : ℝ≥0∞) := by
        simp only [ENNReal.div_eq_inv_mul]
        rw [ENNReal.tsum_mul_left, omegaSum]
      have h2 : (∑' n : ℕ, (if n = 0 then ENNReal.ofReal τ else 0)) = ENNReal.ofReal τ := by
        simp
      rw [ENNReal.tsum_add, h1, h2]
      refine ENNReal.add_ne_top.2 ⟨?_, ENNReal.ofReal_ne_top⟩
      exact ENNReal.div_ne_top (omegaSum_ne_top hm) hcE.ne'
    rw [← ENNReal.ofReal_toReal hsumtop, htoReal]
    exact ENNReal.ofReal_le_one.2 hα1
  -- the dyadic approximation of the new semimeasure
  set xq : ℕ → BitString → BitString → ℚ := fun s bs ctx =>
    ((A s bs ctx : ℚ) / 2 ^ s) / (c : ℚ) with hxqdef
  have hAmono2 : ∀ s bs ctx, 2 * A s bs ctx ≤ A (s + 1) bs ctx :=
    fun s bs ctx => double_le_of_dyadicValue_le _ _ s (Amono s bs ctx)
  have hxqmono : ∀ s bs ctx, xq s bs ctx ≤ xq (s + 1) bs ctx :=
    fun s bs ctx => scaled_dyadic_rat_mono A hAmono2 c s bs ctx
  have hxqval : ∀ s bs ctx, ENNReal.ofReal ((xq s bs ctx : ℚ) : ℝ)
      = dyadicValue (A s bs ctx) s / (c : ℝ≥0∞) :=
    fun s bs ctx => ofReal_scaled_dyadic_rat_eq (A s bs ctx) c s hc
  refine ⟨M, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- the semimeasure condition
    change (∑' bs : BitString, M (bitStringToNat bs)) ≤ 1
    refine le_of_eq_of_le ?_ hMle
    exact tsum_comp_bitStringToNat M
  · -- lower semicomputability
    refine ⟨fun s bs ctx => ratDyadicFloor (xq s bs ctx) s
        + (if bitStringToNat bs = 0 then Aτ s else 0), ?_, ?_, ?_⟩
    · intro s bs ctx
      rw [dyadicValue_add, dyadicValue_add]
      refine add_le_add (dyadicValue_ratDyadicFloor_mono_of_le (hxqmono s bs ctx) s) ?_
      by_cases hb : bitStringToNat bs = 0
      · simp only [hb]; exact Aτmono s
      · simp only [hb]; simp [dyadicValue_zero]
    · intro bs ctx
      have hmono1 : Monotone (fun s => dyadicValue (ratDyadicFloor (xq s bs ctx) s) s) :=
        monotone_nat_of_le_succ
          (fun s => dyadicValue_ratDyadicFloor_mono_of_le (hxqmono s bs ctx) s)
      have hmono2 : Monotone (fun s =>
          dyadicValue (if bitStringToNat bs = 0 then Aτ s else 0) s) := by
        refine monotone_nat_of_le_succ (fun s => ?_)
        by_cases hb : bitStringToNat bs = 0
        · simp only [hb]; exact Aτmono s
        · simp only [hb]; simp [dyadicValue_zero]
      have hsplit : ∀ s, dyadicValue (ratDyadicFloor (xq s bs ctx) s
          + (if bitStringToNat bs = 0 then Aτ s else 0)) s
          = dyadicValue (ratDyadicFloor (xq s bs ctx) s) s
            + dyadicValue (if bitStringToNat bs = 0 then Aτ s else 0) s :=
        fun s => dyadicValue_add _ _ _
      rw [iSup_congr hsplit, ← ENNReal.iSup_add_iSup_of_monotone hmono1 hmono2]
      rw [iSup_dyadicValue_ratDyadicFloor_scaled Asup xq ⟨hxqmono, hxqval⟩ bs ctx]
      rw [iSup_dyadicValue_indicator Aτ Aτsup bs]
    · exact computable_rebuilt_semimeasure_approx hc Acomp Aτcomp
  · -- maximality
    intro m2 hm2
    obtain ⟨k, hk, hdom⟩ := hm.2 m2 hm2
    refine ⟨k / (c : ℝ≥0∞), ?_, fun x => ?_⟩
    · exact ENNReal.div_pos hk.ne' hcEtop
    · have h1 : k / (c : ℝ≥0∞) * m2 x = (k * m2 x) / (c : ℝ≥0∞) := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, mul_assoc]
      rw [h1]
      refine le_trans (ENNReal.div_le_div_right (hdom x) _) ?_
      rw [hMdef]
      exact le_self_add
  · -- the sum is `α`
    rw [omegaReal, omegaSum]
    exact htoReal

end Kolmogorov
