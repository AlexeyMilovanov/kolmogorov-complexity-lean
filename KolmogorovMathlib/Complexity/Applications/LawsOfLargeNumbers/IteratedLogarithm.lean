/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.LawsOfLargeNumbers.PrefixFrequency

/-!
# Iterated Logarithm

An iterated-logarithm bound for the frequency of ones in prefixes of a Martin-Löf random
sequence with respect to the uniform measure: for every `ε > 0`, eventually
`|p_n - 1/2| ≤ (1 + ε) √(ln ln n / 2n)`.  The main declaration is
`abs_prefixFreq_sub_half_le` (Theorem 156 of the book by Shen, Uspensky and Vereshchagin).  The
proof builds a lower semicomputable mixture of symmetrised Bernoulli measures on a geometric
grid of biases and compares it with the a priori probability.
-/

namespace Kolmogorov.Applications
open Filter Topology Asymptotics

/-- The declarations `abs_prefixFreq_sub_half_le_km*` (up to the private theorem
`abs_prefixFreq_sub_half_le_km`) are a private copy of the proof chain of Problem 243,
`abs_prefixFreq_sub_half_le_of_KM`.  That theorem is declared after Theorem 156
(`abs_prefixFreq_sub_half_le`), so it cannot be used in its proof.

Weight of the grid index `m ≥ 1` in the mixture of Bernoulli measures of the proof of
`abs_prefixFreq_sub_half_le_km`: `1 / ((L + 1) (L + 2) 2 ^ L)` with `L = ⌊log₂ m⌋`.  The `2 ^ L`
indices of the block `2 ^ L ≤ m < 2 ^ (L + 1)` carry the total weight `1 / ((L + 1) (L + 2))`, and
these telescope to `1`. -/
private def abs_prefixFreq_sub_half_le_km_mixWeight (m : ℕ) : ℚ :=
  1 / ((((Nat.log 2 m : ℕ) : ℚ) + 1) * (((Nat.log 2 m : ℕ) : ℚ) + 2) * 2 ^ Nat.log 2 m)

/-- Cylinder mass of the symmetrised Bernoulli measure `(B(1/2 + ρ) + B(1/2 - ρ)) / 2`. -/
private def abs_prefixFreq_sub_half_le_km_mixMass (ρ : ℚ) (x : BitString) : ℚ :=
  ((1 / 2 + ρ) ^ x.count true * (1 / 2 - ρ) ^ x.count false +
    (1 / 2 - ρ) ^ x.count true * (1 / 2 + ρ) ^ x.count false) / 2

/-- The `e`-th term of the mixture, for the grid index `m = e + 1`: the weight of `m` times the
symmetrised Bernoulli mass with `ρ = θ ^ m / 2`. -/
private def abs_prefixFreq_sub_half_le_km_mixTerm (θ : ℚ) (e : ℕ) (x : BitString) : ℚ :=
  abs_prefixFreq_sub_half_le_km_mixWeight (e + 1) *
    abs_prefixFreq_sub_half_le_km_mixMass (θ ^ (e + 1) / 2) x

/-- Exponentiation of a rational base by a natural exponent is computable in both arguments. -/
private lemma abs_prefixFreq_sub_half_le_km_aux1_ratPow :
    Computable (fun z : ℚ × ℕ => z.1 ^ z.2) := by
  let step : ℚ × ℕ → ℕ × ℚ → ℚ := fun z q => q.2 * z.1
  have hstep : Computable (fun z : (ℚ × ℕ) × (ℕ × ℚ) => step z.1 z.2) :=
    computable₂_ratMul.comp (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.fst)
  have hrec := Computable.nat_rec (h := step) Computable.snd
    (Computable.const 1) hstep.to₂
  exact hrec.of_eq fun z => by
    induction z.2 with
    | zero => simp
    | succ n ih => simp only [step, ih, pow_succ, mul_comm]

/-- Counting the `true` bits of a bitstring is primitive recursive (private copy of
`Kolmogorov.primrec_count_true`, which is not in the import closure of this file). -/
private lemma abs_prefixFreq_sub_half_le_km_aux1_primrec_count_true :
    Primrec (fun s : BitString => s.count true) := by
  have hstep : Primrec₂ (fun (_ : BitString) (bn : Bool × ℕ) =>
      bif bn.1 then bn.2 + 1 else bn.2) :=
    (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have heq : (fun s : BitString => s.count true)
      = fun s => s.foldr (fun b n => bif b then n + 1 else n) 0 := by
    funext s; induction s with
    | nil => rfl
    | cons b s ih => cases b <;> simp [ih]
  rw [heq]
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) hstep

/-- Every boolean list splits into its `true` and `false` counts (private copy of
`Kolmogorov.count_true_add_count_false`). -/
private lemma abs_prefixFreq_sub_half_le_km_aux1_count_add (s : List Bool) :
    s.count true + s.count false = s.length := by
  induction s with
  | nil => simp
  | cons b s ih => cases b <;> simp <;> omega

/-- The number of `false` bits in a bit string is computable. -/
private lemma abs_prefixFreq_sub_half_le_km_aux1_count_false :
    Computable (fun x : BitString => x.count false) := by
  have hsub : Computable (fun x : BitString => x.length - x.count true) :=
    Primrec.nat_sub.to_comp.comp Primrec.list_length.to_comp
      abs_prefixFreq_sub_half_le_km_aux1_primrec_count_true.to_comp
  exact hsub.of_eq fun x => by
    rw [← abs_prefixFreq_sub_half_le_km_aux1_count_add x]
    exact Nat.add_sub_cancel_left _ _

/-- The mixture weight is computable. -/
private lemma abs_prefixFreq_sub_half_le_km_aux1_weight_computable :
    Computable abs_prefixFreq_sub_half_le_km_mixWeight := by
  have hlog : Computable (fun n : ℕ => Nat.log 2 n) := computable_natLogTwo
  have hD : Computable
      (fun m : ℕ => (Nat.log 2 m + 1) * (Nat.log 2 m + 2) * 2 ^ Nat.log 2 m) := by
    have h1 : Computable (fun m : ℕ => Nat.log 2 m + 1) :=
      Primrec.nat_add.to_comp.comp hlog (Computable.const 1)
    have h2 : Computable (fun m : ℕ => Nat.log 2 m + 2) :=
      Primrec.nat_add.to_comp.comp hlog (Computable.const 2)
    have h3 : Computable (fun m : ℕ => 2 ^ Nat.log 2 m) := comp_pow.comp hlog
    exact Primrec.nat_mul.to_comp.comp (Primrec.nat_mul.to_comp.comp h1 h2) h3
  refine computable_of_num_den (N := fun _ : ℕ => (1 : ℤ))
    (D := fun m : ℕ => (Nat.log 2 m + 1) * (Nat.log 2 m + 2) * 2 ^ Nat.log 2 m)
    (Computable.const 1) hD (fun m => by positivity) (fun m => ?_)
  unfold abs_prefixFreq_sub_half_le_km_mixWeight
  push_cast
  ring

/-- The symmetrised Bernoulli cylinder mass is computable in the parameter and the string. -/
private lemma abs_prefixFreq_sub_half_le_km_aux1_mass_computable :
    Computable (fun p : ℚ × BitString => abs_prefixFreq_sub_half_le_km_mixMass p.1 p.2) := by
  have hρ := (Computable.fst : Computable (fun p : ℚ × BitString => p.1))
  have hx := (Computable.snd : Computable (fun p : ℚ × BitString => p.2))
  have hA := computable₂_ratAdd.comp (Computable.const (1 / 2 : ℚ)) hρ
  have hB := computable₂_ratSub.comp (Computable.const (1 / 2 : ℚ)) hρ
  have ha := abs_prefixFreq_sub_half_le_km_aux1_primrec_count_true.to_comp.comp hx
  have hb := abs_prefixFreq_sub_half_le_km_aux1_count_false.comp hx
  have hAa := abs_prefixFreq_sub_half_le_km_aux1_ratPow.comp (hA.pair ha)
  have hBb := abs_prefixFreq_sub_half_le_km_aux1_ratPow.comp (hB.pair hb)
  have hBa := abs_prefixFreq_sub_half_le_km_aux1_ratPow.comp (hB.pair ha)
  have hAb := abs_prefixFreq_sub_half_le_km_aux1_ratPow.comp (hA.pair hb)
  have hsum := computable₂_ratAdd.comp (computable₂_ratMul.comp hAa hBb)
    (computable₂_ratMul.comp hBa hAb)
  exact (computable_ratHalf.comp hsum).of_eq fun p => rfl

/-- The mixture terms are computable in `(e, x)`, for a fixed rational `θ`. -/
private lemma abs_prefixFreq_sub_half_le_km_aux1_term_computable (θ : ℚ) :
    Computable (fun p : ℕ × BitString =>
      abs_prefixFreq_sub_half_le_km_mixTerm θ p.1 p.2) := by
  have hsucc := (Primrec.succ.comp Primrec.fst :
    Primrec (fun p : ℕ × BitString => p.1.succ)).to_comp
  have hw := abs_prefixFreq_sub_half_le_km_aux1_weight_computable.comp hsucc
  have hρ := computable_ratHalf.comp
    (abs_prefixFreq_sub_half_le_km_aux1_ratPow.comp ((Computable.const θ).pair hsucc))
  have hx := (Computable.snd : Computable (fun p : ℕ × BitString => p.2))
  have hm := abs_prefixFreq_sub_half_le_km_aux1_mass_computable.comp (hρ.pair hx)
  exact (computable₂_ratMul.comp hw hm).of_eq fun p => rfl

/-- Step 1 of the proof of `abs_prefixFreq_sub_half_le_km`: the family of the
mixture terms `x ↦ mixTerm θ e x` is lower semicomputable uniformly in `e` (the terms are
nonnegative rationals, computable in `(e, x)`; use `ratDyadicFloor` as the stage-`s` approximation
and `computable₂_ratMul`, `computable_ratPow`-style `Computable.nat_rec` for the powers). -/
private theorem abs_prefixFreq_sub_half_le_km_mixture_lsc (θ : ℚ) :
    IsUniformlyLowerSemicomputableTreeFamily
      (fun (e : ℕ) (x : BitString) => ENNReal.ofReal
        ((abs_prefixFreq_sub_half_le_km_mixTerm θ e x : ℚ) : ℝ)) := by
  refine ⟨fun e s x => ratDyadicFloor (abs_prefixFreq_sub_half_le_km_mixTerm θ e x) s,
    ?_, ?_, ?_⟩
  · intro e s x
    exact dyadicValue_ratDyadicFloor_mono_of_le (le_refl _) s
  · intro e x
    have h := iSup_dyadicValue_ratDyadicFloor
      (f := fun _ : ℕ => abs_prefixFreq_sub_half_le_km_mixTerm θ e x) monotone_const
    exact h.trans iSup_const
  · have h1 := (abs_prefixFreq_sub_half_le_km_aux1_term_computable θ).comp
      (Computable.fst.pair (Computable.snd.comp Computable.snd) :
        Computable (fun p : ℕ × ℕ × BitString => (p.1, p.2.2)))
    have h2 := computable_ratDyadicFloor.comp h1
      (Computable.fst.comp Computable.snd :
        Computable (fun p : ℕ × ℕ × BitString => p.2.1))
    exact h2.of_eq fun p => rfl

/-- The root mass of the symmetrised Bernoulli measure is `1`. -/
private lemma abs_prefixFreq_sub_half_le_km_aux2_mixMass_nil (ρ : ℚ) :
    abs_prefixFreq_sub_half_le_km_mixMass ρ [] = 1 := by
  unfold abs_prefixFreq_sub_half_le_km_mixMass
  simp

/-- The real value of the `e`-th root term. -/
private lemma abs_prefixFreq_sub_half_le_km_aux2_mixTerm_nil (θ : ℚ) (e : ℕ) :
    ((abs_prefixFreq_sub_half_le_km_mixTerm θ e [] : ℚ) : ℝ) =
      1 / ((((Nat.log 2 (e + 1) : ℕ) : ℝ) + 1) * (((Nat.log 2 (e + 1) : ℕ) : ℝ) + 2) *
        2 ^ Nat.log 2 (e + 1)) := by
  unfold abs_prefixFreq_sub_half_le_km_mixTerm
  rw [abs_prefixFreq_sub_half_le_km_aux2_mixMass_nil, mul_one]
  unfold abs_prefixFreq_sub_half_le_km_mixWeight
  push_cast
  rfl

/-- Block sum of the weights: the `2 ^ J` indices `e` with `2 ^ J ≤ e + 1 < 2 ^ (J + 1)`. -/
private lemma abs_prefixFreq_sub_half_le_km_aux2_block (J : ℕ) :
    ∑ e ∈ Finset.Ico (2 ^ J - 1) (2 ^ (J + 1) - 1),
      (1 / ((((Nat.log 2 (e + 1) : ℕ) : ℝ) + 1) * (((Nat.log 2 (e + 1) : ℕ) : ℝ) + 2) *
        2 ^ Nat.log 2 (e + 1)) : ℝ) = 1 / (((J : ℝ) + 1) * ((J : ℝ) + 2)) := by
  have h1 : 1 ≤ 2 ^ J := Nat.one_le_two_pow
  have h2 : 2 ^ (J + 1) = 2 * 2 ^ J := by ring
  have hconst : ∀ e ∈ Finset.Ico (2 ^ J - 1) (2 ^ (J + 1) - 1),
      (1 / ((((Nat.log 2 (e + 1) : ℕ) : ℝ) + 1) * (((Nat.log 2 (e + 1) : ℕ) : ℝ) + 2) *
        2 ^ Nat.log 2 (e + 1)) : ℝ) = 1 / (((J : ℝ) + 1) * ((J : ℝ) + 2) * 2 ^ J) := by
    intro e he
    rw [Finset.mem_Ico] at he
    have hlog : Nat.log 2 (e + 1) = J := by
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · omega
      · omega
    rw [hlog]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hcard : (2 ^ (J + 1) - 1) - (2 ^ J - 1) = 2 ^ J := by omega
  rw [hcard]
  push_cast
  field_simp

/-- The partial sums of the weights along the subsequence `2 ^ J - 1`. -/
private lemma abs_prefixFreq_sub_half_le_km_aux2_partial (J : ℕ) :
    ∑ e ∈ Finset.range (2 ^ J - 1),
      (1 / ((((Nat.log 2 (e + 1) : ℕ) : ℝ) + 1) * (((Nat.log 2 (e + 1) : ℕ) : ℝ) + 2) *
        2 ^ Nat.log 2 (e + 1)) : ℝ) = 1 - 1 / ((J : ℝ) + 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hle : 2 ^ J - 1 ≤ 2 ^ (J + 1) - 1 := by
      have h : 2 ^ J ≤ 2 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [← Finset.sum_range_add_sum_Ico _ hle, ih,
      abs_prefixFreq_sub_half_le_km_aux2_block J]
    push_cast
    field_simp
    ring

/-- The weights `1 / ((L + 1) (L + 2) 2 ^ L)`, `L = ⌊log₂ (e + 1)⌋`, sum to `1`. -/
private lemma abs_prefixFreq_sub_half_le_km_aux2_hasSum :
    HasSum (fun e : ℕ =>
      (1 / ((((Nat.log 2 (e + 1) : ℕ) : ℝ) + 1) * (((Nat.log 2 (e + 1) : ℕ) : ℝ) + 2) *
        2 ^ Nat.log 2 (e + 1)) : ℝ)) 1 := by
  set f : ℕ → ℝ := fun e =>
    (1 / ((((Nat.log 2 (e + 1) : ℕ) : ℝ) + 1) * (((Nat.log 2 (e + 1) : ℕ) : ℝ) + 2) *
        2 ^ Nat.log 2 (e + 1)) : ℝ) with hf
  have hnn : ∀ e, 0 ≤ f e := fun e => by positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hmono : Monotone (fun n => ∑ e ∈ Finset.range n, f e) := by
    intro a b hab
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
      (fun i _ _ => hnn i)
  apply tendsto_atTop_isLUB hmono
  refine ⟨?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    have hn : n ≤ 2 ^ n - 1 := by
      have := Nat.lt_two_pow_self (n := n)
      omega
    have h1 := hmono hn
    have h2 : ∑ e ∈ Finset.range (2 ^ n - 1), f e = 1 - 1 / ((n : ℝ) + 1) :=
      abs_prefixFreq_sub_half_le_km_aux2_partial n
    simp only [] at h1 ⊢
    have h3 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro b hb
    by_contra hlt
    have hlt : b < 1 := not_le.mp hlt
    have hd : 0 < 1 - b := by linarith
    obtain ⟨J, hJ⟩ := exists_nat_gt (1 / (1 - b))
    have hbJ := hb ⟨2 ^ J - 1, rfl⟩
    have h2 : ∑ e ∈ Finset.range (2 ^ J - 1), f e = 1 - 1 / ((J : ℝ) + 1) :=
      abs_prefixFreq_sub_half_le_km_aux2_partial J
    simp only [] at hbJ
    rw [h2] at hbJ
    have h4 : 1 - b ≤ 1 / ((J : ℝ) + 1) := by linarith
    rw [le_div_iff₀ (by positivity)] at h4
    rw [div_lt_iff₀ hd] at hJ
    nlinarith

/-- Step 2 of the proof of `abs_prefixFreq_sub_half_le_km`: the weights of the mixture
add up to `1`, i.e. the root masses of the mixture terms sum to `1`
(`mixMass ρ [] = 1`, and `∑_{L} 2 ^ L / ((L + 1) (L + 2) 2 ^ L) = ∑_L (1/(L+1) - 1/(L+2)) = 1`). -/
private theorem abs_prefixFreq_sub_half_le_km_mixture_root (θ : ℚ) :
    ∑' e : ℕ, ENNReal.ofReal
      ((abs_prefixFreq_sub_half_le_km_mixTerm θ e [] : ℚ) : ℝ) = 1 := by
  have h := abs_prefixFreq_sub_half_le_km_aux2_hasSum
  simp_rw [abs_prefixFreq_sub_half_le_km_aux2_mixTerm_nil]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun e => by positivity) h.summable, h.tsum_eq]
  simp

/-- Step 3 of the proof of `abs_prefixFreq_sub_half_le_km`: the mixture terms are
nonnegative for `0 < θ < 1`. -/
private theorem abs_prefixFreq_sub_half_le_km_mixture_nonneg (θ : ℚ) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (e : ℕ) (x : BitString) :
    0 ≤ abs_prefixFreq_sub_half_le_km_mixTerm θ e x := by
  have hρ0 : 0 < θ ^ (e + 1) / 2 := by positivity
  have hρ1 : θ ^ (e + 1) / 2 < 1 / 2 := by
    have : θ ^ (e + 1) < 1 := pow_lt_one₀ hθ0.le hθ1 (by omega)
    linarith
  unfold abs_prefixFreq_sub_half_le_km_mixTerm abs_prefixFreq_sub_half_le_km_mixWeight
    abs_prefixFreq_sub_half_le_km_mixMass
  have ha : 0 ≤ 1 / 2 + θ ^ (e + 1) / 2 := by linarith
  have hb : 0 ≤ 1 / 2 - θ ^ (e + 1) / 2 := by linarith
  positivity

/-- Step 4 of the proof of `abs_prefixFreq_sub_half_le_km`: each mixture term is
additive on cylinders, `term x = term (x ++ [false]) + term (x ++ [true])`. -/
private theorem abs_prefixFreq_sub_half_le_km_mixture_add (θ : ℚ) (e : ℕ)
    (x : BitString) :
    abs_prefixFreq_sub_half_le_km_mixTerm θ e x =
      abs_prefixFreq_sub_half_le_km_mixTerm θ e (x ++ [false]) +
        abs_prefixFreq_sub_half_le_km_mixTerm θ e (x ++ [true]) := by
  unfold abs_prefixFreq_sub_half_le_km_mixTerm abs_prefixFreq_sub_half_le_km_mixMass
  simp only [List.count_append, List.count_cons, List.count_nil]
  simp
  ring

/-- Real-number core of the domination bound of Step 5: with `y = θ ^ m`, the Bernoulli mass of
parameter `1/2 + s y / 2` (`s = ±1`) times `w / 2` is at most the symmetrised mass times `w`. -/
private lemma abs_prefixFreq_sub_half_le_km_aux3_real (y s w : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hs : s = 1 ∨ s = -1) (hw : 0 ≤ w) (a b : ℕ) :
    w / 2 * ((1 / 2 + s * y / 2) ^ a * (1 - (1 / 2 + s * y / 2)) ^ b) ≤
      w * (((1 / 2 + y / 2) ^ a * (1 / 2 - y / 2) ^ b +
        (1 / 2 - y / 2) ^ a * (1 / 2 + y / 2) ^ b) / 2) := by
  have h1 : 0 ≤ (1 / 2 + y / 2) ^ a * (1 / 2 - y / 2) ^ b :=
    mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
  have h2 : 0 ≤ (1 / 2 - y / 2) ^ a * (1 / 2 + y / 2) ^ b :=
    mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
  rcases hs with rfl | rfl
  · have e1 : 1 / 2 + 1 * y / 2 = 1 / 2 + y / 2 := by ring
    have e2 : 1 - (1 / 2 + 1 * y / 2) = 1 / 2 - y / 2 := by ring
    rw [e2, e1]
    nlinarith [mul_nonneg hw h2]
  · have e1 : 1 / 2 + -1 * y / 2 = 1 / 2 - y / 2 := by ring
    have e2 : 1 - (1 / 2 + -1 * y / 2) = 1 / 2 + y / 2 := by ring
    rw [e2, e1]
    nlinarith [mul_nonneg hw h1]

/-- Step 5 of the proof of `abs_prefixFreq_sub_half_le_km`: for rational
`0 < θ < 1` there is a computable probability measure `μ` (the mixture of the terms of Steps 1-4,
through `isLSC_tsum_of_uniform` and
`exists_isComputableMeasure_of_isLowerSemicomputableContinuousSemimeasure`) dominating every grid
Bernoulli measure `B(1/2 ± θ ^ m / 2)`, `m ≥ 1`, with the weight `weight m / 2`. -/
private theorem abs_prefixFreq_sub_half_le_km_mixture_measure (θ : ℚ) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) :
    ∃ μ : MeasureTheory.Measure CantorSeq, MeasureTheory.IsProbabilityMeasure μ ∧
      IsComputableMeasure μ ∧
      ∀ (m : ℕ) (s : ℝ), 1 ≤ m → (s = 1 ∨ s = -1) → ∀ x : BitString,
        ENNReal.ofReal
          ((1 / (2 * (((Nat.log 2 m : ℕ) : ℝ) + 1) * (((Nat.log 2 m : ℕ) : ℝ) + 2) *
              2 ^ Nat.log 2 m)) *
            ((1 / 2 + s * (θ : ℝ) ^ m / 2) ^ x.count true *
              (1 - (1 / 2 + s * (θ : ℝ) ^ m / 2)) ^ x.count false)) ≤ cantorMass μ x := by
  obtain ⟨a, ha⟩ : ∃ a : BitString → ENNReal, ∀ x, a x = ∑' e : ℕ, ENNReal.ofReal
      ((abs_prefixFreq_sub_half_le_km_mixTerm θ e x : ℚ) : ℝ) := ⟨fun x => _, fun x => rfl⟩
  have hlsc : IsLSC (fun x (_ : BitString) => a x) := by
    have h := isLSC_tsum_of_uniform
      (abs_prefixFreq_sub_half_le_km_mixture_lsc θ)
    have hfun : (fun x (_ : BitString) => a x) =
        fun x (_ : BitString) => ∑' e : ℕ, ENNReal.ofReal
          ((abs_prefixFreq_sub_half_le_km_mixTerm θ e x : ℚ) : ℝ) := by
      funext x _
      exact ha x
    rw [hfun]
    exact h
  have hroot : a [] = 1 := by
    rw [ha]
    exact abs_prefixFreq_sub_half_le_km_mixture_root θ
  have hadd : ∀ x, a x = a (x ++ [false]) + a (x ++ [true]) := by
    intro x
    rw [ha x, ha (x ++ [false]), ha (x ++ [true]), ← ENNReal.tsum_add]
    refine tsum_congr (fun e => ?_)
    have h0 : (0 : ℝ) ≤ ((abs_prefixFreq_sub_half_le_km_mixTerm θ e (x ++ [false]) : ℚ) : ℝ) := by
      exact_mod_cast abs_prefixFreq_sub_half_le_km_mixture_nonneg θ hθ0 hθ1 e _
    have h1 : (0 : ℝ) ≤ ((abs_prefixFreq_sub_half_le_km_mixTerm θ e (x ++ [true]) : ℚ) : ℝ) := by
      exact_mod_cast abs_prefixFreq_sub_half_le_km_mixture_nonneg θ hθ0 hθ1 e _
    rw [← ENNReal.ofReal_add h0 h1, ← Rat.cast_add,
      ← abs_prefixFreq_sub_half_le_km_mixture_add θ e x]
  have hsemi : IsLowerSemicomputableContinuousSemimeasure a :=
    ⟨⟨hroot, fun x => (hadd x).ge⟩, hlsc⟩
  obtain ⟨μ, hμc, hmass⟩ :=
    exists_isComputableMeasure_of_isLowerSemicomputableContinuousSemimeasure hsemi hadd
  refine ⟨μ, ⟨?_⟩, hμc, ?_⟩
  · have h1 : μ Set.univ = cantorMass μ [] := by
      unfold cantorMass
      rw [cantorCylinder_nil]
    rw [h1, hmass, hroot]
  · intro m s hm hs x
    obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
    rw [hmass x, ha x]
    refine le_trans ?_ (ENNReal.le_tsum e)
    apply ENNReal.ofReal_le_ofReal
    have hθpos : (0 : ℝ) < θ := by exact_mod_cast hθ0
    have hθlt : (θ : ℝ) < 1 := by exact_mod_cast hθ1
    have hy1 : (θ : ℝ) ^ (e + 1) ≤ 1 := pow_le_one₀ hθpos.le hθlt.le
    have hy0 : (0 : ℝ) ≤ (θ : ℝ) ^ (e + 1) := by positivity
    have hcast : ((abs_prefixFreq_sub_half_le_km_mixTerm θ e x : ℚ) : ℝ) =
        (1 / ((((Nat.log 2 (e + 1) : ℕ) : ℝ) + 1) * (((Nat.log 2 (e + 1) : ℕ) : ℝ) + 2) *
            2 ^ Nat.log 2 (e + 1))) *
          (((1 / 2 + (θ : ℝ) ^ (e + 1) / 2) ^ x.count true *
              (1 / 2 - (θ : ℝ) ^ (e + 1) / 2) ^ x.count false +
            (1 / 2 - (θ : ℝ) ^ (e + 1) / 2) ^ x.count true *
              (1 / 2 + (θ : ℝ) ^ (e + 1) / 2) ^ x.count false) / 2) := by
      unfold abs_prefixFreq_sub_half_le_km_mixTerm abs_prefixFreq_sub_half_le_km_mixWeight
        abs_prefixFreq_sub_half_le_km_mixMass
      push_cast
      try ring
    rw [hcast]
    have hw : (0 : ℝ) ≤ 1 / ((((Nat.log 2 (e + 1) : ℕ) : ℝ) + 1) *
        (((Nat.log 2 (e + 1) : ℕ) : ℝ) + 2) * 2 ^ Nat.log 2 (e + 1)) := by positivity
    have hwt : 1 / (2 * (((Nat.log 2 (e + 1) : ℕ) : ℝ) + 1) * (((Nat.log 2 (e + 1) : ℕ) : ℝ) + 2) *
        2 ^ Nat.log 2 (e + 1)) = (1 / ((((Nat.log 2 (e + 1) : ℕ) : ℝ) + 1) *
          (((Nat.log 2 (e + 1) : ℕ) : ℝ) + 2) * 2 ^ Nat.log 2 (e + 1))) / 2 := by
      rw [div_div]
      congr 1
      ring
    rw [hwt]
    exact abs_prefixFreq_sub_half_le_km_aux3_real ((θ : ℝ) ^ (e + 1)) s _ hy0 hy1 hs hw _ _


/-- Auxiliary (Step 6): `2 log₂ (L + 2) ≤ ε L + c` for all `L : ℕ` with one constant `c`. -/
private theorem abs_prefixFreq_sub_half_le_km_aux4_log_le {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, ∀ L : ℕ, 2 * Real.logb 2 ((L : ℝ) + 2) ≤ ε * L + c := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set κ : ℝ := ε * Real.log 2 / 2 with hκ
  have hκpos : 0 < κ := by positivity
  refine ⟨2 * ε - 2 * (1 + Real.log κ) / Real.log 2, fun L => ?_⟩
  have hL2 : (0 : ℝ) < (L : ℝ) + 2 := by positivity
  have h1 : Real.log (((L : ℝ) + 2) * κ) ≤ ((L : ℝ) + 2) * κ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_mul hL2.ne' hκpos.ne'] at h1
  have h2 : Real.log ((L : ℝ) + 2) ≤ ((L : ℝ) + 2) * κ - 1 - Real.log κ := by linarith
  have e1 : ε * L + (2 * ε - 2 * (1 + Real.log κ) / Real.log 2) =
      (((L : ℝ) + 2) * κ * 2 - 2 - 2 * Real.log κ) / Real.log 2 := by
    rw [hκ]
    field_simp
    ring
  unfold Real.logb
  rw [e1, mul_div_assoc']
  gcongr
  linarith

/-- Step 6 of the proof of `abs_prefixFreq_sub_half_le_km`: the logarithmic cost of
the mixture weight is `(1 + ε) log₂ (m + 1) + c`:
`log₂ (2 (L+1) (L+2) 2^L) = 1 + L + log₂ ((L+1)(L+2)) ≤ (1 + ε) log₂ (m + 1) + c`
for `L = ⌊log₂ m⌋ ≤ log₂ m`, because `log₂ ((L+1)(L+2)) = o(L)`. -/
private theorem abs_prefixFreq_sub_half_le_km_weight_log {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, ∀ m : ℕ, 1 ≤ m →
      Real.logb 2 (2 * (((Nat.log 2 m : ℕ) : ℝ) + 1) * (((Nat.log 2 m : ℕ) : ℝ) + 2) *
          2 ^ Nat.log 2 m) ≤ (1 + ε) * Real.logb 2 ((m : ℝ) + 1) + c := by
  obtain ⟨c₀, hc₀⟩ := abs_prefixFreq_sub_half_le_km_aux4_log_le hε
  refine ⟨1 + c₀, fun m hm => ?_⟩
  have hm0 : m ≠ 0 := by omega
  have hpow : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm0
  have hpowR : (2 : ℝ) ^ Nat.log 2 m ≤ (m : ℝ) + 1 := by
    have : ((2 ^ Nat.log 2 m : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpow
    push_cast at this
    linarith
  have hLle : ((Nat.log 2 m : ℕ) : ℝ) ≤ Real.logb 2 ((m : ℝ) + 1) := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hpowR
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
  have hL1 : (0 : ℝ) < ((Nat.log 2 m : ℕ) : ℝ) + 1 := by positivity
  have hL2 : (0 : ℝ) < ((Nat.log 2 m : ℕ) : ℝ) + 2 := by positivity
  have hsplit : Real.logb 2 (2 * (((Nat.log 2 m : ℕ) : ℝ) + 1) * (((Nat.log 2 m : ℕ) : ℝ) + 2) *
        2 ^ Nat.log 2 m) =
      1 + Real.logb 2 (((Nat.log 2 m : ℕ) : ℝ) + 1) + Real.logb 2 (((Nat.log 2 m : ℕ) : ℝ) + 2) +
        ((Nat.log 2 m : ℕ) : ℝ) := by
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
        (by positivity),
      Real.logb_mul (by positivity) (by positivity), Real.logb_self_eq_one (by norm_num),
      Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    ring
  have hle12 : Real.logb 2 (((Nat.log 2 m : ℕ) : ℝ) + 1) ≤
      Real.logb 2 (((Nat.log 2 m : ℕ) : ℝ) + 2) :=
    Real.logb_le_logb_of_le (by norm_num) hL1 (by linarith)
  have h3 := hc₀ (Nat.log 2 m)
  have h4 : (1 + ε) * ((Nat.log 2 m : ℕ) : ℝ) ≤ (1 + ε) * Real.logb 2 ((m : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hLle (by linarith)
  rw [hsplit]
  linarith

/-- Auxiliary (Step 7): the pointwise coding bound in logarithmic form (a copy of the private
`KMOf_toNat_le_neg_logb_of_weight` of `Entropy/Complexity/Expected/Monotone.lean`). -/
private lemma abs_prefixFreq_sub_half_le_km_aux4_KMOf_le_neg_logb {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) (c : ℕ) (x : BitString) {m : ENNReal}
    (hm0 : m ≠ 0) (hmtop : m ≠ ⊤)
    (hw : (2 : ENNReal)⁻¹ ^ c * m ≤ complexityWeight (KMOf D x)) :
    ((KMOf D x).toNat : ℝ) ≤ -Real.logb 2 m.toReal + c := by
  have hk : KMOf D x ≠ ⊤ := KMOf_ne_top_of_isOptimal hD x
  have hcw : complexityWeight (KMOf D x) = (2 : ENNReal)⁻¹ ^ (KMOf D x).toNat := by
    conv_lhs => rw [← ENat.natCast_toNat hk]
    rw [complexityWeight_coe]
  rw [hcw] at hw
  have hmR : 0 < m.toReal := ENNReal.toReal_pos hm0 hmtop
  have e1 : ((2 : ENNReal)⁻¹ ^ c * m).toReal = (2 : ℝ)⁻¹ ^ c * m.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  have e2 : ((2 : ENNReal)⁻¹ ^ (KMOf D x).toNat).toReal = (2 : ℝ)⁻¹ ^ (KMOf D x).toNat := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  have hwR : (2 : ℝ)⁻¹ ^ c * m.toReal ≤ (2 : ℝ)⁻¹ ^ (KMOf D x).toNat := by
    rw [← e1, ← e2]
    exact ENNReal.toReal_mono (by finiteness) hw
  have hlog := (Real.logb_le_logb (b := 2) (by norm_num)
    (mul_pos (by positivity) hmR) (by positivity)).mpr hwR
  have hL : Real.logb 2 ((2 : ℝ)⁻¹ ^ c * m.toReal) = -(c : ℝ) + Real.logb 2 m.toReal := by
    rw [Real.logb_mul (pow_ne_zero c (by norm_num)) hmR.ne', Real.logb_pow, Real.logb_inv,
      Real.logb_self_eq_one (by norm_num)]
    ring
  have hR : Real.logb 2 ((2 : ℝ)⁻¹ ^ (KMOf D x).toNat) = -((KMOf D x).toNat : ℝ) := by
    rw [Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
    ring
  rw [hL, hR] at hlog
  linarith

/-- Step 7 of the proof of `abs_prefixFreq_sub_half_le_km`: the **coding bound**.
For rational `θ ∈ (0, 1)` and `ε > 0` there is a constant `c` such that for every `m ≥ 1`, every
sign `s = ±1` and every string `x`, the monotone complexity of `x` is at most
`-log₂ B(x) + (1 + ε) log₂ (m + 1) + c`, `B` the Bernoulli measure with parameter
`1/2 + s θ ^ m / 2`.  (Coding theorem for the computable mixture measure of Step 5,
`exists_const_cantorMass_mul_le_complexityWeight_KMOf`, plus Step 6.) -/
private theorem abs_prefixFreq_sub_half_le_km_coding_bound
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D)
    (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, ∀ (m : ℕ) (s : ℝ), 1 ≤ m → (s = 1 ∨ s = -1) → ∀ x : BitString,
      ((KMOf D x).toNat : ℝ) ≤
        -Real.logb 2 ((1 / 2 + s * (θ : ℝ) ^ m / 2) ^ x.count true *
            (1 - (1 / 2 + s * (θ : ℝ) ^ m / 2)) ^ x.count false) +
          (1 + ε) * Real.logb 2 ((m : ℝ) + 1) + c := by
  obtain ⟨μ, hprob, hcomp, hlow⟩ :=
    abs_prefixFreq_sub_half_le_km_mixture_measure θ hθ0 hθ1
  have : MeasureTheory.IsProbabilityMeasure μ := hprob
  obtain ⟨c₀, hc₀⟩ := exists_const_cantorMass_mul_le_complexityWeight_KMOf μ hcomp hD
  obtain ⟨c₁, hc₁⟩ := abs_prefixFreq_sub_half_le_km_weight_log hε
  refine ⟨c₁ + c₀, fun m s hm hs x => ?_⟩
  have hlow' := hlow m s hm hs x
  have h6 := hc₁ m hm
  have hθR0 : (0 : ℝ) < θ := by exact_mod_cast hθ0
  have hθR1 : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hθm0 : 0 < (θ : ℝ) ^ m := pow_pos hθR0 m
  have hθm1 : (θ : ℝ) ^ m < 1 := pow_lt_one₀ hθR0.le hθR1 (by omega)
  have hsθ : |s * (θ : ℝ) ^ m| < 1 := by
    rcases hs with h | h <;> simp [h, abs_of_pos hθm0, hθm1]
  rw [abs_lt] at hsθ
  have hq0 : 0 < 1 / 2 + s * (θ : ℝ) ^ m / 2 := by linarith [hsθ.1]
  have hq1 : 0 < 1 - (1 / 2 + s * (θ : ℝ) ^ m / 2) := by linarith [hsθ.2]
  generalize hqdef : 1 / 2 + s * (θ : ℝ) ^ m / 2 = q at hq0 hq1 hlow' ⊢
  generalize hLdef : Nat.log 2 m = L at hlow' h6
  have hB0 : 0 < q ^ x.count true * (1 - q) ^ x.count false :=
    mul_pos (pow_pos hq0 _) (pow_pos hq1 _)
  have hW0 : 0 < 1 / (2 * ((L : ℝ) + 1) * ((L : ℝ) + 2) * 2 ^ L) := by positivity
  have hM0 : ENNReal.ofReal ((1 / (2 * ((L : ℝ) + 1) * ((L : ℝ) + 2) * 2 ^ L)) *
      (q ^ x.count true * (1 - q) ^ x.count false)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos hW0 hB0
  have hMtop : ENNReal.ofReal ((1 / (2 * ((L : ℝ) + 1) * ((L : ℝ) + 2) * 2 ^ L)) *
      (q ^ x.count true * (1 - q) ^ x.count false)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hw : (2 : ENNReal)⁻¹ ^ c₀ * ENNReal.ofReal ((1 / (2 * ((L : ℝ) + 1) * ((L : ℝ) + 2) * 2 ^ L))
      *
      (q ^ x.count true * (1 - q) ^ x.count false)) ≤ complexityWeight (KMOf D x) := by
    calc (2 : ENNReal)⁻¹ ^ c₀ * ENNReal.ofReal ((1 / (2 * ((L : ℝ) + 1) * ((L : ℝ) + 2) * 2 ^ L)) *
          (q ^ x.count true * (1 - q) ^ x.count false))
        ≤ (2 : ENNReal)⁻¹ ^ c₀ * cantorMass μ x := by gcongr
      _ ≤ complexityWeight (KMOf D x) := hc₀ x
  have hkey := abs_prefixFreq_sub_half_le_km_aux4_KMOf_le_neg_logb hD c₀ x hM0 hMtop hw
  rw [ENNReal.toReal_ofReal (mul_pos hW0 hB0).le] at hkey
  have hlogWB : Real.logb 2 ((1 / (2 * ((L : ℝ) + 1) * ((L : ℝ) + 2) * 2 ^ L)) *
      (q ^ x.count true * (1 - q) ^ x.count false)) =
      -Real.logb 2 (2 * ((L : ℝ) + 1) * ((L : ℝ) + 2) * 2 ^ L) +
        Real.logb 2 (q ^ x.count true * (1 - q) ^ x.count false) := by
    rw [Real.logb_mul hW0.ne' hB0.ne', one_div, Real.logb_inv]
  rw [hlogWB] at hkey
  linarith


/-- Step 8 of the proof of `abs_prefixFreq_sub_half_le_km`: **cross-entropy**.  If a
string has `a` ones and `b` zeros (frequency `p = a / (a + b)`) and `q ∈ (0, 1)` lies
between `1/2` and `p` (on the same side of `1/2` as `p` and not farther from `1/2`), then
`-log₂ (q ^ a (1 - q) ^ b) ≤ (a + b) h(q)`
(the difference is `(a + b) (p - q) (log₂ (1 - q) - log₂ q) ≤ 0`; for the empty string both
sides vanish). -/
private theorem abs_prefixFreq_sub_half_le_km_cross_entropy
    (a b : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hside : 0 ≤ (q - 1 / 2) * ((a : ℝ) / ((a : ℝ) + b) - 1 / 2))
    (hmag : |q - 1 / 2| ≤ |(a : ℝ) / ((a : ℝ) + b) - 1 / 2|) :
    -Real.logb 2 (q ^ a * (1 - q) ^ b) ≤ ((a : ℝ) + b) * binaryEntropy q := by
  rcases Nat.eq_zero_or_pos (a + b) with hab | hab
  · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := ⟨by omega, by omega⟩
    simp
  have hn : (0 : ℝ) < (a : ℝ) + b := by exact_mod_cast hab
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (a : ℝ) / ((a : ℝ) + b) := ⟨_, rfl⟩
  rw [← hp] at hside hmag
  have hap : (a : ℝ) = ((a : ℝ) + b) * p := by
    rw [hp]; field_simp
  have hbp : (b : ℝ) = ((a : ℝ) + b) * (1 - p) := by
    rw [hp]; field_simp; ring
  have hq1' : 0 < 1 - q := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the key sign: `(p - q) (log q - log (1 - q)) ≥ 0`
  have key : 0 ≤ (p - q) * (Real.log q - Real.log (1 - q)) := by
    rcases lt_trichotomy q (1 / 2) with h | h | h
    · have hp_le : p ≤ 1 / 2 := by
        by_contra hcon
        have hcon' : 1 / 2 < p := not_le.mp hcon
        have : (q - 1 / 2) * (p - 1 / 2) < 0 :=
          mul_neg_of_neg_of_pos (by linarith) (by linarith)
        linarith
      have hpq : p ≤ q := by
        rw [abs_of_neg (by linarith : q - 1 / 2 < 0),
          abs_of_nonpos (by linarith : p - 1 / 2 ≤ 0)] at hmag
        linarith
      have hlog : Real.log q ≤ Real.log (1 - q) := Real.log_le_log hq0 (by linarith)
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have : 1 - q = q := by rw [h]; norm_num
      rw [this]; simp
    · have hp_ge : 1 / 2 ≤ p := by
        by_contra hcon
        have hcon' : p < 1 / 2 := not_le.mp hcon
        have : (q - 1 / 2) * (p - 1 / 2) < 0 :=
          mul_neg_of_pos_of_neg (by linarith) (by linarith)
        linarith
      have hpq : q ≤ p := by
        rw [abs_of_pos (by linarith : 0 < q - 1 / 2),
          abs_of_nonneg (by linarith : 0 ≤ p - 1 / 2)] at hmag
        linarith
      have hlog : Real.log (1 - q) ≤ Real.log q := Real.log_le_log hq1' (by linarith)
      exact mul_nonneg (by linarith) (by linarith)
  have hL : -Real.logb 2 (q ^ a * (1 - q) ^ b) =
      -((a : ℝ) * Real.log q + (b : ℝ) * Real.log (1 - q)) / Real.log 2 := by
    rw [Real.logb, Real.log_mul (pow_ne_zero _ hq0.ne') (pow_ne_zero _ hq1'.ne'),
      Real.log_pow, Real.log_pow]
    ring
  have hR : ((a : ℝ) + b) * binaryEntropy q =
      ((a : ℝ) + b) * (-q * Real.log q - (1 - q) * Real.log (1 - q)) / Real.log 2 := by
    unfold binaryEntropy negMulLog2 Real.negMulLog
    ring
  rw [hL, hR]
  apply div_le_div_of_nonneg_right _ hlog2.le
  have e : ((a : ℝ) + b) * (-q * Real.log q - (1 - q) * Real.log (1 - q)) +
      ((a : ℝ) * Real.log q + (b : ℝ) * Real.log (1 - q)) =
      ((a : ℝ) + b) * ((p - q) * (Real.log q - Real.log (1 - q))) := by
    linear_combination (Real.log q) * hap + (Real.log (1 - q)) * hbp
  have := mul_nonneg hn.le key
  linarith

/-- Step 9 of the proof of `abs_prefixFreq_sub_half_le_km`: **geometric
approximation**.  For `0 < θ < 1` and `0 < δ ≤ 1/2` the least `m ≥ 1` with `θ ^ m / 2 ≤ δ`
satisfies `θ δ ≤ θ ^ m / 2` and `(m - 1) log (1/θ) ≤ log (1/(2δ))`. -/
private theorem abs_prefixFreq_sub_half_le_km_geometric
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ m : ℕ, 1 ≤ m ∧ θ ^ m / 2 ≤ δ ∧ θ * δ ≤ θ ^ m / 2 ∧
      ((m : ℝ) - 1) * Real.log (1 / θ) ≤ Real.log (1 / (2 * δ)) := by
  classical
  have hex : ∃ m : ℕ, 1 ≤ m ∧ θ ^ m / 2 ≤ δ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < 2 * δ) hθ1
    refine ⟨k + 1, by omega, ?_⟩
    have : θ ^ (k + 1) ≤ θ ^ k := pow_le_pow_of_le_one hθ0.le hθ1.le (Nat.le_succ k)
    linarith
  obtain ⟨m, hm1, hmδ, hmin⟩ : ∃ m : ℕ, 1 ≤ m ∧ θ ^ m / 2 ≤ δ ∧
      ∀ k : ℕ, k < m → 1 ≤ k → δ < θ ^ k / 2 := by
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
    intro k hk hk1
    have hnot := Nat.find_min hex hk
    by_contra hcon
    exact hnot ⟨hk1, not_lt.mp hcon⟩
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have hm : m = 1 := by omega
    subst hm
    refine ⟨1, le_rfl, hmδ, ?_, ?_⟩
    · simp only [pow_one]
      nlinarith
    · simp only [Nat.cast_one, sub_self, zero_mul]
      apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith)]
      linarith
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have hlt : δ < θ ^ k / 2 := hmin k (by omega) hk1
    refine ⟨k + 1, hm1, hmδ, ?_, ?_⟩
    · have h1 := mul_lt_mul_of_pos_left hlt hθ0
      have h2 : θ ^ (k + 1) = θ * θ ^ k := by ring
      rw [h2]
      nlinarith
    · have hpk : 0 < θ ^ k := pow_pos hθ0 k
      have h2δ : 2 * δ < θ ^ k := by linarith
      have hle : 1 / θ ^ k ≤ 1 / (2 * δ) := one_div_le_one_div_of_le (by linarith) h2δ.le
      have hlog := Real.log_le_log (by positivity) hle
      have e1 : Real.log (1 / θ ^ k) = (k : ℝ) * Real.log (1 / θ) := by
        rw [← one_div_pow, Real.log_pow]
      rw [e1] at hlog
      push_cast
      simpa using hlog


/-- Auxiliary (step 10): the binary entropy never exceeds `1`. -/
private lemma abs_prefixFreq_sub_half_le_km_aux6_binaryEntropy_le_one (x : ℝ) :
    binaryEntropy x ≤ 1 := by
  rw [tendsto_prefixFreq_of_plainK_isLittleO_entropy_rigidity_h_eq x,
    div_le_one (Real.log_pos (by norm_num))]
  exact Real.binEntropy_le_log_two

/-- Auxiliary (step 10): `log₂ (ln n) / n → 0`. -/
private lemma abs_prefixFreq_sub_half_le_km_aux6_logb_log_div_tendsto :
    Tendsto (fun n : ℕ => Real.logb 2 (Real.log n) / n) atTop (𝓝 0) := by
  have h1 : (fun n : ℕ => Real.log (Real.log (n : ℝ))) =o[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h2 : (fun n : ℕ => Real.log (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have h3 := (h1.trans h2).tendsto_div_nhds_zero
  have h4 := h3.div_const (Real.log 2)
  rw [zero_div] at h4
  refine h4.congr (fun n => ?_)
  unfold Real.logb
  ring

/-- Auxiliary (step 10): `1/2 + t_n` has entropy tending to `1` under the deficit hypothesis. -/
private lemma abs_prefixFreq_sub_half_le_km_aux6_entropy_tendsto
    (t : ℕ → ℝ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1 / 2)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * (1 - binaryEntropy (1 / 2 + t n)) ≤ (1 + ε) * Real.logb 2 (Real.log n)) :
    Tendsto t atTop (𝓝 0) := by
  have hlow : Tendsto (fun n : ℕ => 1 - 2 * (Real.logb 2 (Real.log n) / n)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (abs_prefixFreq_sub_half_le_km_aux6_logb_log_div_tendsto.const_mul 2)
    simpa using this
  have hH : Tendsto (fun n => binaryEntropy (1 / 2 + t n)) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [h 1 one_pos, eventually_ge_atTop 1] with n hn hn1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have h1 : 1 - binaryEntropy (1 / 2 + t n) ≤ 2 * Real.logb 2 (Real.log n) / n := by
        rw [le_div_iff₀ hnpos]
        linarith
      have h2 : 2 * (Real.logb 2 (Real.log n) / n) = 2 * Real.logb 2 (Real.log n) / n := by
        ring
      linarith
    · exact Eventually.of_forall (fun n =>
        abs_prefixFreq_sub_half_le_km_aux6_binaryEntropy_le_one _)
  have hp : ∀ n, 0 ≤ 1 / 2 + t n ∧ 1 / 2 + t n ≤ 1 :=
    fun n => ⟨by linarith [ht0 n], by linarith [ht1 n]⟩
  have h1 := tendsto_prefixFreq_of_plainK_isLittleO_entropy_rigidity
    (fun n => 1 / 2 + t n) hp hH
  have h2 := h1.sub_const (1 / 2)
  simpa using h2

/-- Step 10 of the proof of `abs_prefixFreq_sub_half_le_km`: **real-analytic step**.
If `n (1 - h(1/2 + t_n)) ≤ (1 + ε) log₂ ln n` eventually for every `ε > 0` (`0 ≤ t_n < 1/2`), then
`t_n ≤ (1 + ε) √(ln ln n / (2 n))` eventually for every `ε > 0`.  (First `t_n → 0` by entropy
rigidity `tendsto_prefixFreq_of_plainK_isLittleO_entropy_rigidity`, then
`binaryEntropy_half_add_isLittleO`: `1 - h(1/2 + t) = (2 / ln 2) t² (1 + o(1))`.) -/
private theorem abs_prefixFreq_sub_half_le_km_real_analytic
    (t : ℕ → ℝ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1 / 2)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * (1 - binaryEntropy (1 / 2 + t n)) ≤ (1 + ε) * Real.logb 2 (Real.log n)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      t n ≤ (1 + ε) * Real.sqrt (Real.log (Real.log n) / (2 * n)) := by
  have hlim : Tendsto t atTop (𝓝 0) :=
    abs_prefixFreq_sub_half_le_km_aux6_entropy_tendsto t ht0 ht1 h
  intro ε hε
  have hD : (0 : ℝ) < 2 + 2 * ε + ε ^ 2 := by positivity
  obtain ⟨a, ha0, ha1, hratio⟩ : ∃ a : ℝ, 0 < a ∧ a < 1 ∧ 1 + a = (1 + ε) ^ 2 * (1 - a) := by
    refine ⟨(2 * ε + ε ^ 2) / (2 + 2 * ε + ε ^ 2), by positivity, ?_, ?_⟩
    · rw [div_lt_one hD]
      linarith
    · field_simp
      ring
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (0 : ℝ) < a * (2 / Real.log 2) := by positivity
  have hTaylor := binaryEntropy_half_add_isLittleO.def hc
  have hT' := hlim.eventually hTaylor
  filter_upwards [hT', h a ha0, eventually_ge_atTop 1] with n hn1 hn2 hn3
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn3
  have hn1' : |binaryEntropy (1 / 2 + t n) - (1 - 2 / Real.log 2 * t n ^ 2)| ≤
      a * (2 / Real.log 2) * t n ^ 2 := by
    have := hn1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (t n))] at this
    exact this
  have hq : 2 / Real.log 2 * (1 - a) * t n ^ 2 ≤ 1 - binaryEntropy (1 / 2 + t n) := by
    have := (abs_le.mp hn1').2
    nlinarith [this]
  have hlogb : Real.logb 2 (Real.log n) * Real.log 2 = Real.log (Real.log n) := by
    unfold Real.logb
    field_simp
  have h7 : (n : ℝ) * (2 / Real.log 2 * (1 - a) * t n ^ 2) * Real.log 2 ≤
      (1 + a) * Real.log (Real.log n) := by
    calc (n : ℝ) * (2 / Real.log 2 * (1 - a) * t n ^ 2) * Real.log 2
        ≤ ((n : ℝ) * (1 - binaryEntropy (1 / 2 + t n))) * Real.log 2 := by gcongr
      _ ≤ ((1 + a) * Real.logb 2 (Real.log n)) * Real.log 2 := by gcongr
      _ = (1 + a) * Real.log (Real.log n) := by rw [mul_assoc, hlogb]
  have h8 : (n : ℝ) * (2 / Real.log 2 * (1 - a) * t n ^ 2) * Real.log 2 =
      2 * n * (1 - a) * t n ^ 2 := by
    field_simp
  have h10 : 2 * (n : ℝ) * t n ^ 2 ≤ (1 + ε) ^ 2 * Real.log (Real.log n) := by
    have h9 : (1 - a) * (2 * (n : ℝ) * t n ^ 2) ≤
        (1 - a) * ((1 + ε) ^ 2 * Real.log (Real.log n)) := by
      calc (1 - a) * (2 * (n : ℝ) * t n ^ 2) = 2 * n * (1 - a) * t n ^ 2 := by ring
        _ ≤ (1 + a) * Real.log (Real.log n) := by rw [← h8]; exact h7
        _ = (1 - a) * ((1 + ε) ^ 2 * Real.log (Real.log n)) := by rw [hratio]; ring
    exact le_of_mul_le_mul_left h9 (by linarith)
  have h11 : t n ^ 2 ≤ (1 + ε) ^ 2 * (Real.log (Real.log n) / (2 * n)) := by
    rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
    calc t n ^ 2 * (2 * (n : ℝ)) = 2 * n * t n ^ 2 := by ring
      _ ≤ (1 + ε) ^ 2 * Real.log (Real.log n) := h10
  calc t n ≤ Real.sqrt ((1 + ε) ^ 2 * (Real.log (Real.log n) / (2 * n))) :=
        Real.le_sqrt_of_sq_le h11
    _ = (1 + ε) * Real.sqrt (Real.log (Real.log n) / (2 * n)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]

/-- Step 11 of the proof of `abs_prefixFreq_sub_half_le_km`: **asymptotic
arithmetic**.  If `e = o(ln ln n)`, `m_n ≤ 1 + A ln n`, and for every `ε > 0` there is `c` with
`n d_n ≤ e_n + (1 + ε) log₂ (m_n + 1) + c` (or `d_n = 0`) for all `n ≥ 3`, then
`n d_n ≤ (1 + ε) log₂ ln n` eventually, for every `ε > 0`. -/
private theorem abs_prefixFreq_sub_half_le_km_arith
    (A : ℝ) (hA : 0 < A) (e d m : ℕ → ℝ)
    (he : e =o[atTop] (fun n : ℕ => Real.log (Real.log n)))
    (hm0 : ∀ n, 0 ≤ m n) (hm : ∀ n : ℕ, 3 ≤ n → m n ≤ 1 + A * Real.log n)
    (hcode : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, ∀ n : ℕ, 3 ≤ n →
      d n = 0 ∨ (n : ℝ) * d n ≤ e n + (1 + ε) * Real.logb 2 (m n + 1) + c) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (n : ℝ) * d n ≤ (1 + ε) * Real.logb 2 (Real.log n) := by
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨c, hc⟩ := hcode (ε / 3) hε3
  have hℓ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hℓ1 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have h1 : ∀ᶠ n : ℕ in atTop, ‖e n‖ ≤ (ε / 3) * ‖Real.log (Real.log n)‖ := he.def hε3
  have hΛ : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hL : Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log 2) atTop atTop :=
    hΛ.atTop_div_const hℓ
  have h2 : ∀ᶠ n : ℕ in atTop,
      3 * ((1 + ε / 3) * Real.logb 2 (2 + A) + c) / ε ≤ Real.logb 2 (Real.log n) :=
    hL.eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop 3, h1, h2] with n hn3 hen hLn
  have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hlog1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hΛpos : 0 < Real.log (Real.log n) := Real.log_pos hlog1
  have hLdef : Real.logb 2 (Real.log n) = Real.log (Real.log n) / Real.log 2 := rfl
  have hLnn : 0 ≤ Real.logb 2 (Real.log n) := Real.logb_nonneg (by norm_num) hlog1.le
  rcases hc n hn3 with hd | hd
  · rw [hd, mul_zero]
    exact mul_nonneg (by linarith) hLnn
  · have hm1 : m n + 1 ≤ (2 + A) * Real.log n := by
      have := hm n hn3
      nlinarith
    have hmpos : 0 < m n + 1 := by linarith [hm0 n]
    have hlogb : Real.logb 2 (m n + 1) ≤ Real.logb 2 (2 + A) + Real.logb 2 (Real.log n) := by
      calc Real.logb 2 (m n + 1) ≤ Real.logb 2 ((2 + A) * Real.log n) :=
            Real.logb_le_logb_of_le (by norm_num) hmpos hm1
        _ = Real.logb 2 (2 + A) + Real.logb 2 (Real.log n) :=
            Real.logb_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith))
    have hfact1 : e n ≤ ε / 3 * Real.logb 2 (Real.log n) := by
      have h' := hen
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hΛpos] at h'
      calc e n ≤ |e n| := le_abs_self _
        _ ≤ ε / 3 * Real.log (Real.log n) := h'
        _ ≤ ε / 3 * Real.logb 2 (Real.log n) := by
          apply mul_le_mul_of_nonneg_left _ hε3.le
          rw [hLdef, le_div_iff₀ hℓ]
          nlinarith
    have hfact2 : (1 + ε / 3) * Real.logb 2 (2 + A) + c ≤ ε / 3 * Real.logb 2 (Real.log n) := by
      rw [div_le_iff₀ hε] at hLn
      linarith
    have h3 := mul_le_mul_of_nonneg_left hlogb (show (0 : ℝ) ≤ 1 + ε / 3 by positivity)
    nlinarith [hd, h3, hfact1, hfact2]

/-- The frequency of ones in the `n`-bit prefix, as a ratio of real numbers. -/
private lemma abs_prefixFreq_sub_half_le_km_aux8_prefixFreq_eq (w : CantorSeq) (n : ℕ) :
    prefixFreq w n = ((cantorPrefix w n).count true : ℝ) / (n : ℝ) := by
  unfold prefixFreq freqOne
  push_cast
  rfl

/-- The frequency of ones lies in `[0, 1]`. -/
private lemma abs_prefixFreq_sub_half_le_km_aux8_bounds (w : CantorSeq) (n : ℕ) :
    0 ≤ prefixFreq w n ∧ prefixFreq w n ≤ 1 := by
  rw [abs_prefixFreq_sub_half_le_km_aux8_prefixFreq_eq]
  refine ⟨by positivity, ?_⟩
  by_cases hn : n = 0
  · simp [hn]
  · have h1 : ((cantorPrefix w n).count true : ℝ) ≤ n := by
      have H : (cantorPrefix w n).count true ≤ (cantorPrefix w n).length :=
        List.count_le_length
      rw [cantorPrefix_length] at H
      exact_mod_cast H
    have h2 : (0 : ℝ) < n := by positivity
    exact (div_le_one h2).mpr h1

/-- A boolean list splits into its `true` and `false` counts. -/
private lemma abs_prefixFreq_sub_half_le_km_aux8_count (s : List Bool) :
    s.count true + s.count false = s.length := by
  induction s with
  | nil => simp
  | cons b s ih => cases b <;> simp <;> omega

/-- The binary entropy function is symmetric about `1/2`. -/
private lemma abs_prefixFreq_sub_half_le_km_aux8_binaryEntropy_one_sub (x : ℝ) :
    binaryEntropy (1 - x) = binaryEntropy x := by
  unfold binaryEntropy
  rw [sub_sub_cancel, add_comm]

/-- Step 12 of the proof of `abs_prefixFreq_sub_half_le_km`: **pointwise bound**
(Steps 7, 8, 9).  For rational `θ ∈ (0, 1)` there are `A > 0` and `c : ℝ → ℝ` such that for every
sequence `w` and `n ≥ 3`, either `|p_n - 1/2| < 1/√n`, or there is a grid index `m ≥ 1`,
`m ≤ 1 + A ln n`, with `θ |p_n - 1/2| ≤ θ ^ m / 2 < 1/2` and, for every `ε > 0`,
`KM((ω)_n) ≤ n h(1/2 + θ ^ m / 2) + (1 + ε) log₂ (m + 1) + c ε`. -/
private theorem abs_prefixFreq_sub_half_le_km_pointwise
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D)
    (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ (A : ℝ) (c : ℝ → ℝ), 0 < A ∧ ∀ (w : CantorSeq) (n : ℕ), 3 ≤ n →
      |prefixFreq w n - 1 / 2| < 1 / Real.sqrt n ∨
      ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ 1 + A * Real.log n ∧
        (θ : ℝ) * |prefixFreq w n - 1 / 2| ≤ (θ : ℝ) ^ m / 2 ∧ (θ : ℝ) ^ m / 2 < 1 / 2 ∧
        ∀ ε : ℝ, 0 < ε →
          ((KMOf D (cantorPrefix w n)).toNat : ℝ) ≤
            (n : ℝ) * binaryEntropy (1 / 2 + (θ : ℝ) ^ m / 2) +
              (1 + ε) * Real.logb 2 ((m : ℝ) + 1) + c ε := by
  classical
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hL : 0 < Real.log (1 / (θ : ℝ)) := Real.log_pos (one_lt_one_div hθ0' hθ1')
  have hL' : Real.log (1 / (θ : ℝ)) ≠ 0 := hL.ne'
  -- the constants of the coding bound, as a function of `ε`
  have h7 : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, ∀ (m : ℕ) (s : ℝ), 1 ≤ m → (s = 1 ∨ s = -1) →
      ∀ x : BitString, ((KMOf D x).toNat : ℝ) ≤
        -Real.logb 2 ((1 / 2 + s * (θ : ℝ) ^ m / 2) ^ x.count true *
            (1 - (1 / 2 + s * (θ : ℝ) ^ m / 2)) ^ x.count false) +
          (1 + ε) * Real.logb 2 ((m : ℝ) + 1) + c :=
    fun ε hε => abs_prefixFreq_sub_half_le_km_coding_bound hD θ hθ0 hθ1 hε
  choose! c hc using h7
  refine ⟨1 / (2 * Real.log (1 / (θ : ℝ))), c, by positivity, ?_⟩
  intro w n hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  obtain ⟨hp0, hp1⟩ := abs_prefixFreq_sub_half_le_km_aux8_bounds w n
  by_cases hsmall : |prefixFreq w n - 1 / 2| < 1 / Real.sqrt n
  · exact Or.inl hsmall
  right
  have hge : 1 / Real.sqrt n ≤ |prefixFreq w n - 1 / 2| := not_lt.mp hsmall
  have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hδpos : 0 < |prefixFreq w n - 1 / 2| := lt_of_lt_of_le (one_div_pos.mpr hsq) hge
  have hδle : |prefixFreq w n - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨m, hm1, hm2, hm3, hm4⟩ := abs_prefixFreq_sub_half_le_km_geometric (θ : ℝ)
    hθ0' hθ1' |prefixFreq w n - 1 / 2| hδpos hδle
  -- the bound on the grid index
  have hlog1 : Real.log (1 / (2 * |prefixFreq w n - 1 / 2|)) ≤ Real.log n / 2 := by
    have h1 : 1 / (2 * |prefixFreq w n - 1 / 2|) ≤ Real.sqrt n := by
      rw [div_le_iff₀ (by positivity)]
      have h2 : 1 ≤ |prefixFreq w n - 1 / 2| * Real.sqrt n := by
        rw [div_le_iff₀ hsq] at hge
        exact hge
      nlinarith
    calc Real.log (1 / (2 * |prefixFreq w n - 1 / 2|)) ≤ Real.log (Real.sqrt n) :=
          Real.log_le_log (by positivity) h1
      _ = Real.log n / 2 := Real.log_sqrt hn0.le
  have hm_le : (m : ℝ) ≤ 1 + 1 / (2 * Real.log (1 / (θ : ℝ))) * Real.log n := by
    have h1 : ((m : ℝ) - 1) * Real.log (1 / (θ : ℝ)) ≤ Real.log n / 2 := hm4.trans hlog1
    have h2 : (m : ℝ) - 1 ≤ Real.log n / 2 / Real.log (1 / (θ : ℝ)) := by
      rw [le_div_iff₀ hL]; exact h1
    have h3 : Real.log n / 2 / Real.log (1 / (θ : ℝ)) =
        1 / (2 * Real.log (1 / (θ : ℝ))) * Real.log n := by
      field_simp
    linarith
  have hθm_lt : (θ : ℝ) ^ m < 1 := pow_lt_one₀ hθ0'.le hθ1' (by omega)
  have hθm_pos : 0 < (θ : ℝ) ^ m := pow_pos hθ0' m
  refine ⟨m, hm1, hm_le, hm3, by linarith, ?_⟩
  intro ε hε
  -- the sign of `p_n - 1/2`
  obtain ⟨s, hs, hsδ⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      s * (prefixFreq w n - 1 / 2) = |prefixFreq w n - 1 / 2| := by
    by_cases hpos : 0 < prefixFreq w n - 1 / 2
    · exact ⟨1, Or.inl rfl, by rw [one_mul, abs_of_pos hpos]⟩
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [abs_of_nonpos (not_lt.mp hpos)]; ring
  have habs_s : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hq0 : 0 < 1 / 2 + s * (θ : ℝ) ^ m / 2 := by
    rcases hs with rfl | rfl <;> nlinarith
  have hq1 : 1 / 2 + s * (θ : ℝ) ^ m / 2 < 1 := by
    rcases hs with rfl | rfl <;> nlinarith
  -- counts
  have hab : (cantorPrefix w n).count true + (cantorPrefix w n).count false = n := by
    have := abs_prefixFreq_sub_half_le_km_aux8_count (cantorPrefix w n)
    rwa [cantorPrefix_length] at this
  have hab_real : ((cantorPrefix w n).count true : ℝ) + ((cantorPrefix w n).count false : ℝ) = n :=
      by
    exact_mod_cast hab
  have hpab : prefixFreq w n = ((cantorPrefix w n).count true : ℝ) /
      (((cantorPrefix w n).count true : ℝ) + ((cantorPrefix w n).count false : ℝ)) := by
    rw [abs_prefixFreq_sub_half_le_km_aux8_prefixFreq_eq, hab_real]
  have hside : 0 ≤ ((1 / 2 + s * (θ : ℝ) ^ m / 2) - 1 / 2) *
      (((cantorPrefix w n).count true : ℝ) /
        (((cantorPrefix w n).count true : ℝ) + ((cantorPrefix w n).count false : ℝ)) - 1 / 2) := by
    rw [← hpab]
    have h1 : ((1 / 2 + s * (θ : ℝ) ^ m / 2) - 1 / 2) * (prefixFreq w n - 1 / 2) =
        (θ : ℝ) ^ m / 2 * (s * (prefixFreq w n - 1 / 2)) := by ring
    rw [h1, hsδ]
    exact mul_nonneg (div_nonneg hθm_pos.le (by norm_num)) (abs_nonneg _)
  have hmag : |(1 / 2 + s * (θ : ℝ) ^ m / 2) - 1 / 2| ≤
      |((cantorPrefix w n).count true : ℝ) /
        (((cantorPrefix w n).count true : ℝ) + ((cantorPrefix w n).count false : ℝ)) - 1 / 2| := by
    rw [← hpab]
    have h1 : (1 / 2 + s * (θ : ℝ) ^ m / 2) - 1 / 2 = s * ((θ : ℝ) ^ m / 2) := by ring
    rw [h1, abs_mul, habs_s, one_mul, abs_of_pos (by positivity)]
    exact hm2
  have h8 := abs_prefixFreq_sub_half_le_km_cross_entropy
    ((cantorPrefix w n).count true) ((cantorPrefix w n).count false)
    (1 / 2 + s * (θ : ℝ) ^ m / 2) hq0 hq1 hside hmag
  have h7' := hc ε hε m s hm1 hs (cantorPrefix w n)
  have hH : binaryEntropy (1 / 2 + s * (θ : ℝ) ^ m / 2) =
      binaryEntropy (1 / 2 + (θ : ℝ) ^ m / 2) := by
    rcases hs with rfl | rfl
    · have : (1 : ℝ) / 2 + 1 * (θ : ℝ) ^ m / 2 = 1 / 2 + (θ : ℝ) ^ m / 2 := by ring
      rw [this]
    · have : (1 : ℝ) / 2 + (-1) * (θ : ℝ) ^ m / 2 = 1 - (1 / 2 + (θ : ℝ) ^ m / 2) := by ring
      rw [this]
      exact abs_prefixFreq_sub_half_le_km_aux8_binaryEntropy_one_sub _
  rw [hab_real, hH] at h8
  linarith

/-- Step 13 of the proof of `abs_prefixFreq_sub_half_le_km`: a rational
`θ ∈ (0, 1)` with `(1 + ε/2) / θ ≤ 1 + ε`. -/
private theorem abs_prefixFreq_sub_half_le_km_theta (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℚ, 0 < θ ∧ θ < 1 ∧ (1 + ε / 2) / (θ : ℝ) ≤ 1 + ε := by
  have hlt : (1 + ε / 2) / (1 + ε) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hpos : (0 : ℝ) < (1 + ε / 2) / (1 + ε) := by positivity
  obtain ⟨θ, hθ1, hθ2⟩ := exists_rat_btwn hlt
  have hθpos : (0 : ℝ) < (θ : ℝ) := lt_trans hpos hθ1
  refine ⟨θ, by exact_mod_cast hθpos, by exact_mod_cast hθ2, ?_⟩
  rw [div_le_iff₀ hθpos]
  have h := (div_lt_iff₀ (by linarith : (0 : ℝ) < 1 + ε)).mp hθ1
  nlinarith

/-- **SUV Problem 243, p. 241.**  The conclusion of Theorem 156 holds for an arbitrary sequence with
`n - KM((ω)_n) = o(log log n)`. -/
private theorem abs_prefixFreq_sub_half_le_km {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) {w : CantorSeq}
    (hKM : (fun n : ℕ => (n : ℝ) - ((KMOf D (cantorPrefix w n)).toNat : ℝ)) =o[atTop]
      (fun n : ℕ => Real.log (Real.log n))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, |prefixFreq w n - 1 / 2| ≤
      (1 + ε) * Real.sqrt (Real.log (Real.log n) / (2 * n)) := by
  classical
  obtain ⟨θ, hθ0, hθ1, hθε⟩ := abs_prefixFreq_sub_half_le_km_theta ε hε
  obtain ⟨A, c, hA, hpt⟩ := abs_prefixFreq_sub_half_le_km_pointwise hD θ hθ0 hθ1
  have hθR0 : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  -- the indices at which the frequency is far from `1/2` carry a grid index `M n`
  have hex : ∀ n : ℕ, ∃ m : ℕ, (3 ≤ n ∧ ¬ (|prefixFreq w n - 1 / 2| < 1 / Real.sqrt n)) →
      (1 ≤ m ∧ (m : ℝ) ≤ 1 + A * Real.log n ∧
        (θ : ℝ) * |prefixFreq w n - 1 / 2| ≤ (θ : ℝ) ^ m / 2 ∧ (θ : ℝ) ^ m / 2 < 1 / 2 ∧
        ∀ ε : ℝ, 0 < ε →
          ((KMOf D (cantorPrefix w n)).toNat : ℝ) ≤
            (n : ℝ) * binaryEntropy (1 / 2 + (θ : ℝ) ^ m / 2) +
              (1 + ε) * Real.logb 2 ((m : ℝ) + 1) + c ε) := by
    intro n
    by_cases hn : 3 ≤ n ∧ ¬ (|prefixFreq w n - 1 / 2| < 1 / Real.sqrt n)
    · rcases hpt w n hn.1 with h | h
      · exact absurd h hn.2
      · obtain ⟨m, hm⟩ := h
        exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose M hM using hex
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, ∀ n, t n =
      if (3 ≤ n ∧ ¬ (|prefixFreq w n - 1 / 2| < 1 / Real.sqrt n)) then (θ : ℝ) ^ M n / 2
      else 0 := ⟨_, fun n => rfl⟩
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ → ℝ, ∀ n, m' n =
      if (3 ≤ n ∧ ¬ (|prefixFreq w n - 1 / 2| < 1 / Real.sqrt n)) then (M n : ℝ) else 0 :=
    ⟨_, fun n => rfl⟩
  have ht_good : ∀ n, (3 ≤ n ∧ ¬ (|prefixFreq w n - 1 / 2| < 1 / Real.sqrt n)) →
      t n = (θ : ℝ) ^ M n / 2 := by
    intro n hn
    rw [ht n, ite_eq_left hn]
  have ht_bad : ∀ n, ¬ (3 ≤ n ∧ ¬ (|prefixFreq w n - 1 / 2| < 1 / Real.sqrt n)) → t n = 0 := by
    intro n hn
    rw [ht n, ite_eq_right hn]
  have ht0 : ∀ n, 0 ≤ t n := by
    intro n
    by_cases hn : 3 ≤ n ∧ ¬ (|prefixFreq w n - 1 / 2| < 1 / Real.sqrt n)
    · rw [ht_good n hn]
      positivity
    · rw [ht_bad n hn]
  have ht1 : ∀ n, t n < 1 / 2 := by
    intro n
    by_cases hn : 3 ≤ n ∧ ¬ (|prefixFreq w n - 1 / 2| < 1 / Real.sqrt n)
    · rw [ht_good n hn]
      exact (hM n hn).2.2.2.1
    · rw [ht_bad n hn]
      norm_num
  have hm0 : ∀ n, 0 ≤ m' n := by
    intro n
    by_cases hn : 3 ≤ n ∧ ¬ (|prefixFreq w n - 1 / 2| < 1 / Real.sqrt n)
    · rw [hm' n, ite_eq_left hn]
      positivity
    · rw [hm' n, ite_eq_right hn]
  have hmA : ∀ n : ℕ, 3 ≤ n → m' n ≤ 1 + A * Real.log n := by
    intro n hn3
    by_cases hn : 3 ≤ n ∧ ¬ (|prefixFreq w n - 1 / 2| < 1 / Real.sqrt n)
    · rw [hm' n, ite_eq_left hn]
      exact (hM n hn).2.1
    · rw [hm' n, ite_eq_right hn]
      have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      positivity
  have hcode : ∀ ε' : ℝ, 0 < ε' → ∃ c' : ℝ, ∀ n : ℕ, 3 ≤ n →
      (1 - binaryEntropy (1 / 2 + t n)) = 0 ∨
        (n : ℝ) * (1 - binaryEntropy (1 / 2 + t n)) ≤
          ((n : ℝ) - ((KMOf D (cantorPrefix w n)).toNat : ℝ)) +
            (1 + ε') * Real.logb 2 (m' n + 1) + c' := by
    intro ε' hε'
    refine ⟨c ε', fun n _ => ?_⟩
    by_cases hn : 3 ≤ n ∧ ¬ (|prefixFreq w n - 1 / 2| < 1 / Real.sqrt n)
    · right
      rw [ht_good n hn, hm' n, ite_eq_left hn]
      have h := (hM n hn).2.2.2.2 ε' hε'
      nlinarith
    · left
      rw [ht_bad n hn]
      have h12 : (1 : ℝ) / 2 + 0 = 1 / 2 := by norm_num
      rw [h12, binaryEntropy_half_add_isLittleO_value]
      norm_num
  have hdef := abs_prefixFreq_sub_half_le_km_arith A hA
    (fun n : ℕ => (n : ℝ) - ((KMOf D (cantorPrefix w n)).toNat : ℝ))
    (fun n => 1 - binaryEntropy (1 / 2 + t n)) m' hKM hm0 hmA hcode
  have hana := abs_prefixFreq_sub_half_le_km_real_analytic t ht0 ht1 hdef (ε / 2)
    (by positivity)
  have hlog2 : ∀ᶠ n : ℕ in atTop, 2 ≤ Real.log (Real.log n) := by
    have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
      Real.tendsto_log_atTop.comp h1
    exact h2.eventually_ge_atTop 2
  filter_upwards [hana, hlog2, eventually_ge_atTop 3] with n hn hll hn3
  have hS : 0 ≤ Real.sqrt (Real.log (Real.log n) / (2 * n)) := Real.sqrt_nonneg _
  by_cases hg : 3 ≤ n ∧ ¬ (|prefixFreq w n - 1 / 2| < 1 / Real.sqrt n)
  · have h1 := (hM n hg).2.2.1
    rw [← ht_good n hg] at h1
    have h2 : (θ : ℝ) * |prefixFreq w n - 1 / 2| ≤
        (1 + ε / 2) * Real.sqrt (Real.log (Real.log n) / (2 * n)) := h1.trans hn
    have h3 : |prefixFreq w n - 1 / 2| ≤
        (1 + ε / 2) / (θ : ℝ) * Real.sqrt (Real.log (Real.log n) / (2 * n)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hθR0]
      linarith
    exact h3.trans (mul_le_mul_of_nonneg_right hθε hS)
  · have hlt : |prefixFreq w n - 1 / 2| < 1 / Real.sqrt n := by
      by_contra hcon
      exact hg ⟨hn3, hcon⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h1 : 1 / Real.sqrt n ≤ Real.sqrt (Real.log (Real.log n) / (2 * n)) := by
      rw [one_div, ← Real.sqrt_inv]
      apply Real.sqrt_le_sqrt
      rw [inv_eq_one_div, div_le_div_iff₀ hn0 (by positivity)]
      nlinarith
    have h2 : Real.sqrt (Real.log (Real.log n) / (2 * n)) ≤
        (1 + ε) * Real.sqrt (Real.log (Real.log n) / (2 * n)) := by
      nlinarith
    exact hlt.le.trans (h1.trans h2)

/-- **SUV Theorem 156, p. 239 (Vovk).**  For a Martin-Löf random sequence with respect to the
uniform measure and every `ε > 0`, the inequality `|p_n - 1/2| ≤ (1 + ε) √(ln ln n / 2n)` holds for
all sufficiently large `n`. -/
theorem abs_prefixFreq_sub_half_le {w : CantorSeq} (hw : IsMartinLofRandom uniformMeasure w) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, |prefixFreq w n - 1 / 2| ≤
      (1 + ε) * Real.sqrt (Real.log (Real.log n) / (2 * n)) := by
  obtain ⟨D, hD⟩ := exists_optimalMonotoneDecompressor
  -- Levin-Schnorr: `|KM((w)_n) - n| ≤ c` for a Martin-Löf random `w`
  obtain ⟨c, hc⟩ := (isMartinLofRandom_uniform_iff_KA_KMOf_eq_length hD w).mp hw
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0).2
  -- `O(1) = o(log log n)`
  have hC : (fun _ : ℕ => c) =o[atTop] (fun n : ℕ => Real.log (Real.log n)) :=
    (Real.isLittleO_const_log_atTop (c := c)).comp_tendsto
      ((Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop)
  have hB : (fun n : ℕ => (n : ℝ) - ((KMOf D (cantorPrefix w n)).toNat : ℝ)) =O[atTop]
      (fun _ : ℕ => c) :=
    IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => by
      have h := (hc n).2
      rw [abs_sub_comm] at h
      simpa [Real.norm_eq_abs, abs_of_nonneg hc0] using h)
  exact abs_prefixFreq_sub_half_le_km hD (hB.trans_isLittleO hC) hε

end Kolmogorov.Applications
