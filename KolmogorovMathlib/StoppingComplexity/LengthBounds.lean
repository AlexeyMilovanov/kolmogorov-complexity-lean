import KolmogorovMathlib.StoppingComplexity.Diagonalization
import KolmogorovMathlib.StoppingComplexity.FixedRatio
import KolmogorovMathlib.StoppingComplexity.UpperBound

/-!
# Explicit T3 lower bounds in the mass depth and in the string length

Blueprint 01 F0 (Targets T3-M and T3-LENGTH) and 04 §7–§8 (the fixed-ratio T3 parameters, the
explicit witnesses W1 and W2, Corollaries T3-B and T3-C).

The generic diagonalization theorem, applied to the reply bound `b c n = n + c` and the T3 word
family `fixedWordFamily` (module `FixedRatio`: exponents at most
`E_R = (2^{c+2} + 1)(c + 2) + 1`, requested vertices of length at most
`2^{(2^{c+3} + 1)(c + 2) + 3}` on every reachable history), gives ONE constant `a` and, for every
tag `c`, a string `z_c` extending `natCode c` with `g(z_c) > c - a`, `m(z_c) ≤ E_R + a` (W1) and
`|z_c| ≤ c + 1 + 2^{(2^{c+3} + 1)(c + 2) + 3}` (W2): this is `fixed_raw`. Comparing `c` with
`X = log₂ m(z_c)` (resp. `Y = log₂ log₂ |z_c|`) gives Corollaries T3-B and T3-C for all large
tags, stated as `∀ c ≥ c₀, ∃ z` below the tag `natCode c` because the witnesses `z_c` are not
Lean objects. U-local makes the mass depths of the witnesses unbounded and the tag makes their
lengths unbounded, which gives Targets T3-M and T3-LENGTH in the F0 form. The length theorem is
kept separate from the T3c theorem MAIN: the enormously larger termination bound of the variable
schedule does not preserve the useful length estimate.

All endpoint statements are about the fixed universal stopping machine and have no hypothesis;
the constants are natural numbers quantified before the tag, the cutoff or the length.
-/

namespace Kolmogorov

/-- **W1 and W2** (explicit T3 witnesses): there is ONE natural constant `a`, quantified before
the tag `c`, such that every `c` has a string `z` extending the tag `natCode c` with stopping gap
`g(z) > c - a`, mass depth `m(z) ≤ (2^{c+2} + 1)(c + 2) + 1 + a` (W1) and length
`|z| ≤ c + 1 + 2^{(2^{c+3} + 1)(c + 2) + 3}` (W2; the `c + 1` is the tag length). Diagonalization
for the reply bound `n + c` and the family `fixedWordFamily`; the exponent and height bounds
reach `z` through the export clause of `diagonalization` and the bridge lemmas
`fixedWordFamily_exp_le`, `fixedWordFamily_length_le`, and `m(z) ≤ n + a` is
`massDepth_le_of_two_pow_neg_le`. Blueprint 04 §8 (W1, W2). -/
theorem fixed_raw :
    ∃ a : ℕ, ∀ c : ℕ, ∃ z : BitString, natCode c <+: z ∧ (c : ℝ) - a < stoppingGap z ∧
      massDepth z ≤ ((2 ^ (c + 2) + 1) * (c + 2) + 1 : ℕ) + a ∧
      z.length ≤ c + 1 + 2 ^ ((2 ^ (c + 3) + 1) * (c + 2) + 3) := by
  have hb : Computable₂ fun c n : ℕ => n + c :=
    Primrec.nat_add.to_comp.comp Computable.snd Computable.fst
  obtain ⟨a, ha⟩ := diagonalization (fun c n => n + c) hb fixedWordFamily
    fixedWordFamily_computable _ fixedWordFamily_winning
  refine ⟨a, fun c => ?_⟩
  obtain ⟨x, n, ⟨h, hh, hσ⟩, hK, hM⟩ := ha c
  have hn : n ≤ (2 ^ (c + 2) + 1) * (c + 2) + 1 := by
    have := fixedWordFamily_exp_le hh
    rwa [hσ] at this
  have hx : x.length ≤ 2 ^ ((2 ^ (c + 3) + 1) * (c + 2) + 3) := by
    have := fixedWordFamily_length_le hh
    rwa [hσ] at this
  refine ⟨natCode c ++ x, List.prefix_append _ _, ?_, ?_, ?_⟩
  · have hK' : ((n : ℕ∞) + ((0 : ℕ) : ℕ∞) + c) < univStopComplexity (natCode c ++ x) := by
      simpa using hK
    have := stoppingGap_gt_of_raw (f := fun _ => 0) hK' hM
    simpa using this
  · have hm := massDepth_le_of_two_pow_neg_le hM
    have hn' : (n : ℝ) ≤ ((2 ^ (c + 2) + 1) * (c + 2) + 1 : ℕ) := by exact_mod_cast hn
    linarith
  · rw [List.length_append, length_natCode]
    omega

/-- The case analysis of Corollaries T3-B and T3-C: if `2 ≤ X ≤ c + d + log₂ (c + 2)` with
`c ≥ 0`, then `X - log₂ X - (d + 1) ≤ c`. Either `c ≥ X`, or `c + 2 ≤ 2X`, whence
`log₂ (c + 2) ≤ 1 + log₂ X` and the hypothesis becomes `X ≤ c + d + 1 + log₂ X`.
Blueprint 04 Corollaries T3-B and T3-C (the case split on `c` versus `X`). -/
private theorem sub_logb_sub_le_of_le_add_logb {X c : ℝ} {d : ℕ} (hX : 2 ≤ X) (hc : 0 ≤ c)
    (h : X ≤ c + d + Real.logb 2 (c + 2)) : X - Real.logb 2 X - (d + 1) ≤ c := by
  have hlogX : 1 ≤ Real.logb 2 X := by
    rw [← Real.logb_self_eq_one (b := 2) (by norm_num)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hX
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rcases le_or_gt X c with hXc | hXc
  · linarith
  · have hlog : Real.logb 2 (c + 2) ≤ 1 + Real.logb 2 X := by
      calc Real.logb 2 (c + 2) ≤ Real.logb 2 (2 * X) :=
            Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
        _ = 1 + Real.logb 2 X := by
            rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)]
    linarith

/-- T3-B for one W1 witness: for a tag `c ≥ a`, a string with `m(z) ≥ 4`, `g(z) > c - a` and
`m(z) ≤ (2^{c+2} + 1)(c + 2) + 1 + a` has `g(z) > log₂ m(z) - log₂ log₂ m(z) - (a + 4)`: the
mass bound gives `m(z) ≤ 2^{c+3} (c + 2)`, so `X = log₂ m(z)` satisfies
`2 ≤ X ≤ c + 3 + log₂ (c + 2)`, and the case split gives `c ≥ X - log₂ X - 4`.
Blueprint 04 Corollary T3-B (proof). -/
private theorem logMass_sub_lt_stoppingGap_of_W1 {a c : ℕ} {z : BitString} (hac : a ≤ c)
    (hm4 : 4 ≤ massDepth z) (hg : (c : ℝ) - a < stoppingGap z)
    (hm : massDepth z ≤ ((2 ^ (c + 2) + 1) * (c + 2) + 1 : ℕ) + a) :
    Real.logb 2 (massDepth z) - Real.logb 2 (Real.logb 2 (massDepth z)) - (a + 4) <
      stoppingGap z := by
  have hbound : massDepth z ≤ 2 ^ (c + 3) * ((c : ℝ) + 2) := by
    have h4 : 4 ≤ 2 ^ (c + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (c + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : (2 ^ (c + 2) + 1) * (c + 2) + 1 + a ≤ 2 ^ (c + 3) * (c + 2) := by
      have h8 : 2 ^ (c + 3) = 2 * 2 ^ (c + 2) := by ring
      rw [h8]
      nlinarith
    have h1' : (((2 ^ (c + 2) + 1) * (c + 2) + 1 + a : ℕ) : ℝ) ≤ 2 ^ (c + 3) * ((c : ℝ) + 2) := by
      exact_mod_cast h1
    push_cast at hm h1'
    linarith
  have hpos : 0 < massDepth z := by linarith
  have hX : Real.logb 2 (massDepth z) ≤ c + 3 + Real.logb 2 (c + 2) := by
    calc Real.logb 2 (massDepth z) ≤ Real.logb 2 (2 ^ (c + 3) * ((c : ℝ) + 2)) :=
          Real.logb_le_logb_of_le (by norm_num) hpos hbound
      _ = c + 3 + Real.logb 2 (c + 2) := by
          rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
            Real.logb_self_eq_one (by norm_num)]
          push_cast
          ring
  have hX2 : 2 ≤ Real.logb 2 (massDepth z) := by
    calc (2 : ℝ) = Real.logb 2 (2 ^ 2) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
          norm_num
      _ ≤ Real.logb 2 (massDepth z) :=
          Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num; linarith)
  have hcore := sub_logb_sub_le_of_le_add_logb (d := 3) hX2 (Nat.cast_nonneg c)
    (by push_cast; linarith)
  have hac' : (a : ℝ) ≤ c := by exact_mod_cast hac
  push_cast at hcore
  linarith

/-- **Corollary T3-B**, in a Lean-expressible form: there are naturals `a` and `c₀` such that for
every tag `c ≥ c₀` some string `z` extending `natCode c` has mass depth `m(z) ≥ 4` and stopping gap
`g(z) > log₂ m(z) - log₂ log₂ m(z) - (a + 4)`. The blueprint's "for all sufficiently large `c`,
the witness `z_c` satisfies" is stated as `∀ c ≥ c₀, ∃ z` below the tag (the witnesses of W1 are
not Lean objects; distinct tags give distinct strings). Blueprint 04 Corollary T3-B. -/
theorem stoppingGap_logMass_lowerBound_eventually :
    ∃ a c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∃ z : BitString, natCode c <+: z ∧ 4 ≤ massDepth z ∧
      Real.logb 2 (massDepth z) - Real.logb 2 (Real.logb 2 (massDepth z)) - (a + 4) <
        stoppingGap z := by
  obtain ⟨a, ha⟩ := fixed_raw
  choose z hz using ha
  obtain ⟨c₁, hc₁⟩ := massDepth_unbounded_of_stoppingGap_gt (fun c => (hz c).2.1) 4
  refine ⟨a, max a c₁, fun c hc => ?_⟩
  have h4 : 4 ≤ massDepth (z c) := (hc₁ c (le_of_max_le_right hc)).le
  exact ⟨z c, (hz c).1, h4, logMass_sub_lt_stoppingGap_of_W1 (le_of_max_le_left hc) h4
    (hz c).2.1 (hz c).2.2.1⟩

/-- T3-C for one W2 witness: for a tag `c ≥ a`, a string with `|z| ≥ 16`, `g(z) > c - a` and
`|z| ≤ c + 1 + 2^A`, `A = (2^{c+3} + 1)(c + 2) + 3`, has
`g(z) > log₂ log₂ |z| - log₂ log₂ log₂ |z| - (a + 5)`: `|z| ≤ 2^{A+1}` and
`A + 1 ≤ 2^{c+4} (c + 2)` give `Y = log₂ log₂ |z| ≤ c + 4 + log₂ (c + 2)`, `|z| ≥ 16` gives
`Y ≥ 2`, and the case split gives `c ≥ Y - log₂ Y - 5`. Blueprint 04 Corollary T3-C (proof). -/
private theorem logLength_sub_lt_stoppingGap_of_W2 {a c : ℕ} {z : BitString} (hac : a ≤ c)
    (h16 : 16 ≤ z.length) (hg : (c : ℝ) - a < stoppingGap z)
    (hlen : z.length ≤ c + 1 + 2 ^ ((2 ^ (c + 3) + 1) * (c + 2) + 3)) :
    Real.logb 2 (Real.logb 2 z.length) - Real.logb 2 (Real.logb 2 (Real.logb 2 z.length)) -
      (a + 5) < stoppingGap z := by
  set A := (2 ^ (c + 3) + 1) * (c + 2) + 3 with hA
  have hcA : c + 1 ≤ 2 ^ A := by
    have h1 : c + 1 ≤ A := by
      rw [hA]
      nlinarith [Nat.one_le_two_pow (n := c + 3)]
    exact le_trans (Nat.lt_two_pow_self (n := c + 1)).le (Nat.pow_le_pow_right (by norm_num) h1)
  have hn : z.length ≤ 2 ^ (A + 1) := by
    rw [pow_succ]
    omega
  have hA1 : A + 1 ≤ 2 ^ (c + 4) * (c + 2) := by
    have h8 : 8 ≤ 2 ^ (c + 3) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (c + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h16' : 2 ^ (c + 4) = 2 * 2 ^ (c + 3) := by ring
    rw [hA, h16']
    nlinarith
  have hlen0 : (0 : ℝ) < z.length := by
    have : (16 : ℝ) ≤ z.length := by exact_mod_cast h16
    linarith
  have hlog4 : 4 ≤ Real.logb 2 z.length := by
    calc (4 : ℝ) = Real.logb 2 (2 ^ 4) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
          norm_num
      _ ≤ Real.logb 2 z.length :=
          Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num; exact_mod_cast h16)
  have hlogn : Real.logb 2 z.length ≤ 2 ^ (c + 4) * ((c : ℝ) + 2) := by
    have hn' : (z.length : ℝ) ≤ 2 ^ (A + 1) := by exact_mod_cast hn
    have hA1' : ((A + 1 : ℕ) : ℝ) ≤ 2 ^ (c + 4) * ((c : ℝ) + 2) := by exact_mod_cast hA1
    calc Real.logb 2 z.length ≤ Real.logb 2 (2 ^ (A + 1)) :=
          Real.logb_le_logb_of_le (by norm_num) hlen0 hn'
      _ = ((A + 1 : ℕ) : ℝ) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
      _ ≤ 2 ^ (c + 4) * ((c : ℝ) + 2) := hA1'
  have hY : Real.logb 2 (Real.logb 2 z.length) ≤ c + 4 + Real.logb 2 (c + 2) := by
    calc Real.logb 2 (Real.logb 2 z.length) ≤ Real.logb 2 (2 ^ (c + 4) * ((c : ℝ) + 2)) :=
          Real.logb_le_logb_of_le (by norm_num) (by linarith) hlogn
      _ = c + 4 + Real.logb 2 (c + 2) := by
          rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
            Real.logb_self_eq_one (by norm_num)]
          push_cast
          ring
  have hY2 : 2 ≤ Real.logb 2 (Real.logb 2 z.length) := by
    calc (2 : ℝ) = Real.logb 2 (2 ^ 2) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
          norm_num
      _ ≤ Real.logb 2 (Real.logb 2 z.length) :=
          Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num; linarith)
  have hcore := sub_logb_sub_le_of_le_add_logb (d := 4) hY2 (Nat.cast_nonneg c)
    (by push_cast; linarith)
  have hac' : (a : ℝ) ≤ c := by exact_mod_cast hac
  push_cast at hcore
  linarith

/-- **Corollary T3-C**, in a Lean-expressible form: there are naturals `a` and `c₀` such that for
every tag `c ≥ c₀` some string `z` extending `natCode c` has length `|z| ≥ 16` and stopping gap
`g(z) > log₂ log₂ |z| - log₂ log₂ log₂ |z| - (a + 5)`. Same form as T3-B; since `|z| ≥ c + 1`,
this holds at arbitrarily large string lengths. Blueprint 04 Corollary T3-C. -/
theorem stoppingGap_logLength_lowerBound_eventually :
    ∃ a c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∃ z : BitString, natCode c <+: z ∧ 16 ≤ z.length ∧
      Real.logb 2 (Real.logb 2 z.length) - Real.logb 2 (Real.logb 2 (Real.logb 2 z.length)) -
        (a + 5) < stoppingGap z := by
  obtain ⟨a, ha⟩ := fixed_raw
  refine ⟨a, max a 15, fun c hc => ?_⟩
  obtain ⟨z, hpre, hg, -, hlen⟩ := ha c
  have h16 : 16 ≤ z.length := by
    have h1 := hpre.length_le
    have h2 := le_of_max_le_right hc
    rw [length_natCode] at h1
    omega
  exact ⟨z, hpre, h16, logLength_sub_lt_stoppingGap_of_W2 (le_of_max_le_left hc) h16 hg hlen⟩

/-- **Target T3-M**: there is a natural constant `C` such that for every real `T` some string `z`
has mass depth `m(z) ≥ max(16, T)` and stopping gap `g(z) ≥ log₂ m(z) - log₂ log₂ m(z) - C`
(`C = a + 4` from Corollary T3-B; U-local makes the mass depths of the T3 witnesses unbounded).
Stated unconditionally about the fixed universal machine, with `C` quantified before `T`.
Blueprint F0 Target T3-M. -/
theorem stoppingGap_logMass_lowerBound :
    ∃ C : ℕ, ∀ T : ℝ, ∃ z : BitString, max 16 T ≤ massDepth z ∧
      Real.logb 2 (massDepth z) - Real.logb 2 (Real.logb 2 (massDepth z)) - C ≤ stoppingGap z := by
  obtain ⟨a, ha⟩ := fixed_raw
  choose z hz using ha
  refine ⟨a + 4, fun T => ?_⟩
  obtain ⟨c₁, hc₁⟩ := massDepth_unbounded_of_stoppingGap_gt (fun c => (hz c).2.1) (max 16 T)
  have hT := hc₁ (max a c₁) (le_max_right _ _)
  have h4 : 4 ≤ massDepth (z (max a c₁)) := by
    have := le_max_left 16 T
    linarith
  refine ⟨z (max a c₁), hT.le, ?_⟩
  have := logMass_sub_lt_stoppingGap_of_W1 (le_max_left a c₁) h4 (hz (max a c₁)).2.1
    (hz (max a c₁)).2.2.1
  push_cast
  linarith

/-- **Target T3-LENGTH**: there is a natural constant `C` such that for every natural `N` some
string `z` has length `|z| ≥ max(16, N)` and stopping gap
`g(z) ≥ log₂ log₂ |z| - log₂ log₂ log₂ |z| - C` (`C = a + 5` from Corollary T3-C). Kept separate
from T3-M and from MAIN (F0: the T3c termination bound does not preserve the length estimate).
Stated unconditionally about the fixed universal machine, with `C` quantified before `N`.
Blueprint F0 Target T3-LENGTH. -/
theorem stoppingGap_logLength_lowerBound :
    ∃ C : ℕ, ∀ N : ℕ, ∃ z : BitString, max 16 N ≤ z.length ∧
      Real.logb 2 (Real.logb 2 z.length) - Real.logb 2 (Real.logb 2 (Real.logb 2 z.length)) - C ≤
        stoppingGap z := by
  obtain ⟨a, c₀, hc⟩ := stoppingGap_logLength_lowerBound_eventually
  use a + 5
  intro N
  let c := max c₀ N
  obtain ⟨z, hprefix, hlen16, hgap⟩ := hc c (le_max_left _ _)
  use z
  constructor
  · apply max_le
    · exact hlen16
    · have h1 : c + 1 ≤ z.length := by
        calc c + 1 = (natCode c).length := (length_natCode c).symm
             _ ≤ z.length := List.IsPrefix.length_le hprefix
      have h2 : N ≤ c := le_max_right _ _
      omega
  · have h_cast : (a : ℝ) + 5 = ((a + 5 : ℕ) : ℝ) := by push_cast; rfl
    rw [← h_cast]
    exact le_of_lt hgap

end Kolmogorov
