import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionSnapshot
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution

namespace Kolmogorov

open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- The binary length `(Nat.bits ·).length` of `k` is at most `k`. -/
theorem length_natBits_le_self (k : ℕ) : (Nat.bits k).length ≤ k := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

/-- **Conditional computable-reconstruction bound.**  If `g` is computable
uniformly in its condition argument `y` and its data argument `x`, then
reconstructing `g y x` from the same condition `y` costs no more than `x` itself,
up to an additive constant: `KP U (g y x) y ≤ KP U x y + O(1)`.

This is the conditional analogue of `KP_map_le` (which maps only the data
argument) and of `KP_cond_map_le` (which maps only the condition).  It is the
coding tool behind `description_count_of_conditional_complexity_gap`: there the
model `A`'s canonical code is reconstructed, in the context of `x` (and `K(x)`),
from a short index, i.e. as `g y (index)` with `y` the context carrying `x`. -/
theorem KP_cond_first_map_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (g : BitString → BitString → BitString)
    (hg : Computable (fun p : BitString × BitString => g p.1 p.2)) :
    ∃ c : ℕ, ∀ x y, KP U (g y x) y ≤ KP U x y + (c : ENat) := by
  -- Mirror of `KP_map_le`: post-compose `U` with `g (condition) (·)`.
  let D : Map := fun pr => (U pr).map (g pr.2)
  have hD_decomp : isDecompressor D := by
    refine Partrec.map hU.isDecompressor ?_
    exact hg.comp ((Computable.snd.comp Computable.fst).pair Computable.snd)
  have hD_prefix : IsPrefixMachine D := by
    intro y p hp q hq hpre
    have hp' : (U (p, y)).Dom := hp
    have hq' : (U (q, y)).Dom := hq
    exact hU.isPrefixMachine y hp' hq' hpre
  have hD : IsPrefixDecompressor D := ⟨hD_decomp, hD_prefix⟩
  obtain ⟨c, hc⟩ := hU.invariance hD
  refine ⟨c, fun x y => ?_⟩
  refine le_trans (hc (g y x) y) ?_
  gcongr
  apply sInf_le_sInf
  rintro n ⟨p, ⟨h_dom, h_eq⟩, rfl⟩
  exact ⟨p, ⟨h_dom, by simp [D, h_eq]⟩, rfl⟩

/-- **Partial-recursive conditional reconstruction bound.**  The partial-recursive
analogue of `KP_cond_first_map_le` (and the conditional analogue of
`KPPlain_partrec_map_le`): if `w` is obtained by a partial-recursive map `f` from
a condition `y` and data `x`, then `KP U w y ≤ KP U x y + O(1)`.

This is the exact coding tool for `description_count_of_conditional_complexity_gap`:
there the model code is reconstructed by a *partial* enumerator (enumerate the
finitely many `(i,j)`-descriptions of `x` and return the indexed one), so the
total-map form does not apply and this partial form is required. -/
theorem KP_partrec_cond_first_map_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString →. BitString)
    (hf : Partrec (fun p : BitString × BitString => f p.2 p.1)) :
    ∃ c : ℕ, ∀ x w y : BitString, w ∈ f y x → KP U w y ≤ KP U x y + (c : ENat) := by
  classical
  set D : Map := fun pr => (U pr).bind (fun z => f pr.2 z) with hDdef
  have hD_decomp : isDecompressor D := by
    have : Partrec (fun pr : BitString × BitString => (U pr).bind (fun z => f pr.2 z)) :=
      Partrec.bind hU.isDecompressor
        (hf.comp (Computable.snd.pair (Computable.snd.comp Computable.fst)))
    exact this
  have hD_sub : ∀ y, domainAt D y ⊆ domainAt U y := by
    intro y p hp
    simp only [domainAt, Set.mem_setOf_eq, hDdef] at hp ⊢
    exact hp.fst
  have hD_prefix : IsPrefixMachine D := fun y =>
    (hU.isPrefixMachine y).mono (hD_sub y)
  have hD_pd : IsPrefixDecompressor D := ⟨hD_decomp, hD_prefix⟩
  obtain ⟨c, hc⟩ := hU.invariance hD_pd
  refine ⟨c, fun x w y hw => ?_⟩
  by_cases hx : KP U x y = ⊤
  · rw [hx, top_add]; exact le_top
  · obtain ⟨p, hp_prod, hp_len⟩ := exists_program_of_KP_ne_top hx
    have hprodD : produces D p y w := by
      simp only [produces, hDdef]
      exact Part.mem_bind_iff.mpr ⟨x, hp_prod, hw⟩
    calc
      KP U w y ≤ KP D w y + (c : ENat) := hc w y
      _ ≤ (programLength p : ENat) + (c : ENat) := by
            gcongr; exact KP_le_programLength_of_produces hprodD
      _ = KP U x y + (c : ENat) := by rw [hp_len]

/--
The optimality-deficiency hypothesis bounds the set complexity: if the uniform
model on `A` has set-optimality deficiency `≤ delta` at `x ∈ A`, then
`setComplexity U A hA ≤ KPPlain U x + delta`.

This is the fact that makes the corrected `logSlack c (n + delta + d)` slack of the
gap-counting bridge and Theorem 4 achievable: the complexity level `i :=
setComplexity U A hA`, which is otherwise an unbounded free parameter, is here
pinned to `KPPlain U x + delta ≤ n + O(log n) + delta`, so `logSlack c (n + i + j)`
can be folded into `logSlack c (n + delta + d)` (up to a constant via
`logSlack_add_le`/`logSlack_mono_right`) rather than escaping the budget. -/
theorem setComplexity_le_of_setOptimalityDeficiency {U : Map} {A : Finset BitString}
    {hA : A.Nonempty} {x : BitString} {delta : ℕ}
    (hxA : x ∈ A) (hdef : SetOptimalityDeficiencyLe U A hA x delta) :
    setComplexity U A hA ≤ KPPlain U x + (delta : ENat) := by
  rw [setOptimalityDeficiencyLe_iff_of_mem hxA] at hdef
  rcases eq_or_ne (KPPlain U x) ⊤ with htop | hfin
  · rw [htop]; exact le_top
  · refine le_add_nat_of_complexityWeight_le hfin ?_
    -- Drop the `(A.card)⁻¹ ≤ 1` factor, then cancel `2^delta` against `2⁻¹^delta`.
    have hcard1 : (A.card : ℝ≥0∞)⁻¹ ≤ 1 := by
      rw [ENNReal.inv_le_one]; exact_mod_cast hA.card_pos
    have h' : complexityWeight (KPPlain U x)
        ≤ (2 : ℝ≥0∞) ^ delta * complexityWeight (setComplexity U A hA) := by
      refine hdef.trans ?_
      calc (2 : ℝ≥0∞) ^ delta * (complexityWeight (setComplexity U A hA) * (A.card : ℝ≥0∞)⁻¹)
          ≤ (2 : ℝ≥0∞) ^ delta * (complexityWeight (setComplexity U A hA) * 1) := by gcongr
        _ = (2 : ℝ≥0∞) ^ delta * complexityWeight (setComplexity U A hA) := by rw [mul_one]
    calc (2 : ℝ≥0∞)⁻¹ ^ delta * complexityWeight (KPPlain U x)
        ≤ (2 : ℝ≥0∞)⁻¹ ^ delta *
          ((2 : ℝ≥0∞) ^ delta * complexityWeight (setComplexity U A hA)) := by
          gcongr
      _ = ((2 : ℝ≥0∞)⁻¹ * 2) ^ delta * complexityWeight (setComplexity U A hA) := by
          rw [mul_pow]; ring
      _ = complexityWeight (setComplexity U A hA) := by
          rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, one_mul]

/-
The conditional-deficiency hypothesis bounds the size of `A`: if the uniform model on `A`
has deficiency `≤ d` at `x`, then `j` can be chosen bounded by `d + KP(x|code)`.
-/
theorem card_le_of_deficiency {U : Map} {A : Finset BitString} {hA : A.Nonempty}
    {x : BitString} {d : ℕ} (hx : x ∈ A)
    (hdef : CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d) :
    ∃ j : ℕ, A.card ≤ 2 ^ j ∧ (j : ENat) ≤ KP U x (codedUniformOn A hA).code + (d : ENat) := by
  by_cases h : KP U x ( codedUniformOn A hA |> CodedFiniteDistribution.code ) = ⊤;
  · refine ⟨A.card, Nat.le_of_lt ?_, by simp only [h, top_add, le_top]⟩
    exact Nat.recOn A.card (by norm_num) fun n ihn => by
      norm_num [Nat.pow_succ] at *
      linarith
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, KP U x (codedUniformOn A hA).code = k :=
      (ENat.ne_top_iff_exists.mp h).imp fun m hm => hm.symm
    refine ⟨ d + k, ?_, ?_ ⟩
    · have h_card : (A.card : ENNReal) ≤ (2 : ENNReal) ^ d * (2 : ENNReal) ^ k := by
        have h_card : (2 : ENNReal)⁻¹ ^ k ≤ (2 : ENNReal) ^ d * (A.card : ENNReal)⁻¹ := by
          convert hdef using 1;
          unfold CodedFiniteDistribution.DeficiencyLe
          simp only [hk, codedUniformOn_mass_of_mem A hA x hx, complexityWeight_coe, mul_comm]
        have h_card_2 : (A.card : ENNReal) * (2 : ENNReal)⁻¹ ^ k ≤ (2 : ENNReal) ^ d := by
          refine le_trans ( mul_le_mul_right h_card _ ) ?_
          rw [ mul_left_comm, ENNReal.mul_inv_cancel ]
          · exact le_of_eq (mul_one _)
          · exact mod_cast ne_of_gt (Finset.card_pos.mpr hA)
          · exact ENNReal.natCast_ne_top _
        refine le_trans ?_ ( mul_le_mul_left h_card_2 _ )
        have h_cancel2 : (2 : ENNReal)⁻¹ ^ k * (2 : ENNReal) ^ k = 1 := by
          rw [← mul_pow, ENNReal.inv_mul_cancel, one_pow]
          · norm_num
          · norm_num
        rw [mul_assoc, h_cancel2, mul_one]
      rw [pow_add]
      exact mod_cast h_card
    · rw [hk]
      push_cast
      exact le_of_eq (add_comm _ _)

/--
**Numeric input for the gap lower bound (S1).**  The two deficiency hypotheses,
read additively, pin down both quantitative sides used by the symmetry-of-information
argument in `gap_lowerBound_conditional_setComplexity`:

* the set-optimality deficiency bounds the **complexity** level,
  `setComplexity U A hA ≤ KPPlain U x + delta` (via
  `setComplexity_le_of_setOptimalityDeficiency`);
* the conditional deficiency bounds the **size** level: some `j` with
  `A.card ≤ 2 ^ j` and `j ≤ KP U x A.code + d` (via `card_le_of_deficiency`).

This is the honest packaging of the two proven deficiency lemmas; it replaces an
earlier formulation that demanded a *single* `j` simultaneously satisfying
`A.card ≤ 2 ^ j` and `j + setComplexity ≤ KPPlain + delta`, which is only possible
when `|A|` is an exact power of two and is therefore false in general. -/
theorem gap_deficiency_numeric_bound (U : Map) (A : Finset BitString) (hA : A.Nonempty)
    (x : BitString) (delta d : ℕ) (hx : x ∈ A)
    (h_opt : SetOptimalityDeficiencyLe U A hA x delta)
    (h_cond : CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d) :
    setComplexity U A hA ≤ KPPlain U x + (delta : ENat) ∧
    ∃ j : ℕ, A.card ≤ 2 ^ j ∧
      (j : ENat) ≤ KP U x (codedUniformOn A hA).code + (d : ENat) :=
  ⟨setComplexity_le_of_setOptimalityDeficiency hx h_opt, card_le_of_deficiency hx h_cond⟩

theorem gap_lowerBound_KPPair (U : Map) (hU : IsOptimalPrefixConditional U)
    (x code : BitString) (kx : ℕ) (hkx : HasPrefixComplexityValue U x kx) :
    ∃ c : ℕ,
      KPPlain U x + KP U code (prefixComplexityContext x kx) ≤ KPPair U x code +
        (c : ENat) := by
  obtain ⟨c, hc⟩ := KPPair_chain_lower U hU
  exact ⟨c, hc x code kx hkx⟩

/-- Monotonicity of `logSlack` in its visible-budget argument. -/
theorem logSlack_mono {c a b : ℕ} (h : a ≤ b) : logSlack c a ≤ logSlack c b := by
  unfold logSlack
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (length_natBits_mono h)) c

/-- Absorbing an additive constant into the `logSlack` slack constant. -/
theorem logSlack_add_const_le (c c' n : ℕ) : logSlack c n + c' ≤ logSlack (c + c') n := by
  unfold logSlack
  nlinarith [Nat.zero_le (c' * (Nat.bits n).length)]

/-- A dyadic bracket bound (multiplicative `ENNReal` form): if `2^j/2 ≤ c ≤ 2^j'`
then `j ≤ j' + 1`.  This matches the `RealizedSetOptimalityGap` size hypothesis
`(2 : ENNReal) ^ j / 2 ≤ A.card`. -/
theorem two_pow_half_ennreal_bracket_le {j j' c : ℕ}
    (h1 : (2 : ENNReal) ^ j / 2 ≤ (c : ENNReal)) (h2 : c ≤ 2 ^ j') : j ≤ j' + 1 := by
  rw [ENNReal.div_le_iff (by norm_num) (by norm_num)] at h1
  have h1' : (2 : ENNReal) ^ j ≤ (2 * c : ℕ) := by
    push_cast; rw [mul_comm]; exact h1
  have h1n : 2 ^ j ≤ 2 * c := by exact_mod_cast h1'
  have hpow : 2 ^ j ≤ 2 ^ (j' + 1) := by
    calc 2 ^ j ≤ 2 * c := h1n
      _ ≤ 2 * 2 ^ j' := by omega
      _ = 2 ^ (j' + 1) := by rw [pow_succ]; ring
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  omega

/-- **Conditional chain rule, index-drop form (log slack).**

Removing an extra numeric index `i` from the right-hand condition costs at most
the complexity of `i`, hence only logarithmic visible slack:
`KP U x code ≤ KP U x (prefixComplexityContext code i) + logSlack c (i+1)`.

Direct corollary of `KP_cond_remove_short_info` (the conditional
symmetry-of-information machinery in `Prefix.ConditionalSymmetry`) at
`z := natCode i`, plus the logarithmic plain-complexity bound for `natCode`. -/
theorem KP_le_prefixComplexityContext_add_logSlack
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x code : BitString) (i : ℕ),
      KP U x code ≤ KP U x (prefixComplexityContext code i) + (logSlack c (i + 1) : ENat) := by
  obtain ⟨c_rem, hc_rem⟩ := KP_cond_remove_short_info U hU
  obtain ⟨c_log, hc_log⟩ := KPPlain_natCode_le_log U hU
  refine ⟨c_log + c_rem + 2, fun x code i => ?_⟩
  have hnat : 2 * (Nat.bits i).length + c_log + c_rem
      ≤ logSlack (c_log + c_rem + 2) (i + 1) := by
    have hmono : (Nat.bits i).length ≤ (Nat.bits (i + 1)).length :=
      length_natBits_mono (Nat.le_succ i)
    have hpos : 1 ≤ (Nat.bits (i + 1)).length := by
      have h0 : 0 < Nat.size (i + 1) := Nat.size_pos.mpr (Nat.succ_pos i)
      have hsz : (Nat.bits (i + 1)).length = Nat.size (i + 1) := by rw [Nat.size_eq_bits_len]
      omega
    unfold logSlack
    nlinarith
  have hbound : KPPlain U (natCode i) + (c_rem : ENat)
      ≤ (logSlack (c_log + c_rem + 2) (i + 1) : ENat) := by
    calc KPPlain U (natCode i) + (c_rem : ENat)
        ≤ 2 * (Nat.bits i).length + (c_log : ENat) + (c_rem : ENat) :=
          add_le_add (hc_log i) le_rfl
      _ = ((2 * (Nat.bits i).length + c_log + c_rem : ℕ) : ENat) := by push_cast; ring
      _ ≤ (logSlack (c_log + c_rem + 2) (i + 1) : ENat) := by exact_mod_cast hnat
  calc KP U x code
      ≤ KP U x (pairCode code (natCode i)) + KPPlain U (natCode i) + (c_rem : ENat) :=
        hc_rem x code (natCode i)
    _ = KP U x (prefixComplexityContext code i)
          + (KPPlain U (natCode i) + (c_rem : ENat)) := by
        unfold prefixComplexityContext
        rw [add_assoc]
    _ ≤ KP U x (prefixComplexityContext code i)
          + (logSlack (c_log + c_rem + 2) (i + 1) : ENat) :=
        add_le_add le_rfl hbound

/-- **Conditional set-complexity lower bound (S1, tight gap).**

The Section-3 symmetry-of-information step: a model whose two-part description is
`delta`-far from optimal must, conditional on `x*`, have model code of complexity
at least the redistributed gap `delta - d`, up to visible-parameter log slack.

This uses the tight/realized optimality deficiency `delta = i + j - kx` directly.
-/
theorem gap_lowerBound_conditional_setComplexity_tight (U : Map) (hU : IsOptimalPrefixConditional U)
    :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (n delta d i j kx c_soi : ℕ),
      x.length = n →
      RealizedSetOptimalityGap U A hA x delta i j kx →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      (delta - d : ENat) ≤ KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) + logSlack
          c (n + delta + d) := by
  obtain ⟨c_lower, hc_lower⟩ := KPPair_chain_lower U hU
  obtain ⟨c_upper, hc_upper⟩ := KPPair_chain_upper U hU
  obtain ⟨c_symm, hc_symm⟩ := KPPair_symm U hU
  obtain ⟨c_plain, hc_plain⟩ := KP_le_KPPlain U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨c1, hc1⟩ := KP_le_prefixComplexityContext_add_logSlack U hU
  obtain ⟨C1, hC1⟩ := logSlack_linear_bound c1 3 (c_len + 1)
  use C1 + c_lower + c_upper + c_symm + 1
  intros A hA x n delta d i j kx c_soi hn h_gap h_def hd
  have hxA := h_gap.1
  have hi := h_gap.2.1
  have hj2 := h_gap.2.2.2.1
  have hkx := h_gap.2.2.2.2.1
  have hdelta := h_gap.2.2.2.2.2
  set code := (codedUniformOn A hA).code
  have hkcode : HasPrefixComplexityValue U code i := hi.symm
  have hkx' : HasPrefixComplexityValue U x kx := hkx
  have h1 : KPPair U x code ≤ (kx : ENat) + KP U code (prefixComplexityContext x kx) + c_upper := by
    have h := hc_upper x code kx hkx'
    rw [hkx'.symm] at h
    exact h
  have h2 : KPPair U code x ≤ KPPair U x code + c_symm := hc_symm code x
  have h3 : (i : ENat) + KP U x (prefixComplexityContext code i) ≤ KPPair U code x + c_lower := by
    have h := hc_lower code x i hkcode
    rw [hkcode.symm] at h
    exact h
  by_cases h_top : KP U code (prefixComplexityContext x kx) = ⊤
  · rw [h_top, top_add]; exact le_top
  obtain ⟨kp_code_kx, hkp_code_kx_raw⟩ := ENat.ne_top_iff_exists.mp h_top
  have hkp_code_kx : KP U code (prefixComplexityContext x kx) = kp_code_kx := hkp_code_kx_raw.symm
  have h_kppair_x_code_ne_top : KPPair U x code ≠ ⊤ := by
    intro h_contra
    have h1_top : ⊤ ≤ (kx : ENat) + kp_code_kx + c_upper := by
      calc ⊤ = KPPair U x code := h_contra.symm
           _ ≤ (kx : ENat) + KP U code (prefixComplexityContext x kx) + c_upper := h1
           _ = (kx : ENat) + kp_code_kx + c_upper := by rw [hkp_code_kx]
    exact ENat.coe_ne_top _ (top_le_iff.mp h1_top)
  obtain ⟨kppair_x_code, hkppair_x_code_raw⟩ := ENat.ne_top_iff_exists.mp h_kppair_x_code_ne_top
  have hkppair_x_code : KPPair U x code = kppair_x_code := hkppair_x_code_raw.symm
  have h_kppair_code_x_ne_top : KPPair U code x ≠ ⊤ := by
    intro h_contra
    have h2_top : ⊤ ≤ (kppair_x_code : ENat) + c_symm := by
      calc ⊤ = KPPair U code x := h_contra.symm
           _ ≤ KPPair U x code + c_symm := h2
           _ = (kppair_x_code : ENat) + c_symm := by rw [hkppair_x_code]
    exact ENat.coe_ne_top _ (top_le_iff.mp h2_top)
  obtain ⟨kppair_code_x, hkppair_code_x_raw⟩ := ENat.ne_top_iff_exists.mp h_kppair_code_x_ne_top
  have hkppair_code_x : KPPair U code x = kppair_code_x := hkppair_code_x_raw.symm
  have h_kp_code_x_ne_top : KP U x (prefixComplexityContext code i) ≠ ⊤ := by
    intro h_contra
    have h3_top : ⊤ ≤ (kppair_code_x : ENat) + c_lower := by
      calc ⊤ = (i : ENat) + ⊤ := (add_top (i : ENat)).symm
           _ = (i : ENat) + KP U x (prefixComplexityContext code i) := by rw [h_contra]
           _ ≤ KPPair U code x + c_lower := h3
           _ = (kppair_code_x : ENat) + c_lower := by rw [hkppair_code_x]
    exact ENat.coe_ne_top _ (top_le_iff.mp h3_top)
  obtain ⟨kp_code_i, hkp_code_i_raw⟩ := ENat.ne_top_iff_exists.mp h_kp_code_x_ne_top
  have hkp_code_i : KP U x (prefixComplexityContext code i) = kp_code_i := hkp_code_i_raw.symm
  have h_kp_x_code_ne_top : KP U x code ≠ ⊤ := by
    intro h_contra
    have hp := hc_plain x code
    have h_top_ineq : ⊤ ≤
        ((x.length : ENat) + 2 * (Nat.bits x.length).length + c_len) + c_plain := by
      calc ⊤ = KP U x code := h_contra.symm
           _ ≤ KPPlain U x + c_plain := hp
           _ ≤ ((x.length : ENat) + 2 * (Nat.bits x.length).length + c_len) + c_plain := by
                gcongr; exact hc_len x
    exact ENat.coe_ne_top _ (top_le_iff.mp h_top_ineq)
  obtain ⟨kp_x_code, hkp_x_code_raw⟩ := ENat.ne_top_iff_exists.mp h_kp_x_code_ne_top
  have hkp_x_code : KP U x code = kp_x_code := hkp_x_code_raw.symm
  -- Convert the KPPair symmetry-of-information chain to ℕ.
  have h1n : kppair_x_code ≤ kx + kp_code_kx + c_upper := by
    have h := h1; rw [hkppair_x_code, hkp_code_kx] at h; exact_mod_cast h
  have h2n : kppair_code_x ≤ kppair_x_code + c_symm := by
    have h := h2; rw [hkppair_code_x, hkppair_x_code] at h; exact_mod_cast h
  have h3n : i + kp_code_i ≤ kppair_code_x + c_lower := by
    have h := h3; rw [hkp_code_i, hkppair_code_x] at h; exact_mod_cast h
  -- Deficiency lower bound, tied to the specific `j`.
  obtain ⟨j', hj'card, hj'le⟩ := card_le_of_deficiency hxA h_def
  have hjle : j ≤ j' + 1 := two_pow_half_ennreal_bracket_le hj2 hj'card
  have hj'n : j' ≤ kp_x_code + d := by
    have h := hj'le; rw [hkp_x_code] at h; exact_mod_cast h
  -- Chain rule: drop the index `i` from the context at log cost.
  have hBn : kp_x_code ≤ kp_code_i + logSlack c1 (i + 1) := by
    have h := hc1 x code i; rw [hkp_x_code, hkp_code_i] at h; exact_mod_cast h
  -- Visible-budget bound for `i`.
  have hbits : (Nat.bits n).length ≤ n := by
    have hsz : (Nat.bits n).length = Nat.size n := by rw [Nat.size_eq_bits_len]
    rw [hsz]; exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hkx_bound : kx ≤ 3 * n + c_len := by
    have h := hc_len x
    rw [← hkx', hn] at h
    have h' : kx ≤ n + 2 * (Nat.bits n).length + c_len := by exact_mod_cast h
    omega
  have hi_bound : i + 1 ≤ 3 * (n + delta + d) + (c_len + 1) := by omega
  have h10 : logSlack c1 (i + 1) ≤ logSlack C1 (n + delta + d) :=
    le_trans (logSlack_mono hi_bound) (hC1 _)
  set S := logSlack c1 (i + 1) with hSdef
  -- Absorb the log slack and constants into a single visible-budget slack.
  have habs : S + (c_lower + c_upper + c_symm + 1)
      ≤ logSlack (C1 + c_lower + c_upper + c_symm + 1) (n + delta + d) := by
    have e : C1 + c_lower + c_upper + c_symm + 1 = C1 + (c_lower + c_upper + c_symm + 1) := by ring
    rw [e]
    calc S + (c_lower + c_upper + c_symm + 1)
        ≤ logSlack C1 (n + delta + d) + (c_lower + c_upper + c_symm + 1) := by omega
      _ ≤ logSlack (C1 + (c_lower + c_upper + c_symm + 1)) (n + delta + d) :=
          logSlack_add_const_le _ _ _
  -- Final ℕ inequality, then cast to `ENat`.
  have hfin : delta ≤ kp_code_kx
      + logSlack (C1 + c_lower + c_upper + c_symm + 1) (n + delta + d) + d := by omega
  rw [hkp_code_kx, tsub_le_iff_right]
  exact_mod_cast hfin

/-!
# Gap Counting (Phase B/E infrastructure)

This module bounds the description count in terms of the conditional
complexity gap, the main quantitative step of Section 3.
-/

def candidateCodes (c : Code) (i j : ℕ) (x : BitString) (t : ℕ) : List BitString :=
  ((snapshotCodes c i t).filter isCanonicalUniformCodeBool).filter (fun w =>
    let S := ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset
    decide (x ∈ S ∧ S.card ≤ 2 ^ j)
  )

theorem candidateCodes_primrec (c : Code) :
    Primrec (fun p : ((ℕ × ℕ) × BitString) × ℕ => candidateCodes c p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  -- Pre-filtered snapshot list: outputs of length-`≤ i` programs halting within `t`,
  -- restricted to canonical-uniform codes.  Same shape as `snapshotDescriptionsAndSizeLe_primrec`.
  have h1 : Primrec (fun p : ((ℕ × ℕ) × BitString) × ℕ => snapshotCodes c p.1.1.1 p.2) :=
    (snapshotCodes_primrec c).comp
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
  have hf : Primrec (fun p : ((ℕ × ℕ) × BitString) × ℕ =>
      (snapshotCodes c p.1.1.1 p.2).filter isCanonicalUniformCodeBool) :=
    list_filter_primrec h1 (isCanonicalUniformCodeBool_primrec.comp Primrec.snd)
  -- The inner membership/size predicate, expressed over the support list `L w`.
  have hL : Primrec (fun q : (((ℕ × ℕ) × BitString) × ℕ) × BitString =>
      (decodeDistributionData q.2).map CodedDistributionEntry.point) :=
    Primrec.list_map (decodeDistributionData_primrec.comp Primrec.snd)
      (entry_point_primrec.comp Primrec.snd)
  have hx : Primrec (fun q : (((ℕ × ℕ) × BitString) × ℕ) × BitString => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hmem : Primrec (fun q : (((ℕ × ℕ) × BitString) × ℕ) × BitString =>
      decide (q.1.1.2 ∈ (decodeDistributionData q.2).map CodedDistributionEntry.point)) :=
    bitString_mem_primrec.comp hx hL
  have hcard : Primrec (fun q : (((ℕ × ℕ) × BitString) × ℕ) × BitString =>
      ((decodeDistributionData q.2).map CodedDistributionEntry.point).dedup.length) :=
    Primrec.list_length.comp (dedup_primrec.comp hL)
  have hpow : Primrec (fun q : (((ℕ × ℕ) × BitString) × ℕ) × BitString => 2 ^ q.1.1.1.2) :=
    twoPow_primrec.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hle : Primrec (fun q : (((ℕ × ℕ) × BitString) × ℕ) × BitString =>
      decide (((decodeDistributionData q.2).map CodedDistributionEntry.point).dedup.length
        ≤ 2 ^ q.1.1.1.2)) :=
    PrimrecPred.decide (Primrec.nat_le.comp hcard hpow)
  have hp : Primrec₂ (fun (p : ((ℕ × ℕ) × BitString) × ℕ) (w : BitString) =>
      decide (p.1.2 ∈ ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset ∧
        ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset.card
          ≤ 2 ^ p.1.1.2)) := by
    refine (Primrec.cond hmem hle (Primrec.const false)).of_eq (fun q => ?_)
    by_cases hxin :
        q.1.1.2 ∈ (decodeDistributionData q.2).map CodedDistributionEntry.point
    · simp [hxin, List.mem_toFinset, List.card_toFinset]
    · simp [hxin, List.mem_toFinset]
  exact (list_filter_primrec hf hp).of_eq (fun _ => rfl)

def appearanceListCodes (c : Code) (i j : ℕ) (x : BitString) : ℕ → List BitString
| 0 => (candidateCodes c i j x 0).eraseDups
| t + 1 => (appearanceListCodes c i j x t ++ candidateCodes c i j x (t + 1)).eraseDups

theorem appearanceListCodes_primrec (c : Code) :
    Primrec (fun p : ((ℕ × ℕ) × BitString) × ℕ =>
      appearanceListCodes c p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  -- Primitive recursion on `t = p.2`: base `candidateCodes … 0`, step appends the
  -- fresh `candidateCodes … (n+1)` and deduplicates.
  have hbase : Primrec (fun p : ((ℕ × ℕ) × BitString) × ℕ =>
      (candidateCodes c p.1.1.1 p.1.1.2 p.1.2 0).eraseDups) :=
    eraseDups_bitstring_primrec.comp
      ((candidateCodes_primrec c).comp (Primrec.pair Primrec.fst (Primrec.const 0)))
  have hstep : Primrec₂ (fun (p : ((ℕ × ℕ) × BitString) × ℕ) (z : ℕ × List BitString) =>
      (z.2 ++ candidateCodes c p.1.1.1 p.1.1.2 p.1.2 (z.1 + 1)).eraseDups) :=
    eraseDups_bitstring_primrec.comp (Primrec.list_append.comp
      (Primrec.snd.comp Primrec.snd)
      ((candidateCodes_primrec c).comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))))
  refine (Primrec.nat_rec' Primrec.snd hbase hstep).of_eq ?_
  rintro ⟨⟨⟨i, j⟩, x⟩, t⟩
  induction t with
  | zero => rfl
  | succ t ih => simp only [appearanceListCodes]; rw [← ih]

/-- Membership is preserved by `eraseDups` on `BitString` lists.  (The core
`List.mem_eraseDups` lemma is only available from Lean `v4.29`; this is the
`v4.28` stand-in proved from `eraseDups_append`.) -/
theorem mem_eraseDups_bitString {a : BitString} :
    ∀ {l : List BitString}, a ∈ l.eraseDups ↔ a ∈ l := by
  intro l
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    rw [List.eraseDups_append, List.mem_append, ih]
    by_cases hx : x ∈ l
    · have h0 : ([x] : List BitString).removeAll l = [] := by
        simp [List.removeAll, hx]
      rw [h0, List.eraseDups_nil]
      simp only [List.not_mem_nil, or_false, List.mem_append, List.mem_singleton]
      exact ⟨Or.inl, fun h => h.elim id (fun hax => hax ▸ hx)⟩
    · have h1 : ([x] : List BitString).removeAll l = [x] := by
        simp [List.removeAll, hx]
      rw [h1]
      have hx1 : ([x] : List BitString).eraseDups = [x] := by
        simp [List.eraseDups_cons]
      rw [hx1]
      simp [List.mem_append]

theorem mem_appearanceListCodes_of_mem_candidateCodes {c : Code} {i j : ℕ} {x : BitString} {t : ℕ}
    {w : BitString} :
    w ∈ candidateCodes c i j x t → w ∈ appearanceListCodes c i j x t := by
  induction t with
  | zero => exact fun h => mem_eraseDups_bitString.mpr h
  | succ t _ =>
    intro h
    simp only [appearanceListCodes]
    exact mem_eraseDups_bitString.mpr (List.mem_append_right _ h)

theorem isCanonicalUniformCode_codedUniformOn (S : Finset BitString) (hS : S.Nonempty) :
    isCanonicalUniformCode (codedUniformOn S hS).code := by
  unfold isCanonicalUniformCode
  have h_prob := codedUniformOn_isProbability S hS
  have h_prob_eq := probModelOfCode_eq h_prob
  have h_supp : (probModelOfCode (codedUniformOn S hS).code).support = S := by
    rw [h_prob_eq]
    exact codedUniformOn_support S hS
  refine ⟨?_, ?_⟩
  · rw [h_supp]; exact hS
  · apply Eq.symm
    apply codedUniformOn_code_congr
    exact h_supp

theorem code_mem_candidateCodes {U : Map} {c : Code} (hc : IsCodeFor c U)
    (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (i j : ℕ)
    (hxA : x ∈ A) (hcomp : setComplexity U A hA = (i : ENat)) (hsize : A.card ≤ 2 ^ j) :
    ∃ t₀, (codedUniformOn A hA).code ∈ candidateCodes c i j x t₀ := by
  obtain ⟨t₀, hmax⟩ := exists_max_countHalts c i
  use t₀
  have hc_mem : (codedUniformOn A hA).code ∈ snapshotCodes c i t₀ := by
    have hcomp' : complexity U (codedUniformOn A hA) = i := hcomp
    obtain ⟨p, hp₁, hp₂⟩ := exists_halting_program_of_complexity_le U
      (codedUniformOn A hA) i (le_of_eq hcomp')
    exact code_mem_snapshot_of_max hc i t₀ hmax hp₁ hp₂
  simp only [candidateCodes, List.mem_filter]
  refine ⟨⟨hc_mem, ?_⟩, ?_⟩
  · exact (isCanonicalUniformCodeBool_iff (codedUniformOn A hA).code).mpr
      (isCanonicalUniformCode_codedUniformOn A hA)
  · rw [decide_eq_true_eq]
    have h_supp : ((decodeDistributionData (codedUniformOn A hA).code).map
        CodedDistributionEntry.point).toFinset = A := by
      rw [dataPoints_codedUniformOn A hA, canonicalFinsetList_toFinset]
    rw [h_supp]
    exact ⟨hxA, hsize⟩

def indexSelectorFn (c : Code) : BitString → BitString →. BitString := fun y w =>
  let x := decodeFirst y
  let i := selNat w
  let j := selAlpha w
  let h := selH w
  (Nat.rfind (fun t => Part.some (decide (h < (appearanceListCodes c i j x t).length)))).bind
    (fun t => Part.some (match (appearanceListCodes c i j x t).drop h with
      | [] => []
      | a :: _ => a))

/-- `List.headI` agrees with the explicit head-or-empty match used in
`indexSelectorFn`, since the default value of `List Bool` is `[]`. -/
theorem headI_eq_matchHead (l : List BitString) :
    l.headI = (match l with | [] => [] | a :: _ => a) := by
  cases l <;> rfl

theorem partrec_indexSelectorFn (c : Code) :
    Partrec (fun p : BitString × BitString => indexSelectorFn c p.2 p.1) := by
  -- Pure `Partrec` assembly, mirroring `partrec_selectorFn` in `Selector.lean`.
  -- Generic `List.drop` over `List BitString`, by recursion peeling one tail at a time.
  have h_drop : Primrec₂ (fun (l : List BitString) (n : ℕ) => l.drop n) := by
    have h : (fun (l : List BitString) (n : ℕ) => l.drop n)
        = fun l n => Nat.rec l (fun _ ih => ih.tail) n := by
      funext l n
      induction n with
      | zero => rfl
      | succ n ih => rw [← List.tail_drop, ih]
    rw [h]
    exact Primrec.nat_rec' Primrec.snd Primrec.fst
      (Primrec.list_tail.comp (Primrec.snd.comp Primrec.snd)).to₂
  -- The recursive snapshot list, as a primitive recursive function of `(y, w, t)`.
  have h_codes : Primrec (fun st : (BitString × BitString) × ℕ =>
      appearanceListCodes c (selNat st.1.1) (selAlpha st.1.1) (decodeFirst st.1.2) st.2) :=
    (appearanceListCodes_primrec c).comp (Primrec.pair (Primrec.pair
      (selNat_primrec.comp (Primrec.fst.comp Primrec.fst))
      (selAlpha_primrec.comp (Primrec.fst.comp Primrec.fst)))
      (decodeFirst_primrec.comp (Primrec.snd.comp Primrec.fst)) |>.pair Primrec.snd)
  -- The `rfind` predicate is computable.  Stated directly as `Computable₂` so that
  -- `Computable₂.partrec₂` applies without an expensive higher-order unification.
  have h_check : Computable₂ (fun (a : BitString × BitString) (t : ℕ) =>
      decide (selH a.1 <
        (appearanceListCodes c (selNat a.1) (selAlpha a.1)
          (decodeFirst a.2) t).length)) :=
    (PrimrecPred.decide (Primrec.nat_lt.comp
      (selH_primrec.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.list_length.comp h_codes))).to_comp
  -- The bind body is computable: it is `List.headI` of the dropped list.
  have h_post : Computable₂ (fun (a : BitString × BitString) (t : ℕ) =>
      match (appearanceListCodes c (selNat a.1) (selAlpha a.1)
          (decodeFirst a.2) t).drop (selH a.1) with
      | [] => [] | a :: _ => a) := by
    have hd : Primrec (fun st : (BitString × BitString) × ℕ =>
        (appearanceListCodes c (selNat st.1.1) (selAlpha st.1.1)
          (decodeFirst st.1.2) st.2).drop (selH st.1.1)) :=
      h_drop.comp h_codes (selH_primrec.comp (Primrec.fst.comp Primrec.fst))
    exact ((Primrec.list_headI.comp hd).of_eq (fun _ => headI_eq_matchHead _)).to_comp
  refine (Partrec.bind (Partrec.rfind h_check.partrec₂) h_post.partrec₂).of_eq ?_
  intro p
  -- Match the constructed `(rfind ↑check).bind ↑post` against `indexSelectorFn`'s
  -- `Part.some`-valued bodies, rewriting the coercion pointwise (`PFun.coe_val`)
  -- so the kernel never reduces `Nat.rfind`/`appearanceListCodes`.
  unfold indexSelectorFn
  refine congr_arg₂ Part.bind (congr_arg Nat.rfind ?_) ?_
  · funext t; exact PFun.coe_val _ t
  · funext t; exact PFun.coe_val _ t

/-- **The model code is enumerated.**  If `A` is a nonempty set containing `x` with
canonical-uniform set-complexity `≤ i` (here pinned to `= i`) and `A.card ≤ 2^j`, then
its canonical uniform code eventually appears in the online enumeration
`appearanceListCodes c i j x`.  This is the "membership" step that lets
`indexSelectorFn` recover `A`'s code from a bounded ordinal index (its rank in the
enumeration), feeding `description_count_of_conditional_complexity_gap`. -/
theorem code_mem_appearanceListCodes {U : Map} {c : Code} (hc : IsCodeFor c U)
    (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (i j : ℕ)
    (hxA : x ∈ A) (hcomp : setComplexity U A hA = (i : ENat)) (hsize : A.card ≤ 2 ^ j) :
    ∃ t₀, (codedUniformOn A hA).code ∈ appearanceListCodes c i j x t₀ := by
  obtain ⟨t₀, ht₀⟩ := code_mem_candidateCodes hc A hA x i j hxA hcomp hsize
  exact ⟨t₀, mem_appearanceListCodes_of_mem_candidateCodes ht₀⟩

/-- Every code enumerated in `appearanceListCodes` came from some `candidateCodes` slice.
Converse of `mem_appearanceListCodes_of_mem_candidateCodes`. -/
theorem exists_candidate_of_mem_appearanceListCodes {c : Code} {i j : ℕ} {x : BitString}
    {t : ℕ} {w : BitString} (hw : w ∈ appearanceListCodes c i j x t) :
    ∃ t', w ∈ candidateCodes c i j x t' := by
  induction t with
  | zero =>
    exact ⟨0, mem_eraseDups_bitString.mp hw⟩
  | succ t ih =>
    simp only [appearanceListCodes] at hw
    rcases List.mem_append.mp (mem_eraseDups_bitString.mp hw) with h | h
    · exact ih h
    · exact ⟨t + 1, h⟩

/-- A canonical uniform code (bool test) is the canonical code of its own decoded support. -/
theorem eq_codedUniformOn_of_isCanonicalUniformCodeBool {w : BitString}
    (hw : isCanonicalUniformCodeBool w = true) :
    ∃ hne : ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset.Nonempty,
      w = (codedUniformOn
        (((decodeDistributionData w).map CodedDistributionEntry.point).toFinset) hne).code := by
  simp only [isCanonicalUniformCodeBool, decide_eq_true_eq] at hw
  obtain ⟨hSne, hc_eq⟩ := hw
  refine ⟨hSne, ?_⟩
  convert hc_eq using 1
  convert codedUniformOn_code_eq _ hSne using 1
  grind +extAll

/-- A member of `candidateCodes` decodes to a size-restricted snapshot description of `x`. -/
theorem mem_snapshotDescriptionsAndSizeLe_of_mem_candidateCodes {c : Code} {i j : ℕ}
    {x : BitString} {t : ℕ} {w : BitString} (hw : w ∈ candidateCodes c i j x t) :
    isCanonicalUniformCodeBool w = true ∧
    x ∈ ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset ∧
    ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset
      ∈ snapshotDescriptionsAndSizeLe c i j t := by
  simp only [candidateCodes, List.mem_filter, decide_eq_true_eq] at hw
  obtain ⟨⟨hsnap, hcanon⟩, hxmem, hsize⟩ := hw
  refine ⟨hcanon, hxmem, ?_⟩
  rw [snapshotDescriptionsAndSizeLe, Finset.mem_filter]
  refine ⟨?_, hsize⟩
  rw [snapshotDescriptions, Finset.mem_image]
  exact ⟨w, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hsnap, hcanon⟩), rfl⟩

/-- The computable size-restricted snapshot universe at any time is contained in the
abstract description universe (it stabilizes to equality at the halting-count maximum). -/
theorem snapshotDescriptionsAndSizeLe_subset_descriptions {U : Map} {c : Code}
    (hc : IsCodeFor c U) (i j t : ℕ) :
    snapshotDescriptionsAndSizeLe c i j t ⊆ descriptionsWithComplexityLeAndSizeLe U i j := by
  obtain ⟨t₀, hmax⟩ := exists_max_countHalts c i
  have hT : ∀ t'', countHalts c i t'' ≤ countHalts c i (max t t₀) :=
    fun t'' => le_trans (hmax t'') (countHalts_mono c i (le_max_right t t₀))
  intro S hS
  rw [← snapshotDescriptionsAndSizeLe_eq_descriptionsWithComplexityLeAndSizeLe hc i j (max t t₀) hT]
  exact snapshotDescriptionsAndSizeLe_subset_of_le c i j (le_max_left t t₀) hS

/-- `eraseDups` on `BitString` lists produces a duplicate-free list.  (The core
`List.nodup_eraseDups` lemma is not available in Lean `v4.28`; this is the stand-in
proved from `eraseDups_cons` and the repo's `mem_eraseDups_bitString`.) -/
theorem nodup_eraseDups_bitString : ∀ (l : List BitString), l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨?_, nodup_eraseDups_bitString _⟩
    intro hmem
    rw [mem_eraseDups_bitString, List.mem_filter] at hmem
    simp at hmem
  termination_by l => l.length
  decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- **Rank bound.**  The online enumeration of `(i,j)`-descriptions of `x` never grows
longer than the number of abstract `(i,j)`-descriptions containing `x`.  The decoded
support is an injective map from the (deduplicated) code list into that finset. -/
theorem appearanceListCodes_length_le_descriptionsContaining {U : Map} {c : Code}
    (hc : IsCodeFor c U) (i j : ℕ) (x : BitString) (t : ℕ) :
    (appearanceListCodes c i j x t).length
      ≤ ((descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => x ∈ S)).card := by
  set L := appearanceListCodes c i j x t with hL
  set f : BitString → Finset BitString :=
    fun w => ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset with hf
  have hnodup : L.Nodup := by
    rw [hL]; cases t <;> exact nodup_eraseDups_bitString _
  have hmaps : ∀ w ∈ L,
      f w ∈ (descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => x ∈ S) := by
    intro w hw
    obtain ⟨t', hw'⟩ := exists_candidate_of_mem_appearanceListCodes hw
    obtain ⟨_, hxS, hSmem⟩ := mem_snapshotDescriptionsAndSizeLe_of_mem_candidateCodes hw'
    rw [Finset.mem_filter]
    exact ⟨snapshotDescriptionsAndSizeLe_subset_descriptions hc i j t' hSmem, hxS⟩
  have hinj : ∀ w1 ∈ L, ∀ w2 ∈ L, f w1 = f w2 → w1 = w2 := by
    intro w1 hw1 w2 hw2 heq
    obtain ⟨t1, hc1⟩ := exists_candidate_of_mem_appearanceListCodes hw1
    obtain ⟨t2, hc2⟩ := exists_candidate_of_mem_appearanceListCodes hw2
    have hcanon1 := (mem_snapshotDescriptionsAndSizeLe_of_mem_candidateCodes hc1).1
    have hcanon2 := (mem_snapshotDescriptionsAndSizeLe_of_mem_candidateCodes hc2).1
    obtain ⟨hne1, he1⟩ := eq_codedUniformOn_of_isCanonicalUniformCodeBool hcanon1
    obtain ⟨hne2, he2⟩ := eq_codedUniformOn_of_isCanonicalUniformCodeBool hcanon2
    rw [he1, he2]
    exact codedUniformOn_code_congr _ _ heq
  have hlen : L.length = (L.map f).length := by simp
  have hnd : (L.map f).Nodup := List.Nodup.map_on hinj hnodup
  have hsub : (L.map f).toFinset
      ⊆ (descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => x ∈ S) := by
    intro S hS
    rw [List.mem_toFinset, List.mem_map] at hS
    obtain ⟨w, hwL, rfl⟩ := hS
    exact hmaps w hwL
  calc L.length = (L.map f).length := hlen
    _ = (L.map f).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- If `x` has fewer than `2^m` `(i,j)`-descriptions, then the online enumeration of its
descriptions stays strictly shorter than `2^m` at every time.  Hence the model code's rank
in the enumeration fits in `m` bits — the bound consumed by
`description_count_of_conditional_complexity_gap`. -/
theorem appearanceListCodes_length_lt_of_not_manyIJ {U : Map} {c : Code}
    (hc : IsCodeFor c U) {x : BitString} {i j m : ℕ}
    (hnm : ¬ ManyIJDescriptions U x i j m) (t : ℕ) :
    (appearanceListCodes c i j x t).length < 2 ^ m := by
  rw [ManyIJDescriptions, not_le] at hnm
  exact lt_of_le_of_lt (appearanceListCodes_length_le_descriptionsContaining hc i j x t) hnm

theorem eraseDups_eq_self_of_nodup {α} [BEq α] [LawfulBEq α] {l : List α} (h : l.Nodup) :
  l.eraseDups = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h1 := List.nodup_cons.mp h
    rw [List.eraseDups_cons]
    have hf : l.filter (fun b => !(b == a)) = l := by
      apply List.filter_eq_self.mpr
      intro x hx
      have hne : x ≠ a := ne_of_mem_of_not_mem hx h1.1
      simp [hne]
    rw [hf, ih h1.2]

theorem prefix_eraseDups_append_of_nodup {α} [BEq α] [LawfulBEq α] (l1 l2 : List α) (h : l1.Nodup) :
  l1 <+: (l1 ++ l2).eraseDups := by
  rw [List.eraseDups_append]
  have heq : l1.eraseDups = l1 := eraseDups_eq_self_of_nodup h
  rw [heq]
  exact List.prefix_append _ _

theorem appearanceListCodes_prefix (c : Code) (i j : ℕ) (x : BitString) (t : ℕ) :
    appearanceListCodes c i j x t <+: appearanceListCodes c i j x (t + 1) := by
  have hn : (appearanceListCodes c i j x t).Nodup := by
    cases t <;> exact nodup_eraseDups_bitString _
  have h_eq : appearanceListCodes c i j x (t + 1) =
      (appearanceListCodes c i j x t ++ candidateCodes c i j x (t + 1)).eraseDups := rfl
  rw [h_eq]
  exact prefix_eraseDups_append_of_nodup _ _ hn

theorem prefix_of_le_appearanceListCodes (c : Code) (i j : ℕ) (x : BitString) {t1 t2 : ℕ}
    (hle : t1 ≤ t2) :
  appearanceListCodes c i j x t1 <+: appearanceListCodes c i j x t2 := by
  induction hle with
  | refl => exact List.prefix_refl _
  | step ht ih => exact List.IsPrefix.trans ih (appearanceListCodes_prefix c i j x _)

theorem exists_drop_eq_cons_of_mem (l : List BitString) (a : BitString) (h : a ∈ l) :
  ∃ r l', r < l.length ∧ l.drop r = a :: l' := by
  induction l with
  | nil => cases h
  | cons x l ih =>
    cases h with
    | head _ =>
      exact ⟨0, l, by simp, rfl⟩
    | tail _ h =>
      obtain ⟨r, l', hr, hl'⟩ := ih h
      exact ⟨r + 1, l', Nat.succ_lt_succ hr, hl'⟩

theorem indexSelectorFn_eq_code (c : Code) (i j : ℕ) (x : BitString) (code : BitString) (t0 : ℕ)
  (h_mem : code ∈ appearanceListCodes c i j x t0) :
  ∃ r < (appearanceListCodes c i j x t0).length,
    ∀ (y w : BitString), decodeFirst y = x → selNat w = i → selAlpha w = j → selH w = r →
        indexSelectorFn c y w = Part.some code := by
  obtain ⟨r, l', hr_lt, h_drop⟩ := exists_drop_eq_cons_of_mem _ _ h_mem
  refine ⟨r, hr_lt, ?_⟩
  intro y w hy hi hj hr
  convert Part.eq_some_iff.mpr _ using 1;
  unfold indexSelectorFn
  simp only [Part.mem_bind_iff, Nat.mem_rfind, Part.mem_some_iff, hy, hi, hj, hr]
  refine ⟨Nat.find (⟨t0, hr_lt⟩ : ∃ t, r < (appearanceListCodes c i j x t).length),
    Nat.mem_rfind.mpr ⟨?_, fun {m} hm => ?_⟩, ?_⟩
  · exact Part.mem_some_iff.mpr (decide_eq_true (Nat.find_spec
      (⟨t0, hr_lt⟩ : ∃ t, r < (appearanceListCodes c i j x t).length))).symm
  · refine Part.mem_some_iff.mpr (decide_eq_false ?_).symm
    exact Nat.find_min (⟨t0, hr_lt⟩ :
      ∃ t, r < (appearanceListCodes c i j x t).length) hm
  · have h_drop_eq :
        (appearanceListCodes c i j x
          (Nat.find (⟨t0, hr_lt⟩ : ∃ t, r < (appearanceListCodes c i j x t).length)))[r]! =
          (appearanceListCodes c i j x t0)[r]! := by
      have h_drop_eq : appearanceListCodes c i j x
          (Nat.find (⟨t0, hr_lt⟩ : ∃ t, r < (appearanceListCodes c i j x t).length)) <+:
          appearanceListCodes c i j x t0 := by
        exact prefix_of_le_appearanceListCodes c i j x ( Nat.find_le hr_lt );
      obtain ⟨ k, hk ⟩ := h_drop_eq;
      grind;
    convert h_drop_eq.symm using 1
    · replace h_drop := congr_arg List.head? h_drop; aesop
    · clear h_drop_eq
      have h_get :
          (appearanceListCodes c i j x
            (Nat.find (⟨t0, hr_lt⟩ : ∃ t,
              r < (appearanceListCodes c i j x t).length)))[r]? =
            (List.drop r (appearanceListCodes c i j x
              (Nat.find (⟨t0, hr_lt⟩ : ∃ t,
                r < (appearanceListCodes c i j x t).length)))).head? :=
        List.head?_drop.symm
      cases h : List.drop r (appearanceListCodes c i j x
        (Nat.find (⟨t0, hr_lt⟩ : ∃ t, r < (appearanceListCodes c i j x t).length)))
      · rw [List.getElem!_eq_getElem?_getD, h_get, h]
        rfl
      · rw [List.getElem!_eq_getElem?_getD, h_get, h]
        rfl

/-- A computable function that extracts the index from `y` to return the right model code.
If `x` has `< 2^m` `(i,j)`-descriptions, it is fully determined by
`x, K(x), i, j` and an `m`-bit index. -/
theorem description_count_of_conditional_complexity_gap (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (n i j m kx : ℕ),
      x.length = n →
      x ∈ A →
      setComplexity U A hA = (i : ENat) →
      A.card ≤ 2 ^ j →
      HasPrefixComplexityValue U x kx →
      ¬ ManyIJDescriptions U x i j m →
      KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) ≤
          (m + logSlack c (n + i + j) : ENat) := by
  obtain ⟨c_opt, hc_opt⟩ : ∃ c_opt : Code, IsCodeFor c_opt U :=
    Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  obtain ⟨c_kp, hkp⟩ := KP_partrec_cond_first_map_le U hU (indexSelectorFn c_opt)
    (partrec_indexSelectorFn c_opt)
  obtain ⟨c_plain, hc_plain⟩ := KP_le_KPPlain U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨C2, hC2⟩ := logSlack_linear_bound 2 3 7
  let C1 := C2 + c_kp + c_plain + c_len + 6
  use C1
  intro A hA x n i j m kx hn hx hi hj hkx h_not_many
  obtain ⟨t₀, ht₀⟩ := code_mem_appearanceListCodes hc_opt A hA x i j hx hi hj
  set y := prefixComplexityContext x kx
  set code := (codedUniformOn A hA).code
  have hy : decodeFirst y = x := by
    dsimp [y, prefixComplexityContext]
    rw [decodeFirst_pairCode]
  obtain ⟨r, hr_lt, hr_spec⟩ := indexSelectorFn_eq_code c_opt i j x code t₀ ht₀
  set w := richInput i j 0 r
  have hw_i : selNat w = i := selNat_richInput i j 0 r
  have hw_j : selAlpha w = j := selAlpha_richInput i j 0 r
  have hw_h : selH w = r := selH_richInput i j 0 r
  have h_some : indexSelectorFn c_opt y w = Part.some code := hr_spec y w hy hw_i hw_j hw_h
  have h_in : code ∈ indexSelectorFn c_opt y w := Part.eq_some_iff.mp h_some
  have h_bound1 : KP U code y ≤ KP U w y + (c_kp : ENat) := hkp w code y h_in
  have h_bound2 : KP U w y ≤ KPPlain U w + (c_plain : ENat) := hc_plain w y
  have h_bound3 : KPPlain U w ≤
      (w.length : ENat) + 2 * (Nat.bits w.length).length + c_len := hc_len w
  have h_w_len_r : w.length ≤ 2 * (Nat.bits i).length + 2 * (Nat.bits j).length +
      (Nat.bits r).length + 6 := by
    unfold w richInput selectorInput pack4
    simp [length_pairCode]
    omega
  have hr_lt_2m : r < 2 ^ m := lt_trans hr_lt
    (appearanceListCodes_length_lt_of_not_manyIJ hc_opt h_not_many t₀)
  have hr_lt_2i : r < 2 ^ (i + 1) := by
    have h1 := appearanceListCodes_length_le_descriptionsContaining hc_opt i j x t₀
    have h2 := Finset.card_filter_le (descriptionsWithComplexityLeAndSizeLe U i j) (fun S => x ∈ S)
    have h3 := card_descriptionsWithComplexityLeAndSizeLe U i j
    exact lt_of_lt_of_le hr_lt (h1.trans (h2.trans h3))
  let M := n + i + j
  have h_w_len_M : w.length ≤ 3 * M + 7 := by
    have hi_len : (Nat.bits i).length ≤ i := length_natBits_le_self i
    have hj_len : (Nat.bits j).length ≤ j := length_natBits_le_self j
    have hr_len : (Nat.bits r).length ≤ i + 1 := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr hr_lt_2i
    omega
  have h_slack : c_kp + c_plain + c_len + 2 * (Nat.bits i).length + 2 * (Nat.bits j).length + 6 + 2
      * (Nat.bits w.length).length ≤ logSlack C1 M := by
    have hw1 : (Nat.bits w.length).length ≤ (Nat.bits (3 * M + 7)).length := by
      have h : w.length < 2 ^ (Nat.size (3 * M + 7)) :=
        lt_of_le_of_lt h_w_len_M (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hw3 : 2 * (Nat.bits (3 * M + 7)).length ≤ logSlack 2 (3 * M + 7) := by
      unfold logSlack
      omega
    have hw5 : logSlack C2 M = C2 * (Nat.bits M).length + C2 := rfl
    have hw6 : logSlack C1 M =
        (C2 + c_kp + c_plain + c_len + 6) * (Nat.bits M).length +
          (C2 + c_kp + c_plain + c_len + 6) := rfl
    have hiM : i ≤ M := by omega
    have hjM : j ≤ M := by omega
    have hi_len : (Nat.bits i).length ≤ (Nat.bits M).length := by
      have h : i < 2 ^ (Nat.size M) := lt_of_le_of_lt hiM (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hj_len : (Nat.bits j).length ≤ (Nat.bits M).length := by
      have h : j < 2 ^ (Nat.size M) := lt_of_le_of_lt hjM (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hC2_M := hC2 M
    nlinarith
  calc KP U code y ≤ KP U w y + c_kp := h_bound1
    _ ≤ KPPlain U w + c_plain + c_kp := by gcongr
    _ ≤ (w.length : ENat) + 2 * (Nat.bits w.length).length + c_len + c_plain + c_kp := by gcongr
    _ ≤ ((2 * (Nat.bits i).length + 2 * (Nat.bits j).length + (Nat.bits r).length + 6 : ℕ) : ENat) +
        2 * (Nat.bits w.length).length + c_len + c_plain + c_kp := by
      have h : w.length + 2 * w.length.bits.length + c_len + c_plain + c_kp ≤
          (2 * i.bits.length + 2 * j.bits.length + r.bits.length + 6) +
            2 * w.length.bits.length + c_len + c_plain + c_kp := by omega
      exact_mod_cast h
    _ ≤ ((2 * (Nat.bits i).length + 2 * (Nat.bits j).length + m + 6 : ℕ) : ENat) + 2 *
        (Nat.bits w.length).length + c_len + c_plain + c_kp := by
      have h_r_m : (Nat.bits r).length ≤ m := by
        rw [Nat.size_eq_bits_len]
        exact Nat.size_le.mpr hr_lt_2m
      have h : (2 * i.bits.length + 2 * j.bits.length + r.bits.length + 6) +
          2 * w.length.bits.length + c_len + c_plain + c_kp ≤
            (2 * i.bits.length + 2 * j.bits.length + m + 6) +
              2 * w.length.bits.length + c_len + c_plain + c_kp := by omega
      exact_mod_cast h
    _ = (m : ENat) + (c_kp + c_plain + c_len + 2 * (Nat.bits i).length +
        2 * (Nat.bits j).length + 6 + 2 * (Nat.bits w.length).length : ℕ) := by
      push_cast
      ring
    _ ≤ (m : ENat) + logSlack C1 M := by gcongr

/-- If `x ∈ A`, `setComplexity U A hA = i`, and `A.card ≤ 2^j`, then `x` has at
least `2^0 = 1` `(i, j)`-description. -/
theorem manyIJDescriptions_zero (U : Map) (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
    (i j : ℕ)
    (hxA : x ∈ A) (h_comp : setComplexity U A hA = (i : ENat)) (h_size : A.card ≤ 2 ^ j) :
    ManyIJDescriptions U x i j 0 := by
  unfold ManyIJDescriptions
  rw [pow_zero]
  refine Finset.card_pos.mpr ?_
  refine ⟨A, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨?_, hxA⟩
  unfold descriptionsWithComplexityLeAndSizeLe
  rw [Finset.mem_filter]
  refine ⟨?_, h_size⟩
  exact mem_descriptionsWithComplexityLe_of_complexity hA (by rw [h_comp])

/-
Arithmetic lemma for bounding the sum of two log-slack terms into a single log-slack term.
-/
theorem gapCounting_slack_arithmetic (U : Map) (hU : IsOptimalPrefixConditional U) (c1 c2 : ℕ) :
    ∃ c_out : ℕ, ∀ (n delta d i j_min : ℕ) (x : BitString) (code : BitString),
      x.length = n →
      (i : ENat) ≤ KPPlain U x + (delta : ENat) →
      (j_min : ENat) ≤ KP U x code + (d : ENat) →
      logSlack c2 (n + i + j_min) + logSlack c1 (n + delta + d) <
        logSlack c_out (n + delta + d) := by
  obtain ⟨cKP⟩ := Kolmogorov.KP_le_KPPlain U hU
  obtain ⟨c0⟩ := Kolmogorov.KPPlain_le_length_add_log U hU
  use 9*c2 + c1 + c2*(2*c0 + cKP + 9) + c2 + c1 + 1
  intro n delta d i j_min x code hx hi hj;
  -- Let `W := L (n + delta + d)`. Using `length_natBits_mono` (monotone in argument) and
  --   `length_natBits_add_le` repeatedly, plus `L k ≤ k` and `L k ≤ W` whenever `k ≤ n + delta +
  --   d`:
  set W := (Nat.bits (n + delta + d)).length
  have hW : (Nat.bits n).length ≤ W ∧ (Nat.bits delta).length ≤ W ∧ (Nat.bits d).length ≤ W := by
    exact ⟨length_natBits_mono (by linarith), length_natBits_mono (by linarith),
      length_natBits_mono (by linarith)⟩
  have hL_i : (Nat.bits i).length ≤ 4*W + c0 + 3 := by
    have hL_i : (Nat.bits i).length ≤
        (Nat.bits (n + 2 * (Nat.bits n).length + c0 + delta)).length := by
      refine length_natBits_mono ?_;
      convert hi.trans _;
      rotate_left;
      · exact ↑ ( n + 2 * n.bits.length + c0 + delta );
      · aesop;
      · norm_cast;
    have hL_i : (Nat.bits (n + 2 * (Nat.bits n).length + c0 + delta)).length ≤ (Nat.bits n).length +
        (Nat.bits (2 * (Nat.bits n).length)).length + (Nat.bits c0).length + (Nat.bits delta).length
        + 3 := by
      have hL_i : ∀ a b : ℕ, (Nat.bits (a + b)).length ≤ (Nat.bits a).length + (Nat.bits b).length +
          1 := by
        intros a b
        have hL_i : (Nat.bits (a + b)).length ≤ (Nat.bits a).length + (Nat.bits b).length + 1 := by
          have := length_natBits_add_le a b
          exact this
        exact hL_i;
      grind;
    have hL_i : (Nat.bits (2 * (Nat.bits n).length)).length ≤ 2 * (Nat.bits n).length :=
      length_natBits_le_self _
    linarith [length_natBits_le_self c0]
  have hL_j_min : (Nat.bits j_min).length ≤ 4*W + c0 + cKP + 4 := by
    have hL_j_min : (Nat.bits j_min).length ≤
        (Nat.bits (n + 2 * (Nat.bits n).length + c0 + cKP + d)).length := by
      refine length_natBits_mono ?_;
      rename_i h₁ h₂;
      contrapose! hj;
      refine lt_of_le_of_lt ( add_le_add ( h₁ _ _ ) le_rfl ) ?_;
      refine lt_of_le_of_lt ?_ ( Nat.cast_lt.mpr hj );
      convert add_le_add_right ( add_le_add_right ( h₂ x ) ( cKP : ENat ) )
          ( d : ENat ) using 1
      all_goals try simp only [KPPlain_eq_KP]
      all_goals first
        | rfl
        | abel1
        | exact mod_cast by rw [hx]; ring
    have hL_j_min : (Nat.bits (n + 2 * (Nat.bits n).length + c0 + cKP + d)).length ≤
        (Nat.bits n).length + (Nat.bits (2 * (Nat.bits n).length)).length + (Nat.bits c0).length +
        (Nat.bits cKP).length + (Nat.bits d).length + 4 := by
      have hL_j_min : ∀ a b : ℕ, (Nat.bits (a + b)).length ≤ (Nat.bits a).length +
          (Nat.bits b).length + 1 := by
        intros a b
        have hL_j_min : (Nat.bits (a + b)).length ≤
            (Nat.bits a).length + (Nat.bits b).length + 1 := by
          have := length_natBits_add_le a b
          exact this
        generalize_proofs at *;
        exact hL_j_min
      generalize_proofs at *;
      grind +ring;
    have hL_j_min : (Nat.bits (2 * (Nat.bits n).length)).length ≤ 2 * (Nat.bits n).length :=
      length_natBits_le_self _
    have hL_j_min : (Nat.bits c0).length ≤ c0 ∧ (Nat.bits cKP).length ≤ cKP :=
      ⟨length_natBits_le_self c0, length_natBits_le_self cKP⟩
    linarith
  have hL_sum : (Nat.bits (n + i + j_min)).length ≤ 9*W + (2*c0 + cKP + 9) := by
    have hL_sum : (Nat.bits (n + i + j_min)).length ≤
        (Nat.bits (n + i)).length + (Nat.bits j_min).length + 1 :=
      length_natBits_add_le (n + i) j_min
    linarith [ length_natBits_add_le n i ]
  simp_all +decide [ logSlack ];
  nlinarith only [ hL_sum, hW, show 0 ≤ c2 * ( 2 * c0 + cKP + 9 ) by positivity ]

/-
The tight gap-counting bridge: realized deficiency gap implies many descriptions.
From `RealizedSetOptimalityGap U A hA x delta i j kx`, `DeficiencyLe U (codedUniformOn A hA) x d`,
`d ≤ delta`, derive `ManyIJDescriptions U x i j (delta - d - slack)`
up to the log-slack already in the theorem.
-/
theorem manyIJDescriptions_of_realizedSetOptimalityGap (U : Map) (hU : IsOptimalPrefixConditional U)
    :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (n delta d i j kx c_soi : ℕ),
      x.length = n →
      RealizedSetOptimalityGap U A hA x delta i j kx →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      ∃ slack : ℕ, slack ≤ logSlack c (n + delta + d) ∧
        ManyIJDescriptions U x i j (delta - d - slack) := by
  rcases gap_lowerBound_conditional_setComplexity_tight U hU with ⟨c1, hc1⟩
  rcases description_count_of_conditional_complexity_gap U hU with ⟨c2, hc2⟩
  rcases gapCounting_slack_arithmetic U hU c1 c2 with ⟨c3, hc3⟩
  refine ⟨c3, fun A hA x n delta d i j kx c_soi hn h_realized hdef_cond hd => ?_⟩
  have hxA := h_realized.1
  have hi := h_realized.2.1
  have hj := h_realized.2.2.1
  have hj_lower := h_realized.2.2.2.1
  have hkx := h_realized.2.2.2.2.1
  have hdelta_eq := h_realized.2.2.2.2.2
  have hi_bound : (i : ENat) ≤ KPPlain U x + (delta : ENat) := by
    have hkx_eq : KPPlain U x = (kx : ENat) := hkx.symm
    rw [hkx_eq]
    norm_cast
    omega
  rcases card_le_of_deficiency hxA hdef_cond with ⟨j_opt, hj_opt, hj_bound⟩
  have h_gap := hc1 A hA x n delta d i j kx c_soi hn
    ⟨hxA, hi, hj, hj_lower, hkx, hdelta_eq⟩ hdef_cond hd
  have hj_min : A.card ≤ 2 ^ min j j_opt := by
    by_cases hle : j ≤ j_opt
    · rw [Nat.min_eq_left hle]
      exact hj
    · rw [Nat.min_eq_right (le_of_not_ge hle)]
      exact hj_opt
  clear hdelta_eq
  set slack := logSlack c3 (n + delta + d)
  use slack
  refine ⟨le_refl slack, ?_⟩
  by_cases h_zero : delta - d ≤ slack
  · rw [Nat.sub_eq_zero_of_le h_zero]
    exact manyIJDescriptions_zero U A hA x i j hxA hi hj
  · -- We derive `ManyIJDescriptions` by contradiction using the slack bound:
    -- combining the conditional lower bound (`hc1`), the description-count upper
    -- bound (`hc2`), and the slack arithmetic (`hc3`).
    contrapose! h_zero
    have := hc2 A hA x n i (Min.min j j_opt) (delta - d - slack) kx hn hxA hi hj_min hkx
    simp_all only [tsub_le_iff_right, ge_iff_le, Nat.sub_sub]
    have := hc3 n delta d i (Min.min j j_opt) x (codedUniformOn A hA).code hn hi_bound
      (le_trans (mod_cast min_le_right _ _) hj_bound)
    simp_all only [logSlack]
    rename_i h
    specialize h (fun h => h_zero <| h.mono_j <| min_le_left _ _)
    simp_all only [slack]
    contrapose! h_gap
    simp_all only [logSlack]
    refine lt_of_le_of_lt (add_le_add_three h le_rfl le_rfl) ?_
    norm_cast
    omega

end Kolmogorov
