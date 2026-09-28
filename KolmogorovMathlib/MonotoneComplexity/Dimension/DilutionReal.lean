/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.DilutionCode
import KolmogorovMathlib.MonotoneComplexity.Dimension.Hausdorff
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveLaws
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.OptimalExistence
import KolmogorovMathlib.Core.Invariance
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria
import KolmogorovMathlib.MonotoneComplexity.Dimension.ChangeOfMeasure

/-!
# Dilution at a real density: SUV Problem 170 (§5.8, p. 175)

For a real `α ∈ [0,1]` we dilute a uniformly Martin-Löf random sequence `ω` by
keeping its bits at the places where `⌈α·n⌉` grows and writing `false`
elsewhere.  Writing `w = rdilate α ω` and `a n = ⌈α·n⌉`, the `n`-bit prefix of
`w` carries exactly `a n` bits of `ω`, so

`C((w)_n) = a n ± O(log n)`, hence `C((w)_n)/n → α`,

and SUV Theorem 120 turns this into `effectiveHausdorffDim {w} = α`.

## The one non-obvious point: describing the schedule

For a general real `α` the schedule `n ↦ ⌈α·n⌉` is not computable, so the
decoder cannot be given `α`.  It does not have to be: **below any fixed `n` the
real schedule coincides with a rational one of denominator `≤ n`**
(`exists_dilCount_eq_rdilCount`).  Indeed `⌈r·k⌉ = ⌈α·k⌉` for all `k ≤ n` as
soon as `r ≥ α` and `r ≤ ⌈α·k⌉/k` for every `k ≤ n`, and `r = ⌈α·k₀⌉/k₀` for a
minimiser `k₀` of `⌈α·k⌉/k` over `1 ≤ k ≤ n` is such an `r`.  So the parameter
`(n, p, q)` -- a single natural number `dilPack n p q < (n+3)^4` -- lets the
computable family `dilDecodeCoded` rebuild `(w)_n` from the payload and lets
`dilExtractCoded` read the payload back.  Its self-delimiting code has
`O(log n)` bits, which is what `exists_const_plainK_codedMap_le`
(`Dimension/DilutionCode.lean`) charges, and `O(log n)/n → 0`.

This is the "adding random bits raises the complexity of an initial segment,
adding zeros lowers it" of the book's hint (p. 175), made uniform in `n`.
-/

namespace Kolmogorov

open Filter MeasureTheory

/-! ## The real dilution schedule -/

/-- `⌈α·n⌉`: the number of free places below `n` at real density `α`. -/
noncomputable def rdilCount (α : ℝ) (n : ℕ) : ℕ := ⌈α * n⌉₊

/-- The free places of the real dilution schedule: those where `⌈α·n⌉` grows. -/
noncomputable def rdilSel (α : ℝ) (i : ℕ) : Bool := decide (rdilCount α (i + 1) = rdilCount α i + 1)

/-- The dilution of `w` at real density `α`: the bits of `w` sit at the free
places, all other places carry `false`. -/
noncomputable def rdilate (α : ℝ) (w : CantorSeq) : CantorSeq :=
  fun i => if rdilSel α i then w (rdilCount α i) else false

/-- No position is selected before position `0` in the real dilution. -/
@[simp] lemma rdilCount_zero (α : ℝ) : rdilCount α 0 = 0 := by
  simp [rdilCount]

/-- For a rate at most `1` the real dilution counter never exceeds the position. -/
lemma rdilCount_le_self {α : ℝ} (h1 : α ≤ 1) (n : ℕ) : rdilCount α n ≤ n := by
  refine Nat.ceil_le.2 ?_
  calc α * (n : ℝ) ≤ 1 * (n : ℝ) := by
        exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n)
    _ = (n : ℝ) := one_mul _

/-- The real dilution counter at `n` is at least `α n`. -/
lemma le_rdilCount {α : ℝ} (n : ℕ) : α * (n : ℝ) ≤ (rdilCount α n : ℝ) := Nat.le_ceil _

/-- The real dilution counter at `n` is below `α n + 1`. -/
lemma rdilCount_lt {α : ℝ} (h0 : 0 ≤ α) (n : ℕ) :
    (rdilCount α n : ℝ) < α * (n : ℝ) + 1 :=
  Nat.ceil_lt_add_one (by positivity)

/-! ## Below any fixed length the schedule is rational -/

/-- **The schedule is locally rational.**  For every `n` there are naturals
`p ≤ q ≤ n + 1` with `⌈p·k/q⌉ = ⌈α·k⌉` for all `k ≤ n`.  Take for `q` a
minimiser `k₀` of `⌈α·k⌉/k` over `1 ≤ k ≤ n + 1` and for `p` the value
`⌈α·k₀⌉`. -/
theorem exists_dilCount_eq_rdilCount {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (n : ℕ) :
    ∃ p q : ℕ, 0 < q ∧ p ≤ q ∧ q ≤ n + 1 ∧ p ≤ n + 1 ∧
      ∀ k, k ≤ n → dilCount p q k = rdilCount α k := by
  classical
  obtain ⟨k₀, hk₀mem, hk₀min⟩ :=
    Finset.exists_min_image (Finset.Icc 1 (n + 1))
      (fun k => (rdilCount α k : ℚ) / (k : ℚ)) ⟨1, by simp⟩
  rw [Finset.mem_Icc] at hk₀mem
  obtain ⟨hk₀1, hk₀2⟩ := hk₀mem
  refine ⟨rdilCount α k₀, k₀, hk₀1, ?_, hk₀2, ?_, ?_⟩
  · exact rdilCount_le_self h1 k₀
  · exact le_trans (rdilCount_le_self h1 k₀) hk₀2
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    have hkmem : k ∈ Finset.Icc 1 (n + 1) := Finset.mem_Icc.2 ⟨hkpos, by omega⟩
    have hmin := hk₀min k hkmem
    -- cross-multiply the minimality
    have hk₀R : (0 : ℚ) < (k₀ : ℚ) := by exact_mod_cast hk₀1
    have hkR : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hkpos
    have hcross : (rdilCount α k₀ : ℚ) * (k : ℚ) ≤ (rdilCount α k : ℚ) * (k₀ : ℚ) := by
      have hmul := mul_le_mul_of_nonneg_right hmin (le_of_lt (mul_pos hk₀R hkR))
      have e1 : (rdilCount α k₀ : ℚ) / (k₀ : ℚ) * ((k₀ : ℚ) * (k : ℚ))
          = (rdilCount α k₀ : ℚ) * (k : ℚ) := by field_simp
      have e2 : (rdilCount α k : ℚ) / (k : ℚ) * ((k₀ : ℚ) * (k : ℚ))
          = (rdilCount α k : ℚ) * (k₀ : ℚ) := by field_simp
      rw [e1, e2] at hmul
      exact hmul
    have hA : rdilCount α k₀ * k ≤ k₀ * rdilCount α k := by
      have : (rdilCount α k₀ * k : ℚ) ≤ ((k₀ * rdilCount α k : ℕ) : ℚ) := by
        push_cast
        linarith [hcross]
      exact_mod_cast this
    -- the reverse strict bound, from `⌈x⌉ < x + 1` and `α·k₀ ≤ ⌈α·k₀⌉`
    have hB : k₀ * rdilCount α k < rdilCount α k₀ * k + k₀ := by
      have h2 : (rdilCount α k : ℝ) < α * (k : ℝ) + 1 := rdilCount_lt h0 k
      have h3 : α * (k₀ : ℝ) ≤ (rdilCount α k₀ : ℝ) := le_rdilCount k₀
      have hk₀Rr : (0 : ℝ) < (k₀ : ℝ) := by exact_mod_cast hk₀1
      have hkRr : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hstep : (k₀ : ℝ) * (rdilCount α k : ℝ)
          < (rdilCount α k₀ : ℝ) * (k : ℝ) + (k₀ : ℝ) := by
        have e1 : (k₀ : ℝ) * (rdilCount α k : ℝ) < (k₀ : ℝ) * (α * (k : ℝ) + 1) := by
          exact mul_lt_mul_of_pos_left h2 hk₀Rr
        have e2 : (k₀ : ℝ) * (α * (k : ℝ) + 1) = (α * (k₀ : ℝ)) * (k : ℝ) + (k₀ : ℝ) := by
          ring
        have e3 : (α * (k₀ : ℝ)) * (k : ℝ) ≤ (rdilCount α k₀ : ℝ) * (k : ℝ) :=
          mul_le_mul_of_nonneg_right h3 hkRr
        linarith
      exact_mod_cast hstep
    -- assemble the division
    have hlo : rdilCount α k * k₀ ≤ rdilCount α k₀ * k + (k₀ - 1) := by
      have hcomm : k₀ * rdilCount α k = rdilCount α k * k₀ := Nat.mul_comm _ _
      omega
    have hhi : rdilCount α k₀ * k + (k₀ - 1) < (rdilCount α k + 1) * k₀ := by
      have hcomm : (rdilCount α k + 1) * k₀ = k₀ * rdilCount α k + k₀ := by ring
      omega
    change (rdilCount α k₀ * k + (k₀ - 1)) / k₀ = rdilCount α k
    exact Nat.div_eq_of_lt_le hlo hhi

/-! ## Prefixes of the real dilution -/

/-- Where the rational and real counters agree, the two dilutions of a sequence agree bit by bit. -/
lemma rdilate_eq_dilate {α : ℝ} {p q n : ℕ}
    (h : ∀ k, k ≤ n → dilCount p q k = rdilCount α k) (w : CantorSeq) {i : ℕ} (hi : i < n) :
    rdilate α w i = dilate p q w i := by
  have h1 : dilCount p q i = rdilCount α i := h i (by omega)
  have h2 : dilCount p q (i + 1) = rdilCount α (i + 1) := h (i + 1) (by omega)
  have hsel : dilSel p q i = rdilSel α i := by
    simp [dilSel, rdilSel, h1, h2]
  simp only [rdilate, dilate, hsel, h1]

/-- Where the rational and real counters agree, the length-`n` prefix of the real dilution is the
expansion of the first `rdilCount α n` source bits. -/
lemma cantorPrefix_rdilate {α : ℝ} {p q : ℕ} (hq : 0 < q) {n : ℕ}
    (h : ∀ k, k ≤ n → dilCount p q k = rdilCount α k) (w : CantorSeq) :
    cantorPrefix (rdilate α w) n = dilExpand p q n (cantorPrefix w (rdilCount α n)) := by
  have hcp : cantorPrefix (rdilate α w) n = cantorPrefix (dilate p q w) n := by
    refine List.ext_getElem (by simp) (fun i hi1 hi2 => ?_)
    have hin : i < n := by simpa using hi1
    simp only [cantorPrefix, List.getElem_ofFn]
    exact rdilate_eq_dilate h w hin
  rw [hcp, cantorPrefix_dilate p q hq w n, h n le_rfl]

/-! ## The code of the parameter is short -/

/-- The packed parameter of Problem 170 is below `(n+3)^4`. -/
private lemma dilPack_lt {n p q : ℕ} (hp : p ≤ n + 1) (hq : q ≤ n + 1) :
    dilPack n p q < (n + 3) ^ 4 := by
  have h1 : Nat.pair p q < (n + 2) ^ 2 := by
    refine lt_of_lt_of_le (Nat.pair_lt_max_add_one_sq p q) ?_
    have : max p q + 1 ≤ n + 2 := by omega
    exact Nat.pow_le_pow_left this 2
  have h2 : Nat.pair n (Nat.pair p q) < (max n (Nat.pair p q) + 1) ^ 2 :=
    Nat.pair_lt_max_add_one_sq _ _
  have h3 : max n (Nat.pair p q) + 1 ≤ (n + 3) ^ 2 := by
    have hn : n + 1 ≤ (n + 3) ^ 2 := by nlinarith
    have hpq : Nat.pair p q + 1 ≤ (n + 3) ^ 2 := by nlinarith [h1]
    omega
  calc dilPack n p q < (max n (Nat.pair p q) + 1) ^ 2 := h2
    _ ≤ ((n + 3) ^ 2) ^ 2 := Nat.pow_le_pow_left h3 2
    _ = (n + 3) ^ 4 := by ring

/-- The logarithmic budget of the header at length `n`. -/
private def hdrBudget (n : ℕ) : ℕ := Nat.log 2 (n + 3) + 1

private lemma length_natToBitString_le_hdr {n p q : ℕ} (hp : p ≤ n + 1) (hq : q ≤ n + 1) :
    (natToBitString (dilPack n p q)).length ≤ 4 * hdrBudget n := by
  refine length_natToBitString_le ?_
  have h1 : dilPack n p q < (n + 3) ^ 4 := dilPack_lt hp hq
  have h2 : n + 3 < 2 ^ hdrBudget n := Nat.lt_pow_succ_log_self (by norm_num) (n + 3)
  have h3 : (n + 3) ^ 4 ≤ (2 ^ hdrBudget n) ^ 4 := Nat.pow_le_pow_left h2.le 4
  have h4 : (2 ^ hdrBudget n) ^ 4 = 2 ^ (4 * hdrBudget n) := by
    rw [← pow_mul]; ring_nf
  omega

private lemma length_natToBitString_le_hdr' {a n : ℕ} (ha : a ≤ n) :
    (natToBitString a).length ≤ hdrBudget n := by
  refine length_natToBitString_le ?_
  have h2 : n + 3 < 2 ^ hdrBudget n := Nat.lt_pow_succ_log_self (by norm_num) (n + 3)
  omega

/-! ## The two-sided complexity estimate -/

private lemma toNat_le_of_le_add {a : ℕ∞} {b c : ℕ} (h : a ≤ (b : ℕ∞) + (c : ℕ∞)) :
    a.toNat ≤ b + c := by
  have h' : a ≤ ((b + c : ℕ) : ℕ∞) := by rw [Nat.cast_add]; exact h
  have := ENat.toNat_le_toNat h' (ENat.coe_ne_top _)
  simpa using this

private lemma le_toNat_add_of_le {a : ℕ∞} (ha : a ≠ ⊤) {b c : ℕ}
    (h : (b : ℕ∞) ≤ a + (c : ℕ∞)) : b ≤ a.toNat + c := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 ha
  subst hm
  have : ((b : ℕ) : ℕ∞) ≤ ((m + c : ℕ) : ℕ∞) := by rw [Nat.cast_add]; exact h
  have hb : b ≤ m + c := by exact_mod_cast this
  simpa using hb

/-- **The prefixes of a real dilution of a random sequence have complexity
`⌈α·n⌉ ± O(log n)`.** -/
theorem exists_const_abs_plainK_rdilate_sub_rdilCount_le (V : Map) (hV : isOptimalConditional V)
    {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {ω : CantorSeq}
    (hω : IsMartinLofRandom uniformMeasure ω) :
    ∃ C : ℕ, ∀ n : ℕ,
      (plainK V (cantorPrefix (rdilate α ω) n)).toNat
          ≤ rdilCount α n + C * hdrBudget n ∧
        rdilCount α n
          ≤ (plainK V (cantorPrefix (rdilate α ω) n)).toNat + C * hdrBudget n := by
  classical
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c₁, hc₁⟩ := exists_const_plainK_codedMap_le V hV computable₂_dilDecodeCoded
  obtain ⟨c₂, hc₂⟩ := plainK_le_length V hV
  obtain ⟨c₃, hc₃⟩ := exists_const_plainK_codedMap_le V hV computable₂_dilExtractCoded
  obtain ⟨c₄, hc₄⟩ := le_plainK_add_KPPlain_of_isMartinLofRandom_uniform hV hU hω
  obtain ⟨c₅, hc₅⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c₁ + c₂ + c₃ + c₄ + c₅ + 11, fun n => ?_⟩
  obtain ⟨p, q, hqpos, hpq, hqn, hpn, hsched⟩ := exists_dilCount_eq_rdilCount h0 h1 n
  set t : ℕ := dilPack n p q with ht
  set a : ℕ := rdilCount α n with ha
  set x : BitString := cantorPrefix ω a with hx
  set wn : BitString := cantorPrefix (rdilate α ω) n with hwn
  have hL : (natToBitString t).length ≤ 4 * hdrBudget n :=
    length_natToBitString_le_hdr hpn hqn
  have han : a ≤ n := rdilCount_le_self h1 n
  have hLa : (natToBitString a).length ≤ hdrBudget n := length_natToBitString_le_hdr' han
  have hbud : 1 ≤ hdrBudget n := by simp [hdrBudget]
  -- the two directions of the coded bijection
  have hdec : dilDecodeCoded t x = wn := by
    rw [ht, dilDecodeCoded_dilPack, hwn, cantorPrefix_rdilate hqpos hsched ω]
  have hext : dilExtractCoded t wn = x := by
    rw [ht, dilExtractCoded_dilPack, hwn, cantorPrefix_rdilate hqpos hsched ω]
    refine dilExtract_dilExpand p q hqpos hpq n _ ?_
    rw [cantorPrefix_length, ← ha, hsched n le_rfl]
  have hfinw : plainK V wn ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hc₂ wn)
    exact WithTop.add_ne_top.mpr ⟨ENat.coe_ne_top _, ENat.coe_ne_top _⟩
  have hfinx : plainK V x ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hc₂ x)
    exact WithTop.add_ne_top.mpr ⟨ENat.coe_ne_top _, ENat.coe_ne_top _⟩
  constructor
  · -- upper bound
    have step1 : plainK V wn
        ≤ plainK V x + ((2 * (natToBitString t).length + 1 + c₁ : ℕ) : ENat) := by
      rw [← hdec]; exact hc₁ t x
    have step2 : plainK V x ≤ ((a + c₂ : ℕ) : ENat) := by
      refine le_trans (hc₂ x) ?_
      have : (programLength x : ENat) = (a : ENat) := by
        simp [programLength, hx, cantorPrefix_length]
      rw [this]
      push_cast
      exact le_rfl
    have step3 : plainK V wn
        ≤ ((a + c₂ : ℕ) : ENat) + ((2 * (natToBitString t).length + 1 + c₁ : ℕ) : ENat) :=
      le_trans step1 (by gcongr)
    have step4 := toNat_le_of_le_add step3
    have hbnd : a + c₂ + (2 * (natToBitString t).length + 1 + c₁)
        ≤ a + (c₁ + c₂ + c₃ + c₄ + c₅ + 11) * hdrBudget n := by
      have h8 : 2 * (natToBitString t).length ≤ 8 * hdrBudget n := by omega
      nlinarith [hbud, hL]
    omega
  · -- lower bound
    have step1 : plainK V x
        ≤ plainK V wn + ((2 * (natToBitString t).length + 1 + c₃ : ℕ) : ENat) := by
      rw [← hext]; exact hc₃ t wn
    have step2 : (a : ℕ∞) ≤ plainK V x + KPNat U a + c₄ := hc₄ a
    have step3 : KPNat U a ≤ ((2 * (natToBitString a).length + c₅ : ℕ) : ENat) := by
      have := hc₅ (natToBitString a)
      rw [KPNat_def]
      refine le_trans this ?_
      push_cast
      exact le_rfl
    have step4 : (a : ℕ∞) ≤ plainK V wn
        + ((2 * (natToBitString t).length + 1 + c₃
            + (2 * (natToBitString a).length + c₅) + c₄ : ℕ) : ENat) := by
      calc (a : ℕ∞) ≤ plainK V x + KPNat U a + c₄ := step2
        _ ≤ (plainK V wn + ((2 * (natToBitString t).length + 1 + c₃ : ℕ) : ENat))
              + ((2 * (natToBitString a).length + c₅ : ℕ) : ENat) + c₄ := by gcongr
        _ = plainK V wn + ((2 * (natToBitString t).length + 1 + c₃
              + (2 * (natToBitString a).length + c₅) + c₄ : ℕ) : ENat) := by
            push_cast; ring
    have step5 := le_toNat_add_of_le hfinw step4
    have hbnd : 2 * (natToBitString t).length + 1 + c₃
        + (2 * (natToBitString a).length + c₅) + c₄
        ≤ (c₁ + c₂ + c₃ + c₄ + c₅ + 11) * hdrBudget n := by
      have h8 : 2 * (natToBitString t).length ≤ 8 * hdrBudget n := by omega
      have h2 : 2 * (natToBitString a).length ≤ 2 * hdrBudget n := by omega
      nlinarith [hbud]
    omega

/-! ## The limit of the normalized complexity -/

private lemma tendsto_hdrBudget_div (C : ℕ) :
    Tendsto (fun n : ℕ => ((C * hdrBudget n : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 3) / ((n : ℝ) + 3)) atTop (nhds 0) :=
    hlog.comp hshift
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) + 3) / (n : ℝ)) atTop (nhds 1) := by
    have h3 : Tendsto (fun n : ℕ => (3 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 3
    have := h3.const_add (1 : ℝ)
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    field_simp
  have hprod : Tendsto (fun n : ℕ =>
      (Real.log ((n : ℝ) + 3) / ((n : ℝ) + 3)) * (((n : ℝ) + 3) / (n : ℝ)))
      atTop (nhds 0) := by
    have := h2.mul hratio
    rwa [zero_mul] at this
  have hkey : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 3) / (n : ℝ)) atTop (nhds 0) := by
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h3R : ((n : ℝ) + 3) ≠ 0 := by positivity
    field_simp
  -- now squeeze `C * hdrBudget n / n` between `0` and a multiple of `log (n+3)/n`
  have hbound : ∀ n : ℕ, 0 < n →
      ((C * hdrBudget n : ℕ) : ℝ) / (n : ℝ)
        ≤ ((C : ℝ) / Real.log 2) * (Real.log ((n : ℝ) + 3) / (n : ℝ)) + (C : ℝ) / (n : ℝ) := by
    intro n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hpow : (2 : ℕ) ^ Nat.log 2 (n + 3) ≤ n + 3 :=
      Nat.pow_log_le_self 2 (by omega)
    have hpowR : (2 : ℝ) ^ Nat.log 2 (n + 3) ≤ (n : ℝ) + 3 := by
      have := (Nat.cast_le (α := ℝ)).2 hpow
      push_cast at this
      linarith
    have hlogle : (Nat.log 2 (n + 3) : ℝ) * Real.log 2 ≤ Real.log ((n : ℝ) + 3) := by
      have hp : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 (n + 3) := by positivity
      have := Real.log_le_log hp hpowR
      rwa [Real.log_pow] at this
    have hnum : ((C * hdrBudget n : ℕ) : ℝ)
        ≤ (C : ℝ) * (Real.log ((n : ℝ) + 3) / Real.log 2) + (C : ℝ) := by
      have hstep : (Nat.log 2 (n + 3) : ℝ) ≤ Real.log ((n : ℝ) + 3) / Real.log 2 := by
        rw [le_div_iff₀ hlog2]
        exact hlogle
      have : ((C * hdrBudget n : ℕ) : ℝ) = (C : ℝ) * ((Nat.log 2 (n + 3) : ℝ) + 1) := by
        simp [hdrBudget]
      rw [this]
      nlinarith [Nat.cast_nonneg (α := ℝ) C]
    rw [div_le_iff₀ hnR]
    have hR : ((C : ℝ) / Real.log 2 * (Real.log ((n : ℝ) + 3) / (n : ℝ))
        + (C : ℝ) / (n : ℝ)) * (n : ℝ)
        = (C : ℝ) * (Real.log ((n : ℝ) + 3) / Real.log 2) + (C : ℝ) := by
      field_simp
    rw [hR]
    exact hnum
  have hmaj : Tendsto (fun n : ℕ =>
      ((C : ℝ) / Real.log 2) * (Real.log ((n : ℝ) + 3) / (n : ℝ)) + (C : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    have hA : Tendsto (fun n : ℕ =>
        ((C : ℝ) / Real.log 2) * (Real.log ((n : ℝ) + 3) / (n : ℝ))) atTop (nhds 0) := by
      have := hkey.const_mul ((C : ℝ) / Real.log 2)
      rwa [mul_zero] at this
    have hB : Tendsto (fun n : ℕ => (C : ℝ) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have := hA.add hB
    rwa [add_zero] at this
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact hbound n hn

/-- **The normalized plain complexity of the prefixes of a real dilution tends
to `α`.** -/
theorem tendsto_normalizedPlainK_rdilate (V : Map) (hV : isOptimalConditional V)
    {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {ω : CantorSeq}
    (hω : IsMartinLofRandom uniformMeasure ω) :
    Tendsto (fun n : ℕ =>
        ((plainK V (cantorPrefix (rdilate α ω) n)).toNat : ℝ) / (n : ℝ)) atTop (nhds α) := by
  obtain ⟨C, hC⟩ := exists_const_abs_plainK_rdilate_sub_rdilCount_le V hV h0 h1 hω
  set K : ℕ → ℕ := fun n => (plainK V (cantorPrefix (rdilate α ω) n)).toNat with hK
  set g : ℕ → ℝ := fun n => ((C * hdrBudget n : ℕ) : ℝ) / (n : ℝ) with hg
  have hgt : Tendsto g atTop (nhds 0) := tendsto_hdrBudget_div C
  have hlo : Tendsto (fun n : ℕ => α - (g n + 1 / (n : ℝ))) atTop (nhds α) := by
    have h1' : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have := (hgt.add h1').const_sub α
    rwa [add_zero, sub_zero] at this
  have hhi : Tendsto (fun n : ℕ => α + (g n + 1 / (n : ℝ))) atTop (nhds α) := by
    have h1' : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have := (hgt.add h1').const_add α
    rwa [add_zero, add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlow := (hC n).2
    have hcast : α * (n : ℝ) ≤ (rdilCount α n : ℝ) := le_rdilCount n
    have hstep : α * (n : ℝ) ≤ (K n : ℝ) + ((C * hdrBudget n : ℕ) : ℝ) := by
      have : ((rdilCount α n : ℕ) : ℝ) ≤ (K n : ℝ) + ((C * hdrBudget n : ℕ) : ℝ) := by
        exact_mod_cast hlow
      linarith
    rw [le_div_iff₀ hnR]
    have e : (α - (g n + 1 / (n : ℝ))) * (n : ℝ)
        = α * (n : ℝ) - ((C * hdrBudget n : ℕ) : ℝ) - 1 := by
      simp only [hg]
      field_simp
      ring
    rw [e]
    linarith [hstep]
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hup := (hC n).1
    have hcast : (rdilCount α n : ℝ) < α * (n : ℝ) + 1 := rdilCount_lt h0 n
    have hstep : (K n : ℝ) ≤ α * (n : ℝ) + 1 + ((C * hdrBudget n : ℕ) : ℝ) := by
      have : (K n : ℝ) ≤ ((rdilCount α n : ℕ) : ℝ) + ((C * hdrBudget n : ℕ) : ℝ) := by
        exact_mod_cast hup
      linarith
    rw [div_le_iff₀ hnR]
    have e : (α + (g n + 1 / (n : ℝ))) * (n : ℝ)
        = α * (n : ℝ) + ((C * hdrBudget n : ℕ) : ℝ) + 1 := by
      simp only [hg]
      field_simp
      ring
    rw [e]
    linarith [hstep]

/-- **SUV Problem 170 (§5.8, p. 175), the singleton form.**  For every real
`α ∈ [0,1]` there is a sequence whose singleton has effective Hausdorff
dimension `α`. -/
theorem exists_effectiveHausdorffDim_singleton_eq {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    ∃ w : CantorSeq, effectiveHausdorffDim {w} = α := by
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  obtain ⟨ω, hω⟩ := exists_isMartinLofRandom_uniform
  refine ⟨rdilate α ω, ?_⟩
  rw [effectiveHausdorffDim_singleton_eq_liminf V hV]
  exact (tendsto_normalizedPlainK_rdilate V hV h0 h1 hω).liminf_eq

end Kolmogorov
