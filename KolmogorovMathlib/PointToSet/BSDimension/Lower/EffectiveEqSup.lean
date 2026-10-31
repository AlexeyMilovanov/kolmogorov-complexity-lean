/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Lower.NullCovers

/-!
# Effective lower Barreira–Schmeling dimension as a supremum of pointwise dimensions

This module proves the inequality `sup_{x ∈ Z} d^A(x) ≤ d^A_eff(Z)` for admissible oracles `A`
and sets `Z` on which the lower Birkhoff average is positive
(blueprint node `bs:effective-lower-lower`), and combines it with the converse inequality of
`NullCovers` into the equality `effectiveLowerBSEqSup` (blueprint node
`bs:effective-lower-equality`).

Given an `A`-enumerable null `s`-cover `E` of `Z`, a point `x ∈ Z` and a rational `t > s`, the
`t`-weighted mass of the part of `E` where the Birkhoff sums are at least half of their
guaranteed linear growth is finite.  The relative coding theorem
(`oracle_coding_finite_mass`) therefore bounds the oracle complexity of the covering indices by
`t` times the Birkhoff sum plus a constant, which shows that the lower pointwise dimension of `x`
is at most `t`.  Letting `t ↓ s` and taking the infimum over covers gives the result.

The exponent `s` is never assumed computable: the coding theorem is only applied with rational
exponents.  The results are used by the point-to-set principle for the Barreira–Schmeling
dimension in `KolmogorovMathlib.PointToSet.BSDimension.Lower`.
-/

namespace Kolmogorov.PointToSet

open Filter

open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- The pairs `(i, n)` of the slice of `E` at scale `p` whose order is at least `N` and whose
Birkhoff sum at the ideal point `P.ι i` exceeds `ρ * n / 2`. -/
private def largeCostSlice (P : Presentation X) (T : X → X) (u : X → ℝ)
    (E : Set (ℕ × ℕ × ℕ)) (p N : ℕ) (ρ : ℚ) : Set (ℕ × ℕ) :=
  {a | (a.1, a.2, p) ∈ E ∧ N ≤ a.2 ∧ (ρ : ℝ) * a.2 / 2 < birkhoffSum T u a.2 (P.ι a.1)}

/-- The `t`-weighted mass of `largeCostSlice` is bounded by the `s`-mass of the cover for every
`t > s`, because the Birkhoff sums on the slice are nonnegative. -/
private lemma tsum_largeCostSlice_le_nullBSMass (P : Presentation X) (T : X → X) (u : X → ℝ)
    {s : ℝ} {t : ℚ} (hst : s < (t : ℝ)) (E : Set (ℕ × ℕ × ℕ)) (p N : ℕ) {ρ : ℚ} (hρ : 0 < ρ) :
    (∑' a : largeCostSlice P T u E p N ρ,
      (2 : ℝ≥0∞) ^ (-((t : ℝ) * birkhoffSum T u a.1.2 (P.ι a.1.1))))
      ≤ nullBSMass P T u s E := by
  classical
  let w : ℕ × ℕ × ℕ → ℝ≥0∞ := fun z ↦ (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u z.2.1 (P.ι z.1))
  have hinj : Function.Injective (fun a : ℕ × ℕ ↦ (a.1, a.2, p)) := fun a b h ↦
    Prod.ext (congrArg (·.1) h) (congrArg (·.2.1) h)
  calc
    _ = ∑' a : ℕ × ℕ, (largeCostSlice P T u E p N ρ).indicator
        (fun a ↦ (2 : ℝ≥0∞) ^ (-((t : ℝ) * birkhoffSum T u a.2 (P.ι a.1)))) a :=
      tsum_subtype _ _
    _ ≤ ∑' a : ℕ × ℕ, E.indicator w (a.1, a.2, p) := by
      refine ENNReal.tsum_le_tsum fun a ↦ ?_
      by_cases h : a ∈ largeCostSlice P T u E p N ρ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h.1]
        have hρ' : (0 : ℝ) ≤ ρ := by exact_mod_cast hρ.le
        have hsum : 0 ≤ birkhoffSum T u a.2 (P.ι a.1) :=
          ((div_nonneg (mul_nonneg hρ' (Nat.cast_nonneg _)) two_pos.le)).trans h.2.2.le
        exact ENNReal.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith)
      · rw [Set.indicator_of_notMem h]
        exact bot_le
    _ ≤ ∑' z : ℕ × ℕ × ℕ, E.indicator w z :=
      ENNReal.tsum_comp_le_tsum_of_injective hinj (E.indicator w)
    _ = ∑' z : E, w z := (tsum_subtype E w).symm
    _ = nullBSMass P T u s E := by
      simp only [nullBSMass, nullPressureMass, neg_zero, zero_mul, zero_add,
        w, birkhoffSum, Finset.mul_sum]

/-- For a rational `t` of either sign, the strict upper cuts `t * v a < q` of a computable real
family `v` form an enumerable predicate on `α × ℚ`. -/
private lemma isREIn_ratMul_lt {α : Type*} [Primcodable α] {A : Set ℕ} {v : α → ℝ}
    (hv : IsComputableRealFamilyIn A v) (t : ℚ) :
    IsREIn A (fun aq : α × ℚ ↦ (t : ℝ) * v aq.1 < (aq.2 : ℝ)) := by
  have hdiv : Computable (fun aq : α × ℚ ↦ (aq.1, aq.2 * t⁻¹)) :=
    Computable.fst.pair (computable₂_ratMul.comp Computable.snd (Computable.const t⁻¹))
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have htR : (t : ℝ) < 0 := by exact_mod_cast ht
    have h := (birkhoff_computableIn_gt A v hv).comp hdiv.computableIn
    have heq (a : α) (q : ℚ) :
        ((q * t⁻¹ : ℚ) : ℝ) < v a ↔ (t : ℝ) * v a < (q : ℝ) := by
      push_cast
      rw [← div_eq_mul_inv, div_lt_iff_of_neg htR, mul_comm (v a)]
    simpa only [heq] using h
  · have h : IsREIn A (fun aq : α × ℚ ↦ (0 : ℚ) < aq.2) :=
      isREIn_of_computable_decide
        (computable₂_ratLt.comp (Computable.const 0) Computable.snd)
    simpa only [Rat.cast_zero, zero_mul, Rat.cast_pos] using h
  · have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have h := (birkhoff_computableIn_lt A v hv).comp hdiv.computableIn
    have heq (a : α) (q : ℚ) :
        v a < ((q * t⁻¹ : ℚ) : ℝ) ↔ (t : ℝ) * v a < (q : ℝ) := by
      push_cast
      rw [← div_eq_mul_inv, lt_div_iff₀ htR, mul_comm (v a)]
    simpa only [heq] using h

/-- A rational multiple of a computable real family is upper semicomputable on any relatively
enumerable domain. -/
private lemma isUpperSemicomputableOnIn_ratMul {α : Type*} [Primcodable α] {A : Set ℕ}
    {v : α → ℝ} (hv : IsComputableRealFamilyIn A v) {D : α → Prop} (hD : IsREIn A D) (t : ℚ) :
    IsUpperSemicomputableOnIn A D (fun a ↦ (t : ℝ) * v a.val) := by
  refine ⟨fun aq ↦ D aq.1 ∧ (t : ℝ) * v aq.1 < (aq.2 : ℝ),
    IsREIn.and (hD.comp Computable.fst.computableIn) (isREIn_ratMul_lt hv t),
    fun a q ha ↦ ⟨ha.1, ha.2⟩, fun a ε hε ↦ ?_⟩
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (lt_add_of_pos_right ((t : ℝ) * v a.val) hε)
  exact ⟨q, ⟨a.property, hq₁⟩, hq₂⟩

/-- The relative coding theorem for costs defined on an arbitrary countable type `α`: an
effective injection `code : α → BitString` with a left inverse transports an upper
semicomputable cost with finite mass to bit strings, and the coding theorem then bounds the
oracle complexity of the codes by the cost plus a constant. -/
private lemma exists_oracleComplexity_code_le {α : Type*} [Primcodable α] {A : Set ℕ}
    {D : α → Prop} (hD : IsREIn A D) {v : α → ℝ}
    (hv : IsUpperSemicomputableOnIn A D (fun a ↦ v a.val))
    (hmass : (∑' a : Subtype D, (2 : ℝ≥0∞) ^ (-v a.val)) < ⊤)
    {code : α → BitString} {decode : BitString → α}
    (hcode : Computable code) (hleft : Function.LeftInverse decode code) :
    ∃ c : ℕ, ∀ a, D a → (oracleComplexity A (code a) : ℝ) ≤ v a + c := by
  let F : BitString → Prop := fun w ↦ ∃ a, D a ∧ code a = w
  have hF : IsREIn A F := hD.image hcode
  let g : Subtype F → ℝ := fun w ↦ v (decode w.val)
  obtain ⟨U, hU, hUsound, hUclose⟩ := hv
  have hV : IsREIn A (fun wq : BitString × ℚ ↦ ∃ aq : α × ℚ, U aq ∧ (code aq.1, aq.2) = wq) :=
    hU.image ((hcode.comp Computable.fst).pair Computable.snd)
  have hg : IsUpperSemicomputableOnIn A F g := by
    refine ⟨_, hV, fun w q ⟨⟨a, r⟩, ha, he⟩ ↦ ?_, fun w ε hε ↦ ?_⟩
    · obtain ⟨haD, hav⟩ := hUsound a r ha
      have hwcode : code a = w := congrArg Prod.fst he
      have hrq : r = q := congrArg Prod.snd he
      exact ⟨⟨a, haD, hwcode⟩, by simpa [g, ← hwcode, hleft a, hrq] using hav⟩
    · obtain ⟨a, haD, haw⟩ := w.property
      obtain ⟨q, hqU, hq⟩ := hUclose ⟨a, haD⟩ ε hε
      exact ⟨q, ⟨(a, q), hqU, Prod.ext haw rfl⟩, by simpa [g, ← haw, hleft a] using hq⟩
  have hdecode (w : Subtype F) : D (decode w.val) := by
    obtain ⟨a, ha, haw⟩ := w.property
    simpa [← haw, hleft a] using ha
  have hdecinj : Function.Injective
      (fun w : Subtype F ↦ (⟨decode w.val, hdecode w⟩ : Subtype D)) := by
    intro w z he
    obtain ⟨a, haD, haw⟩ := w.property
    obtain ⟨b, hbD, hbz⟩ := z.property
    have hab : a = b := by
      simpa [← haw, ← hbz, hleft a, hleft b] using congrArg (·.val) he
    exact Subtype.ext (haw.symm.trans ((congrArg code hab).trans hbz))
  have hgmass : (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w)) < ⊤ :=
    lt_of_le_of_lt (ENNReal.tsum_comp_le_tsum_of_injective hdecinj
      (fun a : Subtype D ↦ (2 : ℝ≥0∞) ^ (-v a.val))) hmass
  obtain ⟨c, hc⟩ := oracle_coding_finite_mass A F g hF hg _ le_rfl hgmass
  exact ⟨c, fun a ha ↦ by simpa [g, hleft a] using hc ⟨code a, ⟨a, ha, rfl⟩⟩⟩

/-- Coding the finite-mass slice of an enumerable cover bounds the oracle complexity of the
covering indices: for a rational `t`, if the `t`-weighted mass of `largeCostSlice` is finite,
then `K^A(i) ≤ t * (Birkhoff sum) + c` for a constant `c` and all `(i, n)` in the slice. -/
private lemma exists_oracleNatComplexity_le (P : Presentation X) (T : X → X) (u : X → ℝ)
    {A : Set ℕ} (hA : IsAdmissible P T (fun _ : Fin 1 ↦ u) A) (t : ℚ)
    {E : Set (ℕ × ℕ × ℕ)} (hRE : IsREIn A E) (p N : ℕ) (ρ : ℚ)
    (hmass : (∑' a : largeCostSlice P T u E p N ρ,
      (2 : ℝ≥0∞) ^ (-((t : ℝ) * birkhoffSum T u a.1.2 (P.ι a.1.1)))) < ⊤) :
    ∃ c : ℝ, ∀ i n, (i, n, p) ∈ E → N ≤ n → (ρ : ℝ) * n / 2 < birkhoffSum T u n (P.ι i) →
      (oracleNatComplexity A i : ℝ) ≤ (t : ℝ) * birkhoffSum T u n (P.ι i) + c := by
  let v : ℕ × ℕ → ℝ := fun a ↦ birkhoffSum T u a.2 (P.ι a.1)
  have hv : IsComputableRealFamilyIn A v := by
    obtain ⟨q, hq, herr⟩ := birkhoff_computableIn P T (fun _ : Fin 1 ↦ u) A hA
    refine ⟨fun ap ↦ q ((0, ap.1.2, ap.1.1), ap.2), ?_, fun a j ↦ herr (0, a.2, a.1) j⟩
    exact hq.comp (((Computable.const (0 : Fin 1)).pair
      ((Computable.snd.comp Computable.fst).pair
        (Computable.fst.comp Computable.fst))).pair Computable.snd).computableIn
  have hD : IsREIn A (fun a ↦ a ∈ largeCostSlice P T u E p N ρ) := by
    refine IsREIn.and (hRE.comp
      (Computable.fst.pair (Computable.snd.pair (Computable.const p))).computableIn)
      (IsREIn.and ?_ ?_)
    · exact isREIn_of_computable_decide
        (Primrec.nat_le.decide.to_comp.comp (Computable.const N) Computable.snd)
    · have hhalf : Computable fun a : ℕ × ℕ ↦ (a, ρ / 2 * (a.2 : ℚ)) :=
        Computable.id.pair (computable₂_ratMul.comp (Computable.const (ρ / 2))
          (computable_nat_to_rat.comp Computable.snd))
      have h := (birkhoff_computableIn_gt A v hv).comp hhalf.computableIn
      simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast,
        div_mul_eq_mul_div, v, id_eq] using h
  have hcode : Computable (fun a : ℕ × ℕ ↦ pairCode (natBits a.1) (natBits a.2)) :=
    Computable₂.comp pairCode_computable (natBits_computable.comp Computable.fst)
      (natBits_computable.comp Computable.snd)
  have hleft : Function.LeftInverse
      (fun w ↦ (decodeBits (decodeFirst w), decodeBits (decodeSecond w)))
      (fun a : ℕ × ℕ ↦ pairCode (natBits a.1) (natBits a.2)) := fun a ↦ by
    simp [decodeFirst_pairCode, decodeSecond_pairCode, natBits, decodeBits_natBits]
  obtain ⟨c, hc⟩ := exists_oracleComplexity_code_le hD (v := fun a ↦ (t : ℝ) * v a)
    (isUpperSemicomputableOnIn_ratMul hv hD t) hmass hcode hleft
  obtain ⟨cTuple, hTuple⟩ := oracle_tuple_bounds A
  refine ⟨c + cTuple, fun i n hi hn hpos ↦ ?_⟩
  have h1 : (oraclePairComplexity A i n : ℝ) ≤ (t : ℝ) * v (i, n) + c := hc (i, n) ⟨hi, hn, hpos⟩
  have h2 : (oracleNatComplexity A i : ℝ) ≤ oraclePairComplexity A i n + cTuple := by
    exact_mod_cast hTuple i n
  linarith

/-- Dyadic radii are eventually below any positive bound. -/
private lemma eventually_dyadicRadius_le {r : ℝ} (hr : 0 < r) :
    ∀ᶠ p : ℕ in atTop, dyadicRadius p ≤ r :=
  ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num)).eventually (gt_mem_nhds hr)).mono fun _ h ↦ h.le

/-- If `K ≤ t * b + c` and `b ≥ r > 0`, then `K / b ≤ t + max c 0 / r` in `ℝ≥0∞`. -/
private lemma natCast_div_ofReal_le {K : ℕ} {t b r c : ℝ} (hr : 0 < r) (hrb : r ≤ b)
    (hK : (K : ℝ) ≤ t * b + c) :
    (K : ℝ≥0∞) / ENNReal.ofReal b ≤
      ENNReal.ofReal t + ENNReal.ofReal (max c 0) / ENNReal.ofReal r := by
  have hb : 0 < b := hr.trans_le hrb
  have hreal : (K : ℝ) / b ≤ t + max c 0 / r := by
    rw [div_le_iff₀ hb]
    have h1 : max c 0 ≤ max c 0 / r * b := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hr]
      exact mul_le_mul_of_nonneg_left hrb (le_max_right c 0)
    nlinarith [le_max_left c 0]
  calc (K : ℝ≥0∞) / ENNReal.ofReal b
      = ENNReal.ofReal ((K : ℝ) / b) := by
        rw [ENNReal.ofReal_div_of_pos hb, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (t + max c 0 / r) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal t + ENNReal.ofReal (max c 0 / r) := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal t + ENNReal.ofReal (max c 0) / ENNReal.ofReal r := by
        rw [ENNReal.ofReal_div_of_pos hr]

/-- A nonnegative constant divided by `ρ * n` tends to `0` in `ℝ≥0∞` as `n → ∞`. -/
private lemma tendsto_ofReal_div_ofReal_mul_natCast {C ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal C / ENNReal.ofReal (ρ * n)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (C / ρ / n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_const_div_atTop_nhds_zero_nat (C / ρ))
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [← div_mul_eq_div_div, ENNReal.ofReal_div_of_pos (mul_pos hρ (by exact_mod_cast hn))]

/-- If for every `k` there is an index `n ≥ k` with `f n ≤ a + g n`, where `g` tends to `0`,
then the `liminf` of `f` is at most `a`. -/
private lemma liminf_le_of_frequently_le_add {f g : ℕ → ℝ≥0∞} {a : ℝ≥0∞}
    (hg : Tendsto g atTop (𝓝 0)) (h : ∀ k, ∃ n ≥ k, f n ≤ a + g n) : liminf f atTop ≤ a := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  refine liminf_le_of_frequently_le ?_ (by isBoundedDefault)
  obtain ⟨k₂, hk₂⟩ := eventually_atTop.mp
    ((hg.eventually (gt_mem_nhds (ENNReal.coe_pos.mpr hε))).mono fun _ h ↦ h.le)
  rw [frequently_atTop]
  intro k
  obtain ⟨n, hn, hle⟩ := h (max k k₂)
  exact ⟨n, (le_max_left _ _).trans hn,
    hle.trans (add_le_add_right (hk₂ n ((le_max_right _ _).trans hn)) a)⟩

/-- At a fixed scale `p`, if a cover supplies covering indices `(i, n)` of arbitrarily large
order whose complexity is at most `t` times the Birkhoff sum plus a constant, then the lower
limit of the finite-scale costs at `x` is at most `t`. -/
private lemma liminf_finiteScaleBSCost_le (P : Presentation X) (T : X → X) (u : X → ℝ)
    (A : Set ℕ) {x : X} {t : ℚ} {E : Set (ℕ × ℕ × ℕ)} {p N : ℕ} {ρ : ℚ} (hρ : 0 < ρ) {c : ℝ}
    (h_cover : ∀ k, ∃ i n, max 1 k ≤ n ∧ (i, n, p) ∈ E ∧
      x ∈ bowenBall T n (P.ι i) (dyadicRadius p))
    (h_bounds : ∀ i n, N ≤ n → P.ι i ∈ bowenBall T n x (dyadicRadius p) →
      (ρ : ℝ) * n ≤ birkhoffSum T u n (P.ι i))
    (h_coding : ∀ i n, (i, n, p) ∈ E → N ≤ n → (ρ : ℝ) * n / 2 < birkhoffSum T u n (P.ι i) →
      (oracleNatComplexity A i : ℝ) ≤ (t : ℝ) * birkhoffSum T u n (P.ι i) + c) :
    liminf (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) atTop ≤
      ENNReal.ofReal (t : ℝ) := by
  refine liminf_le_of_frequently_le_add
    (tendsto_ofReal_div_ofReal_mul_natCast (C := max c 0)
      (by exact_mod_cast hρ : (0 : ℝ) < ρ)) fun k ↦ ?_
  obtain ⟨i, n, hn, hE, hx⟩ := h_cover (max k N)
  have hnk : k ≤ n := (le_max_left k N).trans ((le_max_right 1 _).trans hn)
  have hnN : N ≤ n := (le_max_right k N).trans ((le_max_right 1 _).trans hn)
  have hn0 : n ≠ 0 := by have := (le_max_left 1 _).trans hn; omega
  have hρn : (0 : ℝ) < (ρ : ℝ) * n :=
    mul_pos (by exact_mod_cast hρ) (by exact_mod_cast Nat.pos_of_ne_zero hn0)
  have hbound := h_bounds i n hnN (mem_bowenBall_symm hx)
  refine ⟨n, hnk, (finiteScaleBSCost_le_div P T u A hn0 (mem_bowenBall_symm hx)
    (hρn.trans_le hbound)).trans (natCast_div_ofReal_le hρn hbound ?_)⟩
  exact h_coding i n hE hnN (by linarith)

/-- The lower pointwise dimension is at most `a` as soon as the lower limit of the
finite-scale costs is at most `a` at all sufficiently fine dyadic scales. -/
private lemma pointwiseBSDimension_fst_le_of_eventually (P : Presentation X) (T : X → X)
    (u : X → ℝ) (A : Set ℕ) (x : X) {a : ℝ≥0∞}
    (h : ∀ᶠ p : ℕ in atTop,
      liminf (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) atTop ≤ a) :
    (pointwiseBSDimension P T u A x).1 ≤ a := by
  obtain ⟨p₀, hp₀⟩ := eventually_atTop.mp h
  have H := pointwiseBSDimension_eq_tail P T u A x LimitSide.lower p₀
  dsimp [LimitSide.choose] at H
  rw [H]
  dsimp [LimitSide.timeLimit]
  exact iSup_le fun p ↦ iSup_le fun hp ↦ hp₀ p hp

/-- An extended nonnegative real is at most `ENNReal.ofReal s` as soon as it is at most
`ENNReal.ofReal t` for every rational `t > s`. -/
private lemma le_ofReal_of_forall_rat_gt {a : ℝ≥0∞} {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ t : ℚ, s < (t : ℝ) → a ≤ ENNReal.ofReal (t : ℝ)) : a ≤ ENNReal.ofReal s := by
  refine le_of_forall_gt_imp_ge_of_dense fun b hb ↦ ?_
  rcases eq_top_or_lt_top b with rfl | hlt
  · exact le_top
  rw [← ENNReal.ofReal_toReal hlt.ne] at hb ⊢
  obtain ⟨t, hst, htb⟩ := exists_rat_btwn ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs).mp hb)
  exact (h t hst).trans (ENNReal.ofReal_le_ofReal htb.le)

/-- Coding an enumerable null cover bounds each lower pointwise dimension. Its real
exponent is not assumed computable. Blueprint node `bs:effective-lower-lower`. -/
theorem pointwiseLowerBSLeEffective (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ)
    (hA : IsAdmissible P T (fun _ : Fin 1 => u) A) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (s : ℝ) (hs : 0 ≤ s)
    (E : Set (ℕ × ℕ × ℕ)) (hE : IsNullBSCover P T u Z s E) (hRE : IsREIn A E)
    (x : X) (hx : x ∈ Z) :
    (pointwiseBSDimension P T u A x).1 ≤ ENNReal.ofReal s := by
  refine le_ofReal_of_forall_rat_gt hs fun t hst ↦ ?_
  obtain ⟨ρ, hρ, r₀, hr₀, hRealizer⟩ := birkhoffRealizerBounds_positive P T hT u hu x (hZ x hx)
  refine pointwiseBSDimension_fst_le_of_eventually P T u A x ?_
  filter_upwards [eventually_dyadicRadius_le hr₀] with p hp
  obtain ⟨N, -, hN⟩ := hRealizer (dyadicRadius p) (dyadicRadius_pos p) hp
  obtain ⟨c, hc⟩ := exists_oracleNatComplexity_le P T u hA t hRE p N ρ
    ((tsum_largeCostSlice_le_nullBSMass P T u hst E p N hρ).trans_lt hE.1)
  exact liminf_finiteScaleBSCost_le P T u A hρ (fun k ↦ hE.2 p k x hx)
    (fun i n hn hi ↦ (hN n hn i hi).1) hc

/-- Taking the actual witness infimum bounds the supremum of lower pointwise dimensions.
Blueprint node `bs:effective-lower-lower`. -/
theorem pointwiseLowerBSLeEffective_iSup (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ)
    (hA : IsAdmissible P T (fun _ : Fin 1 => u) A) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    (⨆ x ∈ Z, (pointwiseBSDimension P T u A x).1) ≤ effectiveLowerBSDimension P T u A Z := by
  refine iSup_le fun x ↦ iSup_le fun hx ↦ ?_
  unfold effectiveLowerBSDimension
  refine le_iInf fun s ↦ le_iInf fun hs ↦ le_iInf fun E ↦ le_iInf fun hE ↦ ?_
  exact pointwiseLowerBSLeEffective P T hT u hu A hA Z hZ s hs E hE.1 hE.2 x hx

/-- Effective lower BS dimension equals the lower pointwise supremum for admissible oracles.
Blueprint node `bs:effective-lower-equality`. -/
theorem effectiveLowerBSEqSup (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ)
    (hA : IsAdmissible P T (fun _ : Fin 1 => u) A) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    effectiveLowerBSDimension P T u A Z = ⨆ x ∈ Z, (pointwiseBSDimension P T u A x).1 :=
  le_antisymm (effectiveLowerBSLeSup P T hT u hu A hA Z hZ)
    (pointwiseLowerBSLeEffective_iSup P T hT u hu A hA Z hZ)

end Kolmogorov.PointToSet
