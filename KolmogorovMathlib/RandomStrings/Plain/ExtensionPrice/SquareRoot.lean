/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.ExtensionPrice.Decompositions

/-!
# Structural volume estimates and extension prices

The past/future decompositions and density bounds give the five structural volume estimates
of blueprint node `key:volumes`. These estimates control the computable dyadic extension
price and its completeness and soundness bounds. The resulting square-root slack is used
by the subsequent pricing and accounting arguments in the plain-random-string separation.
-/

namespace Kolmogorov.Milovanov

/-- All five volume estimates with a single constant `C`.
Blueprint node `key:volumes`. Natural witnesses for the lower-base complexity precede its
use in exponents. The signed correction comes from the bounded proxy at the true marker. -/
structure StructuralVolumeBounds (B : Base) (C n : ℕ) (candidate : Candidate)
    (x : BitString) (q : ℕ) : Prop where
  /-- Item 1: a plain description within `q` gives the upper-scale density lower bound. -/
  simple : Simple B.V x q →
    (2 : ℚ) ^ ((extensionScale q : ℤ) - q - C) ≤ strictExtensionCount B q x
  /-- Item 2: the upper total volume is bounded above by the sum and below by the future part. -/
  decomposition :
    (strictExtensionCount B q x : ℚ) ≤ (2 : ℚ) ^ (C : ℤ) *
      (pastExtensionCount B n candidate q x +
        strictExtensionCount B q (upperFutureBase B n candidate x q)) ∧
    (2 : ℚ) ^ (-(C : ℤ)) * strictExtensionCount B q (upperFutureBase B n candidate x q) ≤
      strictExtensionCount B q x
  /-- Item 3: the upper future volume has exponent `Q - Δ - k` with constant error. -/
  future : ∀ k : ℕ, KP B.D (lowerProxyBase B n candidate x q) (bits n) = (k : ENat) →
    (2 : ℚ) ^ ((extensionScale q : ℤ) - structuralProxyDelta B n candidate q - k - C) ≤
      strictExtensionCount B q (upperFutureBase B n candidate x q) ∧
    (strictExtensionCount B q (upperFutureBase B n candidate x q) : ℚ) ≤
      (2 : ℚ) ^ ((extensionScale q : ℤ) - structuralProxyDelta B n candidate q - k + C)
  /-- Item 4: the lower past-plus-marker volume has exponent `N - k` with constant error. -/
  remaining : ∀ k : ℕ,
    KP B.D (lowerProxyBase B n candidate x q) (bits n) = (k : ENat) →
    let R := pastExtensionCount B n candidate n (lowerProxyBase B n candidate x q) +
      strictExtensionCount B n (triple x q candidate.1)
    (2 : ℚ) ^ ((extensionScale n : ℤ) - k - C) ≤ R ∧
      (R : ℚ) ≤ (2 : ℚ) ^ ((extensionScale n : ℤ) - k + C)
  /-- Item 5: relaxed marker-triple volume loses at most `C(δ+1)` bits. -/
  relaxed : ∀ δ : ℕ, (extensionCount B n δ (triple x q candidate.1) : ℚ) ≤
    (2 : ℚ) ^ ((C : ℤ) * (δ + 1)) * strictExtensionCount B n (triple x q candidate.1)

/-- One `C ≥ 1` simultaneously controls all five structural volume estimates.
Blueprint node `key:volumes`. The constant is selected before all variable parameters. -/
theorem key_lemma_structural_volume_interface (B : Base) :
    ∃ C n₀ : ℕ, 1 ≤ C ∧ 32 ≤ n₀ ∧
      ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
        KeyParameters B n₀ n candidate x q → StructuralVolumeBounds B C n candidate x q := by
  obtain ⟨c0d, cDen, hDen⟩ := extension_density B
  obtain ⟨c0r, cRel, hRel⟩ := extension_density_relaxed B
  obtain ⟨cPP, hPP⟩ := plain_prefix_supplied_length_interface B
  obtain ⟨cDec, nDec, hnDec, hDec⟩ := key_lemma_past_future_decompositions_common B
  obtain ⟨cSym, nSym, hnSym, hSym⟩ := structural_proxy_symmetry_transfer B
  obtain ⟨nGap, hnGap, hGap⟩ := key_lemma_information_gaps B (max c0d c0r)
  let C := cPP + cDen + cDec + cSym + cRel + 1
  let n₀ := max nGap (max nDec nSym)
  refine ⟨C, n₀, by omega, le_trans hnGap (le_max_left _ _), ?_⟩
  intro n candidate x q hp
  have hpGap := KeyParameters.of_threshold_le B (le_max_left _ _) _ _ _ hp
  have hpDec := KeyParameters.of_threshold_le B
    (le_trans (le_max_left _ _) (le_max_right _ _)) _ _ _ hp
  have hpSym := KeyParameters.of_threshold_le B
    (le_trans (le_max_right _ _) (le_max_right _ _)) _ _ _ hp
  have gaps := hGap n candidate x q hpGap
  have decs := hDec n candidate x q hpDec
  have hd : (c0d : ENat) ≤ (max c0d c0r : ENat) :=
    WithTop.coe_le_coe.mpr (le_max_left _ _)
  constructor
  · intro hsimp
    obtain ⟨k, hk⟩ := prefix_complexity_finite_value B x (bits q)
    have hgap : (k : ENat) + c0d ≤ (extensionScale q : ENat) := by
      rw [← hk]
      exact (add_le_add le_rfl hd).trans gaps.plain
    have hPPx := hPP x q hsimp
    rw [hk] at hPPx
    have hk_nat : k ≤ q + cPP := by exact_mod_cast hPPx
    have hgap_nat : k + c0d ≤ extensionScale q := by exact_mod_cast hgap
    apply le_trans _ (hDen q x k hk hgap_nat).1
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  · have hcDec : cDec ≤ C := by omega
    obtain ⟨hU1, hU2⟩ := UpperVolumeDecomposition.mono B hcDec candidate x q decs.1
    refine ⟨hU2, le_trans ?_ hU1⟩
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_add_of_nonneg_left (by positivity)
  · intro k hk_proxy
    obtain ⟨k_upper, hk_upper⟩ :=
      prefix_complexity_finite_value B (upperFutureBase B n candidate x q) (bits q)
    have hgap : (k_upper : ENat) + c0d ≤ (extensionScale q : ENat) := by
      rw [← hk_upper]
      exact (add_le_add le_rfl hd).trans gaps.upper
    have hgap_nat : k_upper + c0d ≤ extensionScale q := by exact_mod_cast hgap
    have hDen_upper := hDen q (upperFutureBase B n candidate x q) k_upper hk_upper hgap_nat
    have hsym := hSym n hpSym.1 hp.2.1 candidate q hp.2.2.1 hp.2.2.2.1
      x k_upper k hk_upper hk_proxy
    obtain ⟨hsym_lower, hsym_upper⟩ := abs_le.mp hsym
    constructor
    · apply le_trans _ hDen_upper.1
      apply zpow_le_zpow_right₀ (by norm_num)
      dsimp [structuralProxyDelta]
      omega
    · apply le_trans hDen_upper.2
      apply zpow_le_zpow_right₀ (by norm_num)
      dsimp [structuralProxyDelta]
      omega
  · intro k hk_proxy
    obtain ⟨hL1, hL2⟩ := decs.2
    have hgap : (k : ENat) + c0d ≤ (extensionScale n : ENat) := by
      rw [← hk_proxy]
      exact (add_le_add le_rfl hd).trans gaps.lower
    have hgap_nat : k + c0d ≤ extensionScale n := by exact_mod_cast hgap
    have hDen_lower := hDen n (lowerProxyBase B n candidate x q) k hk_proxy hgap_nat
    let R := pastExtensionCount B n candidate n (lowerProxyBase B n candidate x q) +
      strictExtensionCount B n (triple x q candidate.1)
    have hpow : 0 < (2 : ℚ) ^ (cDec : ℤ) := by positivity
    have hleft : (2 : ℚ) ^ (-(cDec : ℤ)) *
        strictExtensionCount B n (lowerProxyBase B n candidate x q) ≤ R := by
      rw [zpow_neg, inv_mul_le_iff₀ hpow]
      exact hL2
    have hright : (R : ℚ) ≤ (2 : ℚ) ^ (cDec : ℤ) *
        strictExtensionCount B n (lowerProxyBase B n candidate x q) := by
      rwa [zpow_neg, inv_mul_le_iff₀ hpow] at hL1
    constructor
    · calc
        (2 : ℚ) ^ ((extensionScale n : ℤ) - k - C)
            ≤ (2 : ℚ) ^ (-(cDec : ℤ)) *
              (2 : ℚ) ^ ((extensionScale n : ℤ) - k - cDen) := by
          rw [← zpow_add₀ (by norm_num)]
          apply zpow_le_zpow_right₀ (by norm_num)
          omega
        _ ≤ (2 : ℚ) ^ (-(cDec : ℤ)) *
            strictExtensionCount B n (lowerProxyBase B n candidate x q) :=
          mul_le_mul_of_nonneg_left hDen_lower.1 (by positivity)
        _ ≤ R := hleft
    · calc
        (R : ℚ) ≤ (2 : ℚ) ^ (cDec : ℤ) *
            strictExtensionCount B n (lowerProxyBase B n candidate x q) := hright
        _ ≤ (2 : ℚ) ^ (cDec : ℤ) * (2 : ℚ) ^ ((extensionScale n : ℤ) - k + cDen) :=
          mul_le_mul_of_nonneg_left hDen_lower.2 (by positivity)
        _ ≤ (2 : ℚ) ^ ((extensionScale n : ℤ) - k + C) := by
          rw [← zpow_add₀ (by norm_num)]
          apply zpow_le_zpow_right₀ (by norm_num)
          omega
  · intro δ
    have hgap : KP B.D (triple x q candidate.1) (bits n) + c0r ≤
        (extensionScale n : ENat) := by
      have hr : (c0r : ENat) ≤ (max c0d c0r : ENat) :=
        WithTop.coe_le_coe.mpr (le_max_right _ _)
      exact (add_le_add le_rfl hr).trans gaps.marker
    apply le_trans (hRel n (triple x q candidate.1) hgap δ)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply zpow_le_zpow_right₀ (by norm_num)
    have hcRel : cRel ≤ C := by omega
    nlinarith

/-- The simple-string lower bound, exported separately from the common volume interface.
Blueprint node `key:volumes`. -/
theorem key_lemma_structural_volume_interface_simple (B : Base) :
    ∃ C n₀ : ℕ, 1 ≤ C ∧ 32 ≤ n₀ ∧
      ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
        KeyParameters B n₀ n candidate x q → Simple B.V x q →
        (2 : ℚ) ^ ((extensionScale q : ℤ) - q - C) ≤ strictExtensionCount B q x := by
  obtain ⟨C, n₀, hC, hn₀, h⟩ := key_lemma_structural_volume_interface B
  exact ⟨C, n₀, hC, hn₀, fun n candidate x q hp ↦ (h n candidate x q hp).simple⟩

/-- The two upper decomposition estimates, exported with the same existential constant.
Blueprint node `key:volumes`. -/
theorem key_lemma_structural_volume_interface_decomposition (B : Base) :
    ∃ C n₀ : ℕ, 1 ≤ C ∧ 32 ≤ n₀ ∧
      ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
        KeyParameters B n₀ n candidate x q →
        (strictExtensionCount B q x : ℚ) ≤ (2 : ℚ) ^ (C : ℤ) *
          (pastExtensionCount B n candidate q x +
            strictExtensionCount B q (upperFutureBase B n candidate x q)) ∧
        (2 : ℚ) ^ (-(C : ℤ)) *
          strictExtensionCount B q (upperFutureBase B n candidate x q) ≤
            strictExtensionCount B q x := by
  obtain ⟨C, n₀, hC, hn₀, h⟩ := key_lemma_structural_volume_interface B
  exact ⟨C, n₀, hC, hn₀, fun n candidate x q hp ↦ (h n candidate x q hp).decomposition⟩

/-- The upper future exponent estimate. Blueprint node `key:volumes`. -/
theorem key_lemma_structural_volume_interface_future (B : Base) :
    ∃ C n₀ : ℕ, 1 ≤ C ∧ 32 ≤ n₀ ∧
      ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
        KeyParameters B n₀ n candidate x q → ∀ k : ℕ,
        KP B.D (lowerProxyBase B n candidate x q) (bits n) = (k : ENat) →
        (2 : ℚ) ^ ((extensionScale q : ℤ) - structuralProxyDelta B n candidate q - k - C) ≤
          strictExtensionCount B q (upperFutureBase B n candidate x q) ∧
        (strictExtensionCount B q (upperFutureBase B n candidate x q) : ℚ) ≤
          (2 : ℚ) ^ ((extensionScale q : ℤ) - structuralProxyDelta B n candidate q - k + C) := by
  obtain ⟨C, n₀, hC, hn₀, h⟩ := key_lemma_structural_volume_interface B
  exact ⟨C, n₀, hC, hn₀, fun n candidate x q hp ↦ (h n candidate x q hp).future⟩

/-- The lower past-plus-marker exponent estimate. Blueprint node `key:volumes`. -/
theorem key_lemma_structural_volume_interface_remaining (B : Base) :
    ∃ C n₀ : ℕ, 1 ≤ C ∧ 32 ≤ n₀ ∧
      ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
        KeyParameters B n₀ n candidate x q → ∀ k : ℕ,
        KP B.D (lowerProxyBase B n candidate x q) (bits n) = (k : ENat) →
        let R := pastExtensionCount B n candidate n (lowerProxyBase B n candidate x q) +
          strictExtensionCount B n (triple x q candidate.1)
        (2 : ℚ) ^ ((extensionScale n : ℤ) - k - C) ≤ R ∧
          (R : ℚ) ≤ (2 : ℚ) ^ ((extensionScale n : ℤ) - k + C) := by
  obtain ⟨C, n₀, hC, hn₀, h⟩ := key_lemma_structural_volume_interface B
  exact ⟨C, n₀, hC, hn₀, fun n candidate x q hp ↦ (h n candidate x q hp).remaining⟩

/-- The relaxed marker-triple estimate. Blueprint node `key:volumes`. -/
theorem key_lemma_structural_volume_interface_relaxed (B : Base) :
    ∃ C n₀ : ℕ, 1 ≤ C ∧ 32 ≤ n₀ ∧
      ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
        KeyParameters B n₀ n candidate x q → ∀ δ : ℕ,
        (extensionCount B n δ (triple x q candidate.1) : ℚ) ≤
          (2 : ℚ) ^ ((C : ℤ) * (δ + 1)) * strictExtensionCount B n (triple x q candidate.1) := by
  obtain ⟨C, n₀, hC, hn₀, h⟩ := key_lemma_structural_volume_interface B
  exact ⟨C, n₀, hC, hn₀, fun n candidate x q hp ↦ (h n candidate x q hp).relaxed⟩

/-- The positive rational price before rounding, with a signed exponent.
Blueprint node `key:algorithm`. `lam` is computational input, not an existential choice. -/
def extensionPriceDyadic (B : Base) (lam n : ℕ) (candidate : Candidate) (q : ℕ) : ℚ :=
  (2 : ℚ) ^ ((extensionScale n : ℤ) - q + structuralProxyDelta B n candidate q - lam)

/-- The total extension price, using the two snapshot tests and the rational ceiling.
Blueprint node `key:algorithm`. Invalid records and scales below `n₀` return zero.
The explicit inputs `lam` and `n₀` are fixed uniformly in the correctness theorems. -/
def compute_extension_price (B : Base) (lam n₀ n : ℕ) (candidate : Candidate)
    (x : BitString) (q : ℕ) : ℕ :=
  if validCandidate B n candidate then
    if n < n₀ then 0
    else if (2 : ℚ) ^ ((extensionScale q : ℤ) - q - lam) ≤
        (pastExtensionCount B n candidate q x : ℚ) then 0
    else
      let z := extensionPriceDyadic B lam n candidate q
      if z ≤ (pastExtensionCount B n candidate n (lowerProxyBase B n candidate x q) : ℚ)
      then 0 else ⌈z⌉₊
  else 0

/-- Encodable input data for a total candidate-price algorithm. Blueprint node `key:algorithm`. -/
abbrev CandidatePriceInput := ℕ × Candidate × BitString × ℕ

/-- A total natural-valued algorithm on explicitly timestamped candidates.
Blueprint node `key:algorithm`. Computability is an additional theorem, not a field. -/
abbrev CandidatePrice := CandidatePriceInput → ℕ

/-- The tuple-input version of the explicit price algorithm.
Blueprint node `key:algorithm`. This is the algorithm existentially exhibited in correctness. -/
def extensionPriceAlgorithm (B : Base) (lam n₀ : ℕ) : CandidatePrice :=
  fun p ↦ compute_extension_price B lam n₀ p.1 p.2.1 p.2.2.1 p.2.2.2

/-- Powers of two with signed exponents are computable rationals. -/
private lemma rat_two_zpow_computable :
    Computable (fun e : ℤ ↦ (2 : ℚ) ^ e) := by
  have hpos : Computable (fun e : ℤ ↦ 2 ^ e.toNat) :=
    primrec_two_pow_aux.to_comp.comp ComputableReals.primrec_intToNat.to_comp
  have hneg : Computable (fun e : ℤ ↦ 2 ^ (-e).toNat) :=
    primrec_two_pow_aux.to_comp.comp ComputableReals.primrec_intNegToNat.to_comp
  refine computable_of_num_den
    (N := fun e : ℤ ↦ ((2 ^ e.toNat : ℕ) : ℤ))
    (D := fun e : ℤ ↦ 2 ^ (-e).toNat)
    (ComputableReals.primrec_natCastInt.to_comp.comp hpos) hneg
    (fun e ↦ pow_pos (by decide) _) (fun e ↦ ?_)
  cases e with
  | ofNat n => simp
  | negSucc n => simp [zpow_negSucc, Int.neg_negSucc]

/-- The first snapshot threshold is computable in its loss and scale. -/
private lemma price_threshold_computable :
    Computable (fun p : ℕ × ℕ ↦
      (2 : ℚ) ^ ((extensionScale p.2 : ℤ) - p.2 - p.1)) := by
  have hs : Computable (fun p : ℕ × ℕ ↦ (extensionScale p.2 : ℤ)) :=
    ComputableReals.primrec_natCastInt.to_comp.comp
      (primrec_two_pow_aux.to_comp.comp Computable.snd)
  have hq : Computable (fun p : ℕ × ℕ ↦ (p.2 : ℤ)) :=
    ComputableReals.primrec_natCastInt.to_comp.comp Computable.snd
  have hl : Computable (fun p : ℕ × ℕ ↦ (p.1 : ℤ)) :=
    ComputableReals.primrec_natCastInt.to_comp.comp Computable.fst
  exact rat_two_zpow_computable.comp
    (Computable₂.comp primrec_intSub.to_comp
      (Computable₂.comp primrec_intSub.to_comp hs hq) hl)

/-- The lower snapshot price is computable from the bounded proxy correction. -/
private lemma extensionPriceDyadic_computable (B : Base) :
    Computable (fun p : ℕ × ℕ × Candidate × ℕ ↦
      extensionPriceDyadic B p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hs : Computable (fun p : ℕ × ℕ × Candidate × ℕ ↦
      (extensionScale p.2.1 : ℤ)) :=
    ComputableReals.primrec_natCastInt.to_comp.comp
      (primrec_two_pow_aux.to_comp.comp (Computable.fst.comp Computable.snd))
  have hq : Computable (fun p : ℕ × ℕ × Candidate × ℕ ↦ (p.2.2.2 : ℤ)) :=
    ComputableReals.primrec_natCastInt.to_comp.comp
      (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hl : Computable (fun p : ℕ × ℕ × Candidate × ℕ ↦ (p.1 : ℤ)) :=
    ComputableReals.primrec_natCastInt.to_comp.comp Computable.fst
  have hd : Computable (fun p : ℕ × ℕ × Candidate × ℕ ↦
      structuralProxyDelta B p.2.1 p.2.2.1 p.2.2.2) :=
    (compute_structural_proxy B).2.2.2.comp Computable.snd
  exact rat_two_zpow_computable.comp
    (Computable₂.comp primrec_intSub.to_comp
      (Computable₂.comp ComputableReals.primrec_intAdd.to_comp
        (Computable₂.comp primrec_intSub.to_comp hs hq) hd) hl)

/-- Price computation is uniform even in its explicit loss and threshold constants.
Blueprint node `key:algorithm`. There is no call to exact complexity or an unbounded search. -/
theorem compute_extension_price_computable (B : Base) :
    Computable (fun p : ℕ × ℕ × CandidatePriceInput =>
      extensionPriceAlgorithm B p.1 p.2.1 p.2.2) := by
  let lam : ℕ × ℕ × CandidatePriceInput → ℕ := fun p ↦ p.1
  let n₀ : ℕ × ℕ × CandidatePriceInput → ℕ := fun p ↦ p.2.1
  let n : ℕ × ℕ × CandidatePriceInput → ℕ := fun p ↦ p.2.2.1
  let candidate : ℕ × ℕ × CandidatePriceInput → Candidate := fun p ↦ p.2.2.2.1
  let x : ℕ × ℕ × CandidatePriceInput → BitString := fun p ↦ p.2.2.2.2.1
  let q : ℕ × ℕ × CandidatePriceInput → ℕ := fun p ↦ p.2.2.2.2.2
  have hlam : Computable lam := Computable.fst
  have hn₀ : Computable n₀ := Computable.fst.comp Computable.snd
  have hn : Computable n := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hc : Computable candidate :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hx : Computable x :=
    Computable.fst.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hq : Computable q :=
    Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hvalid := (canonical_enumeration_spec_prefix_computable B).1.comp hn hc
  have hsmall := Computable₂.comp (f := fun a b : ℕ ↦ decide (a < b))
      Primrec.nat_lt.decide.to_comp hn hn₀
  have hpast := (past_extension_count_computable B).comp (hn.pair (hc.pair (hq.pair hx)))
  have hthreshold := price_threshold_computable.comp (hlam.pair hq)
  have hfirst := Computable₂.comp ComputableReals.primrec_ratLe.decide.to_comp
      hthreshold (ComputableReals.computable_natCastRat.comp hpast)
  have hdyadic := (extensionPriceDyadic_computable B).comp
      (hlam.pair (hn.pair (hc.pair hq)))
  have hproxy := (compute_structural_proxy B).1.comp (hn.pair (hc.pair hq))
  have hbase := Computable₂.comp pairCode_computable hproxy hx
  have hlower := (past_extension_count_computable B).comp (hn.pair (hc.pair (hn.pair hbase)))
  have hsecond := Computable₂.comp ComputableReals.primrec_ratLe.decide.to_comp
      hdyadic (ComputableReals.computable_natCastRat.comp hlower)
  have hceil := primrec_rat_natCeil.to_comp.comp hdyadic
  have hresult := Computable.cond hvalid
    (Computable.cond hsmall (Computable.const 0)
      (Computable.cond hfirst (Computable.const 0)
        (Computable.cond hsecond (Computable.const 0) hceil))) (Computable.const 0)
  exact hresult.of_eq (fun p ↦ by
    simp only [Bool.cond_eq_ite, decide_eq_true_eq]
    rfl)

/-- The unrounded dyadic is strictly positive even when its exponent is negative.
Blueprint node `key:algorithm`. -/
theorem extension_price_dyadic_pos (B : Base) (lam n : ℕ) (candidate : Candidate) (q : ℕ) :
    0 < extensionPriceDyadic B lam n candidate q := by
  unfold extensionPriceDyadic
  positivity

/-- Malformed candidate records always receive the default price.
Blueprint node `key:algorithm`. -/
theorem compute_extension_price_invalid (B : Base) (lam n₀ n : ℕ) (candidate : Candidate)
    (x : BitString) (q : ℕ) (hc : validCandidate B n candidate = false) :
    compute_extension_price B lam n₀ n candidate x q = 0 := by
  simp [compute_extension_price, hc]

/-- Valid candidates below the fixed correctness threshold also receive the default price.
Blueprint node `key:algorithm`. -/
theorem compute_extension_price_small (B : Base) (lam n₀ n : ℕ) (candidate : Candidate)
    (x : BitString) (q : ℕ) (hn : n < n₀) :
    compute_extension_price B lam n₀ n candidate x q = 0 := by
  simp [compute_extension_price, hn]

/-- Constants for the price use the same `C` as all five structural volume estimates.
Blueprint node `key:algorithm`. This proposition does not choose any computational input. -/
def ExtensionPriceConstants (B : Base) (C lam n₀ : ℕ) : Prop :=
  1 ≤ C ∧ lam = 6 * C + 4 ∧ 32 ≤ n₀ ∧
    ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
      KeyParameters B n₀ n candidate x q → StructuralVolumeBounds B C n candidate x q

/-- The simple-string lower bound and the first failed test force a lower bound on the future
volume. Blueprint node `key:complete`. -/
private lemma future_volume_lower_of_small_past
    (Q q : ℤ) (C : ℕ) (P F V : ℚ)
    (hs : (2 : ℚ) ^ (Q - q - C) ≤ V)
    (hdec : V ≤ (2 : ℚ) ^ (C : ℤ) * (P + F))
    (hfirst : P < (2 : ℚ) ^ (Q - q - (6 * C + 4))) :
    (2 : ℚ) ^ (Q - q - 2 * C - 1) ≤ F := by
  have hsum : (2 : ℚ) ^ (Q - q - 2 * C) ≤ P + F := by
    apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℚ) < 2 ^ (C : ℤ))).mp
    calc
      (2 : ℚ) ^ (C : ℤ) * 2 ^ (Q - q - 2 * C) = 2 ^ (Q - q - C) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        congr 1
        ring
      _ ≤ V := hs
      _ ≤ (2 : ℚ) ^ (C : ℤ) * (P + F) := hdec
  have hsmall : (2 : ℚ) ^ (Q - q - (6 * C + 4)) ≤ 2 ^ (Q - q - 2 * C - 1) := by
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  have hdouble : (2 : ℚ) ^ (Q - q - 2 * C) =
      2 * 2 ^ (Q - q - 2 * C - 1) := by
    calc
      (2 : ℚ) ^ (Q - q - 2 * C) = 2 ^ (1 + (Q - q - 2 * C - 1)) := by
        congr 1
        ring
      _ = _ := zpow_one_add₀ (by norm_num : (2 : ℚ) ≠ 0) _
  rw [hdouble] at hsum
  linarith [hfirst.trans_le hsmall]

/-- Comparing lower and upper bounds on the future volume gives a complexity bound.
Blueprint node `key:complete`. -/
private lemma complexity_bound_of_future_volume_bounds
    (Q q d C k : ℤ) (F : ℚ)
    (hlower : (2 : ℚ) ^ (Q - q - 2 * C - 1) ≤ F)
    (hupper : F ≤ (2 : ℚ) ^ (Q - d - k + C)) :
    k ≤ q - d + 3 * C + 1 := by
  have := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mp
    (hlower.trans hupper)
  omega

/-- The complexity bound and the remaining-volume lower bound make that volume at least
twice the price. Blueprint node `key:complete`. -/
private lemma remaining_volume_ge_twice_price
    (N q d : ℤ) (C : ℕ) (k : ℤ) (R : ℚ)
    (hk : k ≤ q - d + 3 * C + 1)
    (hremaining : (2 : ℚ) ^ (N - k - C) ≤ R) :
    2 * (2 : ℚ) ^ (N - q + d - (6 * C + 4)) ≤ R := by
  calc
    2 * (2 : ℚ) ^ (N - q + d - (6 * C + 4)) = 2 ^ (1 + (N - q + d - (6 * C + 4))) :=
      (zpow_one_add₀ (by norm_num : (2 : ℚ) ≠ 0) _).symm
    _ ≤ (2 : ℚ) ^ (N - k - C) := by
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    _ ≤ R := hremaining

/-- A total price with uniform constants is complete for strict extension counts.
Blueprint node `key:complete`. The algorithm and both computational constants are existential. -/
theorem extension_price_complete (B : Base) :
    ∃ (C lam n₀ : ℕ) (A : CandidatePrice), ExtensionPriceConstants B C lam n₀ ∧
      A = extensionPriceAlgorithm B lam n₀ ∧ Computable A ∧
      ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
        KeyParameters B n₀ n candidate x q → Simple B.V x q →
        A (n, candidate, x, q) ≤ strictExtensionCount B n (triple x q candidate.1) := by
  obtain ⟨C, n₀, hC, hn₀, hvol⟩ := key_lemma_structural_volume_interface B
  refine ⟨C, 6 * C + 4, n₀, extensionPriceAlgorithm B (6 * C + 4) n₀,
    ⟨hC, rfl, hn₀, hvol⟩, rfl, ?_, ?_⟩
  · have hcomp := @Computable.comp _ _ _ _ _ _
      (fun p : ℕ × ℕ × CandidatePriceInput ↦ extensionPriceAlgorithm B p.1 p.2.1 p.2.2)
      (fun p : CandidatePriceInput ↦ (6 * C + 4, n₀, p))
      (compute_extension_price_computable B)
      (Computable.pair (Computable.const (6 * C + 4))
        (Computable.pair (Computable.const n₀) Computable.id))
    exact hcomp
  · intro n candidate x q hp hs
    change compute_extension_price B (6 * C + 4) n₀ n candidate x q ≤ _
    unfold compute_extension_price
    dsimp only
    split_ifs with hvalid hsmall hfirst hsecond
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · apply Nat.ceil_le.mpr
      have hV := hvol n candidate x q hp
      obtain ⟨k, hk⟩ := prefix_complexity_finite_value B
        (lowerProxyBase B n candidate x q) (bits n)
      have hF := future_volume_lower_of_small_past
        (extensionScale q) q C
        (pastExtensionCount B n candidate q x)
        (strictExtensionCount B q (upperFutureBase B n candidate x q))
        (strictExtensionCount B q x)
        (hV.simple hs) hV.decomposition.1
        (by push_cast at hfirst; exact lt_of_not_ge hfirst)
      have hK := complexity_bound_of_future_volume_bounds
        (extensionScale q) q (structuralProxyDelta B n candidate q) C k
        (strictExtensionCount B q (upperFutureBase B n candidate x q))
        hF (hV.future k hk).2
      have hR := remaining_volume_ge_twice_price
        (extensionScale n) q (structuralProxyDelta B n candidate q) C k
        ((pastExtensionCount B n candidate n (lowerProxyBase B n candidate x q) +
          strictExtensionCount B n (triple x q candidate.1) : ℕ) : ℚ)
        hK (hV.remaining k hk).1
      push_cast at hR
      change 2 * extensionPriceDyadic B (6 * C + 4) n candidate q ≤ _ at hR
      have hP := lt_of_not_ge hsecond
      linarith only [hR, hP]
    · exact Nat.zero_le _

/-- Prefix complexity within `q+t` yields plain complexity with the exact prefix cost of `t`.
Blueprint node `key:slack`. The unconditional natural uses `bits t` and the empty condition. -/
theorem plain_complexity_of_prefix_bound_with_slack (B : Base) :
    ∃ cSlack : ℕ, ∀ (x : BitString) (q t : ℕ), KP B.D x (bits q) ≤ (q + t : ℕ) →
      plainK B.V x ≤ (q + t : ℕ) + KP B.D (bits t) [] + cSlack := by
  -- The first field supplies `t`; the raw suffix is the integer code of the
  -- unused budget followed by the conditional prefix program.
  let args : BitString × BitString → BitString × BitString := fun ar ↦
    let p := decodeSecond ar.2
    let e := (decodeNat (decodeFirst ar.2)).getD 0
    let t := (decodeNat ar.1).getD 0
    (p, bits (p.length + e - t))
  have hargs : Computable args := by
    have hp : Computable (fun ar : BitString × BitString ↦ decodeSecond ar.2) :=
      decodeSecond_computable.comp Computable.snd
    have he : Computable (fun ar : BitString × BitString ↦
        (decodeNat (decodeFirst ar.2)).getD 0) :=
      Computable.option_getD
        (bits_computable.2.comp (decodeFirst_computable.comp Computable.snd))
        (Computable.const 0)
    have ht : Computable (fun ar : BitString × BitString ↦
        (decodeNat ar.1).getD 0) :=
      Computable.option_getD (bits_computable.2.comp Computable.fst)
        (Computable.const 0)
    have hq : Computable (fun ar : BitString × BitString ↦
        (decodeSecond ar.2).length + (decodeNat (decodeFirst ar.2)).getD 0 -
          (decodeNat ar.1).getD 0) :=
      Primrec.nat_sub.to_comp.comp
        (Primrec.nat_add.to_comp.comp (Computable.list_length.comp hp) he) ht
    exact hp.pair (bits_computable.1.comp hq)
  let f : BitString × BitString →. BitString := fun ar ↦ B.D (args ar)
  have hf : Partrec f := B.optimalD.isDecompressor.comp hargs
  obtain ⟨c, hc⟩ := plain_prefix_program_raw_suffix B f hf
  refine ⟨c + 6, fun x q t hqt ↦ ?_⟩
  have hfinite : KP B.D x (bits q) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hqt
  obtain ⟨p, hp, hp_len⟩ := exists_program_of_KP_ne_top hfinite
  have hplen : p.length ≤ q + t := by
    apply ENat.natCast_le_natCast.mp
    rw [hp_len]
    exact hqt
  let e := q + t - p.length
  have hq : p.length + e - t = q := by dsimp [e]; omega
  have hx : x ∈ f (bits t, pairCode (bits e) p) := by
    dsimp [f, args]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode, decodeNat_bits,
      Option.getD_some]
    rw [hq]
    exact hp
  have hlen : (pairCode (bits e) p).length ≤ q + t + 6 := by
    have hcode :=
      length_pairCode_bits_le e p
    exact hcode.trans (by dsimp [e]; omega)
  calc
    plainK B.V x ≤ KPPlain B.D (bits t) +
        ((pairCode (bits e) p).length : ENat) + c := hc _ _ _ hx
    _ ≤ KPPlain B.D (bits t) + ((q + t + 6 : ℕ) : ENat) + c := by gcongr
    _ = (q + t : ℕ) + KP B.D (bits t) [] + (c + 6 : ℕ) := by
      simp only [KPPlain_eq_KP, Nat.cast_add]
      ac_rfl

/-- The slack expression is bounded by a uniform multiple of `t+1` beyond `q`.
Blueprint node `key:slack`. The coefficient is chosen after the fixed additive overhead. -/
theorem plain_complexity_of_prefix_bound_with_slack_bound (B : Base) (cSlack : ℕ) :
    ∃ cLinear : ℕ, ∀ q t : ℕ,
      (q + t : ℕ) + KP B.D (bits t) [] + cSlack ≤ (q + cLinear * (t + 1) : ℕ) := by
  obtain ⟨c, hc⟩ := literal_and_tuple_code_interface_integer B
  use c + cSlack + 4
  intro q t
  have hc_t := hc t
  rw [KPPlain_eq_KP, integerLiteralBound] at hc_t
  have hlog : Nat.clog 2 (t + 2) ≤ t + 2 := by
    apply (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).2
    exact (Nat.lt_two_pow_self : t + 2 < 2 ^ (t + 2)).le
  have hKP : KP B.D (bits t) [] ≤ (2 * (t + 2) + c : ℕ) := by
    calc
      KP B.D (bits t) [] ≤ (2 * Nat.clog 2 (t + 2) + c : ℕ) := hc_t
      _ ≤ (2 * (t + 2) + c : ℕ) := by
        exact ENat.natCast_le_natCast.mpr (by nlinarith)
  have h1 : KP B.D (bits t) [] + (cSlack : ENat) ≤
      ((2 * (t + 2) + c : ℕ) : ENat) + (cSlack : ENat) := by
    gcongr
  have h2 : ((q + t : ℕ) : ENat) + KP B.D (bits t) [] + cSlack =
      ((q + t : ℕ) : ENat) + (KP B.D (bits t) [] + cSlack) := by
    exact add_assoc _ _ _
  rw [h2]
  calc
    ((q + t : ℕ) : ENat) + (KP B.D (bits t) [] + cSlack)
      ≤ ((q + t : ℕ) : ENat) + (((2 * (t + 2) + c : ℕ) : ENat) + (cSlack : ENat)) := by
        gcongr
    _ = (((q + t : ℕ) : ENat) + ((2 * (t + 2) + c : ℕ) : ENat)) + (cSlack : ENat) := by
        exact (add_assoc _ _ _).symm
    _ = (((q + t : ℕ) + (2 * (t + 2) + c : ℕ) : ℕ) : ENat) + (cSlack : ENat) := by
        push_cast
        rfl
    _ = (((q + t : ℕ) + (2 * (t + 2) + c : ℕ) + cSlack : ℕ) : ENat) := by
        push_cast
        rfl
    _ ≤ (q + (c + cSlack + 4) * (t + 1) : ℕ) := by
        have hzero_le_t : 0 ≤ t := Nat.zero_le t
        exact ENat.natCast_le_natCast.mpr (by nlinarith)

/-- Prefix-to-plain conversion with a fully natural linear slack bound.
Blueprint node `key:slack`. No term depends logarithmically on the target or tower. -/
theorem plain_complexity_of_prefix_bound_with_slack_linear (B : Base) :
    ∃ cLinear : ℕ, ∀ (x : BitString) (q t : ℕ), KP B.D x (bits q) ≤ (q + t : ℕ) →
      Simple B.V x (q + cLinear * (t + 1)) := by
  obtain ⟨cSlack, hs⟩ := plain_complexity_of_prefix_bound_with_slack B
  obtain ⟨cLinear, hl⟩ := plain_complexity_of_prefix_bound_with_slack_bound B cSlack
  exact ⟨cLinear, fun x q t h ↦ (hs x q t h).trans (hl q t)⟩

/-- Strict completeness and uniform integer-slack soundness for one price algorithm.
Blueprint node `key:main`. Natural `δ` represents precisely the nonnegative integer relaxations. -/
def ExtensionPriceSpec (B : Base) (A : CandidatePrice) (cGap n₀ : ℕ) : Prop :=
  ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
    KeyParameters B n₀ n candidate x q →
    (Simple B.V x q → A (n, candidate, x, q) ≤
      strictExtensionCount B n (triple x q candidate.1)) ∧
    (∀ δ : ℕ, A (n, candidate, x, q) ≤ extensionCount B n δ (triple x q candidate.1) →
      Simple B.V x (q + cGap * (δ + 1)))

/-- Branches 2 and 3 of the price: a bound `z ≤ 2^t * R` for the dyadic price `z` and the
lower-scale volume `R` gives `KP(x | q) ≤ q + (lam + 3 * C + t) + cDen`;
`hinv` inverts the density at `x`. -/
private lemma complexity_bound_of_dyadic_price_le (B : Base) (C lam cDen : ℕ)
    (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ)
    (hvol : StructuralVolumeBounds B C n candidate x q) (k : ℕ)
    (hinv : ∀ m : ℕ, (2 : ℚ) ^ ((extensionScale q : ℤ) - q - m) ≤ strictExtensionCount B q x →
      k ≤ q + m + cDen)
    (t : ℕ)
    (hz : extensionPriceDyadic B lam n candidate q ≤ (2 : ℚ) ^ (t : ℤ) *
      ((pastExtensionCount B n candidate n (lowerProxyBase B n candidate x q) +
        strictExtensionCount B n (triple x q candidate.1) : ℕ) : ℚ)) :
    k ≤ q + (lam + 3 * C + t) + cDen := by
  apply hinv (lam + 3 * C + t)
  obtain ⟨m, hm⟩ := prefix_complexity_finite_value B (lowerProxyBase B n candidate x q) (bits n)
  have hrem := hvol.remaining m hm
  have hfut := hvol.future m hm
  have h1 : extensionPriceDyadic B lam n candidate q ≤
      (2 : ℚ) ^ ((t : ℤ) + ((extensionScale n : ℤ) - m + C)) := by
    rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    exact hz.trans (by gcongr; exact hrem.2)
  unfold extensionPriceDyadic at h1
  have h2 := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mp h1
  have h3 : (2 : ℚ) ^ (-(C : ℤ)) * (2 : ℚ) ^ ((extensionScale q : ℤ) -
      structuralProxyDelta B n candidate q - m - C) ≤ strictExtensionCount B q x :=
    le_trans (by gcongr; exact hfut.1) hvol.decomposition.2
  refine le_trans ?_ h3
  rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  apply zpow_le_zpow_right₀ (by norm_num)
  push_cast
  omega

/-- Soundness of the price at a large valid marker: the three branches of
`compute_extension_price`. -/
private lemma complexity_bound_of_price_le (B : Base) (C lam n₀ cDen : ℕ)
    (hvol : ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
      KeyParameters B n₀ n candidate x q → StructuralVolumeBounds B C n candidate x q)
    (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ)
    (hp : KeyParameters B n₀ n candidate x q) (hvalid : validCandidate B n candidate = true)
    (k : ℕ)
    (hinv : ∀ m : ℕ, (2 : ℚ) ^ ((extensionScale q : ℤ) - q - m) ≤ strictExtensionCount B q x →
      k ≤ q + m + cDen)
    (δ : ℕ)
    (hprem : compute_extension_price B lam n₀ n candidate x q ≤
      extensionCount B n δ (triple x q candidate.1)) :
    k ≤ q + (lam + 3 * C + C * (δ + 1)) + cDen := by
  have hV := hvol n candidate x q hp
  have hn : ¬ n < n₀ := by have := hp.1; omega
  unfold compute_extension_price at hprem
  simp only [hvalid, hn, ↓reduceIte] at hprem
  have hpast : (0 : ℚ) ≤ pastExtensionCount B n candidate n (lowerProxyBase B n candidate x q) :=
    Nat.cast_nonneg _
  by_cases h1 : (2 : ℚ) ^ ((extensionScale q : ℤ) - q - lam) ≤
      (pastExtensionCount B n candidate q x : ℚ)
  · have hP := past_extension_count_le_strict
      B n candidate q x
    have := hinv lam (h1.trans (by exact_mod_cast hP))
    omega
  · simp only [h1, ↓reduceIte] at hprem
    by_cases h2 : extensionPriceDyadic B lam n candidate q ≤
        (pastExtensionCount B n candidate n (lowerProxyBase B n candidate x q) : ℚ)
    · have := complexity_bound_of_dyadic_price_le B C lam cDen n candidate x q hV k hinv 0
        (h2.trans (by push_cast; simp))
      omega
    · simp only [h2, ↓reduceIte] at hprem
      have hz2 := ((Nat.le_ceil _).trans (by exact_mod_cast hprem)).trans (hV.relaxed δ)
      refine complexity_bound_of_dyadic_price_le B C lam cDen n candidate x q hV k hinv
        (C * (δ + 1)) (hz2.trans ?_)
      push_cast
      gcongr
      linarith

/-- Uniform soundness follows from the branch estimates above the density and marker
thresholds, and from the literal length bound at the finitely many smaller scales. -/
private lemma exists_uniform_price_soundness (B : Base) (C lam n₀ : ℕ)
    (A : CandidatePrice) (hc : ExtensionPriceConstants B C lam n₀)
    (ha : A = extensionPriceAlgorithm B lam n₀) :
    ∃ cGap : ℕ, ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
      KeyParameters B n₀ n candidate x q → ∀ δ : ℕ,
      A (n, candidate, x, q) ≤ extensionCount B n δ (triple x q candidate.1) →
      Simple B.V x (q + cGap * (δ + 1)) := by
  obtain ⟨-, -, -, hvol⟩ := hc
  obtain ⟨c0, cDen, hDen⟩ := extension_density B
  obtain ⟨n1, -, hgapK⟩ := key_lemma_information_gaps_plain B c0
  obtain ⟨n2, -, hmark⟩ := last_program_stabilizes_short_descriptions B
  obtain ⟨cSl, hSl⟩ := plain_complexity_of_prefix_bound_with_slack_linear B
  obtain ⟨cLen, hLen⟩ := plainK_le_length B.V B.optimalV
  -- below `N` the marker may be invalid or the density gap may fail: use the length bound
  set N := max n₀ (max n1 n2) with hN
  refine ⟨max (cSl * (lam + 3 * C + cDen + C + 1)) (N ^ N + cLen), ?_⟩
  intro n candidate x q hp δ hprem
  subst ha
  by_cases hbig : N ≤ n
  · have hp1 : KeyParameters B n1 n candidate x q :=
      ⟨by omega, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩
    have hvalid : validCandidate B n candidate = true := by
      rw [hp.2.2.1]
      exact (hmark n (by omega)).1
    obtain ⟨k, hk⟩ := prefix_complexity_finite_value B x (bits q)
    have hgap : k + c0 ≤ extensionScale q := by
      have := hgapK n candidate x q hp1
      rw [hk] at this
      exact_mod_cast this
    have hinv : ∀ m : ℕ, (2 : ℚ) ^ ((extensionScale q : ℤ) - q - m) ≤
        strictExtensionCount B q x → k ≤ q + m + cDen := fun m h ↦ by
      have := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mp
        (h.trans (hDen q x k hk hgap).2)
      omega
    have hmain := complexity_bound_of_price_le B C lam n₀ cDen hvol n candidate x q
      hp hvalid k hinv δ hprem
    refine simple_mono B.V x ?_ (hSl x q (lam + 3 * C + C * (δ + 1) + cDen) (by
      rw [hk]
      exact_mod_cast (by omega : k ≤ q + (lam + 3 * C + C * (δ + 1) + cDen))))
    have h5 : lam + 3 * C + C * (δ + 1) + cDen + 1 ≤
        (lam + 3 * C + cDen + C + 1) * (δ + 1) := by
      nlinarith
    have h6 : cSl * (lam + 3 * C + C * (δ + 1) + cDen + 1) ≤
        cSl * (lam + 3 * C + cDen + C + 1) * (δ + 1) := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ h5
    have h7 := Nat.mul_le_mul_right (δ + 1)
      (le_max_left (cSl * (lam + 3 * C + cDen + C + 1)) (N ^ N + cLen))
    omega
  · have hnN : n < N := lt_of_not_ge hbig
    have hpow : towerRangeBound n ≤ N ^ N := by
      unfold towerRangeBound
      calc n ^ Nat.log2 n ≤ N ^ Nat.log2 n := Nat.pow_le_pow_left hnN.le _
        _ ≤ N ^ N := Nat.pow_le_pow_right (by omega) ((Nat.log2_le_self n).trans hnN.le)
    have h8 : N ^ N + cLen ≤
        max (cSl * (lam + 3 * C + cDen + C + 1)) (N ^ N + cLen) * (δ + 1) :=
      (le_max_right _ _).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos δ))
    refine (hLen x).trans ?_
    have := hp.2.2.2.2
    change ((x.length : ℕ) : ENat) + cLen ≤ _
    exact_mod_cast (by omega : x.length + cLen ≤ q + _)

/-- The uniform integer-slack Key Lemma for the explicitly defined total price algorithm.
Blueprint node `key:main`. The common volume constant, `lam = 6C+4`, and `n₀ ≥ 32`
are fixed before all input parameters and before any later padding parameter. -/
theorem extension_price_sound_complete (B : Base) :
    ∃ (C lam n₀ cGap : ℕ) (A : CandidatePrice), ExtensionPriceConstants B C lam n₀ ∧
      A = extensionPriceAlgorithm B lam n₀ ∧ Computable A ∧ ExtensionPriceSpec B A cGap n₀ := by
  obtain ⟨C, lam, n₀, A, hc, ha, hcomp, hs⟩ := extension_price_complete B
  obtain ⟨cGap, hg⟩ := exists_uniform_price_soundness B C lam n₀ A hc ha
  exact ⟨C, lam, n₀, cGap, A, hc, ha, hcomp,
    fun n candidate x q hp ↦ ⟨hs n candidate x q hp, hg n candidate x q hp⟩⟩

/-- The strict-completeness part of the same total algorithm's joint specification.
Blueprint node `key:main`. The joint theorem retains the shared constants for both directions. -/
theorem extension_price_sound_complete_strict (B : Base) :
    ∃ (C lam n₀ : ℕ) (A : CandidatePrice), ExtensionPriceConstants B C lam n₀ ∧
      A = extensionPriceAlgorithm B lam n₀ ∧ Computable A ∧
      ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
        KeyParameters B n₀ n candidate x q → Simple B.V x q →
        A (n, candidate, x, q) ≤ strictExtensionCount B n (triple x q candidate.1) := by
  obtain ⟨C, lam, n₀, cGap, A, hc, ha, hcomp, h⟩ := extension_price_sound_complete B
  exact ⟨C, lam, n₀, A, hc, ha, hcomp, fun n candidate x q hp ↦ (h n candidate x q hp).1⟩

/-- The soundness part of the same total algorithm, uniformly for every natural relaxation.
Blueprint node `key:main`. The premise includes zero prices without a positivity assumption. -/
theorem extension_price_sound_complete_sound (B : Base) :
    ∃ (C lam n₀ cGap : ℕ) (A : CandidatePrice), ExtensionPriceConstants B C lam n₀ ∧
      A = extensionPriceAlgorithm B lam n₀ ∧ Computable A ∧
      ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
        KeyParameters B n₀ n candidate x q → ∀ δ : ℕ,
        A (n, candidate, x, q) ≤ extensionCount B n δ (triple x q candidate.1) →
        Simple B.V x (q + cGap * (δ + 1)) := by
  obtain ⟨C, lam, n₀, cGap, A, hc, ha, hcomp, h⟩ := extension_price_sound_complete B
  exact ⟨C, lam, n₀, cGap, A, hc, ha, hcomp,
    fun n candidate x q hp ↦ (h n candidate x q hp).2⟩

/-- A fixed integer-slack coefficient is eventually absorbed by half of an even padding.
Blueprint node `key:sqrt`. `Nat.sqrt` is the floor square root. -/
theorem extension_price_square_root_slack (cGap : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, Even d → cGap * (Nat.sqrt d + 1) ≤ d / 2 := by
  refine ⟨(2 * cGap + 1) ^ 2, ?_⟩
  intro d hd _
  have hr : 2 * cGap + 1 ≤ Nat.sqrt d := Nat.le_sqrt'.2 hd
  have hm := Nat.mul_le_mul_right (Nat.sqrt d + 1) hr
  have hs := Nat.sqrt_le d
  have hbound : 2 * (cGap * (Nat.sqrt d + 1)) ≤ d := by nlinarith
  omega

/-- The manuscript's square-root soundness for the same total candidate-price algorithm.
Blueprint node `key:sqrt`. Its constants, including `d₀`, precede all even padding parameters;
the joint integer-slack specification remains available for this chosen algorithm. -/
theorem extension_price_square_root_soundness (B : Base) :
    ∃ (C lam n₀ cGap d₀ : ℕ) (A : CandidatePrice), ExtensionPriceConstants B C lam n₀ ∧
      A = extensionPriceAlgorithm B lam n₀ ∧ Computable A ∧ ExtensionPriceSpec B A cGap n₀ ∧
      ∀ d ≥ d₀, Even d → ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
        KeyParameters B n₀ n candidate x q →
        A (n, candidate, x, q) ≤ extensionCount B n (Nat.sqrt d) (triple x q candidate.1) →
        Simple B.V x (q + d / 2) := by
  obtain ⟨C, lam, n₀, cGap, A, hc, ha, hcomp, hspec⟩ := extension_price_sound_complete B
  obtain ⟨d₀, hd₀⟩ := extension_price_square_root_slack cGap
  refine ⟨C, lam, n₀, cGap, d₀, A, hc, ha, hcomp, hspec, ?_⟩
  intro d hd he n candidate x q hp hcount
  exact simple_mono B.V x (Nat.add_le_add_left (hd₀ d hd he) q)
    ((hspec n candidate x q hp).2 (Nat.sqrt d) hcount)

end Kolmogorov.Milovanov
