/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.LowerSemicomputable.Theorem181

/-!
# Randomness Tests

Characterisations of Martin-Löf randomness with respect to a computable measure `π` through
lower semicomputable martingales, following Theorem 181 of the book by Shen, Uspensky and
Vereshchagin.

Main declarations:
* `exists_lsc_stronglyWins_of_wins`: winning can be strengthened to strong winning while keeping
  lower semicomputability;
* `isMartinLofRandom_iff_forall_lsc_not_wins`: a sequence is Martin-Löf random exactly when no
  lower semicomputable `π`-martingale wins on it;
* the universal lower semicomputable ratio of the universal continuous semimeasure to the
  measure `π` is a largest lower semicomputable superfair capital, up to a constant factor.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-- **SUV p. 278.**  Winning can be strengthened to strong winning while keeping lower
semicomputability.  One route is Theorem 181(a), followed by its strong converse 181(b).
The raw first-hit `stoppedCapital` operation should not be assumed to preserve lower
semicomputability: deciding whether an earlier capital reaches a threshold is not effective. -/
theorem exists_lsc_stronglyWins_of_wins {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) {m : BitString → ℝ} (hm : IsFairCapital π m)
    (hlsc : IsLowerSemicomputableOnStrings m) :
    ∃ m', IsFairCapital π m' ∧ IsLowerSemicomputableOnStrings m' ∧
      ∀ w, Wins m w → StronglyWins m' w := by
  have hX := isEffectivelyNull_wins hπ hm hlsc
  obtain ⟨m', hm', hlscm', hw⟩ := exists_lsc_stronglyWins_of_isEffectivelyNull hπ hX
  exact ⟨m', hm', hlscm', fun w hw_win => hw w hw_win⟩

/-- The `π`-martingale characterisation of Martin-Löf randomness that Theorem 181 gives: `ω` is
random exactly when no lower semicomputable `π`-martingale wins on it. -/
theorem isMartinLofRandom_iff_forall_lsc_not_wins {π : Measure CantorSeq}
    [IsProbabilityMeasure π] (hπ : IsComputableMeasure π) (w : CantorSeq) :
    IsMartinLofRandom π w ↔
      ∀ m, IsFairCapital π m → IsLowerSemicomputableOnStrings m → ¬ Wins m w := by
  constructor
  · intro hw m hm hlsc hwins
    have heff : IsEffectivelyNull π {w | Wins m w} :=
      isEffectivelyNull_wins hπ hm hlsc
    have h_not_rand := (isEffectivelyNull_iff_forall_not_random hπ _).mp heff w hwins
    exact h_not_rand hw
  · intro h
    by_contra hw_not_rand
    obtain ⟨U, hU⟩ := exists_universal_martinLof_test hπ
    have h_in_U : w ∈ ⋂ n, U n :=
      (not_isMartinLofRandom_iff_mem_universal_test hU w).mp hw_not_rand
    have hU_null : IsEffectivelyNull π (⋂ n, U n) :=
      ⟨U, hU.1.1, Set.Subset.refl _, hU.1.2⟩
    obtain ⟨m, hm, hlsc, hwins⟩ := exists_lsc_stronglyWins_of_isEffectivelyNull hπ hU_null
    have h_strong : StronglyWins m w := hwins w h_in_U
    exact h m hm hlsc h_strong.wins


/-- Step 1 of the proof of `isLargest_universalRatio`: the ratio is a superfair capital.
-/
private lemma isLargest_universalRatio_superfair {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hpos : ∀ x, 0 < cantorMass π x) :
    let M : BitString → ℝ := fun x => (universalContinuousSemimeasure x).toReal / massR π x
    IsSuperfairCapital π M := by
  have hmpos : ∀ x, 0 < massR π x := fun x =>
    ENNReal.toReal_pos (hpos x).ne' (measure_ne_top _ _)
  have ha := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  intro M
  have hM : ∀ x, M x * massR π x = (universalContinuousSemimeasure x).toReal := fun x => by
    simp only [M]
    field_simp [(hmpos x).ne']
  refine ⟨fun x => div_nonneg ENNReal.toReal_nonneg (hmpos x).le, fun x => ?_⟩
  rw [hM, hM, hM]
  exact ha.toReal_children_le x

/-- Step 2 of the proof of `isLargest_universalRatio`: the ratio is lower semicomputable.
-/
private lemma isLargest_universalRatio_lsc {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) :
    let M : BitString → ℝ := fun x => (universalContinuousSemimeasure x).toReal / massR π x
    IsLowerSemicomputableOnStrings M := by
  classical
  obtain ⟨a, ha, hab⟩ := hπ
  obtain ⟨A, hmono, hsup, hAc⟩ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.2
  have hmul : Computable₂ (fun u v : ℕ => u * v) := Primrec.nat_mul.to_comp
  have hlt : Computable₂ (fun u v : ℕ => decide (u < v)) := primrec_decide_nat_lt.to_comp
  have hqL : Computable fun t : ℚ × BitString => t.1 := Computable.fst
  have hneg : IsRE fun t : ℚ × BitString => t.1 < 0 := by
    refine isRE_of_computable_bool _ (fun t : ℚ × BitString => decide (t.1 < 0))
      (fun _ => by simp) ?_
    exact computable₂_ratLt.comp hqL (Computable.const 0)
  have hqR : Computable fun r : (ℚ × BitString) × ℕ => r.1.1 :=
    Computable.fst.comp Computable.fst
  have hnum : Computable fun r : (ℚ × BitString) × ℕ => r.1.1.num.toNat :=
    ComputableReals.primrec_intToNat.to_comp.comp (computable_ratNum.comp hqR)
  have hden : Computable fun r : (ℚ × BitString) × ℕ => r.1.1.den :=
    computable_ratDen.comp hqR
  have haS : Computable fun r : (ℚ × BitString) × ℕ => a r.1.2 r.2 + 1 :=
    Primrec.succ.to_comp.comp (ha.comp (Computable.snd.comp Computable.fst) Computable.snd)
  have hmS : Computable fun r : (ℚ × BitString) × ℕ => A r.2 r.1.2 [] :=
    hAc.comp (Computable.pair Computable.snd
      (Computable.pair (Computable.snd.comp Computable.fst) (Computable.const [])))
  have hstage : IsRE fun r : (ℚ × BitString) × ℕ =>
      r.1.1.num.toNat * (a r.1.2 r.2 + 1) < A r.2 r.1.2 [] * r.1.1.den := by
    refine isRE_of_computable_bool _
      (fun r => decide (r.1.1.num.toNat * (a r.1.2 r.2 + 1) < A r.2 r.1.2 [] * r.1.1.den))
      (fun _ => by rw [decide_eq_true_iff]) ?_
    exact hlt.comp (hmul.comp hnum haS) (hmul.comp hmS hden)
  have hex : IsRE fun t : ℚ × BitString => ∃ s : ℕ,
      t.1.num.toNat * (a t.2 s + 1) < A s t.2 [] * t.1.den :=
    IsRE.exists_encodable (R := fun (t : ℚ × BitString) (s : ℕ) =>
      t.1.num.toNat * (a t.2 s + 1) < A s t.2 [] * t.1.den) hstage
  refine (hneg.or hex).of_iff fun t => ?_
  obtain ⟨q, x⟩ := t
  have hne : universalContinuousSemimeasure x ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  have hpos' : 0 < massR π x :=
    ENNReal.toReal_pos (hpos x).ne' (measure_ne_top π _)
  have hapos : 0 < (universalContinuousSemimeasure x).toReal :=
    ENNReal.toReal_pos (universalContinuousSemimeasure_pos x).ne' hne
  have hMpos : 0 < (universalContinuousSemimeasure x).toReal / massR π x := div_pos hapos hpos'
  change (q < 0 ∨ ∃ s : ℕ, q.num.toNat * (a x s + 1) < A s x [] * q.den) ↔
    (q : ℝ) < (universalContinuousSemimeasure x).toReal / massR π x
  rcases lt_or_ge q 0 with hq | hq
  · have hqr : (q : ℝ) < 0 := by exact_mod_cast hq
    simp only [hq, true_or, true_iff]
    exact lt_trans hqr hMpos
  · have hqr : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    rw [or_iff_right (not_lt.mpr hq)]
    rw [exists_stage_iff_ofReal_lt_ratio hab hmono hsup hq x]
    have hdt : universalContinuousSemimeasure x / cantorMass π x ≠ ⊤ :=
      (ENNReal.div_lt_top hne (hpos x).ne').ne
    rw [ENNReal.ofReal_lt_iff_lt_toReal hqr hdt, ENNReal.toReal_div]
    rfl

/-- Step 1 of the proof of `isLargest_universalRatio_max`: a non-negative real
function on strings whose rational left cut `{(q, x) : q < g x}` is enumerable is lower
semicomputable in the sense of `IsLSC` (computable monotone dyadic numerators).  Take the monotone
stage test `chk` from `IsRE.exists_stageApprox`, let `num s x` be the largest `n ≤ s * 2^s` with
`n / 2^s` confirmed at stage `s` (`Nat.findGreatest`, computable by `Computable.nat_rec`), show
`2 * num s x ≤ num (s+1) x`, and that the supremum of `num s x / 2^s` is `g x` (use the dyadic point
`⌈g x * 2^j⌉ - 1`). -/
private lemma isLargest_universalRatio_bridge {g : BitString → ℝ}
    (hre : IsRE (fun p : ℚ × BitString => (p.1 : ℝ) < g p.2)) :
    IsLSC (fun x _ => ENNReal.ofReal (g x)) := by
  obtain ⟨chk, hcomp, hmono, hspec⟩ := hre.exists_stageApprox
  let F : ℕ → BitString → ℕ → ℕ := fun s x k =>
    if chk (((k : ℚ) / 2 ^ s), x) s = true then k else 0
  let num : ℕ → BitString → BitString → ℕ := fun s x _ => lscBMax (F s x) (s * 2 ^ s + 1)
  -- a confirmed numerator is below `g x`
  have hfound_lt : ∀ (s : ℕ) (x : BitString) (k : ℕ), chk (((k : ℚ) / 2 ^ s), x) s = true →
      dyadicValue k s < ENNReal.ofReal (g x) := by
    intro s x k h
    have hlt : (((k : ℚ) / 2 ^ s : ℚ) : ℝ) < g x := (hspec (((k : ℚ) / 2 ^ s), x)).2 ⟨s, h⟩
    rw [lscDyadicValue_eq_ofReal]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by exact_mod_cast lscDyadicRat_nonneg k s)).2 hlt
  have hnum_le : ∀ s x, dyadicValue (lscBMax (F s x) (s * 2 ^ s + 1)) s ≤ ENNReal.ofReal (g x) := by
    intro s x
    rcases lscBMax_spec (F s x) (s * 2 ^ s + 1) with h0 | ⟨k, _, hkv⟩
    · rw [h0, dyadicValue_zero]; exact bot_le
    · by_cases hf : chk (((k : ℚ) / 2 ^ s), x) s = true
      · have hkeq : k = lscBMax (F s x) (s * 2 ^ s + 1) := by
          rw [← hkv]; simp [F, hf]
        rw [← hkeq]
        exact (hfound_lt s x k hf).le
      · have h0 : lscBMax (F s x) (s * 2 ^ s + 1) = 0 := by
          rw [← hkv]; simp [F, hf]
        rw [h0, dyadicValue_zero]; exact bot_le
  refine ⟨num, ?_, ?_, ?_⟩
  · intro s x ctx
    change dyadicValue (lscBMax (F s x) (s * 2 ^ s + 1)) s ≤
      dyadicValue (lscBMax (F (s + 1) x) ((s + 1) * 2 ^ (s + 1) + 1)) (s + 1)
    rcases lscBMax_spec (F s x) (s * 2 ^ s + 1) with h0 | ⟨k, hk, hkv⟩
    · rw [h0, dyadicValue_zero]; exact bot_le
    · by_cases hf : chk (((k : ℚ) / 2 ^ s), x) s = true
      · have hkeq : k = lscBMax (F s x) (s * 2 ^ s + 1) := by
          rw [← hkv]; simp [F, hf]
        have hrat : ((2 * k : ℕ) : ℚ) / 2 ^ (s + 1) = (k : ℚ) / 2 ^ s := by
          push_cast; ring
        have hf' : chk ((((2 * k : ℕ) : ℚ) / 2 ^ (s + 1)), x) (s + 1) = true := by
          rw [hrat]; exact hmono _ s (s + 1) (Nat.le_succ s) hf
        have hb : 2 * k < (s + 1) * 2 ^ (s + 1) + 1 := by
          have h1 : 2 * k ≤ 2 * (s * 2 ^ s) := by omega
          have h2 : 2 * (s * 2 ^ s) = s * 2 ^ (s + 1) := by ring
          have h3 : s * 2 ^ (s + 1) ≤ (s + 1) * 2 ^ (s + 1) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        have hle : 2 * k ≤ lscBMax (F (s + 1) x) ((s + 1) * 2 ^ (s + 1) + 1) := by
          have hmax := lscLe_bMax (F (s + 1) x) hb
          simp only [F, hf', ite_true] at hmax
          exact hmax
        calc dyadicValue (lscBMax (F s x) (s * 2 ^ s + 1)) s
            = dyadicValue (2 * k) (s + 1) := by rw [← hkeq, dyadicValue_two_mul_succ]
          _ ≤ _ := lscDyadicValue_mono _ hle
      · have h0 : lscBMax (F s x) (s * 2 ^ s + 1) = 0 := by
          rw [← hkv]; simp [F, hf]
        rw [h0, dyadicValue_zero]; exact bot_le
  · intro x ctx
    change ⨆ s, dyadicValue (lscBMax (F s x) (s * 2 ^ s + 1)) s = ENNReal.ofReal (g x)
    refine le_antisymm (iSup_le fun s => hnum_le s x) ?_
    refine le_of_forall_lt fun c hc => ?_
    have hctop : c ≠ ⊤ := ne_top_of_lt hc
    have hcr : c.toReal < g x := by
      rw [← ENNReal.ofReal_toReal hctop] at hc
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).1 hc
    have hgpos : 0 < g x := lt_of_le_of_lt ENNReal.toReal_nonneg hcr
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (1 : ℝ) / 2 ^ j < g x - c.toReal := by
      obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (sub_pos.2 hcr) (by norm_num : (1 : ℝ) / 2 < 1)
      exact ⟨j, by rwa [div_pow, one_pow] at hj⟩
    have hpj : (0 : ℝ) < 2 ^ j := by positivity
    set n : ℕ := ⌈g x * 2 ^ j⌉₊ - 1 with hn
    have hpos : 0 < g x * 2 ^ j := mul_pos hgpos hpj
    have hceil : 1 ≤ ⌈g x * 2 ^ j⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hpos).ne'
    have hn1 : (n : ℝ) < g x * 2 ^ j := by
      have h := Nat.ceil_lt_add_one hpos.le
      have : ((⌈g x * 2 ^ j⌉₊ - 1 : ℕ) : ℝ) = (⌈g x * 2 ^ j⌉₊ : ℝ) - 1 := by
        rw [Nat.cast_sub hceil]; simp
      rw [hn, this]; linarith
    have hn2 : g x * 2 ^ j ≤ (n : ℝ) + 1 := by
      have h := Nat.le_ceil (g x * 2 ^ j)
      have : ((⌈g x * 2 ^ j⌉₊ - 1 : ℕ) : ℝ) = (⌈g x * 2 ^ j⌉₊ : ℝ) - 1 := by
        rw [Nat.cast_sub hceil]; simp
      rw [hn, this]; linarith
    have hcut : (((n : ℚ) / 2 ^ j : ℚ) : ℝ) < g x := by
      push_cast
      rw [div_lt_iff₀ hpj]; exact hn1
    obtain ⟨t, ht⟩ := (hspec (((n : ℚ) / 2 ^ j), x)).1 hcut
    set s : ℕ := max (max t j) ⌈g x⌉₊ with hs
    have hts : t ≤ s := le_trans (le_max_left _ _) (le_max_left _ _)
    have hjs : j ≤ s := le_trans (le_max_right _ _) (le_max_left _ _)
    have hgs : g x ≤ s := le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right _ _)
    set k : ℕ := n * 2 ^ (s - j) with hk
    have hrat : (k : ℚ) / 2 ^ s = (n : ℚ) / 2 ^ j := by
      have : (2 : ℚ) ^ s = 2 ^ j * 2 ^ (s - j) := by rw [← pow_add]; congr 1; omega
      rw [hk, this]; push_cast
      field_simp
    have hkc : chk (((k : ℚ) / 2 ^ s), x) s = true := by
      rw [hrat]; exact hmono _ t s hts ht
    have hkb : k < s * 2 ^ s + 1 := by
      have h1 : (k : ℝ) ≤ s * 2 ^ s := by
        have : (k : ℝ) = n * 2 ^ (s - j) := by rw [hk]; push_cast; ring
        have h2 : (2 : ℝ) ^ s = 2 ^ j * 2 ^ (s - j) := by rw [← pow_add]; congr 1; omega
        have h3 : (0 : ℝ) < 2 ^ (s - j) := by positivity
        rw [this]
        calc (n : ℝ) * 2 ^ (s - j) ≤ g x * 2 ^ j * 2 ^ (s - j) :=
              mul_le_mul_of_nonneg_right hn1.le h3.le
          _ = g x * 2 ^ s := by rw [h2]; ring
          _ ≤ s * 2 ^ s := mul_le_mul_of_nonneg_right hgs (by positivity)
      have : k ≤ s * 2 ^ s := by exact_mod_cast h1
      omega
    have hle : k ≤ lscBMax (F s x) (s * 2 ^ s + 1) := by
      have hmax := lscLe_bMax (F s x) hkb
      simp only [F, hkc, ite_true] at hmax
      exact hmax
    have hcn : c < dyadicValue k s := by
      rw [lscDyadicValue_eq_ofReal, hrat, ← ENNReal.ofReal_toReal hctop]
      refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2 ?_
      push_cast
      rw [lt_div_iff₀ hpj]
      rw [div_lt_iff₀ hpj] at hj
      nlinarith
    calc c < dyadicValue k s := hcn
      _ ≤ dyadicValue (lscBMax (F s x) (s * 2 ^ s + 1)) s := lscDyadicValue_mono _ hle
      _ ≤ _ := le_iSup (fun s => dyadicValue (lscBMax (F s x) (s * 2 ^ s + 1)) s) s
  · have hFc : Computable₂ (fun (a : ℕ × BitString × BitString) (k : ℕ) => F a.1 a.2.1 k) := by
      have hq : Computable (fun c : (ℕ × BitString × BitString) × ℕ =>
          ((c.2 : ℚ) / 2 ^ c.1.1)) :=
        (lscComputable_dyadicRat.comp (Computable.snd.pair
          (Computable.fst.comp Computable.fst))).of_eq (fun _ => rfl)
      have hcc : Computable (fun c : (ℕ × BitString × BitString) × ℕ =>
          chk (((c.2 : ℚ) / 2 ^ c.1.1), c.1.2.1) c.1.1) :=
        hcomp.comp (hq.pair (Computable.fst.comp (Computable.snd.comp Computable.fst)))
          (Computable.fst.comp Computable.fst)
      have hc := Computable.cond hcc Computable.snd (Computable.const 0)
      refine hc.of_eq (fun c => ?_)
      cases h : chk (((c.2 : ℚ) / 2 ^ c.1.1), c.1.2.1) c.1.1 <;> simp [F, h]
    have hN : Computable (fun a : ℕ × BitString × BitString => a.1 * 2 ^ a.1 + 1) := by
      have hpow : Primrec (fun a : ℕ × BitString × BitString => 2 ^ a.1) :=
        (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.fst
      have hmul : Primrec (fun a : ℕ × BitString × BitString => a.1 * 2 ^ a.1) :=
        Primrec₂.comp Primrec.nat_mul Primrec.fst hpow
      exact (Primrec₂.comp Primrec.nat_add hmul (Primrec.const 1)).to_comp
    exact lscComputable_bMax hFc hN

/-- Clearing denominators: for rationals `q, r ≥ 0` the real inequality `q * k < r * A / 2^s` is the
natural-number inequality `num q * k * den r * 2^s < num r * den q * A`. -/
private lemma isLargest_universalRatio_cut_key (q r : ℚ) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (k A s : ℕ) :
    ((q : ℝ) * k < r * A / 2 ^ s) ↔
      q.num.toNat * k * r.den * 2 ^ s < r.num.toNat * q.den * A := by
  have hqn : ((q.num.toNat : ℕ) : ℝ) = (q : ℝ) * q.den := by
    have h1 : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
    have h2 : (q : ℚ) * q.den = q.num := Rat.mul_den_eq_num q
    have h3 : ((q.num.toNat : ℕ) : ℚ) = q * q.den := by rw [h2]; exact_mod_cast h1
    exact_mod_cast h3
  have hrn : ((r.num.toNat : ℕ) : ℝ) = (r : ℝ) * r.den := by
    have h1 : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hr)
    have h2 : (r : ℚ) * r.den = r.num := Rat.mul_den_eq_num r
    have h3 : ((r.num.toNat : ℕ) : ℚ) = r * r.den := by rw [h2]; exact_mod_cast h1
    exact_mod_cast h3
  rw [lt_div_iff₀ (by positivity), ← Nat.cast_lt (α := ℝ)]
  push_cast
  rw [hqn, hrn]
  have hpos : (0 : ℝ) < q.den * r.den := by positivity
  constructor
  · intro h
    have := mul_lt_mul_of_pos_right h hpos
    linarith
  · intro h
    exact lt_of_mul_lt_mul_right (by linarith) hpos.le

/-- The dyadic approximation of `IsComputableMeasure`, in real terms. -/
private lemma isLargest_universalRatio_cut_bounds {π : Measure CantorSeq}
    [IsProbabilityMeasure π] {a : BitString → ℕ → ℕ}
    (hab : ∀ x s, dyadicValue (a x s) s ≤ cantorMass π x + dyadicValue 1 s ∧
      cantorMass π x ≤ dyadicValue (a x s) s + dyadicValue 1 s) (x : BitString) (s : ℕ) :
    (a x s : ℝ) / 2 ^ s ≤ massR π x + 1 / 2 ^ s ∧ massR π x ≤ (a x s : ℝ) / 2 ^ s + 1 / 2 ^ s := by
  have h := hab x s
  have hd : ∀ n : ℕ, dyadicValue n s ≠ ⊤ := fun n =>
    (ENNReal.div_lt_top (ENNReal.natCast_ne_top n) (pow_ne_zero _ (by norm_num))).ne
  have hdy : ∀ n : ℕ, (dyadicValue n s).toReal = (n : ℝ) / 2 ^ s := fun n => by
    simp [dyadicValue, ENNReal.toReal_div]
  have hm : cantorMass π x ≠ ⊤ := measure_ne_top _ _
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hm, hd 1⟩) h.1
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hd _, hd 1⟩) h.2
  rw [ENNReal.toReal_add hm (hd 1), hdy, hdy] at h1
  rw [ENNReal.toReal_add (hd _) (hd 1), hdy, hdy] at h2
  simp only [Nat.cast_one] at h1 h2
  exact ⟨h1, h2⟩

/-- Step 2 of the proof of `isLargest_universalRatio_max`: for a computable
probability measure `π` and a non-negative lower semicomputable `m`, the left cut
`{(q, x) : q < m x * π(x) / k}` is enumerable.  For `q < 0` it always holds; for `q ≥ 0` it holds
iff there are a rational `r ≥ 0` with `r < m x` (enumerable) and a stage `s` with `q * k < r * l_s
x`,
where `l_s x = max (α x s - 1) 0 / 2^s` for the approximation `α` of `IsComputableMeasure`, which
satisfies `l_s x ≤ π x` and `π x - 2 * 2^{-s} ≤ l_s x`.  Use `IsRE.comp_computable`,
`IsRE.and_computable`, `IsRE.exists_encodable`, `IsRE.or`. -/
private lemma isLargest_universalRatio_cut {π : Measure CantorSeq}
    [IsProbabilityMeasure π] (hπ : IsComputableMeasure π) {m : BitString → ℝ}
    (hnn : ∀ x, 0 ≤ m x) (hlsc : IsLowerSemicomputableOnStrings m) {k : ℕ} (hk : 0 < k) :
    IsRE (fun p : ℚ × BitString => (p.1 : ℝ) < m p.2 * massR π p.2 / k) := by
  classical
  obtain ⟨a, ha, hab⟩ := hπ
  have hbd := isLargest_universalRatio_cut_bounds hab
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmul : Computable₂ (fun u v : ℕ => u * v) := Primrec.nat_mul.to_comp
  have hlt : Computable₂ (fun u v : ℕ => decide (u < v)) := primrec_decide_nat_lt.to_comp
  have hpow₂ : Computable₂ (fun u v : ℕ => u ^ v) := nat_pow_primrec₂.to_comp
  have hneg : IsRE fun t : ℚ × BitString => t.1 < 0 := by
    refine isRE_of_computable_bool _ (fun t : ℚ × BitString => decide (t.1 < 0))
      (fun _ => by simp) ?_
    exact computable₂_ratLt.comp Computable.fst (Computable.const 0)
  have hqQ : Computable fun t : (ℚ × BitString) × (ℚ × ℕ) => t.1.1 :=
    Computable.fst.comp Computable.fst
  have hrQ : Computable fun t : (ℚ × BitString) × (ℚ × ℕ) => t.2.1 :=
    Computable.fst.comp Computable.snd
  have hqn : Computable fun t : (ℚ × BitString) × (ℚ × ℕ) => t.1.1.num.toNat :=
    ComputableReals.primrec_intToNat.to_comp.comp (computable_ratNum.comp hqQ)
  have hqd : Computable fun t : (ℚ × BitString) × (ℚ × ℕ) => t.1.1.den :=
    computable_ratDen.comp hqQ
  have hrn : Computable fun t : (ℚ × BitString) × (ℚ × ℕ) => t.2.1.num.toNat :=
    ComputableReals.primrec_intToNat.to_comp.comp (computable_ratNum.comp hrQ)
  have hrd : Computable fun t : (ℚ × BitString) × (ℚ × ℕ) => t.2.1.den :=
    computable_ratDen.comp hrQ
  have hs : Computable fun t : (ℚ × BitString) × (ℚ × ℕ) => t.2.2 :=
    Computable.snd.comp Computable.snd
  have hA : Computable fun t : (ℚ × BitString) × (ℚ × ℕ) => a t.1.2 t.2.2 - 1 :=
    Primrec.nat_sub.to_comp.comp
      (ha.comp (Computable.snd.comp Computable.fst) hs) (Computable.const 1)
  have hpw : Computable fun t : (ℚ × BitString) × (ℚ × ℕ) => 2 ^ t.2.2 :=
    hpow₂.comp (Computable.const 2) hs
  have hL : Computable fun t : (ℚ × BitString) × (ℚ × ℕ) =>
      t.1.1.num.toNat * k * t.2.1.den * 2 ^ t.2.2 :=
    hmul.comp (hmul.comp (hmul.comp hqn (Computable.const k)) hrd) hpw
  have hR' : Computable fun t : (ℚ × BitString) × (ℚ × ℕ) =>
      t.2.1.num.toNat * t.1.1.den * (a t.1.2 t.2.2 - 1) :=
    hmul.comp (hmul.comp hrn hqd) hA
  have hp : Computable fun t : (ℚ × BitString) × (ℚ × ℕ) => decide
      (t.1.1.num.toNat * k * t.2.1.den * 2 ^ t.2.2 <
        t.2.1.num.toNat * t.1.1.den * (a t.1.2 t.2.2 - 1)) :=
    hlt.comp hL hR'
  have hl : IsRE (fun p : ℚ × BitString => (p.1 : ℝ) < m p.2) := hlsc
  have hR : IsRE (fun t : (ℚ × BitString) × (ℚ × ℕ) => (t.2.1 : ℝ) < m t.1.2) :=
    hl.comp_computable (g := fun t : (ℚ × BitString) × (ℚ × ℕ) => (t.2.1, t.1.2))
      (Computable.pair hrQ (Computable.snd.comp Computable.fst))
  have hAnd := hR.and_computable hp
  have hex : IsRE fun t : ℚ × BitString => ∃ b : ℚ × ℕ,
      decide (t.1.num.toNat * k * b.1.den * 2 ^ b.2 <
        b.1.num.toNat * t.1.den * (a t.2 b.2 - 1)) = true ∧ (b.1 : ℝ) < m t.2 :=
    IsRE.exists_encodable
      (R := fun (t : ℚ × BitString) (b : ℚ × ℕ) =>
        decide (t.1.num.toNat * k * b.1.den * 2 ^ b.2 <
          b.1.num.toNat * t.1.den * (a t.2 b.2 - 1)) = true ∧ (b.1 : ℝ) < m t.2) hAnd
  refine (hneg.or hex).of_iff fun t => ?_
  obtain ⟨q, x⟩ := t
  have hmassnn : 0 ≤ massR π x := ENNReal.toReal_nonneg
  change (q < 0 ∨ ∃ b : ℚ × ℕ, decide (q.num.toNat * k * b.1.den * 2 ^ b.2 <
        b.1.num.toNat * q.den * (a x b.2 - 1)) = true ∧ (b.1 : ℝ) < m x) ↔
    (q : ℝ) < m x * massR π x / k
  rcases lt_or_ge q 0 with hq | hq
  · have hqr : (q : ℝ) < 0 := by exact_mod_cast hq
    simp only [hq, true_or, true_iff]
    exact lt_of_lt_of_le hqr (div_nonneg (mul_nonneg (hnn x) hmassnn) hkR.le)
  · have hqr : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    rw [or_iff_right (not_lt.mpr hq), lt_div_iff₀ hkR]
    constructor
    · rintro ⟨⟨r, s⟩, hpr, hr⟩
      rw [decide_eq_true_iff] at hpr
      have hr0 : 0 ≤ r := by
        by_contra h
        have h1 : r.num ≤ 0 := Rat.num_nonpos.mpr (not_le.mp h).le
        have h2 : r.num.toNat = 0 := Int.toNat_eq_zero.mpr h1
        rw [h2] at hpr
        simp at hpr
      have hkey := (isLargest_universalRatio_cut_key q r hq hr0 k (a x s - 1) s).mpr
        hpr
      have hsub : ((a x s - 1 : ℕ) : ℝ) ≤ massR π x * 2 ^ s := by
        have h2s : (0 : ℝ) < 2 ^ s := by positivity
        rcases Nat.eq_zero_or_pos (a x s) with h0 | h0
        · rw [h0, Nat.zero_sub, Nat.cast_zero]; positivity
        · have h1 := (hbd x s).1
          rw [div_le_iff₀ h2s, add_mul, one_div, inv_mul_cancel₀ h2s.ne'] at h1
          rw [Nat.cast_sub h0]
          simp only [Nat.cast_one]
          linarith
      have h2s : (0 : ℝ) < 2 ^ s := by positivity
      have h3 : (r : ℝ) * ((a x s - 1 : ℕ) : ℝ) / 2 ^ s ≤ r * massR π x := by
        rw [div_le_iff₀ h2s]
        have := mul_le_mul_of_nonneg_left hsub (show (0 : ℝ) ≤ r by exact_mod_cast hr0)
        linarith
      have h4 : (r : ℝ) * massR π x ≤ m x * massR π x :=
        mul_le_mul_of_nonneg_right hr.le hmassnn
      linarith
    · intro h
      have hmR : 0 < massR π x := by
        by_contra h0
        have : massR π x = 0 := le_antisymm (not_lt.mp h0) hmassnn
        rw [this, mul_zero] at h
        have : (0 : ℝ) ≤ q * k := mul_nonneg hqr hkR.le
        linarith
      have hm0 : 0 < m x := by
        by_contra h0
        have : m x = 0 := le_antisymm (not_lt.mp h0) (hnn x)
        rw [this, zero_mul] at h
        have : (0 : ℝ) ≤ q * k := mul_nonneg hqr hkR.le
        linarith
      have hdiv : (q : ℝ) * k / massR π x < m x := (div_lt_iff₀ hmR).mpr h
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hdiv
      have hr0' : (0 : ℝ) < r :=
        lt_of_le_of_lt (div_nonneg (mul_nonneg hqr hkR.le) hmR.le) hr1
      have hr0 : 0 ≤ r := by exact_mod_cast hr0'.le
      have hδ : (q : ℝ) * k < r * massR π x := (div_lt_iff₀ hmR).mp hr1
      obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt (2 * (r : ℝ) / (r * massR π x - q * k))
        (by norm_num : (1 : ℝ) < 2)
      have h2s : (0 : ℝ) < 2 ^ s := by positivity
      have hδpos : 0 < (r : ℝ) * massR π x - q * k := by linarith
      have hs' : 2 * (r : ℝ) < (r * massR π x - q * k) * 2 ^ s := by
        rw [div_lt_iff₀ hδpos] at hs
        linarith
      have hlow : massR π x * 2 ^ s - 2 ≤ ((a x s - 1 : ℕ) : ℝ) := by
        have h1' : massR π x * 2 ^ s ≤ a x s + 1 := by
          have h1 := (hbd x s).2
          have e : (a x s : ℝ) / 2 ^ s + 1 / 2 ^ s = ((a x s : ℝ) + 1) / 2 ^ s := by ring
          rw [e, le_div_iff₀ h2s] at h1
          exact h1
        have h5 : (a x s : ℝ) ≤ ((a x s - 1 : ℕ) : ℝ) + 1 := by
          have : a x s ≤ (a x s - 1) + 1 := by omega
          exact_mod_cast this
        linarith
      have hlt' : (q : ℝ) * k < r * ((a x s - 1 : ℕ) : ℝ) / 2 ^ s := by
        rw [lt_div_iff₀ h2s]
        have := mul_le_mul_of_nonneg_left hlow hr0'.le
        nlinarith
      have hkey := (isLargest_universalRatio_cut_key q r hq hr0 k (a x s - 1) s).mp
        hlt'
      exact ⟨(r, s), decide_eq_true hkey, hr2⟩

/-- Step 3 of the proof of `isLargest_universalRatio_max`: if `m` is a superfair
capital with `m [] ≤ k`, the weight `w x = ofReal (m x * π(x) / k)` has sum at most `1` over every
finite prefix-free set.  The superfair inequality gives `w (x0) + w (x1) ≤ w x`; with `w'` equal to
`1` at `[]` and to `w` elsewhere, `w'` is a continuous tree semimeasure and
`IsContinuousTreeSemimeasure.sum_antichain_le` applies. -/
private lemma isLargest_universalRatio_sum {π : Measure CantorSeq}
    [IsProbabilityMeasure π] {m : BitString → ℝ} (hm : IsSuperfairCapital π m) {k : ℕ}
    (hk : 0 < k) (hmk : m [] ≤ k) (S : Finset BitString) (hS : IsPrefixFree (S : Set BitString)) :
    ∑ x ∈ S, ENNReal.ofReal (m x * massR π x / k) ≤ 1 := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmass0 : massR π [] = 1 := by
    simp [massR, cantorMass, cantorCylinder_nil]
  have hmass_nn : ∀ x, 0 ≤ massR π x := fun x => ENNReal.toReal_nonneg
  let w' : BitString → ENNReal := fun x =>
    if x = [] then 1 else ENNReal.ofReal (m x * massR π x / k)
  have hw'1 : ∀ x, ENNReal.ofReal (m x * massR π x / k) ≤ w' x := by
    intro x
    by_cases hx : x = []
    · subst hx
      simp only [w', ite_true]
      rw [hmass0, mul_one]
      rw [ENNReal.ofReal_le_one]
      rw [div_le_one hkR]; exact hmk
    · simp [w', hx]
  have htree : IsContinuousTreeSemimeasure w' := by
    refine ⟨by simp [w'], fun x => ?_⟩
    have hne0 : x ++ [false] ≠ [] := by simp
    have hne1 : x ++ [true] ≠ [] := by simp
    simp only [w', hne0, hne1, ite_false]
    rw [← ENNReal.ofReal_add
      (div_nonneg (mul_nonneg (hm.nonneg _) (hmass_nn _)) hkR.le)
      (div_nonneg (mul_nonneg (hm.nonneg _) (hmass_nn _)) hkR.le), ← add_div]
    by_cases hx : x = []
    · subst hx
      simp only [ite_true]
      rw [ENNReal.ofReal_le_one, div_le_one hkR]
      have := hm.superfair []
      rw [hmass0, mul_one] at this
      exact this.trans hmk
    · simp only [hx, ite_false]
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hm.superfair x) hkR.le)
  calc ∑ x ∈ S, ENNReal.ofReal (m x * massR π x / k) ≤ ∑ x ∈ S, w' x :=
        Finset.sum_le_sum fun x _ => hw'1 x
    _ ≤ 1 := htree.sum_antichain_le S (fun y hy z hz h => hS hy hz h)

/-- Step 3 of the proof of `isLargest_universalRatio`: any lower semicomputable superfair
capital is bounded by the ratio up to a constant. -/
private lemma isLargest_universalRatio_max {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) :
    let M : BitString → ℝ := fun x => (universalContinuousSemimeasure x).toReal / massR π x
    ∀ m, IsSuperfairCapital π m → IsLowerSemicomputableOnStrings m →
        ∃ c : ℝ, 0 < c ∧ ∀ x, m x ≤ c * M x := by
  intro M m hm hlsc
  obtain ⟨k, hk, hmk⟩ : ∃ k : ℕ, 0 < k ∧ m [] ≤ k :=
    ⟨⌈m []⌉₊ + 1, Nat.succ_pos _, by have := Nat.le_ceil (m []); push_cast; linarith⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmass : ∀ x, 0 < massR π x := fun x =>
    ENNReal.toReal_pos (hpos x).ne' (measure_ne_top _ _)
  have hwnn : ∀ x, 0 ≤ m x * massR π x / k := fun x =>
    div_nonneg (mul_nonneg (hm.nonneg x) (hmass x).le) hkR.le
  have hLSC := isLargest_universalRatio_bridge (g := fun x => m x * massR π x / k)
    (isLargest_universalRatio_cut hπ hm.nonneg hlsc hk)
  obtain ⟨C, hCtop, hC⟩ := lsc_prefixFreeWeight_dominated_by_universal _ hLSC
    (fun S hS => isLargest_universalRatio_sum hm hk hmk S hS)
  refine ⟨k * C.toReal + 1, by positivity, fun x => ?_⟩
  have hatop : universalContinuousSemimeasure x ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top hCtop hatop) (hC x)
  rw [ENNReal.toReal_ofReal (hwnn x), ENNReal.toReal_mul] at h1
  have hM : 0 ≤ M x := div_nonneg ENNReal.toReal_nonneg (hmass x).le
  have h2 : m x * massR π x ≤ k * C.toReal * (universalContinuousSemimeasure x).toReal := by
    have := (div_le_iff₀ hkR).mp h1
    linarith
  have h3 : m x ≤ k * C.toReal * M x := by
    have : M x = (universalContinuousSemimeasure x).toReal / massR π x := rfl
    rw [this, ← mul_div_assoc, le_div_iff₀ (hmass x)]
    exact h2
  have hC0 : 0 ≤ k * C.toReal := by positivity
  nlinarith

/-- **SUV p. 279.**  For computable `π` with positive cylinders, `a(x) / π(x)`, with `a` the a
priori probability (`universalContinuousSemimeasure`), is the largest lower semicomputable
supermartingale up to a constant factor.  The book writes the ratio without comment; it needs
`π(x) > 0`. -/
theorem isLargest_universalRatio {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) :
    let M : BitString → ℝ := fun x => (universalContinuousSemimeasure x).toReal / massR π x
    IsSuperfairCapital π M ∧ IsLowerSemicomputableOnStrings M ∧
      ∀ m, IsSuperfairCapital π m → IsLowerSemicomputableOnStrings m →
        ∃ c : ℝ, 0 < c ∧ ∀ x, m x ≤ c * M x := by
  refine ⟨isLargest_universalRatio_superfair hpos,
          isLargest_universalRatio_lsc hπ hpos,
          isLargest_universalRatio_max hπ hpos⟩


/-- Step 1 of the proof of `isProbabilityBoundedRandomnessTest_sup`: the supremum function
is lower semicomputable. -/
private lemma isProbabilityBoundedRandomnessTest_sup_lsc {m : BitString → ℝ}
    (hlsc : IsLowerSemicomputableOnStrings m) :
    IsLowerSemicomputableFun (fun w => ⨆ n, ENNReal.ofReal (m (cantorPrefix w n))) := by
  classical
  have hg : Computable (fun q : ℕ × BitString => (Denumerable.ofNat ℚ q.1, q.2)) :=
    ((Computable.ofNat ℚ).comp Computable.fst).pair Computable.snd
  have hS : IsRE (fun q : ℕ × BitString =>
      q.2 ∈ {σ : BitString | ((Denumerable.ofNat ℚ q.1 : ℚ) : ℝ) < m σ}) :=
    IsRE.of_iff (IsRE.compComputable hlsc hg) (fun q => by simp)
  obtain ⟨f, hf, hfeq⟩ := isUniformlyEffectiveOpen_prefixHitSet_of_isRE
    (S := fun n => {σ : BitString | ((Denumerable.ofNat ℚ n : ℚ) : ℝ) < m σ}) hS
  have hidx : Computable (fun p : ℚ × ℕ => Kolmogorov.ComputableReals.ratIndex p.1) :=
    (Primrec.encode (α := ℚ)).to_comp.comp Computable.fst
  have hcyl : cantorCylinder ([] : BitString) = Set.univ := by
    ext w; simp [cantorCylinder, IsCantorPrefix]
  refine ⟨fun q i => if q < 0 then some [] else f (Kolmogorov.ComputableReals.ratIndex q) i,
    ?_, ?_⟩
  · have hb : Computable (fun p : ℚ × ℕ => decide (p.1 < 0)) :=
      (computable_ratLtConst 0).comp Computable.fst
    have hfc : Computable (fun p : ℚ × ℕ =>
        f (Kolmogorov.ComputableReals.ratIndex p.1) p.2) :=
      Computable₂.comp hf hidx Computable.snd
    have hc := Computable.cond hb (Computable.const (some ([] : BitString))) hfc
    refine hc.of_eq (fun p => ?_)
    by_cases h : p.1 < 0 <;> simp [h]
  · intro q
    by_cases hq : q < 0
    · have hq' : (q : ℝ) < 0 := by exact_mod_cast hq
      have : {w : CantorSeq | (q : ℝ) < 0 ∨
          ENNReal.ofReal (q : ℝ) < ⨆ n, ENNReal.ofReal (m (cantorPrefix w n))} = Set.univ := by
        ext w; simp [hq']
      rw [this]
      symm
      rw [Set.eq_univ_iff_forall]
      intro w
      refine Set.mem_iUnion.2 ⟨0, ?_⟩
      simp [hq, hcyl]
    · have hq0 : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast not_lt.1 hq
      have h1 := hfeq (Kolmogorov.ComputableReals.ratIndex q)
      simp only [Kolmogorov.ComputableReals.ofNat_ratIndex] at h1
      have h2 : {w : CantorSeq | (q : ℝ) < 0 ∨
          ENNReal.ofReal (q : ℝ) < ⨆ n, ENNReal.ofReal (m (cantorPrefix w n))} =
          prefixHitSet {σ : BitString | (q : ℝ) < m σ} := by
        ext w
        simp only [Set.mem_ofPred_eq, prefixHitSet, lt_iSup_iff, not_lt.2 hq0, false_or]
        refine exists_congr (fun n => ?_)
        exact ENNReal.ofReal_lt_ofReal_iff'.trans (by
          constructor
          · exact fun h => h.1
          · exact fun h => ⟨h, lt_of_le_of_lt hq0 h⟩)
      rw [h2, h1]
      simp [hq]

/-- Step 2 of the proof of `isProbabilityBoundedRandomnessTest_sup`: bound the measure of
the test exceeding `c`. -/
private lemma isProbabilityBoundedRandomnessTest_sup_measure {m : BitString → ℝ}
    (hm : IsMartingale uniformMeasure m) (c : ℚ) (hc : 0 < c) :
    uniformMeasure {w | ⨆ n, ENNReal.ofReal (m (cantorPrefix w n)) > ENNReal.ofReal (c : ℝ)}
      < (ENNReal.ofReal (c : ℝ))⁻¹ := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  set S : Set BitString := {x | (c : ℝ) < m x} with hS
  have hset : {w | ⨆ n, ENNReal.ofReal (m (cantorPrefix w n)) > ENNReal.ofReal (c : ℝ)}
      = prefixHitSet S := by
    ext w
    simp only [Set.mem_ofPred_eq, prefixHitSet, gt_iff_lt, lt_iSup_iff, hS]
    refine exists_congr fun n => ?_
    rw [ENNReal.ofReal_lt_ofReal_iff']
    exact ⟨fun h => h.1, fun h => ⟨h, hcR.trans h⟩⟩
  -- the tree semimeasure `a x = m x * 2^{-|x|}`
  set a : BitString → ENNReal := fun x => ENNReal.ofReal (m x * massR uniformMeasure x) with ha_def
  have hmass_nn : ∀ x : BitString, 0 ≤ massR uniformMeasure x := fun x => by
    rw [massR_uniformMeasure]; positivity
  have ha : IsContinuousTreeSemimeasure a := by
    refine ⟨?_, fun x => ?_⟩
    · simp only [ha_def, hm.init, massR_uniformMeasure, List.length_nil, pow_zero, mul_one,
        ENNReal.ofReal_one]
    · simp only [ha_def]
      rw [← ENNReal.ofReal_add (mul_nonneg (hm.nonneg _) (hmass_nn _))
        (mul_nonneg (hm.nonneg _) (hmass_nn _)), ← hm.fair x]
  have hcyl : ∀ x : BitString, cantorMass uniformMeasure x
      = ENNReal.ofReal (massR uniformMeasure x) := fun x => by
    unfold massR
    rw [ENNReal.ofReal_toReal (by
      rw [cantorMass, uniformMeasure_cantorCylinder]
      exact ENNReal.pow_ne_top (by simp))]
  have hlt : ∀ x ∈ S, ENNReal.ofReal (c : ℝ) * cantorMass uniformMeasure x < a x := by
    intro x hx
    have hxS : (c : ℝ) < m x := hx
    have hpos : 0 < massR uniformMeasure x := by rw [massR_uniformMeasure]; positivity
    rw [hcyl, ← ENNReal.ofReal_mul hcR.le]
    simp only [ha_def]
    rw [ENNReal.ofReal_lt_ofReal_iff (mul_pos (hcR.trans hxS) hpos)]
    exact mul_lt_mul_of_pos_right hxS hpos
  set F := minimalPrefixElements S with hF
  have hbound := measure_prefixHitSet_le_tsum_minimalPrefixElements uniformMeasure S
  have hKraft : ∑' x : F, a x ≤ 1 :=
    ha.tsum_antichain_le F (minimalPrefixElements_antichain S)
  rw [hset]
  by_cases hFe : IsEmpty F
  · have h0 : ∑' x : F, cantorMass uniformMeasure (x : BitString) = 0 := by
      simp
    have h1 : uniformMeasure (prefixHitSet S) = 0 := le_antisymm (h0 ▸ hbound) bot_le
    rw [h1]
    exact ENNReal.inv_pos.2 ENNReal.ofReal_ne_top
  · rw [not_isEmpty_iff] at hFe
    obtain ⟨x₀⟩ := hFe
    have hstrict : ∑' x : F, ENNReal.ofReal (c : ℝ) * cantorMass uniformMeasure (x : BitString)
        < ∑' x : F, a x := by
      have hfin : ∑' x : F, ENNReal.ofReal (c : ℝ) * cantorMass uniformMeasure (x : BitString)
          ≠ ⊤ := by
        refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
        refine le_trans (ENNReal.tsum_le_tsum fun x => (hlt x (minimalPrefixElements_subset S
            x.2)).le)
          hKraft
      exact ENNReal.tsum_lt_tsum hfin (fun x => (hlt x (minimalPrefixElements_subset S x.2)).le)
        (hlt x₀ (minimalPrefixElements_subset S x₀.2))
    have hmul : ENNReal.ofReal (c : ℝ) * uniformMeasure (prefixHitSet S) < 1 := by
      calc ENNReal.ofReal (c : ℝ) * uniformMeasure (prefixHitSet S)
          ≤ ENNReal.ofReal (c : ℝ) * ∑' x : F, cantorMass uniformMeasure (x : BitString) :=
            by gcongr
        _ = ∑' x : F, ENNReal.ofReal (c : ℝ) * cantorMass uniformMeasure (x : BitString) :=
            ENNReal.tsum_mul_left.symm
        _ < ∑' x : F, a x := hstrict
        _ ≤ 1 := hKraft
    have hc0 : ENNReal.ofReal (c : ℝ) ≠ 0 := by simpa using hcR
    have hinv0 : (ENNReal.ofReal (c : ℝ))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
    have hinvt : (ENNReal.ofReal (c : ℝ))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hc0
    calc uniformMeasure (prefixHitSet S)
        = (ENNReal.ofReal (c : ℝ))⁻¹ * (ENNReal.ofReal (c : ℝ) * uniformMeasure (prefixHitSet S)) :=
            by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
      _ < (ENNReal.ofReal (c : ℝ))⁻¹ * 1 := (ENNReal.mul_lt_mul_iff_right hinv0 hinvt).2 hmul
      _ = (ENNReal.ofReal (c : ℝ))⁻¹ := mul_one _

/-- **SUV Problem 264, p. 272.**  For a lower semicomputable martingale `m`, the function
`t(ω) = sup_{x ≺ ω} m(x)` is a probability-bounded randomness test in the sense of Section 3.5 (the
library's `IsProbabilityBoundedRandomnessTest`). -/
theorem isProbabilityBoundedRandomnessTest_sup {m : BitString → ℝ}
    (hm : IsMartingale uniformMeasure m) (hlsc : IsLowerSemicomputableOnStrings m) :
    IsProbabilityBoundedRandomnessTest uniformMeasure
      (fun w => ⨆ n, ENNReal.ofReal (m (cantorPrefix w n))) := by
  exact ⟨isProbabilityBoundedRandomnessTest_sup_lsc hlsc,
      isProbabilityBoundedRandomnessTest_sup_measure hm⟩

end Kolmogorov.FrequencyGames
