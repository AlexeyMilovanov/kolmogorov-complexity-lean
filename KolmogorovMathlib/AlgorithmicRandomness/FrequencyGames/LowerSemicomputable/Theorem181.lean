/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.Martingale
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.PrefixRatioLSC
import KolmogorovMathlib.MonotoneComplexity.SubSemimeasureDomination

/-!
# Theorem181

Schnorr's characterization of effectively null sets by lower semicomputable martingales
(Theorem 181 of Shen, Uspensky and Vereshchagin, p. 278).

Main declarations:
* `IsLowerSemicomputableOnStrings`, `IsComputableOnStrings`: lower semicomputable and computable
  real functions on binary strings.
* `isEffectivelyNull_wins`: the sequences on which a lower semicomputable `π`-martingale wins form
  an effectively null set.
* the converse direction: an effectively null set is strongly won by a lower semicomputable
  martingale.
-/

namespace Kolmogorov.FrequencyGames

open MeasureTheory Filter Topology

/-- **SUV p. 277.**  `m` is *lower semicomputable*: the set of `⟨r, x⟩` with `r` rational and
`r < m(x)` is enumerable. -/
def IsLowerSemicomputableOnStrings (m : BitString → ℝ) : Prop :=
  IsRE (fun p : ℚ × BitString => (p.1 : ℝ) < m p.2)

/-- A *computable* real function on strings: the values have rational approximations with
prescribed error, uniformly in the string. -/
def IsComputableOnStrings (m : BitString → ℝ) : Prop :=
  ∃ q : BitString × ℕ → ℚ, Computable q ∧ ∀ x s, |(q (x, s) : ℝ) - m x| ≤ (2 : ℝ)⁻¹ ^ s

/-- Step 1 of the proof of `isEffectivelyNull_wins`: the initial capital is bounded by a
positive integer `c` (take `c = ⌈m(Λ)⌉ + 1`; no hypothesis on `m` is needed). -/
private lemma isEffectivelyNull_wins_bound (m : BitString → ℝ) :
    ∃ c : ℕ, 0 < c ∧ m [] ≤ c :=
  ⟨⌈m []⌉₊ + 1, Nat.succ_pos _, by have := Nat.le_ceil (m []); push_cast; linarith⟩

/-- Step 2 of the proof of `isEffectivelyNull_wins`: for a lower semicomputable `m` and
a fixed `c`, the sets of sequences having a prefix `σ` with `c * 2^n < m(σ)` form a uniformly
effectively open family.  The set of strings `σ` with `c * 2^n < m(σ)` is enumerable uniformly in
`n`, since the rational `c * 2^n` is computed from `n`; the bridge from enumerable sets of strings
to effectively open sets of sequences is `isUniformlyEffectiveOpen_prefixHitSet_of_isRE`. -/
private lemma isEffectivelyNull_wins_open {m : BitString → ℝ}
    (hlsc : IsLowerSemicomputableOnStrings m) (c : ℕ) :
    IsUniformlyEffectiveOpen
      (fun n : ℕ => {w : CantorSeq | ∃ k, ((c * 2 ^ n : ℕ) : ℝ) < m (cantorPrefix w k)}) := by
  have hg : Computable (fun q : ℕ × BitString => (((c * 2 ^ q.1 : ℕ) : ℚ), q.2)) :=
    (computable_nat_to_rat.comp (Primrec.nat_mul.comp (Primrec.const c)
      (nat_pow_primrec₂.comp (Primrec.const 2) Primrec.fst)).to_comp).pair Computable.snd
  have hS : IsRE (fun q : ℕ × BitString =>
      q.2 ∈ {σ : BitString | ((c * 2 ^ q.1 : ℕ) : ℝ) < m σ}) :=
    IsRE.of_iff (IsRE.compComputable hlsc hg) (fun q => by simp)
  exact isUniformlyEffectiveOpen_prefixHitSet_of_isRE
    (S := fun n => {σ : BitString | ((c * 2 ^ n : ℕ) : ℝ) < m σ}) hS

/-- Step 3 of the proof of `isEffectivelyNull_wins`: Ville's inequality at the level
`c * 2^n`.  If the initial capital `m(Λ)` is at most `c`, the `π`-measure of the sequences having a
prefix on which the capital strictly exceeds `c * 2^n` is at most `2⁻ⁿ` (`dyadicValue 1 n`). -/
private lemma isEffectivelyNull_wins_ville
    {π : Measure CantorSeq} [IsProbabilityMeasure π] {m : BitString → ℝ}
    (hm : IsSuperfairCapital π m) {c : ℕ} (hc : 0 < c) (hinit : m [] ≤ c) (n : ℕ) :
    π {w | ∃ k, ((c * 2 ^ n : ℕ) : ℝ) < m (cantorPrefix w k)} ≤ dyadicValue 1 n := by
  have hK : (0 : ℝ) < ((c * 2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hc (by positivity)
  have hville := measure_exists_ge_le_of_superfair hm hK
  refine le_trans (measure_mono ?_) (hville.trans ?_)
  · rintro w ⟨k, hk⟩
    exact ⟨k, hk.le⟩
  · have h1 : m [] / ((c * 2 ^ n : ℕ) : ℝ) ≤ (2 : ℝ)⁻¹ ^ n := by
      rw [div_le_iff₀ hK]
      have h2 : (2 : ℝ)⁻¹ ^ n * ((c * 2 ^ n : ℕ) : ℝ) = c := by
        push_cast
        rw [inv_pow]
        field_simp
      rw [h2]
      exact hinit
    have h3 : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n) = (2 : ENNReal)⁻¹ ^ n := by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
      simp
    refine (ENNReal.ofReal_le_ofReal h1).trans ?_
    rw [h3]
    unfold dyadicValue
    rw [Nat.cast_one, div_eq_mul_inv, one_mul]
    exact ENNReal.inv_pow.symm.le

/-- Step 4 of the proof of `isEffectivelyNull_wins`: a sequence on which `m` wins (its
values on the prefixes are unbounded) has, for every `n`, a prefix on which `m` strictly exceeds
`c * 2^n`. -/
private lemma isEffectivelyNull_wins_subset {m : BitString → ℝ} (c : ℕ) :
    {w | Wins m w} ⊆ ⋂ n : ℕ,
      {w : CantorSeq | ∃ k, ((c * 2 ^ n : ℕ) : ℝ) < m (cantorPrefix w k)} := by
  intro w hw
  simp only [Wins, not_bddAbove_iff] at hw
  simp only [Set.mem_iInter]
  intro n
  obtain ⟨x, hx_mem, hx_gt⟩ := hw ((c * 2 ^ n : ℕ) : ℝ)
  obtain ⟨k, rfl⟩ := hx_mem
  exact ⟨k, hx_gt⟩

/-- **SUV Theorem 181(a), p. 278 (Schnorr).**  The sequences on which a lower semicomputable
`π`-martingale wins form an effectively null set, for computable `π`. -/
theorem isEffectivelyNull_wins {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (_hπ : IsComputableMeasure π) {m : BitString → ℝ} (hm : IsFairCapital π m)
    (hlsc : IsLowerSemicomputableOnStrings m) : IsEffectivelyNull π {w | Wins m w} := by
  obtain ⟨c, hc_pos, hc_le⟩ := isEffectivelyNull_wins_bound m
  exact ⟨_, isEffectivelyNull_wins_open hlsc c, isEffectivelyNull_wins_subset c,
    isEffectivelyNull_wins_ville hm.isSuperfairCapital hc_pos hc_le⟩


/-- Step 1 of the proof of `isEffectivelyNull_wins_of_superfair`: bounding the initial
capital by a positive integer. -/
private lemma isEffectivelyNull_wins_of_superfair_step1
    {π : Measure CantorSeq} [IsProbabilityMeasure π] {m : BitString → ℝ}
    (hm : IsSuperfairCapital π m) :
    ∃ c : ℕ, 0 < c ∧ m [] ≤ c := by
  have hm0 := hm.nonneg []
  rcases lt_or_eq_of_le hm0 with h | h
  · obtain ⟨c, hc⟩ := exists_nat_gt (m [])
    exact ⟨c, by exact_mod_cast h.trans hc, hc.le⟩
  · exact ⟨1, Nat.one_pos, by rw [← h]; norm_num⟩

/-- Step 2 of the proof of `isEffectivelyNull_wins_of_superfair`: the sequences where the
capital strictly exceeds `c * 2^n` form a uniformly effectively open set sequence. -/
private lemma isEffectivelyNull_wins_of_superfair_step2
    {m : BitString → ℝ} (hlsc : IsLowerSemicomputableOnStrings m) (c : ℕ) :
    ∃ U : ℕ → Set CantorSeq, IsUniformlyEffectiveOpen U ∧
      ∀ n, U n = {w | ∃ k, ((c * 2^n : ℕ) : ℝ) < m (cantorPrefix w k)} := by
  exact ⟨_, isEffectivelyNull_wins_open hlsc c, fun n => rfl⟩

/-- Step 3 of the proof of `isEffectivelyNull_wins_of_superfair`: the measure of sequences
where the capital strictly exceeds `c * 2^n` is bounded by `2⁻ⁿ`. -/
private lemma isEffectivelyNull_wins_of_superfair_step3
    {π : Measure CantorSeq} [IsProbabilityMeasure π] {m : BitString → ℝ}
    (hm : IsSuperfairCapital π m) {c : ℕ} (_hc : 0 < c) (hinit : m [] ≤ c) (n : ℕ) :
    π {w | ∃ k, ((c * 2^n : ℕ) : ℝ) < m (cantorPrefix w k)} ≤ dyadicValue 1 n := by
  have hK : (0 : ℝ) < ((c * 2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos _hc (by positivity)
  have hville := measure_exists_ge_le_of_superfair hm hK
  refine le_trans (measure_mono ?_) (hville.trans ?_)
  · rintro w ⟨k, hk⟩
    exact ⟨k, hk.le⟩
  · have h1 : m [] / ((c * 2 ^ n : ℕ) : ℝ) ≤ (2 : ℝ)⁻¹ ^ n := by
      rw [div_le_iff₀ hK]
      have h2 : (2 : ℝ)⁻¹ ^ n * ((c * 2 ^ n : ℕ) : ℝ) = c := by
        push_cast
        rw [inv_pow]
        field_simp
      rw [h2]
      exact hinit
    have h3 : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n) = (2 : ENNReal)⁻¹ ^ n := by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
      simp
    refine (ENNReal.ofReal_le_ofReal h1).trans ?_
    rw [h3]
    unfold dyadicValue
    rw [Nat.cast_one, div_eq_mul_inv, one_mul]
    exact ENNReal.inv_pow.symm.le

/-- Step 4 of the proof of `isEffectivelyNull_wins_of_superfair`: the winning set is
contained in the intersection of these open sets. -/
private lemma isEffectivelyNull_wins_of_superfair_step4
    {m : BitString → ℝ} {c : ℕ} (_hc : 0 < c) :
    {w | Wins m w} ⊆ ⋂ n,
      {w | ∃ k, ((c * 2^n : ℕ) : ℝ) < m (cantorPrefix w k)} := by
  intro w hw
  simp only [Wins, not_bddAbove_iff] at hw
  simp only [Set.mem_iInter]
  intro n
  obtain ⟨x, hx_mem, hx_gt⟩ := hw ((c * 2^n : ℕ) : ℝ)
  obtain ⟨k, rfl⟩ := hx_mem
  exact ⟨k, hx_gt⟩

/-- **SUV p. 278.**  Theorem 181(a) for lower semicomputable supermartingales. -/
theorem isEffectivelyNull_wins_of_superfair {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (_hπ : IsComputableMeasure π) {m : BitString → ℝ} (hm : IsSuperfairCapital π m)
    (hlsc : IsLowerSemicomputableOnStrings m) : IsEffectivelyNull π {w | Wins m w} := by
  obtain ⟨c, hc_pos, hc_le⟩ := isEffectivelyNull_wins_of_superfair_step1 hm
  obtain ⟨U, hU_open, hU_eq⟩ := isEffectivelyNull_wins_of_superfair_step2 hlsc c
  refine ⟨U, hU_open, ?_, ?_⟩
  · have h_sub := isEffectivelyNull_wins_of_superfair_step4 (m := m) hc_pos
    refine h_sub.trans ?_
    intro w hw
    simp_rw [Set.mem_iInter]
    intro n
    rw [hU_eq]
    exact (Set.mem_iInter.mp hw) n
  · intro n
    rw [hU_eq]
    exact isEffectivelyNull_wins_of_superfair_step3 hm hc_pos hc_le n


private def exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_hit
    (f : ℕ → ℕ → Option BitString) (n : ℕ) (x : BitString) : Prop :=
  n ≤ x.length ∧ ∃ i s, f n i = some s ∧ s <+: x

/-- The conditional open-set capital, with the payoff on null cylinders delayed until depth `n`.
The enumeration is an explicit argument, so the payoff uses precisely its emitted strings. -/
private noncomputable def exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital
    (π : Measure CantorSeq) (U : ℕ → Set CantorSeq)
    (f : ℕ → ℕ → Option BitString) (n : ℕ) (x : BitString) : ℝ := by
  classical
  exact if massR π x = 0 then
    if exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_hit f n x then
      (2 : ℝ) ^ n else 0
    else (2 : ℝ) ^ n * (π (U n ∩ cantorCylinder x)).toReal / massR π x

/-- Step 1 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_martingales`: an enumerated prefix of `x`
certifies that its cylinder is contained in the open set. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_subset
    {U : ℕ → Set CantorSeq} {f : ℕ → ℕ → Option BitString}
    (hfU : ∀ n, U n = ⋃ i, (f n i).elim ∅ cantorCylinder) {n : ℕ} {x : BitString}
    (hx : exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_hit f n x) :
    cantorCylinder x ⊆ U n := by
  obtain ⟨_, i, s, hs, hsx⟩ := hx
  rw [hfU n]
  refine (cantorCylinder_subset_of_prefix hsx).trans ?_
  exact Set.subset_iUnion_of_subset i (by rw [hs]; exact Set.Subset.rfl)

/-- Step 2 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_martingales`: multiplication by the
cylinder mass removes the quotient, including on null cylinders, and gives fairness. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_fair
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (U : ℕ → Set CantorSeq) (f : ℕ → ℕ → Option BitString) :
    ∀ n, IsFairCapital π
      (exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital π U f n) := by
  classical
  intro n
  have hmul : ∀ x,
      exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital π U f n x *
        massR π x = (2 : ℝ) ^ n * (π (U n ∩ cantorCylinder x)).toReal := by
    intro x
    by_cases hx : massR π x = 0
    · have hzero : π (cantorCylinder x) = 0 :=
        by simpa [massR, cantorMass, ENNReal.toReal_eq_zero_iff, measure_ne_top] using hx
      have hint : π (U n ∩ cantorCylinder x) = 0 :=
        measure_mono_null Set.inter_subset_right hzero
      simp [exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital, hx, hint]
    · simp [exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital, hx]
  refine ⟨?_, ?_⟩
  · intro x
    have hx : 0 ≤ massR π x := ENNReal.toReal_nonneg
    unfold exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital
    split_ifs <;> positivity
  · intro x
    rw [hmul, hmul, hmul, ← mul_add]
    congr 1
    have hadd := cantorMass_add (π.restrict (U n)) x
    have heq : ∀ y, cantorMass (π.restrict (U n)) y = π (U n ∩ cantorCylinder y) := by
      intro y
      rw [cantorMass, Measure.restrict_apply (measurableSet_cantorCylinder y), Set.inter_comm]
    simp only [heq] at hadd
    rw [hadd, ENNReal.toReal_add (measure_ne_top π _) (measure_ne_top π _)]

/-- Step 3 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_martingales`: the measure bound gives
initial capital at most one. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_root
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {U : ℕ → Set CantorSeq} (hU_meas : ∀ n, π (U n) ≤ dyadicValue 1 n)
    (f : ℕ → ℕ → Option BitString) :
    ∀ n, exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital π U f n [] ≤ 1 := by
  intro n
  have hroot : massR π [] = 1 := by simp [massR, cantorMass, cantorCylinder_nil_eq]
  have hbound : (π (U n)).toReal ≤ ((2 : ℝ) ^ n)⁻¹ := by
    have h := ENNReal.toReal_mono (by simp [dyadicValue]) (hU_meas n)
    simpa [dyadicValue, ENNReal.toReal_div, ENNReal.toReal_pow] using h
  simp only [exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital,
    hroot, one_ne_zero, ↓reduceIte, cantorCylinder_nil_eq, Set.inter_univ, div_one]
  calc (2 : ℝ) ^ n * (π (U n)).toReal ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ n)⁻¹ := by
         gcongr
    _ = 1 := mul_inv_cancel₀ (by positivity)

/-- Step 4 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_martingales`: the delayed payoff vanishes
on null cylinders of length less than the component index. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_null
    (π : Measure CantorSeq) (U : ℕ → Set CantorSeq) (f : ℕ → ℕ → Option BitString) :
    ∀ n x, massR π x = 0 → x.length < n →
      exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital π U f n x = 0 := by
  intro n x hx hn
  simp [exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital, hx,
    exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_hit, not_le.mpr hn]

/-- Step 5 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_martingales`: after an enumerated cylinder
has been reached and the depth is at least `n`, the capital stays equal to `2^n`. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_wins
    {π : Measure CantorSeq} {U : ℕ → Set CantorSeq} {f : ℕ → ℕ → Option BitString}
    (hfU : ∀ n, U n = ⋃ i, (f n i).elim ∅ cantorCylinder) :
    ∀ n, ∀ w ∈ U n, ∃ k, ∀ l, k ≤ l →
      (2 : ℝ) ^ n ≤
        exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital π U f n
          (cantorPrefix w l) := by
  classical
  intro n w hw
  rw [hfU n, Set.mem_iUnion] at hw
  obtain ⟨i, hi⟩ := hw
  cases hfi : f n i with
  | none => simp [hfi] at hi
  | some s =>
    change w ∈ (f n i).elim ∅ cantorCylinder at hi
    rw [hfi] at hi
    change IsCantorPrefix s w at hi
    refine ⟨max n s.length, ?_⟩
    intro l hl
    have hn : n ≤ l := (le_max_left _ _).trans hl
    have hs : s.length ≤ l := (le_max_right _ _).trans hl
    have hpre : s <+: cantorPrefix w l := by
      rw [List.prefix_iff_eq_take, cantorPrefix_take w s.length l hs]
      exact ((isCantorPrefix_iff_cantorPrefix_eq s w).mp hi).symm
    have hhit : exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_hit f n
        (cantorPrefix w l) := ⟨by simpa using hn, i, s, hfi, hpre⟩
    have hsub :=
      exists_lsc_stronglyWins_of_isEffectivelyNull_subset hfU hhit
    have hint : U n ∩ cantorCylinder (cantorPrefix w l) = cantorCylinder (cantorPrefix w l) :=
      Set.inter_eq_right.mpr hsub
    unfold exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital
    split_ifs with hx
    · simp
    · rw [hint]
      change (2 : ℝ) ^ n ≤ (2 : ℝ) ^ n * massR π (cantorPrefix w l) /
        massR π (cantorPrefix w l)
      rw [mul_div_cancel_right₀ _ hx]

/-- The (possibly empty) cylinder obtained by intersecting two cylinders. -/
private def exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_inter
    (s x : BitString) : Option BitString :=
  if s <+: x then some x else if x <+: s then some s else none

/-- Step 6 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_martingales`: prefix tests on finite strings
are computable. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_prefix :
    Computable₂ (fun s x : BitString => decide (s <+: x)) := by
  have htake : Primrec (fun p : BitString × BitString => p.2.take p.1.length) :=
    Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd
  have h : Primrec (fun p : BitString × BitString => decide (p.1 = p.2.take p.1.length)) :=
    primrec_decideEq.comp Primrec.fst htake
  exact h.to_comp.of_eq (fun p => by simp only [List.prefix_iff_eq_take])

/-- Step 7 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_martingales`: cylinder intersection is a
computable operation on its two string parameters. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_inter_comp :
    Computable₂ exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_inter := by
  have hp := exists_lsc_stronglyWins_of_isEffectivelyNull_prefix
  refine (Computable.cond hp
    (Primrec.option_some.to_comp.comp Computable.snd)
    (Computable.cond (hp.comp Computable.snd Computable.fst)
      (Primrec.option_some.to_comp.comp Computable.fst) (Computable.const none))).of_eq ?_
  intro p
  simp [exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_inter]

/-- Step 8 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_martingales`: the computed intersection
has exactly the measure of the intersection of the original cylinders. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_inter_mass
    (π : Measure CantorSeq) (s x : BitString) :
    (exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_inter s x).elim 0
      (cantorMass π) = π (cantorCylinder s ∩ cantorCylinder x) := by
  unfold exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_inter
  split_ifs with hs hx
  · rw [cantorCylinder_inter_of_prefix hs]
    rfl
  · rw [Set.inter_comm, cantorCylinder_inter_of_prefix hx]
    rfl
  · rw [(cantorCylinder_disjoint_of_incompatible hs hx).inter_eq]
    simp

/-- Step 9 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_martingales`: disjointify the enumeration,
intersect each emitted cylinder with `Ω_x`, and sum its uniformly computable lower
approximations. This supplies a single monotone dyadic approximation to `π(U_n ∩ Ω_x)`. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_mass_lsc
    {π : Measure CantorSeq} (hπ : IsComputableMeasure π)
    {U : ℕ → Set CantorSeq} {f : ℕ → ℕ → Option BitString} (hf : Computable₂ f)
    (hfU : ∀ n, U n = ⋃ i, (f n i).elim ∅ cantorCylinder) :
    ∃ A : ℕ → ℕ → BitString → ℕ,
      Computable (fun p : ℕ × ℕ × BitString => A p.1 p.2.1 p.2.2) ∧
      (∀ s n x, dyadicValue (A s n x) s ≤ dyadicValue (A (s + 1) n x) (s + 1)) ∧
      (∀ n x, ⨆ s, dyadicValue (A s n x) s = π (U n ∩ cantorCylinder x)) := by
  obtain ⟨M, hMmono, hMsup, hMcomp⟩ := isLSC_cantorMass hπ
  let N : BitString → ℕ := fun z => (Nat.unpair (bitStringToNat z)).1
  let X : BitString → BitString := fun z => natToBitString (Nat.unpair (bitStringToNat z)).2
  have hN : Computable N :=
    (Primrec.fst.comp Primrec.unpair).to_comp.comp computable_bitStringToNat
  have hX : Computable X := computable_natToBitString.comp
    ((Primrec.snd.comp Primrec.unpair).to_comp.comp computable_bitStringToNat)
  let G : ℕ → BitString → Option BitString := fun i z =>
    (disjEnum (f (N z)) i).bind fun s =>
      exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_inter s (X z)
  have hG : Computable₂ G := by
    apply Computable.option_bind
      ((computable_disjEnum hf).comp (hN.comp Computable.snd) Computable.fst)
    exact exists_lsc_stronglyWins_of_isEffectivelyNull_inter_comp.comp
      Computable.snd (hX.comp (Computable.snd.comp Computable.fst))
  let T : ℕ → ℕ → BitString → ℕ := fun i s z =>
    if (G i z).isSome then M s ((G i z).getD []) [] else 0
  have hTmono : ∀ i s z,
      dyadicValue (T i s z) s ≤ dyadicValue (T i (s + 1) z) (s + 1) := by
    intro i s z
    dsimp only [T]
    split_ifs
    · exact hMmono s _ []
    · simp [dyadicValue]
  have hTsup : ∀ i z, ⨆ s, dyadicValue (T i s z) s =
      (G i z).elim 0 (cantorMass π) := by
    intro i z
    cases hg : G i z with
    | none => simp [T, hg, dyadicValue]
    | some y => simpa [T, hg] using hMsup y []
  have hTcomp : Computable (fun p : ℕ × ℕ × BitString => T p.1 p.2.1 p.2.2) := by
    have hg : Computable (fun p : ℕ × ℕ × BitString => G p.1 p.2.2) :=
      hG.comp Computable.fst (Computable.snd.comp Computable.snd)
    have hsome := Primrec.option_isSome.to_comp.comp hg
    have hget := Primrec.option_getD.to_comp.comp hg (Computable.const [])
    have hval := hMcomp.comp ((Computable.fst.comp Computable.snd).pair
      (hget.pair (Computable.const [])))
    exact (Computable.cond hsome hval (Computable.const 0)).of_eq (fun _ => by simp [T])
  have hsum : ∀ z, ∑' i, (G i z).elim 0 (cantorMass π) =
      π (U (N z) ∩ cantorCylinder (X z)) := by
    intro z
    calc ∑' i, (G i z).elim 0 (cantorMass π)
        = ∑' i, (disjEnum (f (N z)) i).elim 0
            (cantorMass (π.restrict (cantorCylinder (X z)))) := by
          refine tsum_congr fun i => ?_
          cases hd : disjEnum (f (N z)) i with
          | none => simp [G, hd]
          | some y =>
            simp only [G, hd, Option.bind_some, Option.elim_some]
            rw [exists_lsc_stronglyWins_of_isEffectivelyNull_inter_mass,
              cantorMass, Measure.restrict_apply (measurableSet_cantorCylinder y)]
      _ = (π.restrict (cantorCylinder (X z))) (⋃ j, coverSet (f (N z)) j) :=
          tsum_measure_disjEnum _ _
      _ = π (U (N z) ∩ cantorCylinder (X z)) := by
          change (π.restrict (cantorCylinder (X z)))
            (⋃ j, (f (N z) j).elim ∅ cantorCylinder) = _
          rw [← hfU (N z)]
          have hmeas : MeasurableSet (U (N z)) :=
            IsEffectiveOpen.measurableSet ⟨f (N z),
              hf.comp (Computable.const _) Computable.id, hfU (N z)⟩
          rw [Measure.restrict_apply hmeas]
  obtain ⟨B, hBmono, hBsup, hBcomp⟩ :=
    isLSC_tsum_nsmul_of_uniform (Computable.const 1) hTmono hTsup hTcomp
  refine ⟨fun s n x => B s (natPairCode n (bitStringToNat x)) [], ?_, ?_, ?_⟩
  · exact hBcomp.comp (Computable.fst.pair
      (((computable_natPairCode.comp (Computable.fst.comp Computable.snd)
        (computable_bitStringToNat.comp (Computable.snd.comp Computable.snd))).pair
          (Computable.const []))))
  · intro s n x
    exact hBmono s _ []
  · intro n x
    simpa [hsum, N, X, natPairCode] using hBsup (natPairCode n (bitStringToNat x)) []

/-- Step 10 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_martingales`: a finite-stage integer
comparison certifies the strict comparison between a rational multiple of the cylinder mass
and the scaled open-set intersection mass. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_stage
    {π : Measure CantorSeq} [IsFiniteMeasure π]
    {U : ℕ → Set CantorSeq} {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass π x + dyadicValue 1 s ∧
      cantorMass π x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {A : ℕ → ℕ → BitString → ℕ}
    (hAmono : ∀ s n x, dyadicValue (A s n x) s ≤ dyadicValue (A (s + 1) n x) (s + 1))
    (hAsup : ∀ n x, ⨆ s, dyadicValue (A s n x) s = π (U n ∩ cantorCylinder x))
    (q : ℚ) (hq : 0 ≤ q) (n : ℕ) (x : BitString) :
    (∃ s, q.num.toNat * (a x s + 1) < (2 ^ n * A s n x) * q.den) ↔
      (q : ℝ) * massR π x < (2 : ℝ) ^ n * (π (U n ∩ cantorCylinder x)).toReal := by
  have hmono : ∀ (s : ℕ) (out ctx : BitString),
      dyadicValue (2 ^ n * A s n out) s ≤ dyadicValue (2 ^ n * A (s + 1) n out) (s + 1) := by
    intro s out ctx
    simp only [dyadicValue_natCast_mul_left]
    exact mul_le_mul_of_nonneg_left (hAmono s n out) zero_le
  have hsup : ∀ out ctx : BitString, ⨆ s, dyadicValue (2 ^ n * A s n out) s =
      (2 : ENNReal) ^ n * π (U n ∩ cantorCylinder out) := by
    intro out ctx
    simp only [dyadicValue_natCast_mul_left, Nat.cast_pow, Nat.cast_ofNat]
    rw [← ENNReal.mul_iSup, hAsup]
  have h := exists_stage_iff_ofReal_lt_ratio ha
    (mApprox := fun s out (_ : BitString) => 2 ^ n * A s n out) hmono hsup hq x
  have hPne : cantorMass π x ≠ ⊤ := measure_ne_top π _
  rw [ENNReal.lt_div_iff_mul_lt (Or.inr ENNReal.ofReal_ne_top)
    (Or.inl hPne)] at h
  rw [← ENNReal.toReal_lt_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPne)
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) (measure_ne_top π _))] at h
  have hqr : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hqr, ENNReal.toReal_pow, massR] using h

/-- Step 11 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_martingales`: the delayed prefix-hit
predicate is recursively enumerable uniformly in the component and string. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_hit_re
    {f : ℕ → ℕ → Option BitString} (hf : Computable₂ f) :
    IsRE (fun p : ℕ × BitString =>
      exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_hit f p.1 p.2) := by
  have hF : Computable (fun p : (ℕ × BitString) × ℕ => f p.1.1 p.2) :=
    hf.comp (Computable.fst.comp Computable.fst) Computable.snd
  have hget := Primrec.option_getD.to_comp.comp hF (Computable.const [])
  have hcheck : Computable (fun p : (ℕ × BitString) × ℕ =>
      (f p.1.1 p.2).isSome && decide ((f p.1.1 p.2).getD [] <+: p.1.2)) :=
    Primrec.and.to_comp.comp (Primrec.option_isSome.to_comp.comp hF)
      (exists_lsc_stronglyWins_of_isEffectivelyNull_prefix.comp
        hget (Computable.snd.comp Computable.fst))
  have hbase : IsRE (fun p : ℕ × BitString => ∃ i,
      ((f p.1 i).isSome && decide ((f p.1 i).getD [] <+: p.2)) = true) :=
    IsRE.exists_encodable (isRE_of_computable_bool _ _ (fun _ => Iff.rfl) hcheck)
  have hlen : Computable (fun p : ℕ × BitString => decide (p.1 ≤ p.2.length)) :=
    (PrimrecPred.decide (Primrec.nat_le.comp Primrec.fst
      (Primrec.list_length.comp Primrec.snd))).to_comp
  refine (hbase.and_computable hlen).of_iff fun p => ?_
  simp only [decide_eq_true_iff]
  constructor
  · rintro ⟨hn, i, hi⟩
    refine ⟨hn, i, ?_⟩
    cases hfi : f p.1 i with
    | none => simp [hfi] at hi
    | some s => exact ⟨s, rfl, by simpa [hfi] using hi⟩
  · rintro ⟨hn, i, s, hs, hsx⟩
    exact ⟨hn, i, by simp [hs, hsx]⟩

/-- Step 12 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_martingales`: the capital's strict lower
graph is the union of negative thresholds, certified delayed payoffs, and strict comparisons
of the scaled intersection mass with the rational multiple of the cylinder mass. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_lower_iff
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {U : ℕ → Set CantorSeq} {f : ℕ → ℕ → Option BitString}
    (hfU : ∀ n, U n = ⋃ i, (f n i).elim ∅ cantorCylinder)
    (q : ℚ) (n : ℕ) (x : BitString) :
    (q : ℝ) <
        exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital π U f n x ↔
      q < 0 ∨
        (q < (2 : ℚ) ^ n ∧
          exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_hit f n x) ∨
        (q : ℝ) * massR π x < (2 : ℝ) ^ n * (π (U n ∩ cantorCylinder x)).toReal := by
  classical
  have hnonneg :=
    (exists_lsc_stronglyWins_of_isEffectivelyNull_fair
      (π := π) U f n).nonneg x
  have hmass : 0 ≤ massR π x := ENNReal.toReal_nonneg
  have hzero : massR π x = 0 → π (U n ∩ cantorCylinder x) = 0 := by
    intro hx
    have hπx : π (cantorCylinder x) = 0 := by
      simpa [massR, cantorMass, ENNReal.toReal_eq_zero_iff, measure_ne_top] using hx
    exact measure_mono_null Set.inter_subset_right hπx
  constructor
  · intro hq
    by_cases hneg : q < 0
    · exact Or.inl hneg
    right
    by_cases hx : massR π x = 0
    · left
      have hhit : exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_hit f n x := by
        by_contra hhit
        simp only [exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital,
          hx, ↓reduceIte, hhit] at hq
        exact hneg (by exact_mod_cast hq)
      refine ⟨?_, hhit⟩
      exact_mod_cast (by simpa
        [exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital, hx, hhit]
        using hq : (q : ℝ) < (2 : ℝ) ^ n)
    · right
      apply (lt_div_iff₀ (lt_of_le_of_ne hmass (Ne.symm hx))).mp
      simpa [exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital, hx] using hq
  · rintro (hneg | ⟨hq, hhit⟩ | hq)
    · exact lt_of_lt_of_le (by exact_mod_cast hneg) hnonneg
    · have hsub :=
        exists_lsc_stronglyWins_of_isEffectivelyNull_subset hfU hhit
      have hint := Set.inter_eq_right.mpr hsub
      have hqr : (q : ℝ) < (2 : ℝ) ^ n := by exact_mod_cast hq
      unfold exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital
      split_ifs with hx
      · simpa [hhit] using hqr
      · rw [hint]
        change (q : ℝ) < (2 : ℝ) ^ n * massR π x / massR π x
        rwa [mul_div_cancel_right₀ _ hx]
    · by_cases hx : massR π x = 0
      · simp [hx, hzero hx] at hq
      · unfold exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital
        rw [ite_eq_right hx]
        exact (lt_div_iff₀ (lt_of_le_of_ne hmass (Ne.symm hx))).mpr hq

/-- Step 13 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_martingales`: the rational strict lower
graph of the explicitly defined conditional capitals is enumerable uniformly in `n`. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_lsc
    {π : Measure CantorSeq} [IsProbabilityMeasure π] (hπ : IsComputableMeasure π)
    {U : ℕ → Set CantorSeq} {f : ℕ → ℕ → Option BitString} (hf : Computable₂ f)
    (hfU : ∀ n, U n = ⋃ i, (f n i).elim ∅ cantorCylinder) :
    IsRE (fun p : ℚ × ℕ × BitString => (p.1 : ℝ) <
      exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital π U f
        p.2.1 p.2.2) := by
  obtain ⟨A, hAcomp, hAmono, hAsup⟩ :=
    exists_lsc_stronglyWins_of_isEffectivelyNull_mass_lsc hπ hf hfU
  obtain ⟨a, hacomp, ha⟩ := hπ
  have hnegC : Computable (fun p : ℚ × ℕ × BitString => decide (p.1 < 0)) :=
    computable₂_ratLt.comp Computable.fst (Computable.const 0)
  have hneg : IsRE (fun p : ℚ × ℕ × BitString => p.1 < 0) :=
    isRE_of_computable_bool _ _ (fun _ => by simp) hnegC
  have hhit : IsRE (fun p : ℚ × ℕ × BitString =>
      exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_hit f p.2.1 p.2.2) :=
    IsRE.comp_computable
      (exists_lsc_stronglyWins_of_isEffectivelyNull_hit_re hf)
      Computable.snd
  have hpow : Computable (fun p : ℚ × ℕ × BitString => ((2 ^ p.2.1 : ℕ) : ℚ)) :=
    computable_nat_to_rat.comp
      (primrec_two_pow_aux.to_comp.comp (Computable.fst.comp Computable.snd))
  have hpay : IsRE (fun p : ℚ × ℕ × BitString => p.1 < (2 : ℚ) ^ p.2.1 ∧
      exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_hit f p.2.1 p.2.2) :=
    (hhit.and_computable (computable₂_ratLt.comp Computable.fst hpow)).of_iff
      (fun p => by simp)
  have hq : Computable (fun r : (ℚ × ℕ × BitString) × ℕ => r.1.1) :=
    Computable.fst.comp Computable.fst
  have hn : Computable (fun r : (ℚ × ℕ × BitString) × ℕ => r.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hx : Computable (fun r : (ℚ × ℕ × BitString) × ℕ => r.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hnum := ComputableReals.primrec_intToNat.to_comp.comp (computable_ratNum.comp hq)
  have hden := computable_ratDen.comp hq
  have haS : Computable (fun r : (ℚ × ℕ × BitString) × ℕ => a r.1.2.2 r.2 + 1) :=
    Primrec.succ.to_comp.comp (hacomp.comp hx Computable.snd)
  have hAS : Computable (fun r : (ℚ × ℕ × BitString) × ℕ => A r.2 r.1.2.1 r.1.2.2) :=
    hAcomp.comp (Computable.snd.pair (hn.pair hx))
  have hmul : Computable₂ (fun i j : ℕ => i * j) := Primrec.nat_mul.to_comp
  have hlt : Computable₂ (fun i j : ℕ => decide (i < j)) := primrec_decide_nat_lt.to_comp
  have hcheck : Computable (fun r : (ℚ × ℕ × BitString) × ℕ =>
      decide (r.1.1.num.toNat * (a r.1.2.2 r.2 + 1) <
        (2 ^ r.1.2.1 * A r.2 r.1.2.1 r.1.2.2) * r.1.1.den)) :=
    hlt.comp (hmul.comp hnum haS)
      (hmul.comp (hmul.comp (primrec_two_pow_aux.to_comp.comp hn) hAS) hden)
  have hstage : IsRE (fun p : ℚ × ℕ × BitString => ∃ s,
      p.1.num.toNat * (a p.2.2 s + 1) < (2 ^ p.2.1 * A s p.2.1 p.2.2) * p.1.den) :=
    IsRE.exists_encodable (isRE_of_computable_bool _ _ (fun _ => by simp) hcheck)
  refine (hneg.or (hpay.or hstage)).of_iff fun p => ?_
  rw [exists_lsc_stronglyWins_of_isEffectivelyNull_lower_iff hfU]
  by_cases hq : p.1 < 0
  · simp [hq]
  · rw [exists_lsc_stronglyWins_of_isEffectivelyNull_stage ha
      hAmono hAsup p.1 (le_of_not_gt hq) p.2.1 p.2.2]

/-- Step 1 of the proof of `exists_lsc_stronglyWins_of_isEffectivelyNull`:
construct individual martingales. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_martingales
    {π : Measure CantorSeq} [IsProbabilityMeasure π] (hπ : IsComputableMeasure π)
    {U : ℕ → Set CantorSeq} (hU : IsUniformlyEffectiveOpen U)
    (hU_meas : ∀ n, π (U n) ≤ dyadicValue 1 n) :
    ∃ m : ℕ → BitString → ℝ,
      (∀ n, IsFairCapital π (m n)) ∧
      (∀ n, m n [] ≤ 1) ∧
      (IsRE (fun p : ℚ × ℕ × BitString => (p.1 : ℝ) < m p.2.1 p.2.2)) ∧
      (∀ n x, massR π x = 0 → x.length < n → m n x = 0) ∧
      (∀ n, ∀ w ∈ U n, ∃ k, ∀ l, k ≤ l →
        (2 : ℝ)^n ≤ m n (cantorPrefix w l)) := by
  obtain ⟨f, hf, hfU⟩ := hU
  exact ⟨exists_lsc_stronglyWins_of_isEffectivelyNull_martingales_capital π U f,
    exists_lsc_stronglyWins_of_isEffectivelyNull_fair U f,
    exists_lsc_stronglyWins_of_isEffectivelyNull_root hU_meas f,
    exists_lsc_stronglyWins_of_isEffectivelyNull_lsc hπ hf hfU,
    exists_lsc_stronglyWins_of_isEffectivelyNull_null π U f,
    exists_lsc_stronglyWins_of_isEffectivelyNull_wins hfU⟩


private noncomputable def exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1) ^ 2

private noncomputable def exists_lsc_stronglyWins_of_isEffectivelyNull_sum_M
    (m : ℕ → BitString → ℝ) (x : BitString) : ℝ :=
  ∑' n, exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c n * m n x

/-- Step 1 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_sum_fair`: the mass-weighted
capital at any node is at most the initial capital. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_bound
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : BitString → ℝ} (hm : IsFairCapital π m) (x : BitString) :
    m x * massR π x ≤ m [] := by
  induction x using List.reverseRecOn with
  | nil => simp [massR, cantorMass, cantorCylinder_nil_eq]
  | append_singleton x b ih =>
    refine le_trans ?_ ih
    have hf := hm.fair x
    have h0 := mul_nonneg (hm.nonneg (x ++ [false]))
      (show 0 ≤ massR π (x ++ [false]) from ENNReal.toReal_nonneg)
    have h1 := mul_nonneg (hm.nonneg (x ++ [true]))
      (show 0 ≤ massR π (x ++ [true]) from ENNReal.toReal_nonneg)
    cases b <;> linarith

/-- Step 2 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_sum_fair`: the weighted capitals
are summable at every string, by comparison with the square reciprocal series on positive
cylinders and by finite support on null cylinders. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_summable
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : ℕ → BitString → ℝ} (hm : ∀ n, IsFairCapital π (m n))
    (hbound : ∀ n, m n [] ≤ 1)
    (hnull : ∀ n x, massR π x = 0 → x.length < n → m n x = 0) (x : BitString) :
    Summable (fun n => exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c n * m n x) := by
  by_cases hx : massR π x = 0
  · refine summable_of_ne_finset_zero (s := Finset.range (x.length + 1)) ?_
    intro n hn
    have hlen : x.length < n := by simpa using hn
    rw [hnull n x hx hlen, mul_zero]
  · have hx_pos : 0 < massR π x :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hx)
    have h_bound : ∀ n, m n x ≤ 1 / massR π x := by
      intro n
      apply (le_div_iff₀ hx_pos).mpr
      exact (exists_lsc_stronglyWins_of_isEffectivelyNull_bound
        (hm n) x).trans (hbound n)
    have hc : ∀ n, 0 ≤ exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c n := by
      intro n
      unfold exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c
      positivity
    have hsum : Summable exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c := by
      have h := (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (show 1 < 2 by norm_num))
      apply Summable.congr h
      intro n
      simp only [exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c,
        Nat.cast_add, Nat.cast_one]
    exact Summable.of_nonneg_of_le (fun n => mul_nonneg (hc n) ((hm n).nonneg x))
      (fun n => mul_le_mul_of_nonneg_left (h_bound n) (hc n))
      (hsum.mul_right (1 / massR π x))

/-- Step 1 of the proof of `exists_lsc_stronglyWins_of_isEffectivelyNull_sum`:
sum of fair capitals is fair -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_sum_fair
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : ℕ → BitString → ℝ} (hm : ∀ n, IsFairCapital π (m n))
    (hbound : ∀ n, m n [] ≤ 1)
    (hnull : ∀ n x, massR π x = 0 → x.length < n → m n x = 0) :
    IsFairCapital π (exists_lsc_stronglyWins_of_isEffectivelyNull_sum_M m) := by
  have hs :=
    exists_lsc_stronglyWins_of_isEffectivelyNull_summable
      hm hbound hnull
  refine ⟨?_, ?_⟩
  · intro x
    apply tsum_nonneg
    intro n
    refine mul_nonneg ?_ ((hm n).nonneg x)
    unfold exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c
    positivity
  · intro x
    let f : ℕ → BitString → ℝ := fun n y =>
      exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c n * m n y
    change (∑' n, f n x) * massR π x =
      (∑' n, f n (x ++ [false])) * massR π (x ++ [false]) +
      (∑' n, f n (x ++ [true])) * massR π (x ++ [true])
    rw [← tsum_mul_right]
    calc
      _ = ∑' n, (f n (x ++ [false]) * massR π (x ++ [false]) +
          f n (x ++ [true]) * massR π (x ++ [true])) := by
        apply tsum_congr
        intro n
        dsimp [f]
        simp only [mul_assoc, (hm n).fair x, mul_add]
      _ = _ := by
        rw [((hs (x ++ [false])).mul_right
          (massR π (x ++ [false]))).tsum_add
          ((hs (x ++ [true])).mul_right (massR π (x ++ [true])))]
        rw [tsum_mul_right, tsum_mul_right]


/-- Step 1 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_step2_sum_step2_lsc`: term nonnegativity. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_nonneg
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : ℕ → BitString → ℝ} (hm : ∀ n, IsFairCapital π (m n)) :
    ∀ n x, 0 ≤ exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c n * m n x := by
  intro n x
  have h1 : 0 ≤ exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c n := by
    unfold exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c; positivity
  have h2 : 0 ≤ m n x := (hm n).nonneg x
  positivity

private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_summable_massR_nil
    (π : Measure CantorSeq) [IsProbabilityMeasure π] : massR π [] = 1 := by
  have hcyl : cantorCylinder [] = Set.univ := by
    ext w
    simp [cantorCylinder, IsCantorPrefix]
  simp [massR, cantorMass, hcyl]

private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_summable_isFairCapital_mul_massR_le
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : BitString → ℝ} (hm : IsFairCapital π m) (x : BitString) :
    m x * massR π x ≤ m [] := by
  induction x using List.reverseRecOn with
  | nil =>
    rw [exists_lsc_stronglyWins_of_isEffectivelyNull_summable_massR_nil]
    ring_nf
    exact le_rfl
  | append_singleton y b ih =>
    refine le_trans ?_ ih
    have hf := hm.fair y
    have h1 := hm.nonneg (y ++ [false])
    have h2 := hm.nonneg (y ++ [true])
    have p1 : 0 ≤ massR π (y ++ [false]) := ENNReal.toReal_nonneg
    have p2 : 0 ≤ massR π (y ++ [true]) := ENNReal.toReal_nonneg
    cases b
    · linarith [mul_nonneg h2 p2]
    · linarith [mul_nonneg h1 p1]

/-- Step 2 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_step2_sum_step2_lsc`: term summability. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_lsc_summable
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : ℕ → BitString → ℝ} (hm : ∀ n, IsFairCapital π (m n))
    (hbound : ∀ n, m n [] ≤ 1)
    (hnull : ∀ n x, massR π x = 0 → x.length < n → m n x = 0) :
    ∀ x, Summable (fun n => exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c n * m n x) :=
        by
  intro x
  by_cases hx : massR π x = 0
  · -- finitely supported
    have hsupp : ∀ n > x.length, exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c n * m n x
        = 0 := by
      intro n hn
      rw [hnull n x hx hn, mul_zero]
    refine summable_of_ne_finset_zero (s := Finset.range (x.length + 1)) ?_
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    exact hsupp n hn
  · -- bounded
    have hx_pos : 0 < massR π x := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hx)
    have h_bound : ∀ n, m n x ≤ 1 / massR π x := by
      intro n
      have h1 := exists_lsc_stronglyWins_of_isEffectivelyNull_summable_isFairCapital_mul_massR_le
          (hm n) x
      have h2 := hbound n
      have h3 : m n x * massR π x ≤ 1 := le_trans h1 h2
      rw [le_div_iff₀ hx_pos]
      linarith
    have h_c_nonneg : ∀ n, 0 ≤ exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c n := fun n
        => by
      dsimp [exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c]
      positivity
    have h_m_nonneg : ∀ n, 0 ≤ m n x := fun n => (hm n).nonneg x
    have h_le : ∀ n, exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c n * m n x ≤
        exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c n * (1 / massR π x) := by
      intro n
      exact mul_le_mul_of_nonneg_left (h_bound n) (h_c_nonneg n)
    have h_sum_c : Summable exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c := by
      have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      have h' := (summable_nat_add_iff 1).mpr h
      apply Summable.congr h'
      intro n
      dsimp [exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c]
      push_cast
      rfl
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (h_c_nonneg n) (h_m_nonneg n)) h_le
    exact Summable.mul_right _ h_sum_c

/-- Step 3 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_step2_sum_step2_lsc`: term lsc. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_term_lsc
    {m : ℕ → BitString → ℝ}
    (hlsc : IsRE (fun p : ℚ × ℕ × BitString => (p.1 : ℝ) < m p.2.1 p.2.2)) :
    IsRE (fun p : ℚ × ℕ × BitString => (p.1 : ℝ) <
        exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c p.2.1 * m p.2.1 p.2.2) := by
  have hn : Computable (fun p : ℚ × ℕ × BitString => (((p.2.1 : ℚ) + 1) ^ 2)) := by
    have h1 : Computable (fun p : ℚ × ℕ × BitString => ((p.2.1 : ℚ) + 1)) :=
      computable₂_ratAdd.comp (computable_nat_to_rat.comp (Computable.fst.comp Computable.snd))
        (Computable.const (1 : ℚ))
    exact computable₂_ratMul.comp h1 h1 |>.of_eq fun p => by ring
  have hg : Computable (fun p : ℚ × ℕ × BitString =>
      (p.1 * (((p.2.1 : ℚ) + 1) ^ 2), p.2.1, p.2.2)) :=
    (computable₂_ratMul.comp Computable.fst hn).pair Computable.snd
  refine IsRE.of_iff (IsRE.compComputable hlsc hg) (fun p => ?_)
  obtain ⟨q, n, x⟩ := p
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  simp only [exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c]
  push_cast
  rw [one_div, ← div_eq_inv_mul, lt_div_iff₀ hpos]

/-- Step 4 of the proof of
`exists_lsc_stronglyWins_of_isEffectivelyNull_step2_sum_step2_lsc`: sum of LSC is LSC. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_iff
    (f : ℕ → BitString → ℝ) (hf_nonneg : ∀ i y, 0 ≤ f i y)
    (hf_sum : ∀ y, Summable (fun i => f i y)) (y : BitString) (r : ℚ) :
    (r : ℝ) < ∑' i, f i y ↔
    ∃ (N : ℕ) (l : List ℚ) (hl : l.length = N),
      (∀ i : Fin N, (l[i.1] : ℝ) < f i.1 y) ∧
      (r : ℝ) < ∑ i : Fin N, (l[i.1] : ℝ) := by
  classical
  constructor
  · intro hr
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (r : ℝ) < ∑ i ∈ Finset.range N, f i y :=
      ((hf_sum y).hasSum.tendsto_sum_nat.eventually_const_lt hr).exists
    let S : ℝ := ∑ i ∈ Finset.range N, f i y
    let ε : ℝ := (S - r) / ((N : ℝ) + 1)
    have hεpos : 0 < ε := div_pos (sub_pos.mpr hN) (by positivity)
    have hεN : ε * ((N : ℝ) + 1) = S - r := by
      dsimp only [ε]
      exact div_mul_cancel₀ _ (by positivity)
    have hq : ∀ i : ℕ, ∃ q : ℚ, f i y - ε < (q : ℝ) ∧ (q : ℝ) < f i y :=
      fun i => exists_rat_btwn (by linarith)
    choose q hq1 hq2 using hq
    refine ⟨N, List.ofFn (fun i : Fin N => q i.1), List.length_ofFn, ?_, ?_⟩
    · intro i
      simpa only [List.getElem_ofFn] using hq2 i.1
    · simp only [List.getElem_ofFn]
      have hle : ∑ i : Fin N, (f i.1 y - ε) ≤ ∑ i : Fin N, (q i.1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (hq1 i.1).le)
      rw [Finset.sum_sub_distrib, Fin.sum_univ_eq_sum_range (fun i => f i y) N,
        Fin.sum_const, nsmul_eq_mul] at hle
      change S - (N : ℝ) * ε ≤ _ at hle
      nlinarith
  · rintro ⟨N, l, hl, hlt, hr⟩
    apply lt_of_lt_of_le hr
    calc
      ∑ i : Fin N, (l[i.1] : ℝ) ≤ ∑ i : Fin N, f i.1 y :=
        Finset.sum_le_sum (fun i _ => (hlt i).le)
      _ = ∑ i ∈ Finset.range N, f i y := Fin.sum_univ_eq_sum_range (fun i => f i y) N
      _ ≤ ∑' i, f i y := (hf_sum y).sum_le_tsum _ (fun i _ => hf_nonneg i y)

private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_enum_aux1
    (f : ℕ → BitString → ℝ)
    (hf_lsc : IsRE (fun p : ℚ × ℕ × BitString => (p.1 : ℝ) < f p.2.1 p.2.2)) :
    IsRE (fun p : List ℚ × BitString => 
      ∀ i : Fin p.1.length, (p.1[i.1] : ℝ) < f i.1 p.2) := by
  classical
  obtain ⟨chk, hchk, hmono, hiff⟩ := IsRE.exists_stageApprox hf_lsc
  let B : (List ℚ × BitString) × ℕ → Bool := fun a =>
    (List.range a.1.1.length).foldr
      (fun i acc => (((a.1.1)[i]?).map (fun q => chk (q, i, a.1.2) a.2)).getD true && acc) true
  have hB : Computable B := by
    have hh : Computable₂ (fun (a : (List ℚ × BitString) × ℕ) (p : ℕ × Bool) =>
        (((a.1.1)[p.1]?).map (fun q => chk (q, p.1, a.1.2) a.2)).getD true && p.2) := by
      have hl : Computable (fun x : ((List ℚ × BitString) × ℕ) × ℕ × Bool => x.1.1.1) :=
        Computable.fst.comp (Computable.fst.comp Computable.fst)
      have hi : Computable (fun x : ((List ℚ × BitString) × ℕ) × ℕ × Bool => x.2.1) :=
        Computable.fst.comp Computable.snd
      have hacc : Computable (fun x : ((List ℚ × BitString) × ℕ) × ℕ × Bool => x.2.2) :=
        Computable.snd.comp Computable.snd
      have hget : Computable (fun x : ((List ℚ × BitString) × ℕ) × ℕ × Bool => x.1.1.1[x.2.1]?) :=
        Computable.list_getElem?.comp hl hi
      have hg : Computable₂ (fun (x : ((List ℚ × BitString) × ℕ) × ℕ × Bool) (q : ℚ) =>
          chk (q, x.2.1, x.1.1.2) x.1.2) := by
        have h1 : Computable (fun z : (((List ℚ × BitString) × ℕ) × ℕ × Bool) × ℚ =>
            (z.2, z.1.2.1, z.1.1.1.2)) :=
          Computable.pair Computable.snd
            (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
              (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))))
        have h2 : Computable (fun z : (((List ℚ × BitString) × ℕ) × ℕ × Bool) × ℚ =>
            z.1.1.2) := Computable.snd.comp (Computable.fst.comp Computable.fst)
        exact hchk.comp h1 h2
      have hm := Computable.option_map hget hg
      have hd := Computable.option_getD hm (Computable.const true)
      exact (Primrec.and.to_comp).comp hd hacc
    have := Computable.list_foldr
      (l := fun a : (List ℚ × BitString) × ℕ => List.range a.1.1.length)
      (g := fun _ => true)
      (Primrec.list_range.to_comp.comp (Computable.list_length.comp
        (Computable.fst.comp Computable.fst))) (Computable.const true) hh
    exact this
  have hfold : ∀ (L : List ℕ) (P : ℕ → Bool),
      L.foldr (fun i acc => P i && acc) true = true ↔ ∀ i ∈ L, P i = true := by
    intro L P
    induction L with
    | nil => simp
    | cons a t ih => simp [ih]
  have hBiff : ∀ a : (List ℚ × BitString) × ℕ, B a = true ↔
      ∀ i : Fin a.1.1.length, chk (a.1.1[i.1], i.1, a.1.2) a.2 = true := by
    intro a
    simp only [B]
    rw [hfold (List.range a.1.1.length)
      (fun i => (((a.1.1)[i]?).map (fun q => chk (q, i, a.1.2) a.2)).getD true)]
    constructor
    · intro h i
      have := h i.1 (List.mem_range.mpr i.2)
      simpa [List.getElem?_eq_getElem i.2] using this
    · intro h i hi
      have hi' : i < a.1.1.length := List.mem_range.mp hi
      simpa [List.getElem?_eq_getElem hi'] using h ⟨i, hi'⟩
  have hex : IsRE (fun p : List ℚ × BitString => ∃ s : ℕ, B (p, s) = true) := by
    have h1 : IsRE (fun a : (List ℚ × BitString) × ℕ => B a = true) :=
      isRE_of_computable_bool _ B (fun _ => Iff.rfl) hB
    exact IsRE.exists_encodable (R := fun (p : List ℚ × BitString) (s : ℕ) => B (p, s) = true) h1
  refine IsRE.of_iff hex ?_
  rintro ⟨l, y⟩
  constructor
  · rintro ⟨s, hs⟩ i
    have := (hBiff ((l, y), s)).mp hs i
    exact (hiff (l[i.1], i.1, y)).mpr ⟨s, this⟩
  · intro h
    have h' : ∀ i : Fin l.length, ∃ s, chk (l[i.1], i.1, y) s = true :=
      fun i => (hiff (l[i.1], i.1, y)).mp (h i)
    choose s hs using h'
    refine ⟨Finset.univ.sup s, (hBiff ((l, y), Finset.univ.sup s)).mpr ?_⟩
    intro i
    exact hmono _ _ _ (Finset.le_sup (Finset.mem_univ i)) (hs i)

private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_enum
    (f : ℕ → BitString → ℝ)
    (hf_lsc : IsRE (fun p : ℚ × ℕ × BitString => (p.1 : ℝ) < f p.2.1 p.2.2)) :
    IsRE (fun p : ℚ × BitString => ∃ (N : ℕ) (l : List ℚ) (hl : l.length = N),
      (∀ i : Fin N, (l[i.1] : ℝ) < f i.1 p.2) ∧
      (p.1 : ℝ) < ∑ i : Fin N, (l[i.1] : ℝ)) := by
  classical
  have hA := exists_lsc_stronglyWins_of_isEffectivelyNull_enum_aux1 f hf_lsc
  have hsum : Computable (fun p : (ℚ × BitString) × List ℚ => decide (p.1.1 < p.2.sum)) := by
    have hl : Computable (fun p : (ℚ × BitString) × List ℚ => p.2) := Computable.snd
    have hadd : Computable₂ (fun (_ : (ℚ × BitString) × List ℚ) (p : ℚ × ℚ) => p.1 + p.2) :=
      (computable₂_ratAdd.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd))
    have hs : Computable (fun p : (ℚ × BitString) × List ℚ => p.2.sum) := by
      have := Computable.list_foldr
        (l := fun p : (ℚ × BitString) × List ℚ => p.2) (g := fun _ => (0 : ℚ))
        (h := fun _ (p : ℚ × ℚ) => p.1 + p.2) hl (Computable.const 0) hadd
      refine this.of_eq (fun p => ?_)
      induction p.2 with
      | nil => rfl
      | cons a t ih => simp [ih]
    exact computable₂_ratLt.comp (Computable.fst.comp Computable.fst) hs
  have h1 := IsRE.and_computable
    (hA.comp_computable (g := fun p : (ℚ × BitString) × List ℚ => (p.2, p.1.2))
      (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))) hsum
  have h2 := IsRE.exists_encodable
    (R := fun (a : ℚ × BitString) (l : List ℚ) =>
      decide (a.1 < l.sum) = true ∧ ∀ i : Fin l.length, (l[i.1] : ℝ) < f i.1 a.2) h1
  refine IsRE.of_iff h2 ?_
  rintro ⟨r, y⟩
  have hs : ∀ l : List ℚ, ∑ i : Fin l.length, (l[i.1] : ℝ) = ((l.sum : ℚ) : ℝ) := by
    intro l
    simp [Rat.cast_list_sum]
  constructor
  · rintro ⟨l, hr, hl⟩
    refine ⟨l.length, l, rfl, hl, ?_⟩
    rw [hs l]
    exact_mod_cast of_decide_eq_true hr
  · rintro ⟨N, l, hN, hl, hr⟩
    subst hN
    refine ⟨l, ?_, hl⟩
    rw [hs l] at hr
    exact decide_eq_true (by exact_mod_cast hr)

private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_sum_lsc
    (f : ℕ → BitString → ℝ) (hf_nonneg : ∀ i y, 0 ≤ f i y)
    (hf_lsc : IsRE (fun p : ℚ × ℕ × BitString => (p.1 : ℝ) < f p.2.1 p.2.2))
    (hf_sum : ∀ y, Summable (fun i => f i y)) :
    IsLowerSemicomputableOnStrings (fun y => ∑' i, f i y) := by
  have h1 : IsRE (fun p : ℚ × BitString => ∃ (N : ℕ) (l : List ℚ) (hl : l.length = N),
      (∀ i : Fin N, (l[i.1] : ℝ) < f i.1 p.2) ∧
      (p.1 : ℝ) < ∑ i : Fin N, (l[i.1] : ℝ)) :=
          exists_lsc_stronglyWins_of_isEffectivelyNull_enum
          f hf_lsc
  unfold IsLowerSemicomputableOnStrings
  apply IsRE.of_iff h1
  intro p
  exact (exists_lsc_stronglyWins_of_isEffectivelyNull_iff f
      hf_nonneg hf_sum p.2 p.1).symm

/-- Step 2 of the proof of `exists_lsc_stronglyWins_of_isEffectivelyNull_sum`:
sum of lsc capitals is lsc -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_step2_sum_step2_lsc
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : ℕ → BitString → ℝ} (hm : ∀ n, IsFairCapital π (m n))
    (hbound : ∀ n, m n [] ≤ 1)
    (hlsc : IsRE (fun p : ℚ × ℕ × BitString => (p.1 : ℝ) < m p.2.1 p.2.2))
    (hnull : ∀ n x, massR π x = 0 → x.length < n → m n x = 0) :
    IsLowerSemicomputableOnStrings (exists_lsc_stronglyWins_of_isEffectivelyNull_sum_M m) :=
        by
  exact exists_lsc_stronglyWins_of_isEffectivelyNull_sum_lsc
    (fun n x => exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c n * m n x)
    (exists_lsc_stronglyWins_of_isEffectivelyNull_nonneg hm)
    (exists_lsc_stronglyWins_of_isEffectivelyNull_term_lsc hlsc)
    (exists_lsc_stronglyWins_of_isEffectivelyNull_lsc_summable hm hbound
        hnull)

/-- Step 3 of the proof of `exists_lsc_stronglyWins_of_isEffectivelyNull_sum`:
the sum strongly wins -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_sum_wins
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : ℕ → BitString → ℝ} (hm : ∀ n, IsFairCapital π (m n))
    (hbound : ∀ n, m n [] ≤ 1)
    (hnull : ∀ n x, massR π x = 0 → x.length < n → m n x = 0)
    (w : CantorSeq)
    (hw : ∀ n, ∃ k, ∀ l, k ≤ l → (2 : ℝ) ^ n ≤ m n (cantorPrefix w l)) :
    StronglyWins (exists_lsc_stronglyWins_of_isEffectivelyNull_sum_M m) w := by
  have hs :=
    exists_lsc_stronglyWins_of_isEffectivelyNull_summable
      hm hbound hnull
  have hc : ∀ n, 0 ≤ exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c n := by
    intro n
    unfold exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c
    positivity
  -- every weighted summand is dominated by the sum of the nonnegative series
  have hle : ∀ n x, exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c n * m n x ≤
      exists_lsc_stronglyWins_of_isEffectivelyNull_sum_M m x := fun n x =>
    (hs x).le_tsum n (fun j _ => mul_nonneg (hc j) ((hm j).nonneg x))
  -- the weights decay only polynomially: `4^k / 16 ≤ c (4k) * 2^(4k)`
  have hgrow : ∀ k : ℕ, (4 : ℝ) ^ k / 16 ≤
      exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c (4 * k) * 2 ^ (4 * k) := by
    intro k
    have ht : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k))
    have h4 : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h16 : (2 : ℝ) ^ (4 * k) = ((2 : ℝ) ^ k) ^ 4 := by
      rw [← pow_mul, mul_comm]
    unfold exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c
    rw [h4, h16, one_div, inv_mul_eq_div, div_le_div_iff₀ (by norm_num) (by positivity)]
    push_cast
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : 0 ≤ 4 * (2 : ℝ) ^ k - (4 * k + 1) := by linarith
    have h2 : 0 ≤ 4 * (2 : ℝ) ^ k + (4 * k + 1) := by positivity
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ((2 : ℝ) ^ k)) h1) h2]
  rw [StronglyWins, tendsto_atTop_atTop]
  intro b
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (16 * b) (by norm_num : (1 : ℝ) < 4)
  obtain ⟨l₀, hl₀⟩ := hw (4 * k)
  refine ⟨l₀, fun l hl => ?_⟩
  calc b ≤ (4 : ℝ) ^ k / 16 := by linarith
    _ ≤ exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c (4 * k) * 2 ^ (4 * k) :=
        hgrow k
    _ ≤ exists_lsc_stronglyWins_of_isEffectivelyNull_sum_c (4 * k) *
          m (4 * k) (cantorPrefix w l) :=
        mul_le_mul_of_nonneg_left (hl₀ l hl) (hc _)
    _ ≤ _ := hle _ _

/-- Step 2 of the proof of `exists_lsc_stronglyWins_of_isEffectivelyNull`:
combine the martingales into one. -/
private lemma exists_lsc_stronglyWins_of_isEffectivelyNull_sum
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    {m : ℕ → BitString → ℝ} (hm : ∀ n, IsFairCapital π (m n))
    (hbound : ∀ n, m n [] ≤ 1)
    (hlsc : IsRE (fun p : ℚ × ℕ × BitString => (p.1 : ℝ) < m p.2.1 p.2.2))
    (hnull : ∀ n x, massR π x = 0 → x.length < n → m n x = 0) :
    ∃ M : BitString → ℝ, IsFairCapital π M ∧ IsLowerSemicomputableOnStrings M ∧
      ∀ w, (∀ n, ∃ k, ∀ l, k ≤ l →
        (2 : ℝ)^n ≤ m n (cantorPrefix w l)) → StronglyWins M w := by
  use exists_lsc_stronglyWins_of_isEffectivelyNull_sum_M m
  exact ⟨exists_lsc_stronglyWins_of_isEffectivelyNull_sum_fair hm hbound hnull,
         exists_lsc_stronglyWins_of_isEffectivelyNull_step2_sum_step2_lsc hm hbound hlsc hnull,
         fun w hw => exists_lsc_stronglyWins_of_isEffectivelyNull_sum_wins hm hbound
             hnull w hw⟩

/-- **SUV Theorem 181(b), p. 278, and the strengthening of the same page.**  For an effectively null
set `X` of a computable `π` there is a lower semicomputable `π`-martingale strongly winning on all
sequences in `X`. -/
theorem exists_lsc_stronglyWins_of_isEffectivelyNull {π : Measure CantorSeq}
    [IsProbabilityMeasure π] (hπ : IsComputableMeasure π) {X : Set CantorSeq}
    (hX : IsEffectivelyNull π X) :
    ∃ m, IsFairCapital π m ∧ IsLowerSemicomputableOnStrings m ∧ ∀ w ∈ X, StronglyWins m w := by
  rcases hX with ⟨U, hU, hX_sub, hU_meas⟩
  rcases exists_lsc_stronglyWins_of_isEffectivelyNull_martingales hπ hU hU_meas with
    ⟨m, hm, hbound, hlsc, hnull, hwins⟩
  rcases exists_lsc_stronglyWins_of_isEffectivelyNull_sum hm hbound hlsc hnull with
    ⟨M, hM, hMlsc, hMwins⟩
  use M, hM, hMlsc
  intro w hw
  apply hMwins
  intro n
  have hwU : w ∈ U n := by
    have h1 := hX_sub hw
    rw [Set.mem_iInter] at h1
    exact h1 n
  exact hwins n w hwU

end Kolmogorov.FrequencyGames
