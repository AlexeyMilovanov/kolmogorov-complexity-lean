/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.Gales.LowerSemicomputableGales

/-!
# Effective Dimension Via Gales

Effective Hausdorff dimension of a set of sequences is characterised by lower semicomputable
gales and supergales.  The main results show that the effective dimension of a set `A` equals the
infimum of the computable exponents `α > 0` for which some lower semicomputable `α`-gale (or
`α`-supergale) with initial value at most `1` is unbounded on every sequence of `A`.  The key step
is that the set of sequences on whose prefixes such a gale is unbounded is effectively `β`-null
for every computable `β > α` (Theorem 186 of Shen, Uspensky and Vereshchagin).  The module also
relates the dimension of a single sequence to the `liminf` of the prefix complexity ratio.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-- Level sum of a gale: `∑_{|y| = N} m y = (2^α)^N m(Λ)`. -/
private lemma isEffectiveAlphaNull_wins_of_lsc_level_sum {α : ℝ} {m : BitString → ℝ}
    (hm : IsGale α m) (N : ℕ) :
    ∑ y ∈ levelFinset N, m y = ((2 : ℝ) ^ α) ^ N * m [] := by
  induction N with
  | zero => simp [levelFinset, levelList]
  | succ N ih =>
    rw [sum_levelFinset_eq_sum_levelList] at ih ⊢
    simp only [levelList, List.map_append, List.sum_append, List.map_map]
    have : ∀ x : BitString, (m ∘ fun x => x ++ [false]) x + (m ∘ fun x => x ++ [true]) x
        = (2 : ℝ) ^ α * m x := fun x => (hm.gale x).symm
    rw [← List.sum_map_add (l := levelList N) (f := m ∘ fun x => x ++ [false])
      (g := m ∘ fun x => x ++ [true])]
    rw [List.map_congr_left (fun x _ => this x)]
    rw [List.sum_map_mul_left, ih]
    ring

/-- The `β`-weight of an interval as an `ofReal` of a real power of two. -/
private lemma isEffectiveAlphaNull_wins_of_lsc_weight (β : ℝ) (y : BitString) :
    intervalAlphaMass β y = ENNReal.ofReal ((2 : ℝ) ^ (-(β * y.length))) := by
  rw [intervalAlphaMass_eq_inv_two_pow]
  have h1 : (2 : ℝ) ^ (-(β * y.length)) = (((2 : ℝ)⁻¹) ^ y.length) ^ β := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.inv_rpow (by norm_num) ,
      ← Real.rpow_neg (by norm_num)]
    rw [mul_comm]
  rw [h1, ← ENNReal.ofReal_rpow_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

/-- Sum of the `β`-weights of all strings with `m x > K`, for a gale with `m(Λ) ≤ 1`. -/
private lemma isEffectiveAlphaNull_wins_of_lsc_tsum_bound {α β : ℝ} (hαβ : α < β)
    {m : BitString → ℝ} (hm : IsGale α m) (hinit : m [] ≤ 1) {K : ℝ} (hK : 0 < K) :
    (∑' x : BitString, if K < m x then intervalAlphaMass β x else 0)
      ≤ ENNReal.ofReal (1 / (K * (1 - (2 : ℝ) ^ (α - β)))) := by
  set r : ℝ := (2 : ℝ) ^ (α - β) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hlevel : ∀ N : ℕ, ∑ y ∈ levelFinset N, (if K < m y then intervalAlphaMass β y else 0)
      ≤ ENNReal.ofReal (r ^ N / K) := by
    intro N
    have hterm : ∀ y ∈ levelFinset N, (if K < m y then intervalAlphaMass β y else 0)
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(β * N)) * (m y / K)) := by
      intro y hy
      have hl : y.length = N := mem_levelFinset.1 hy
      split_ifs with h
      · rw [isEffectiveAlphaNull_wins_of_lsc_weight, hl]
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 ≤ m y / K := (one_le_div hK).2 h.le
        have hp : 0 < (2 : ℝ) ^ (-(β * N)) := by positivity
        nlinarith
      · exact zero_le
    have hrN : r ^ N = (2 : ℝ) ^ (-(β * N)) * ((2 : ℝ) ^ α) ^ N := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1
      ring
    calc _ ≤ ∑ y ∈ levelFinset N, ENNReal.ofReal ((2 : ℝ) ^ (-(β * N)) * (m y / K)) :=
          Finset.sum_le_sum hterm
      _ = ENNReal.ofReal (∑ y ∈ levelFinset N, (2 : ℝ) ^ (-(β * N)) * (m y / K)) :=
          (ENNReal.ofReal_sum_of_nonneg (fun y _ => by
            have := hm.nonneg y; positivity)).symm
      _ ≤ ENNReal.ofReal (r ^ N / K) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Finset.mul_sum, ← Finset.sum_div,
          isEffectiveAlphaNull_wins_of_lsc_level_sum hm, hrN]
        rw [← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ hK.le
        have hab : 0 ≤ (2 : ℝ) ^ (-(β * N)) * ((2 : ℝ) ^ α) ^ N := by positivity
        calc (2 : ℝ) ^ (-(β * N)) * (((2 : ℝ) ^ α) ^ N * m [])
            = ((2 : ℝ) ^ (-(β * N)) * ((2 : ℝ) ^ α) ^ N) * m [] := by ring
          _ ≤ ((2 : ℝ) ^ (-(β * N)) * ((2 : ℝ) ^ α) ^ N) * 1 :=
              mul_le_mul_of_nonneg_left hinit hab
          _ = _ := mul_one _
  rw [tsum_eq_tsum_sum_levelFinset]
  calc ∑' N : ℕ, ∑ y ∈ levelFinset N, (if K < m y then intervalAlphaMass β y else 0)
      ≤ ∑' N : ℕ, ENNReal.ofReal (r ^ N / K) := ENNReal.tsum_le_tsum hlevel
    _ = ENNReal.ofReal (∑' N : ℕ, r ^ N / K) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity)
          ((summable_geometric_of_lt_one hr0.le hr1).div_const K)).symm
    _ = ENNReal.ofReal (1 / (K * (1 - r))) := by
        rw [tsum_div_const, tsum_geometric_of_lt_one hr0.le hr1]
        congr 1
        have : (1 - r) ≠ 0 := by linarith
        field_simp

/-- The cover: the string `x` with `m x > 2 C den ε`, emitted once, at its first stage. -/
private def isEffectiveAlphaNull_wins_of_lsc_cover (chk : ℕ × BitString → ℕ → Bool) (C : ℕ)
    (ε : ℚ) (j : ℕ) : Option BitString :=
  bif firstStage chk (2 * C * ε.den) (natToBitString (Nat.unpair j).1) (Nat.unpair j).2 then
    some (natToBitString (Nat.unpair j).1)
  else none

private lemma isEffectiveAlphaNull_wins_of_lsc_cover_computable
    {chk : ℕ × BitString → ℕ → Bool} (hchk : Computable₂ chk) (C : ℕ) :
    Computable₂ (isEffectiveAlphaNull_wins_of_lsc_cover chk C) := by
  have hstr : Computable (fun p : ℚ × ℕ => natToBitString (Nat.unpair p.2).1) :=
    computable_natToBitString.comp ((Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd)
  have hK : Computable (fun p : ℚ × ℕ => 2 * C * p.1.den) :=
    Primrec.nat_mul.to_comp.comp (Computable.const (2 * C)) (computable_ratDen.comp Computable.fst)
  have hstage : Computable (fun p : ℚ × ℕ => (Nat.unpair p.2).2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.snd
  have hfs : Computable (fun p : ℚ × ℕ =>
      firstStage chk (2 * C * p.1.den) (natToBitString (Nat.unpair p.2).1)
        (Nat.unpair p.2).2) :=
    ((computable_firstStage hchk).comp (Computable.pair (Computable.pair hK hstr) hstage)).of_eq
      fun p => rfl
  exact (Computable.cond hfs (Computable.option_some.comp hstr)
    (Computable.const none)).of_eq fun p => rfl

private lemma isEffectiveAlphaNull_wins_of_lsc_cover_pair {chk : ℕ × BitString → ℕ → Bool}
    (β : ℝ) (C : ℕ) (ε : ℚ) (a b : ℕ) :
    coverAlphaMass β (isEffectiveAlphaNull_wins_of_lsc_cover chk C ε (Nat.pair a b))
      = if firstStage chk (2 * C * ε.den) (natToBitString a) b = true then
          intervalAlphaMass β (natToBitString a) else 0 := by
  cases hb : firstStage chk (2 * C * ε.den) (natToBitString a) b <;>
    simp [isEffectiveAlphaNull_wins_of_lsc_cover, Nat.unpair_pair, hb]

private lemma isEffectiveAlphaNull_wins_of_lsc_cover_tsum {chk : ℕ × BitString → ℕ → Bool}
    (hmono : ∀ q s t, s ≤ t → chk q s = true → chk q t = true) {m : BitString → ℝ} (β : ℝ)
    (C : ℕ) (ε : ℚ)
    (hspec : ∀ q : ℕ × BitString, ((q.1 : ℝ) < m q.2) ↔ ∃ s, chk q s = true) :
    (∑' j, coverAlphaMass β (isEffectiveAlphaNull_wins_of_lsc_cover chk C ε j))
      ≤ ∑' x : BitString, if ((2 * C * ε.den : ℕ) : ℝ) < m x then intervalAlphaMass β x else 0 := by
  have hstep : ∀ a : ℕ,
      (∑' b, coverAlphaMass β (isEffectiveAlphaNull_wins_of_lsc_cover chk C ε (Nat.pair a b)))
        ≤ if ((2 * C * ε.den : ℕ) : ℝ) < m (natToBitString a) then
            intervalAlphaMass β (natToBitString a) else 0 := by
    intro a
    refine tsum_le_of_subsingleton_support ?_ ?_
    · intro b
      rw [isEffectiveAlphaNull_wins_of_lsc_cover_pair]
      split_ifs with hb h
      · exact le_rfl
      · exact absurd ((hspec (2 * C * ε.den, natToBitString a)).2 ⟨b, firstStage_imp hb⟩) h
      · exact zero_le
      · exact le_rfl
    · intro b b' hb hb'
      have key : ∀ u : ℕ,
          coverAlphaMass β (isEffectiveAlphaNull_wins_of_lsc_cover chk C ε (Nat.pair a u)) ≠ 0 →
          firstStage chk (2 * C * ε.den) (natToBitString a) u = true := by
        intro u hu
        by_contra hcon
        exact hu (by rw [isEffectiveAlphaNull_wins_of_lsc_cover_pair]; simp [hcon])
      exact firstStage_unique hmono (key b hb) (key b' hb')
  calc (∑' j, coverAlphaMass β (isEffectiveAlphaNull_wins_of_lsc_cover chk C ε j))
      = ∑' a, ∑' b, coverAlphaMass β
          (isEffectiveAlphaNull_wins_of_lsc_cover chk C ε (Nat.pair a b)) := tsum_nat_pair _
    _ ≤ ∑' a : ℕ, (if ((2 * C * ε.den : ℕ) : ℝ) < m (natToBitString a) then
            intervalAlphaMass β (natToBitString a) else 0) := ENNReal.tsum_le_tsum hstep
    _ = _ := tsum_comp_natToBitString
          (fun x => if ((2 * C * ε.den : ℕ) : ℝ) < m x then intervalAlphaMass β x else 0)

private lemma isEffectiveAlphaNull_wins_of_lsc_cover_mem {chk : ℕ × BitString → ℕ → Bool}
    {m : BitString → ℝ} (C : ℕ) (ε : ℚ)
    (hspec : ∀ q : ℕ × BitString, ((q.1 : ℝ) < m q.2) ↔ ∃ s, chk q s = true)
    {w : CantorSeq} (hw : Wins m w) :
    w ∈ ⋃ j, (isEffectiveAlphaNull_wins_of_lsc_cover chk C ε j).elim (∅ : Set CantorSeq)
      cantorCylinder := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((2 * C * ε.den : ℕ) : ℝ) < m (cantorPrefix w n) := by
    have := not_bddAbove_iff.1 hw ((2 * C * ε.den : ℕ) : ℝ)
    obtain ⟨_, ⟨n, rfl⟩, h⟩ := this
    exact ⟨n, h⟩
  obtain ⟨t, ht⟩ := exists_firstStage
    ((hspec (2 * C * ε.den, cantorPrefix w n)).1 hn)
  refine Set.mem_iUnion.2 ⟨Nat.pair (bitStringToNat (cantorPrefix w n)) t, ?_⟩
  have hval : isEffectiveAlphaNull_wins_of_lsc_cover chk C ε
      (Nat.pair (bitStringToNat (cantorPrefix w n)) t) = some (cantorPrefix w n) := by
    simp only [isEffectiveAlphaNull_wins_of_lsc_cover, Nat.unpair_pair,
      natToBitString_bitStringToNat, ht, Bool.cond_true]
  rw [hval]
  exact mem_cantorCylinder_cantorPrefix w n

/-- **SUV Theorem 186, p. 286.**  For a lower semicomputable `α`-gale, the set of sequences on whose
prefixes it is unbounded is effectively `β`-null, for every computable `β > α`.  The computability
of `α` and `β` is the book's standing assumption.  The set is not claimed to be effectively
`α`-null: the book points out on p. 286 that this fails.  The initial bound `m(Λ) ≤ 1` is the
standing effective-gale convention on p. 285, retained here.  Allowing `α > 1` is a harmless
extension, because then `β > 1` and all of Cantor space is effectively `β`-null. -/
theorem isEffectiveAlphaNull_wins_of_lsc {α β : ℝ} (_hαc : ComputableReals.IsComputableReal α)
    (_hβc : ComputableReals.IsComputableReal β) (_hα0 : 0 < α) (hαβ : α < β) {m : BitString → ℝ}
    (hm : IsGale α m) (hlsc : IsLowerSemicomputableOnStrings m) (hinit : m [] ≤ 1) :
    IsEffectiveAlphaNull β {w | Wins m w} := by
  have hr1 : (2 : ℝ) ^ (α - β) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr0 : 0 < (2 : ℝ) ^ (α - β) := by positivity
  obtain ⟨C, hC⟩ := exists_nat_ge (1 / (1 - (2 : ℝ) ^ (α - β)))
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le (by
    have : 0 < 1 - (2 : ℝ) ^ (α - β) := by linarith
    positivity) hC
  have hRE : IsRE (fun p : ℕ × BitString => (p.1 : ℝ) < m p.2) := by
    have hg : Computable (fun p : ℕ × BitString => (((p.1 : ℕ) : ℚ), p.2)) :=
      (computable_nat_to_rat.comp Computable.fst).pair Computable.snd
    refine (hlsc.comp_computable hg).of_iff ?_
    intro p
    simp
  obtain ⟨chk, hchk, hmono, hspec⟩ := hRE.exists_stageApprox
  refine ⟨isEffectiveAlphaNull_wins_of_lsc_cover chk C,
    isEffectiveAlphaNull_wins_of_lsc_cover_computable hchk C, fun ε hε => ⟨?_, ?_⟩⟩
  · intro w hw
    exact isEffectiveAlphaNull_wins_of_lsc_cover_mem C ε hspec hw
  · have hden : (0 : ℝ) < (ε.den : ℝ) := by exact_mod_cast ε.pos
    have hK : (0 : ℝ) < ((2 * C * ε.den : ℕ) : ℝ) := by push_cast; positivity
    have h1 := isEffectiveAlphaNull_wins_of_lsc_tsum_bound hαβ hm hinit hK
    have h2 := isEffectiveAlphaNull_wins_of_lsc_cover_tsum hmono β C ε hspec
    have hεq : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hd := one_div_den_le_rat hε
    have hlt : 1 / (((2 * C * ε.den : ℕ) : ℝ) * (1 - (2 : ℝ) ^ (α - β))) < (ε : ℝ) := by
      have h1r : 0 < 1 - (2 : ℝ) ^ (α - β) := by linarith
      have : 1 / (((2 * C * ε.den : ℕ) : ℝ) * (1 - (2 : ℝ) ^ (α - β)))
          = (1 / (1 - (2 : ℝ) ^ (α - β))) / ((2 * C * ε.den : ℕ) : ℝ) := by
        field_simp
      rw [this]
      have h3 : (1 / (1 - (2 : ℝ) ^ (α - β))) / ((2 * C * ε.den : ℕ) : ℝ)
          ≤ (C : ℝ) / ((2 * C * ε.den : ℕ) : ℝ) := div_le_div_of_nonneg_right hC hK.le
      have h4 : (C : ℝ) / ((2 * C * ε.den : ℕ) : ℝ) = (1 / (ε.den : ℝ)) / 2 := by
        push_cast
        field_simp
      linarith
    exact lt_of_le_of_lt (h2.trans h1) ((ENNReal.ofReal_lt_ofReal_iff hεq).2 hlt)

/-- Step 1 of the proof of `effectiveHausdorffDim_eq_sInf_gale`: the effective Hausdorff
dimension is at most the infimum of the exponents of lower semicomputable gales unbounded on `A`. -/
private theorem effectiveHausdorffDim_eq_sInf_gale_le (A : Set CantorSeq) :
    effectiveHausdorffDim A ≤ sInf {α : ℝ | 0 < α ∧ ComputableReals.IsComputableReal α ∧
      ∃ m, IsGale α m ∧ IsLowerSemicomputableOnStrings m ∧ m [] ≤ 1 ∧ ∀ w ∈ A, Wins m w} := by
  obtain ⟨m2, hm2⟩ : ∃ m2 : BitString → ℝ, ∀ x, m2 x = (2:ℝ) ^ x.length := ⟨_, fun _ => rfl⟩
  have hG2 : IsGale 2 m2 := by
    refine ⟨fun x => by rw [hm2]; positivity, fun x => ?_⟩
    have h4 : (2:ℝ) ^ (2:ℝ) = 4 := by rw [Real.rpow_two]; norm_num
    rw [h4]; simp only [hm2, List.length_append, List.length_singleton, pow_succ]; ring
  have hlsc2 : IsLowerSemicomputableOnStrings m2 := by
    unfold IsLowerSemicomputableOnStrings
    refine isRE_of_computable_bool _
      (fun p : ℚ × BitString => decide (p.1 < ((2 ^ p.2.length : ℕ) : ℚ))) ?_ ?_
    · intro p
      rw [decide_eq_true_eq, hm2]
      constructor <;> intro h <;> exact_mod_cast h
    · have hg : Computable (fun p : ℚ × BitString => (((2 ^ p.2.length : ℕ)) : ℚ)) :=
        computable_nat_to_rat.comp (nat_pow_primrec₂.comp (Primrec.const 2)
          (Primrec.list_length.comp Primrec.snd)).to_comp
      exact computable₂_ratLt.comp Computable.fst hg
  have hwins2 : ∀ w : CantorSeq, Wins m2 w := by
    intro w
    unfold Wins
    rintro ⟨B, hB⟩
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (by norm_num : (1:ℝ) < 2)
    have := hB (Set.mem_range_self n)
    rw [show m2 (cantorPrefix w n) = (2:ℝ) ^ (cantorPrefix w n).length from hm2 _] at this
    rw [cantorPrefix_length] at this
    linarith
  have hGne : {α : ℝ | 0 < α ∧ ComputableReals.IsComputableReal α ∧ ∃ m, IsGale α m ∧
      IsLowerSemicomputableOnStrings m ∧ m [] ≤ 1 ∧ ∀ w ∈ A, Wins m w}.Nonempty :=
    ⟨2, by norm_num, by simpa using ComputableReals.isComputableReal_ratCast (2:ℚ), m2, hG2, hlsc2,
      by rw [hm2]; simp, fun w _ => hwins2 w⟩
  refine le_csInf hGne ?_
  rintro α ⟨hα0, hαc, m, hm, hlsc, hinit, hw⟩
  refine le_of_forall_gt_imp_ge_of_dense fun q hq => ?_
  obtain ⟨r, hαr, hrq⟩ := exists_rat_btwn hq
  have hnull := (isEffectiveAlphaNull_wins_of_lsc hαc
    (ComputableReals.isComputableReal_ratCast r) hα0 hαr hm hlsc hinit).mono_set
    (fun w hw' => hw w hw')
  exact (csInf_le (bddBelow_effectiveAlphaSet A)
    ⟨by exact_mod_cast hα0.trans hαr, hnull⟩).trans hrq.le

/-- The function `x ↦ 2 ^ ((a / b) * |x|)` is lower semicomputable (for `b > 0`): for a rational
`r` and `n = |x|`, `r < 2 ^ ((a / b) n)` iff `(max r 0) ^ b < 2 ^ (a n)`, a decidable relation. -/
private lemma effectiveHausdorffDim_eq_sInf_gale_ge_lsc_pow (a b : ℕ) (hb : 0 < b) :
    IsLowerSemicomputableOnStrings
      (fun x : BitString => (2 : ℝ) ^ (((a : ℝ) / (b : ℝ)) * (x.length : ℝ))) := by
  unfold IsLowerSemicomputableOnStrings
  have hq : Computable (fun p : ℚ × BitString => max p.1 0) :=
    Computable₂.comp (f := fun x y : ℚ => max x y) ComputableReals.primrec_ratMax.to_comp
      (Computable.fst : Computable (fun p : ℚ × BitString => p.1)) (Computable.const (0 : ℚ))
  have hlen : Computable (fun p : ℚ × BitString => a * p.2.length) :=
    (Primrec.nat_mul.comp (Primrec.const a) (Primrec.list_length.comp Primrec.snd)).to_comp
  have h1 : Computable (fun p : ℚ × BitString => (max p.1 0) ^ b) :=
    Computable.comp (f := fun z : ℚ × ℕ => z.1 ^ z.2)
      (g := fun p : ℚ × BitString => (max p.1 0, b))
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_ratPow
      (hq.pair (Computable.const b))
  have h2 : Computable (fun p : ℚ × BitString => (2 : ℚ) ^ (a * p.2.length)) :=
    Computable.comp (f := fun z : ℚ × ℕ => z.1 ^ z.2)
      (g := fun p : ℚ × BitString => ((2 : ℚ), a * p.2.length))
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_ratPow
      ((Computable.const (2 : ℚ)).pair hlen)
  have hcomp : Computable (fun p : ℚ × BitString =>
      decide ((max p.1 0) ^ b < (2 : ℚ) ^ (a * p.2.length))) :=
    Computable₂.comp (f := fun x y : ℚ => decide (x < y))
      ((PrimrecRel.decide ComputableReals.primrec_ratLt).to_comp) h1 h2
  refine isRE_of_computable_bool _ _ (fun p => ?_) hcomp
  obtain ⟨r, x⟩ := p
  simp only [decide_eq_true_eq]
  have hs : (0 : ℝ) < (2 : ℝ) ^ (((a : ℝ) / (b : ℝ)) * (x.length : ℝ)) := by positivity
  have hsb : ((2 : ℝ) ^ (((a : ℝ) / (b : ℝ)) * (x.length : ℝ))) ^ b
      = (2 : ℝ) ^ (a * x.length) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    have : ((a : ℝ) / (b : ℝ)) * (x.length : ℝ) * (b : ℝ) = ((a * x.length : ℕ) : ℝ) := by
      push_cast
      field_simp
    rw [this, Real.rpow_natCast]
  have hmax : (r : ℝ) < (2 : ℝ) ^ (((a : ℝ) / (b : ℝ)) * (x.length : ℝ)) ↔
      ((max r 0 : ℚ) : ℝ) < (2 : ℝ) ^ (((a : ℝ) / (b : ℝ)) * (x.length : ℝ)) := by
    push_cast
    simp [max_lt_iff, hs]
  rw [hmax]
  have ht : 0 ≤ ((max r 0 : ℚ) : ℝ) := by exact_mod_cast le_max_right _ _
  rw [← pow_lt_pow_iff_left₀ ht hs.le hb.ne', hsb]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- For real `c`, the function `x ↦ 2 ^ (c |x|)` is a `(1 + c)`-gale. -/
private lemma effectiveHausdorffDim_eq_sInf_gale_ge_isGale_pow (c : ℝ) :
    IsGale (1 + c) (fun x : BitString => (2 : ℝ) ^ (c * (x.length : ℝ))) := by
  refine ⟨fun x => by positivity, fun x => ?_⟩
  simp only [List.length_append, List.length_singleton]
  push_cast
  rw [Real.rpow_add (by norm_num), mul_add, mul_one, Real.rpow_add (by norm_num)]
  simp only [Real.rpow_one]
  ring

/-- For `c > 0`, the function `x ↦ 2 ^ (c |x|)` is unbounded on the prefixes of every sequence. -/
private lemma effectiveHausdorffDim_eq_sInf_gale_ge_wins_pow {c : ℝ} (hc : 0 < c)
    (w : CantorSeq) : Wins (fun x : BitString => (2 : ℝ) ^ (c * (x.length : ℝ))) w := by
  unfold Wins
  rintro ⟨B, hB⟩
  have h2 : 1 < (2 : ℝ) ^ c := Real.one_lt_rpow (by norm_num) hc
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h2
  have h3 := hB ⟨n, rfl⟩
  simp only [cantorPrefix_length] at h3
  rw [Real.rpow_mul (by norm_num), Real.rpow_natCast] at h3
  linarith

/-- Step 2 of the proof of `effectiveHausdorffDim_eq_sInf_gale`: the infimum of the
exponents of lower semicomputable gales unbounded on `A` is at most the effective Hausdorff
dimension. -/
private theorem effectiveHausdorffDim_eq_sInf_gale_ge (A : Set CantorSeq) :
    sInf {α : ℝ | 0 < α ∧ ComputableReals.IsComputableReal α ∧
      ∃ m, IsGale α m ∧ IsLowerSemicomputableOnStrings m ∧ m [] ≤ 1 ∧ ∀ w ∈ A, Wins m w} ≤
        effectiveHausdorffDim A := by
  have hbdd : BddBelow {α : ℝ | 0 < α ∧ ComputableReals.IsComputableReal α ∧
      ∃ m, IsGale α m ∧ IsLowerSemicomputableOnStrings m ∧ m [] ≤ 1 ∧ ∀ w ∈ A, Wins m w} :=
    ⟨0, fun α hα => hα.1.le⟩
  refine le_of_forall_gt_imp_ge_of_dense fun β hβ => ?_
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hβ
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (effectiveHausdorffDim_mem_Icc A).1 hq1
  refine le_trans (csInf_le hbdd ?_) hq2.le
  refine ⟨hq0, ComputableReals.isComputableReal_ratCast q, ?_⟩
  by_cases hq1' : (q : ℝ) ≤ 1
  · exact exists_lsc_isGale_wins_of_isEffectiveAlphaNull
      (ComputableReals.isComputableReal_ratCast q) hq0 hq1'
      (isEffectiveAlphaNull_of_effectiveHausdorffDim_lt hq0 hq1)
  · have hq1'' : (1 : ℝ) < q := lt_of_not_ge hq1'
    have hpos : (0 : ℚ) < q - 1 := sub_pos.2 (by exact_mod_cast hq1'')
    have hnum : (q - 1).num = ((q - 1).num.toNat : ℤ) :=
      (Int.toNat_of_nonneg (Rat.num_pos.2 hpos).le).symm
    have ha : 0 < (q - 1).num.toNat := Int.lt_toNat.2 (Rat.num_pos.2 hpos)
    have hb : 0 < (q - 1).den := Rat.den_pos _
    have hc : (q : ℝ) = 1 + ((q - 1).num.toNat : ℝ) / ((q - 1).den : ℝ) := by
      have h1 : (((q - 1 : ℚ)) : ℝ) = (q : ℝ) - 1 := by push_cast; ring
      have h2 : (((q - 1).num : ℤ) : ℝ) = (((q - 1).num.toNat : ℕ) : ℝ) := by
        exact_mod_cast hnum
      have h3 := Rat.cast_def (K := ℝ) (q - 1)
      rw [h1, h2] at h3
      linarith
    have hcpos : (0 : ℝ) < ((q - 1).num.toNat : ℝ) / ((q - 1).den : ℝ) := by
      positivity
    refine ⟨fun x : BitString => (2 : ℝ) ^ ((((q - 1).num.toNat : ℝ) / ((q - 1).den : ℝ)) *
      (x.length : ℝ)), ?_, ?_, ?_, fun w _ => ?_⟩
    · rw [hc]
      exact effectiveHausdorffDim_eq_sInf_gale_ge_isGale_pow _
    · exact effectiveHausdorffDim_eq_sInf_gale_ge_lsc_pow _ _ hb
    · simp
    · exact effectiveHausdorffDim_eq_sInf_gale_ge_wins_pow hcpos w

/-- **SUV Theorem 187, p. 286.**  The effective Hausdorff dimension of an arbitrary set `A` is the
infimum of the `α` for which a lower semicomputable `α`-gale is unbounded on all elements of `A`.
We retain computable exponents and `m(Λ) ≤ 1` from the effective-case convention.  All positive
exponents are allowed so that the infimum is nonempty even for `A = Ω`; restricting to computable
exponents leaves the infimum unchanged, using computable exponents arbitrarily close from above. -/
theorem effectiveHausdorffDim_eq_sInf_gale (A : Set CantorSeq) :
    effectiveHausdorffDim A = sInf {α : ℝ | 0 < α ∧ ComputableReals.IsComputableReal α ∧
      ∃ m, IsGale α m ∧ IsLowerSemicomputableOnStrings m ∧ m [] ≤ 1 ∧ ∀ w ∈ A, Wins m w} := by
  exact le_antisymm (effectiveHausdorffDim_eq_sInf_gale_le A)
      (effectiveHausdorffDim_eq_sInf_gale_ge A)

/-- The level-`N` sum of a supergale with `m [] ≤ 1` is at most `2^{αN}`. -/
private lemma supergaleNull_aux1
    {α : ℝ} {m : BitString → ℝ} (hm : IsSupergale α m)
    (hinit : m [] ≤ 1) (N : ℕ) :
    ∑ x ∈ levelFinset N, m x ≤ ((2 : ℝ) ^ α) ^ N := by
  induction N with
  | zero => simpa [levelFinset, levelList] using hinit
  | succ N ih =>
    have h : ∑ x ∈ levelFinset (N + 1), m x
        = ∑ x ∈ levelFinset N, (m (x ++ [false]) + m (x ++ [true])) := by
      rw [sum_levelFinset_eq_sum_levelList, sum_levelFinset_eq_sum_levelList]
      simp only [levelList, List.map_append, List.map_map, List.sum_append]
      rw [List.sum_map_add]
      rfl
    rw [h]
    calc ∑ x ∈ levelFinset N, (m (x ++ [false]) + m (x ++ [true]))
        ≤ ∑ x ∈ levelFinset N, (2 : ℝ) ^ α * m x :=
          Finset.sum_le_sum fun x _ => hm.supergale x
      _ = (2 : ℝ) ^ α * ∑ x ∈ levelFinset N, m x := by rw [Finset.mul_sum]
      _ ≤ (2 : ℝ) ^ α * ((2 : ℝ) ^ α) ^ N :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = ((2 : ℝ) ^ α) ^ (N + 1) := by ring

/-- At most `2^{αN}/k` strings of length `N` have `m x > k`. -/
private lemma supergaleNull_aux2
    {α : ℝ} {m : BitString → ℝ} (hm : IsSupergale α m)
    (hinit : m [] ≤ 1) (N : ℕ) {k : ℕ} :
    (((levelFinset N).filter (fun x => (k : ℝ) < m x)).card : ℝ) * k ≤ ((2 : ℝ) ^ α) ^ N := by
  classical
  have h1 : (((levelFinset N).filter (fun x => (k : ℝ) < m x)).card : ℝ) * k
      ≤ ∑ x ∈ (levelFinset N).filter (fun x => (k : ℝ) < m x), m x := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ (fun x hx => (Finset.mem_filter.1 hx).2.le)
  refine h1.trans ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun x _ _ => hm.nonneg x)).trans
      (supergaleNull_aux1
        hm hinit N))

/-- The `β`-weight of an interval of length `n` is `(2^β)^{-n}`. -/
private lemma supergaleNull_aux3
    (β : ℝ) (x : BitString) :
    intervalAlphaMass β x = ENNReal.ofReal ((((2 : ℝ) ^ β) ^ x.length)⁻¹) := by
  rw [intervalAlphaMass_eq_inv_two_pow]
  have h1 : ((2 : ENNReal)⁻¹ ^ x.length) = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ x.length) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  have h2 : ((((2 : ℝ) ^ β) ^ x.length)⁻¹) = (((2:ℝ)⁻¹ ^ x.length)) ^ β := by
    rw [inv_pow, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  rw [h2, h1, ENNReal.ofReal_rpow_of_pos (by positivity)]

/-- The real-number estimate of one level of the cover. -/
private lemma supergaleNull_aux4
    {α β : ℝ} {M : ℕ} (hM : 0 < M) (hMβ : 1 / (M : ℝ) ≤ β - α)
    {k : ℕ} (hk : 0 < k) (N : ℕ) (c : ℝ) (hc : c * k ≤ ((2 : ℝ) ^ α) ^ N) :
    c * ((((2 : ℝ) ^ β) ^ N)⁻¹) ≤ (k : ℝ)⁻¹ * ((2 : ℝ)⁻¹) ^ (N / M) := by
  have ha : (0 : ℝ) < 2 ^ α := by positivity
  have hb : (0 : ℝ) < 2 ^ β := by positivity
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  set r : ℝ := (2 : ℝ) ^ β / (2 : ℝ) ^ α with hr
  have hr2 : (2 : ℝ) ^ (1 / (M : ℝ)) ≤ r := by
    rw [hr, ← Real.rpow_sub (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hMβ
  have hrM : (2 : ℝ) ≤ r ^ M := by
    have h1 : ((2 : ℝ) ^ (1 / (M : ℝ))) ^ M = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [one_div, inv_mul_cancel₀ hMR.ne', Real.rpow_one]
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / (M : ℝ))) ^ M := h1.symm
      _ ≤ r ^ M := pow_le_pow_left₀ (by positivity) hr2 M
  have hr1 : 1 ≤ r := by
    by_contra h
    push Not at h
    have : r ^ M < 1 := pow_lt_one₀ (by positivity) h hM.ne'
    linarith
  have hrN : (2 : ℝ) ^ (N / M) ≤ r ^ N := by
    calc (2 : ℝ) ^ (N / M) ≤ (r ^ M) ^ (N / M) := pow_le_pow_left₀ (by norm_num) hrM _
      _ = r ^ (M * (N / M)) := by rw [← pow_mul]
      _ ≤ r ^ N := pow_le_pow_right₀ hr1 (Nat.mul_div_le N M)
  have hcard : c ≤ ((2 : ℝ) ^ α) ^ N / k := by
    rw [le_div_iff₀ hkR]; exact hc
  calc c * ((((2 : ℝ) ^ β) ^ N)⁻¹) ≤ (((2 : ℝ) ^ α) ^ N / k) * ((((2 : ℝ) ^ β) ^ N)⁻¹) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (k : ℝ)⁻¹ * (r ^ N)⁻¹ := by
        rw [hr, div_pow]
        field_simp
    _ ≤ (k : ℝ)⁻¹ * ((2 : ℝ) ^ (N / M))⁻¹ := by
        gcongr
    _ = (k : ℝ)⁻¹ * ((2 : ℝ)⁻¹) ^ (N / M) := by rw [inv_pow]

/-- The `β`-weight of the strings of length `N` with `k < m x`, summed over the level
enumeration, is at most `k⁻¹ * 2^{-⌊N/M⌋}`. -/
private lemma supergaleNull_aux5
    {α β : ℝ} {m : BitString → ℝ} (hm : IsSupergale α m)
    (hinit : m [] ≤ 1) {M : ℕ} (hM : 0 < M) (hMβ : 1 / (M : ℝ) ≤ β - α) {k : ℕ} (hk : 0 < k)
    (N : ℕ) :
    (∑' c, (levelEnum N c).elim 0
        (fun x => if (k : ℝ) < m x then intervalAlphaMass β x else 0))
      ≤ (k : ENNReal)⁻¹ * ((2 : ENNReal)⁻¹) ^ (N / M) := by
  classical
  set F : Finset BitString := (levelFinset N).filter (fun x => (k : ℝ) < m x) with hF
  set S : Finset ℕ := F.image Encodable.encode with hS
  set G : ℕ → ENNReal := fun c => (levelEnum N c).elim 0
    (fun x => if (k : ℝ) < m x then intervalAlphaMass β x else 0) with hG
  set w : ENNReal := ENNReal.ofReal ((((2 : ℝ) ^ β) ^ N)⁻¹) with hw
  have hzero : ∀ c ∉ S, G c = 0 := by
    intro c hc
    cases hlev : levelEnum N c with
    | none => simp [hG, hlev]
    | some x =>
      simp only [hG, hlev, Option.elim_some]
      by_cases hlow : (k : ℝ) < m x
      · exfalso
        obtain ⟨hlen, hcode⟩ := levelEnum_eq_some_iff.1 hlev
        exact hc (Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨mem_levelFinset.2 hlen, hlow⟩, hcode⟩)
      · rw [ite_eq_right_iff.2 (fun h => absurd h hlow)]
  have hval : ∀ c ∈ S, G c ≤ w := by
    intro c hc
    cases hlev : levelEnum N c with
    | none => simp [hG, hlev]
    | some x =>
      simp only [hG, hlev, Option.elim_some]
      have hlen : x.length = N := (levelEnum_eq_some_iff.1 hlev).1
      by_cases hlow : (k : ℝ) < m x
      · rw [ite_eq_left hlow,
          supergaleNull_aux3,
          hlen]
      · rw [ite_eq_right_iff.2 (fun h => absurd h hlow)]; exact zero_le
  rw [tsum_eq_sum hzero]
  refine le_trans (Finset.sum_le_card_nsmul S G _ hval) ?_
  rw [nsmul_eq_mul, hS, Finset.card_image_of_injective _ Encodable.encode_injective, hw]
  have hreal :=
    supergaleNull_aux4
      (α := α) (β := β) hM hMβ hk N (F.card : ℝ)
      (supergaleNull_aux2
        hm hinit N)
  calc (F.card : ENNReal) * ENNReal.ofReal ((((2 : ℝ) ^ β) ^ N)⁻¹)
      = ENNReal.ofReal ((F.card : ℝ) * ((((2 : ℝ) ^ β) ^ N)⁻¹)) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((k : ℝ)⁻¹ * ((2 : ℝ)⁻¹) ^ (N / M)) := ENNReal.ofReal_le_ofReal hreal
    _ = (k : ENNReal)⁻¹ * ((2 : ENNReal)⁻¹) ^ (N / M) := by
        have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
        have h2 : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (N / M)) = ((2 : ENNReal)⁻¹) ^ (N / M) := by
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
          simp
        rw [ENNReal.ofReal_mul (inv_nonneg.2 hkpos.le), ENNReal.ofReal_inv_of_pos hkpos,
          ENNReal.ofReal_natCast, h2]

/-- The cover of the proof: level `N`, stage `t`, code `c`; the string `x` of code `c` and length
`N` is listed at the first stage `t` at which `k(ε) < m x` is seen. -/
private def supergaleNull_cover
    (chk : ℕ × BitString → ℕ → Bool) (kf : ℚ → ℕ) (ε : ℚ) (j : ℕ) :
    Option BitString :=
  (levelEnum (Nat.unpair j).1 (Nat.unpair (Nat.unpair j).2).2).bind
    fun x => bif firstStage chk (kf ε) x (Nat.unpair (Nat.unpair j).2).1 then some x else none

/-- The cover is computable. -/
private lemma supergaleNull_computable_cover
    {chk : ℕ × BitString → ℕ → Bool} (hchk : Computable₂ chk)
    {kf : ℚ → ℕ} (hkf : Computable kf) :
    Computable₂
      (supergaleNull_cover
        chk kf) := by
  have hlevel : Computable (fun p : ℚ × ℕ => (Nat.unpair p.2).1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd
  have hcode : Computable (fun p : ℚ × ℕ => (Nat.unpair (Nat.unpair p.2).2).2) :=
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp.comp
      Computable.snd
  have hstage : Computable (fun p : ℚ × ℕ => (Nat.unpair (Nat.unpair p.2).2).1) :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp.comp
      Computable.snd
  have hthr : Computable (fun p : ℚ × ℕ => kf p.1) := hkf.comp Computable.fst
  have hbase : Computable (fun p : ℚ × ℕ =>
      levelEnum (Nat.unpair p.2).1 (Nat.unpair (Nat.unpair p.2).2).2) :=
    computable₂_levelEnum.comp hlevel hcode
  have hbranch : Computable₂ (fun (p : ℚ × ℕ) (x : BitString) =>
      bif firstStage chk (kf p.1) x (Nat.unpair (Nat.unpair p.2).2).1 then some x else none) := by
    have htest' := (computable_firstStage hchk).comp
        (Computable.pair (Computable.pair (hthr.comp Computable.fst) Computable.snd)
          (hstage.comp Computable.fst))
    have htest : Computable (fun q : (ℚ × ℕ) × BitString =>
        firstStage chk (kf q.1.1) q.2 (Nat.unpair (Nat.unpair q.1.2).2).1) := htest'
    exact (Computable.cond htest (Computable.option_some.comp Computable.snd)
      (Computable.const none)).to₂
  exact (Computable.option_bind hbase hbranch).to₂

/-- The `t`-sum over one code: at most one stage emits, and only for strings with `k(ε) < m x`. -/
private lemma supergaleNull_stage_le
    {m : BitString → ℝ} {chk : ℕ × BitString → ℕ → Bool}
    (hmono : ∀ q s t, s ≤ t → chk q s = true → chk q t = true)
    (hspec : ∀ q : ℕ × BitString, (q.1 : ℝ) < m q.2 ↔ ∃ s, chk q s = true)
    (β : ℝ) (kf : ℚ → ℕ) (ε : ℚ) (N c : ℕ) :
    (∑' t, coverAlphaMass β
        (supergaleNull_cover
          chk kf ε (Nat.pair N (Nat.pair t c))))
      ≤ (levelEnum N c).elim 0
          (fun x => if ((kf ε : ℕ) : ℝ) < m x then intervalAlphaMass β x else 0) := by
  have hunf : ∀ t,
      supergaleNull_cover
        chk kf ε (Nat.pair N (Nat.pair t c))
      = (levelEnum N c).bind fun x => bif firstStage chk (kf ε) x t then some x else none := by
    intro t
    unfold supergaleNull_cover
    simp only [Nat.unpair_pair]
  cases hlev : levelEnum N c with
  | none =>
    have : ∀ t, coverAlphaMass β
        (supergaleNull_cover
          chk kf ε (Nat.pair N (Nat.pair t c))) = 0 := by
      intro t; rw [hunf t, hlev]; simp
    simp [this]
  | some x =>
    simp only [Option.elim_some]
    by_cases hlow : ((kf ε : ℕ) : ℝ) < m x
    · rw [ite_eq_left hlow]
      refine tsum_le_of_subsingleton_support (fun t => ?_) (fun t t' ht ht' => ?_)
      · rw [hunf t, hlev]
        simp only [Option.bind_some]
        cases hf : firstStage chk (kf ε) x t <;> simp
      · have hne : ∀ u : ℕ, coverAlphaMass β
            (supergaleNull_cover
              chk kf ε (Nat.pair N (Nat.pair u c))) ≠ 0 →
            firstStage chk (kf ε) x u = true := by
          intro u hu
          cases hff : firstStage chk (kf ε) x u with
          | true => rfl
          | false =>
            exfalso
            rw [hunf u, hlev] at hu
            simp only [Option.bind_some, hff, Bool.cond_false] at hu
            simp at hu
        exact firstStage_unique hmono (hne t ht) (hne t' ht')
    · rw [ite_eq_right_iff.2 (fun h => absurd h hlow)]
      have : ∀ t, coverAlphaMass β
          (supergaleNull_cover
            chk kf ε (Nat.pair N (Nat.pair t c))) = 0 := by
        intro t
        rw [hunf t, hlev]
        simp only [Option.bind_some]
        cases hf : firstStage chk (kf ε) x t
        · simp
        · exact absurd ((hspec (kf ε, x)).2 ⟨t, firstStage_imp hf⟩) hlow
      simp [this]

/-- Step 1 of the proof of `effectiveHausdorffDim_eq_sInf_supergale`: Theorem 186 for
lower semicomputable supergales. -/
private theorem supergaleNull
  {α β : ℝ} (hαβ : α < β) {m : BitString → ℝ} (hm : IsSupergale α m)
  (hlsc : IsLowerSemicomputableOnStrings m) (hinit : m [] ≤ 1) :
  IsEffectiveAlphaNull β {w | Wins m w} := by
  classical
  obtain ⟨M, hM, hMβ⟩ : ∃ M : ℕ, 0 < M ∧ 1 / (M : ℝ) ≤ β - α := by
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / (β - α))
    have hd : 0 < β - α := sub_pos.2 hαβ
    have h0 : (0 : ℝ) < 1 / (β - α) := by positivity
    have hMpos : 0 < M := Nat.cast_pos.1 (h0.trans hM)
    refine ⟨M, hMpos, ?_⟩
    rw [div_le_iff₀ (by exact_mod_cast hMpos)]
    rw [div_lt_iff₀ hd] at hM
    nlinarith
  have hg : Computable (fun q : ℕ × BitString => (((q.1 : ℕ) : ℚ), q.2)) :=
    (computable_nat_to_rat.comp Computable.fst).pair Computable.snd
  have hS : IsRE (fun q : ℕ × BitString => ((q.1 : ℕ) : ℝ) < m q.2) :=
    IsRE.of_iff (IsRE.compComputable hlsc hg) (fun q => by simp)
  obtain ⟨chk, hchk, hmono, hspec⟩ := hS.exists_stageApprox
  set kf : ℚ → ℕ := fun ε => 2 * M * ε.den + 1 with hkf
  have hkfc : Computable kf :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const (2 * M))
      computable_ratDen) (Computable.const 1)
  refine ⟨supergaleNull_cover
    chk kf,
    supergaleNull_computable_cover
      hchk hkfc, fun ε hε => ⟨?_, ?_⟩⟩
  · intro w hw
    have hw' : Wins m w := hw
    simp only [Wins, not_bddAbove_iff] at hw'
    obtain ⟨x, ⟨n, rfl⟩, hx⟩ := hw' ((kf ε : ℕ) : ℝ)
    obtain ⟨t, ht⟩ := exists_firstStage ((hspec (kf ε, cantorPrefix w n)).1 hx)
    refine Set.mem_iUnion.2 ⟨Nat.pair n (Nat.pair t (Encodable.encode (cantorPrefix w n))), ?_⟩
    have hval :
        supergaleNull_cover
          chk kf ε (Nat.pair n (Nat.pair t (Encodable.encode (cantorPrefix w n))))
        = some (cantorPrefix w n) := by
      unfold supergaleNull_cover
      simp only [Nat.unpair_pair]
      rw [levelEnum_encode (cantorPrefix_length w n)]
      simp only [Option.bind_some, ht, Bool.cond_true]
    rw [hval]
    exact mem_cantorCylinder_cantorPrefix w n
  · set F : ℕ → ENNReal := fun j => coverAlphaMass β
      (supergaleNull_cover
        chk kf ε j) with hF
    have hkpos : 0 < kf ε := by simp [hkf]
    have hstep1 : (∑' j, F j) = ∑' N, ∑' s, F (Nat.pair N s) := tsum_nat_pair F
    have hstep2 : ∀ N : ℕ,
        (∑' s, F (Nat.pair N s)) = ∑' t, ∑' c, F (Nat.pair N (Nat.pair t c)) :=
      fun N => tsum_nat_pair (fun s => F (Nat.pair N s))
    have hstep3 : ∀ N : ℕ,
        (∑' t, ∑' c, F (Nat.pair N (Nat.pair t c)))
          = ∑' c, ∑' t, F (Nat.pair N (Nat.pair t c)) :=
      fun N => ENNReal.tsum_comm
    have hlevel : ∀ N : ℕ,
        (∑' c, ∑' t, F (Nat.pair N (Nat.pair t c)))
          ≤ ((kf ε : ℕ) : ENNReal)⁻¹ * ((2 : ENNReal)⁻¹) ^ (N / M) := fun N =>
      le_trans (ENNReal.tsum_le_tsum (fun c =>
        supergaleNull_stage_le
          hmono hspec β kf ε N c))
        (supergaleNull_aux5
          hm hinit hM hMβ hkpos N)
    have hsum : (∑' j, F j) ≤ ((kf ε : ℕ) : ENNReal)⁻¹ * ((M : ENNReal) * 2) := by
      calc (∑' j, F j) = ∑' N, ∑' c, ∑' t, F (Nat.pair N (Nat.pair t c)) := by
            rw [hstep1]; exact tsum_congr (fun N => (hstep2 N).trans (hstep3 N))
        _ ≤ ∑' N : ℕ, ((kf ε : ℕ) : ENNReal)⁻¹ * ((2 : ENNReal)⁻¹) ^ (N / M) :=
            ENNReal.tsum_le_tsum hlevel
        _ = ((kf ε : ℕ) : ENNReal)⁻¹ * ∑' N : ℕ, ((2 : ENNReal)⁻¹) ^ (N / M) :=
            ENNReal.tsum_mul_left
        _ = ((kf ε : ℕ) : ENNReal)⁻¹ * ((M : ENNReal) * 2) := by
            rw [tsum_inv_two_pow_natDiv M hM]
    refine lt_of_le_of_lt hsum ?_
    have hkR : (0 : ℝ) < ((kf ε : ℕ) : ℝ) := by exact_mod_cast hkpos
    have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hdR : (0 : ℝ) < (ε.den : ℝ) := by exact_mod_cast ε.pos
    have hconv : ((kf ε : ℕ) : ENNReal)⁻¹ * ((M : ENNReal) * 2)
        = ENNReal.ofReal ((((kf ε : ℕ) : ℝ))⁻¹ * ((M : ℝ) * 2)) := by
      rw [ENNReal.ofReal_mul (inv_nonneg.2 hkR.le), ENNReal.ofReal_inv_of_pos hkR,
        ENNReal.ofReal_natCast, ENNReal.ofReal_mul hMR.le, ENNReal.ofReal_natCast]
      simp
    rw [hconv]
    refine (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hε)).2 ?_
    have h1 : (((kf ε : ℕ) : ℝ))⁻¹ * ((M : ℝ) * 2) < 1 / (ε.den : ℝ) := by
      rw [inv_mul_eq_div, div_lt_div_iff₀ hkR hdR]
      simp only [hkf]
      push_cast
      nlinarith
    exact h1.trans_le (one_div_den_le_rat hε)

/-- **SUV p. 287.**  Theorem 187 for `α`-supergales. -/
theorem effectiveHausdorffDim_eq_sInf_supergale (A : Set CantorSeq) :
    effectiveHausdorffDim A = sInf {α : ℝ | 0 < α ∧ ComputableReals.IsComputableReal α ∧
      ∃ m, IsSupergale α m ∧ IsLowerSemicomputableOnStrings m ∧ m [] ≤ 1 ∧ ∀ w ∈ A, Wins m w} := by
  obtain ⟨m2, hm2⟩ : ∃ m2 : BitString → ℝ, ∀ x, m2 x = (2:ℝ) ^ x.length := ⟨_, fun _ => rfl⟩
  have hG2 : IsGale 2 m2 := by
    refine ⟨fun x => by rw [hm2]; positivity, fun x => ?_⟩
    have h4 : (2:ℝ) ^ (2:ℝ) = 4 := by rw [Real.rpow_two]; norm_num
    rw [h4]; simp only [hm2, List.length_append, List.length_singleton, pow_succ]; ring
  have hlsc2 : IsLowerSemicomputableOnStrings m2 := by
    unfold IsLowerSemicomputableOnStrings
    refine isRE_of_computable_bool _
      (fun p : ℚ × BitString => decide (p.1 < ((2 ^ p.2.length : ℕ) : ℚ))) ?_ ?_
    · intro p
      rw [decide_eq_true_eq, hm2]
      constructor <;> intro h <;> exact_mod_cast h
    · have hg : Computable (fun p : ℚ × BitString => (((2 ^ p.2.length : ℕ)) : ℚ)) :=
        computable_nat_to_rat.comp (nat_pow_primrec₂.comp (Primrec.const 2)
          (Primrec.list_length.comp Primrec.snd)).to_comp
      exact computable₂_ratLt.comp Computable.fst hg
  have hwins2 : ∀ w : CantorSeq, Wins m2 w := by
    intro w
    unfold Wins
    rintro ⟨B, hB⟩
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (by norm_num : (1:ℝ) < 2)
    have := hB (Set.mem_range_self n)
    rw [show m2 (cantorPrefix w n) = (2:ℝ) ^ (cantorPrefix w n).length from hm2 _] at this
    rw [cantorPrefix_length] at this
    linarith
  have hGne : {α : ℝ | 0 < α ∧ ComputableReals.IsComputableReal α ∧ ∃ m, IsGale α m ∧
      IsLowerSemicomputableOnStrings m ∧ m [] ≤ 1 ∧ ∀ w ∈ A, Wins m w}.Nonempty :=
    ⟨2, by norm_num, by simpa using ComputableReals.isComputableReal_ratCast (2:ℚ), m2, hG2, hlsc2,
      by rw [hm2]; simp, fun w _ => hwins2 w⟩
  have hsub : {α : ℝ | 0 < α ∧ ComputableReals.IsComputableReal α ∧ ∃ m, IsGale α m ∧
      IsLowerSemicomputableOnStrings m ∧ m [] ≤ 1 ∧ ∀ w ∈ A, Wins m w} ⊆
      {α : ℝ | 0 < α ∧ ComputableReals.IsComputableReal α ∧ ∃ m, IsSupergale α m ∧
      IsLowerSemicomputableOnStrings m ∧ m [] ≤ 1 ∧ ∀ w ∈ A, Wins m w} :=
    fun α ⟨h0, hc, m, hm, h⟩ => ⟨h0, hc, m, hm.isSupergale, h⟩
  refine le_antisymm ?_ ?_
  · refine le_csInf (hGne.mono hsub) ?_
    rintro α ⟨hα0, hαc, m, hm, hlsc, hinit, hw⟩
    refine le_of_forall_gt_imp_ge_of_dense fun q hq => ?_
    obtain ⟨r, hαr, hrq⟩ := exists_rat_btwn hq
    have hnull :=
        (supergaleNull
      hαr hm hlsc hinit).mono_set
      (fun w hw' => hw w hw')
    exact (csInf_le (bddBelow_effectiveAlphaSet A)
      ⟨by exact_mod_cast hα0.trans hαr, hnull⟩).trans hrq.le
  · exact (csInf_le_csInf ⟨0, fun α hα => hα.1.le⟩ hGne hsub).trans
      (effectiveHausdorffDim_eq_sInf_gale A).symm.le

/-- Step 1 of the proof of `effectiveHausdorffDim_singleton_eq_liminf_KA`: bound the
absolute difference between `KA` and `plainK`. -/
private lemma effectiveHausdorffDim_singleton_eq_liminf_KA_abs_sub_le (V U : Map)
    (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℝ, ∀ x : BitString,
      |KA x - ((plainK V x).toNat : ℝ)| ≤ 2 * Real.logb 2 ((x.length : ℝ) + 1) + c := by
  have toNat_le_add_of_le : ∀ {a b : ℕ∞} {c : ℕ}, a ≤ b + (c : ℕ∞) → b ≠ ⊤ →
      a.toNat ≤ b.toNat + c := by
    intro a b c h hb
    have hrhs : b + (c : ℕ∞) ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hb, ENat.natCast_ne_top c⟩
    have h' := ENat.toNat_le_toNat h hrhs
    rwa [ENat.toNat_add hb (ENat.natCast_ne_top c), ENat.toNat_natCast] at h'
  obtain ⟨c₀, h₀⟩ := plain_le_prefix V U hV hU.isPrefixDecompressor
  obtain ⟨c₁, h₁⟩ := KPPlain_le_KA_add_two_mul_log_length U hU
  obtain ⟨c₂, h₂⟩ := KA_le_KPPlain U hU
  obtain ⟨c₄, h₄⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨c₅, h₅⟩ := plainK_le_length V hV
  obtain ⟨c₆, h₆⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨max (c₀ + c₁) (c₂ + (c₄ + c₆ : ℕ) + 2 * Real.logb 2 ((c₅ : ℝ) + 1) + 2), fun x => ?_⟩
  have hlogmono : Real.logb 2 (x.length : ℝ) ≤ Real.logb 2 ((x.length : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos x.length with h | h
    · rw [h]
      simp only [Nat.cast_zero, Real.logb_zero]
      exact Real.logb_nonneg (by norm_num) (by norm_num)
    · exact (Real.logb_le_logb (by norm_num) (by exact_mod_cast h) (by positivity)).mpr
        (by linarith)
  have hmA : c₀ + c₁ ≤ max (c₀ + c₁) (c₂ + (c₄ + c₆ : ℕ) + 2 * Real.logb 2 ((c₅ : ℝ) + 1) + 2) :=
    le_max_left _ _
  have hmB : c₂ + (c₄ + c₆ : ℕ) + 2 * Real.logb 2 ((c₅ : ℝ) + 1) + 2 ≤
      max (c₀ + c₁) (c₂ + (c₄ + c₆ : ℕ) + 2 * Real.logb 2 ((c₅ : ℝ) + 1) + 2) :=
    le_max_right _ _
  rw [abs_sub_le_iff]
  constructor
  · -- `KA x ≤ C x + 2 log (l x + 1) + c`
    set kC : ℕ := (plainK V x).toNat with hkC
    have hfin : plainK V x = (kC : ℕ∞) :=
      (ENat.natCast_toNat (plainK_ne_top_of_isOptimalConditional hV x)).symm
    set L : ℕ := (Nat.bits kC).length with hL
    have hK : KPPlain U x ≤ ((kC + 2 * L + (c₄ + c₆) : ℕ) : ℕ∞) := by
      have hB : KPPlain U x ≤ (kC : ℕ∞) + KPPlain U (Nat.bits kC) + (c₄ : ℕ∞) := h₄ x kC hfin
      have hC : KPPlain U (Nat.bits kC) ≤ 2 * (L : ℕ∞) + (c₆ : ℕ∞) := by
        simpa [hL] using h₆ (Nat.bits kC)
      calc KPPlain U x ≤ (kC : ℕ∞) + KPPlain U (Nat.bits kC) + (c₄ : ℕ∞) := hB
        _ ≤ (kC : ℕ∞) + (2 * (L : ℕ∞) + (c₆ : ℕ∞)) + (c₄ : ℕ∞) := by gcongr
        _ = ((kC + 2 * L + (c₄ + c₆) : ℕ) : ℕ∞) := by push_cast; ring
    have hnat : (KPPlain U x).toNat ≤ kC + 2 * L + (c₄ + c₆) :=
      ENat.toNat_le_toNat hK (ENat.natCast_ne_top _)
    have hreal : ((KPPlain U x).toNat : ℝ) ≤ (kC : ℝ) + 2 * (L : ℝ) + ((c₄ + c₆ : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hLlog : (L : ℝ) ≤ Real.logb 2 (kC : ℝ) + 1 := natBits_length_le_logb_add_one kC
    have hkCle : kC ≤ x.length + c₅ := by
      have := h₅ x
      have h' : plainK V x ≤ ((x.length + c₅ : ℕ) : ℕ∞) := by push_cast; exact_mod_cast this
      have := ENat.toNat_le_toNat h' (ENat.natCast_ne_top _)
      exact (by rwa [hkC] : kC ≤ x.length + c₅)
    have hkCreal : (kC : ℝ) ≤ (x.length : ℝ) + (c₅ : ℝ) := by exact_mod_cast hkCle
    have hlogkC : Real.logb 2 (kC : ℝ) ≤ Real.logb 2 ((x.length : ℝ) + (c₅ : ℝ)) := by
      rcases Nat.eq_zero_or_pos kC with h | h
      · rw [h]
        simp only [Nat.cast_zero, Real.logb_zero]
        rcases Nat.eq_zero_or_pos (x.length + c₅) with h0 | hpos
        · have hx : (x.length : ℝ) + (c₅ : ℝ) = 0 := by
            have hx0 : x.length = 0 := by omega
            have hc0 : c₅ = 0 := by omega
            simp [hx0, hc0]
          rw [hx]
          simp
        · exact Real.logb_nonneg (by norm_num) (by
            have h1 : (1 : ℝ) ≤ ((x.length + c₅ : ℕ) : ℝ) := by exact_mod_cast hpos
            push_cast at h1
            linarith)
      · exact (Real.logb_le_logb (by norm_num) (by exact_mod_cast h)
          (by
            have : (0 : ℝ) < (kC : ℝ) := by exact_mod_cast h
            linarith)).mpr hkCreal
    have hsplit := logb_two_nat_add_le x.length c₅
    have h2 := h₂ x
    have hplain : ((plainK V x).toNat : ℝ) = (kC : ℝ) := by rw [hkC]
    rw [hplain]
    push_cast at hreal hmB ⊢
    linarith
  · -- `C x ≤ KA x + 2 log (l x + 1) + c`
    have hstep0 : (plainK V x).toNat ≤ (KPPlain U x).toNat + c₀ :=
      toNat_le_add_of_le (h₀ x) (KPPlain_ne_top_of_isOptimalPrefixConditional hU x)
    have hstep0' : ((plainK V x).toNat : ℝ) ≤ ((KPPlain U x).toNat : ℝ) + c₀ := by
      exact_mod_cast hstep0
    have h1 := h₁ x
    linarith

/-- Auxiliary real-analysis fact for Step 2: two real sequences with eventually small differences,
the second one eventually in `[0, M]`, have the same lower limit. -/
private lemma effectiveHausdorffDim_singleton_eq_liminf_KA_liminf_aux_liminf_eq
    (a b : ℕ → ℝ) (M : ℝ) (hb0 : ∀ᶠ n in atTop, 0 ≤ b n) (hbM : ∀ᶠ n in atTop, b n ≤ M)
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, |a n - b n| ≤ δ) :
    liminf a atTop = liminf b atTop := by
  have h1 := h 1 one_pos
  have hbb : Filter.IsBoundedUnder (· ≥ ·) atTop b :=
    Filter.isBoundedUnder_of_eventually_ge (a := 0) hb0
  have hbc : Filter.IsCoboundedUnder (· ≥ ·) atTop b :=
    Filter.isCoboundedUnder_ge_of_eventually_le atTop hbM
  have hab : Filter.IsBoundedUnder (· ≥ ·) atTop a :=
    Filter.isBoundedUnder_of_eventually_ge (a := -1) (by
      filter_upwards [h1, hb0] with n hn hn0
      have := (abs_le.mp hn).1
      linarith)
  have hac : Filter.IsCoboundedUnder (· ≥ ·) atTop a :=
    Filter.isCoboundedUnder_ge_of_eventually_le atTop (x := M + 1) (by
      filter_upwards [h1, hbM] with n hn hnM
      have := (abs_le.mp hn).2
      linarith)
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hbd : Filter.IsCoboundedUnder (· ≥ ·) atTop (fun n => b n + δ) :=
      Filter.isCoboundedUnder_ge_of_eventually_le atTop (x := M + δ) (by
        filter_upwards [hbM] with n hn
        linarith)
    calc liminf a atTop ≤ liminf (fun n => b n + δ) atTop := by
          refine Filter.liminf_le_liminf ?_ hab hbd
          filter_upwards [h δ hδ] with n hn
          have := (abs_le.mp hn).2
          linarith
      _ = liminf b atTop + δ := liminf_add_const atTop b δ hbc hbb
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have had : Filter.IsCoboundedUnder (· ≥ ·) atTop (fun n => a n + δ) :=
      Filter.isCoboundedUnder_ge_of_eventually_le atTop (x := M + 1 + δ) (by
        filter_upwards [h1, hbM] with n hn hnM
        have := (abs_le.mp hn).2
        linarith)
    calc liminf b atTop ≤ liminf (fun n => a n + δ) atTop := by
          refine Filter.liminf_le_liminf ?_ hbb had
          filter_upwards [h δ hδ] with n hn
          have := (abs_le.mp hn).1
          linarith
      _ = liminf a atTop + δ := liminf_add_const atTop a δ hac hab

/-- Auxiliary asymptotics for Step 2: `(2 log₂(n+1) + c) / n → 0`. -/
private lemma effectiveHausdorffDim_singleton_eq_liminf_KA_liminf_aux_tendsto (c : ℝ) :
    Tendsto (fun n : ℕ => (2 * Real.logb 2 ((n : ℝ) + 1) + c) / (n : ℝ)) atTop (nhds 0) := by
  have h0 := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have h1 : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ)) atTop (nhds 0) := by
    refine h0.congr fun n => ?_
    simp only [Function.comp, pow_one]
    congr 1
    ring
  have h2 : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h3 := ((h1.const_mul (2 / Real.log 2)).add h2)
  rw [mul_zero, zero_add] at h3
  refine h3.congr fun n => ?_
  simp only [Real.logb]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (n : ℝ) ≠ 0 := by positivity
    field_simp

/-- Step 2 of the proof of `effectiveHausdorffDim_singleton_eq_liminf_KA`: the liminf of
the two complexities ratio is the same. -/
private lemma effectiveHausdorffDim_singleton_eq_liminf_KA_liminf (w : CantorSeq)
    (V : Map) (hV : isOptimalConditional V) :
    liminf (fun n : ℕ => KA (cantorPrefix w n) / (n : ℝ)) atTop =
      liminf (fun n : ℕ => ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ)) atTop := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c, hc⟩ := effectiveHausdorffDim_singleton_eq_liminf_KA_abs_sub_le V U hV hU
  obtain ⟨c', hc'⟩ := plainK_le_length V hV
  have htoNat : ∀ n : ℕ, (plainK V (cantorPrefix w n)).toNat ≤ n + c' := by
    intro n
    have h1 := hc' (cantorPrefix w n)
    simp only [programLength, cantorPrefix_length] at h1
    have hrhs : ((n : ℕ∞) + (c' : ℕ∞)) ≠ ⊤ :=
      WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top n, ENat.natCast_ne_top c'⟩
    have h2 := ENat.toNat_le_toNat h1 hrhs
    rwa [ENat.toNat_add (ENat.natCast_ne_top n) (ENat.natCast_ne_top c'), ENat.toNat_natCast,
      ENat.toNat_natCast] at h2
  refine effectiveHausdorffDim_singleton_eq_liminf_KA_liminf_aux_liminf_eq _ _ (1 + c')
    (Filter.Eventually.of_forall fun n => by positivity) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hcast : ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤ (n : ℝ) + (c' : ℝ) := by
      exact_mod_cast htoNat n
    rw [div_le_iff₀ hnpos]
    have : (c' : ℝ) ≤ (c' : ℝ) * (n : ℝ) := by
      nlinarith [(by positivity : (0 : ℝ) ≤ (c' : ℝ))]
    nlinarith
  · intro δ hδ
    have ht := (effectiveHausdorffDim_singleton_eq_liminf_KA_liminf_aux_tendsto c).eventually
      (Iio_mem_nhds hδ)
    filter_upwards [ht, Filter.eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have := hc (cantorPrefix w n)
    rw [cantorPrefix_length] at this
    rw [← sub_div, abs_div, abs_of_pos hnpos]
    rw [div_le_iff₀ hnpos]
    rw [div_lt_iff₀ hnpos] at hn
    linarith

/-- **SUV p. 287.**  The alternative route to Theorem 120 through the maximal semimeasure: the
effective dimension of a point is the lower limit of `KA(ω_0 … ω_{n-1}) / n`.  The library's
Theorem 120, `effectiveHausdorffDim_singleton_eq_liminf`, is the plain-complexity form. -/
theorem effectiveHausdorffDim_singleton_eq_liminf_KA (w : CantorSeq) :
    effectiveHausdorffDim {w} =
      liminf (fun n : ℕ => KA (cantorPrefix w n) / (n : ℝ)) atTop := by
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  rw [effectiveHausdorffDim_singleton_eq_liminf_KA_liminf w V hV]
  exact effectiveHausdorffDim_singleton_eq_liminf V hV w

end FrequencyGames
end Kolmogorov
