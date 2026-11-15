/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.PartialRules
import KolmogorovMathlib.Complexity.Applications.LipschitzBesicovitch
import KolmogorovMathlib.Oracle.KraftChaitin
import KolmogorovMathlib.Oracle.PrefixComplexity.MonotonicityThreshold
import Mathlib.Data.Bool.Count
import KolmogorovMathlib.MonotoneComplexity.GacsDayPartrecFold

/-!
# Bounded Bet Strategy

Bets of bounded size against a set of strings of a fixed length.  The main declarations are
`betGainOnOne`, the total gain of a betting strategy on a finite string (with a positive bet
meaning a bet on `1`), and `exists_bet_strategy_of_card_le`, the lemma of Shen, Uspensky and
Vereshchagin (p. 294) that a set `A` of `n`-bit strings with at most `2^s` elements admits a
strategy with bets in `[-1, 1]` winning at least `n - s` on every element of `A`.  The remaining
lemmas apply this to relate the plain complexity of prefixes to Mises-Kolmogorov-Loveland
randomness in the discussion of non-monotone selection rules.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-! ### Fixed-size bets and the complexity of prefixes -/

/-- The gain in the bounded-bet game with the convention of **SUV p. 293**: a positive value is a
bet on `1`.  Theorem 170 uses the opposite one (`betGain`, p. 266). -/
noncomputable def betGainOnOne (S : BitString → ℝ) (x : BitString) : ℝ :=
  ∑ i : Fin x.length, S (x.take i) * (if x[i] then 1 else -1)

private noncomputable def exists_bet_strategy_of_card_le_c (A : Finset BitString) (x : BitString) :
    ℕ :=
  (A.filter (fun y => x <+: y)).card

private noncomputable def exists_bet_strategy_of_card_le_S (A : Finset BitString) (x : BitString) :
    ℝ :=
  let c := exists_bet_strategy_of_card_le_c A x
  let c1 := exists_bet_strategy_of_card_le_c A (x ++ [true])
  if c == 0 then 0
  else if c1 == 0 then -1
  else min 1 (max (-1) (Real.logb 2 (2 * (c1 : ℝ) / (c : ℝ))))

private noncomputable def exists_bet_strategy_of_card_le_I (A : Finset BitString) (n : ℕ)
    (x : BitString) : ℝ :=
  let c := exists_bet_strategy_of_card_le_c A x
  if c == 0 then 0 else (n : ℝ) - x.length - Real.logb 2 (c : ℝ)

/-- Step 1 of the proof of `exists_bet_strategy_of_card_le`: the bet is always in [-1, 1].
-/
private lemma exists_bet_strategy_of_card_le_bound (A : Finset BitString) (x : BitString) :
    |exists_bet_strategy_of_card_le_S A x| ≤ 1 := by
  dsimp [exists_bet_strategy_of_card_le_S]
  split_ifs
  · norm_num
  · norm_num
  · rcases le_total (Real.logb 2 (2 * (exists_bet_strategy_of_card_le_c A (x ++ [true]) : ℝ) /
      (exists_bet_strategy_of_card_le_c A x : ℝ))) (-1) with h | h
    · have : max (-1) (Real.logb 2 (2 * (exists_bet_strategy_of_card_le_c A (x ++ [true]) : ℝ) /
        (exists_bet_strategy_of_card_le_c A x : ℝ))) = -1 := max_eq_left h
      rw [this]
      norm_num
    · have : max (-1) (Real.logb 2 (2 * (exists_bet_strategy_of_card_le_c A (x ++ [true]) : ℝ) /
        (exists_bet_strategy_of_card_le_c A x : ℝ))) = Real.logb 2
        (2 * (exists_bet_strategy_of_card_le_c A (x ++ [true]) : ℝ) /
        (exists_bet_strategy_of_card_le_c A x : ℝ)) := max_eq_right h
      rw [this]
      rcases le_total (Real.logb 2 (2 * (exists_bet_strategy_of_card_le_c A (x ++ [true]) : ℝ) /
          (exists_bet_strategy_of_card_le_c A x : ℝ))) 1 with h2 | h2
      · have : min 1 (Real.logb 2 (2 * (exists_bet_strategy_of_card_le_c A (x ++ [true]) : ℝ) /
          (exists_bet_strategy_of_card_le_c A x : ℝ))) = Real.logb 2
          (2 * (exists_bet_strategy_of_card_le_c A (x ++ [true]) : ℝ) /
          (exists_bet_strategy_of_card_le_c A x : ℝ)) := min_eq_right h2
        rw [this]
        exact abs_le.mpr ⟨h, h2⟩
      · have : min 1 (Real.logb 2 (2 * (exists_bet_strategy_of_card_le_c A (x ++ [true]) : ℝ) /
          (exists_bet_strategy_of_card_le_c A x : ℝ))) = 1 := min_eq_left h2
        rw [this]
        norm_num

/-- Step 2 of the proof of `exists_bet_strategy_of_card_le`: the initial information
capital is at least n - s. -/
private lemma exists_bet_strategy_of_card_le_init (n : ℕ) {s : ℝ} (A : Finset BitString)
    (hA : A.Nonempty)
    (hcard : (A.card : ℝ) ≤ (2 : ℝ) ^ s) :
    (n : ℝ) - s ≤ exists_bet_strategy_of_card_le_I A n [] := by
  have hc : exists_bet_strategy_of_card_le_c A [] = A.card := by
    unfold exists_bet_strategy_of_card_le_c
    simp
  have hpos : 0 < A.card := Finset.card_pos.mpr hA
  have hposR : (0 : ℝ) < A.card := by exact_mod_cast hpos
  have hlog : Real.logb 2 (A.card : ℝ) ≤ s :=
    (Real.logb_le_iff_le_rpow (by norm_num) hposR).mpr hcard
  unfold exists_bet_strategy_of_card_le_I
  simp only [hc]
  have hne : (A.card == 0) = false := by simpa using hpos.ne'
  rw [hne]
  simp only [Bool.false_eq_true, ite_false, List.length_nil, Nat.cast_zero]
  linarith

/-- Step 3(a) of the proof: the c-split lemma. -/
private lemma exists_bet_strategy_of_card_le_c_split (A : Finset BitString) (n : ℕ)
    (hlen : ∀ x ∈ A, x.length = n) (x : BitString) (hx : x.length < n) :
    exists_bet_strategy_of_card_le_c A x = exists_bet_strategy_of_card_le_c A (x ++ [false]) +
        exists_bet_strategy_of_card_le_c A (x ++ [true]) := by
  unfold exists_bet_strategy_of_card_le_c
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hyA, t, rfl⟩
      have hl := hlen _ hyA
      rcases t with _ | ⟨b, t'⟩
      · simp at hl; omega
      · cases b
        · left; exact ⟨hyA, t', by simp⟩
        · right; exact ⟨hyA, t', by simp⟩
    · rintro (⟨hyA, h⟩ | ⟨hyA, h⟩)
      · exact ⟨hyA, (List.prefix_append _ _).trans h⟩
      · exact ⟨hyA, (List.prefix_append _ _).trans h⟩
  · rw [Finset.disjoint_filter]
    intro y _ h1 h2
    have := List.prefix_of_prefix_length_le h1 h2 (by simp)
    have h3 := this.eq_of_length (by simp)
    simp at h3

/-- Step 3(b) of the proof: one-step inequality. -/
private lemma exists_bet_strategy_of_card_le_one_step (A : Finset BitString) (n : ℕ)
    (hlen : ∀ x ∈ A, x.length = n) (x : BitString) (b : Bool) (hx : x.length < n)
        (hc : 0 < exists_bet_strategy_of_card_le_c A (x ++ [b])) :
    exists_bet_strategy_of_card_le_I A n x ≤ exists_bet_strategy_of_card_le_I A n (x ++ [b]) +
        exists_bet_strategy_of_card_le_S A x * (if b then 1 else -1) := by
  have hsplit := exists_bet_strategy_of_card_le_c_split A n hlen x hx
  set c := exists_bet_strategy_of_card_le_c A x with hcdef
  set c0 := exists_bet_strategy_of_card_le_c A (x ++ [false]) with hc0def
  set c1 := exists_bet_strategy_of_card_le_c A (x ++ [true]) with hc1def
  have hcpos : 0 < c := by
    cases b
    · have : 0 < c0 := hc
      omega
    · have : 0 < c1 := hc
      omega
  have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hsplitR : (c : ℝ) = c0 + c1 := by exact_mod_cast hsplit
  have hIx : exists_bet_strategy_of_card_le_I A n x = (n : ℝ) - x.length - Real.logb 2 (c : ℝ) := by
    unfold exists_bet_strategy_of_card_le_I
    simp [← hcdef, hcpos.ne']
  have hle1 : (c1 : ℝ) ≤ c := by
    have : (0:ℝ) ≤ c0 := by positivity
    linarith
  have hle0 : (c0 : ℝ) ≤ c := by
    have : (0:ℝ) ≤ c1 := by positivity
    linarith
  have hSc : exists_bet_strategy_of_card_le_S A x = if c1 = 0 then -1 else
      min 1 (max (-1) (Real.logb 2 (2 * (c1 : ℝ) / (c : ℝ)))) := by
    unfold exists_bet_strategy_of_card_le_S
    simp [← hcdef, ← hc1def, hcpos.ne']
  cases b
  · -- b = false
    simp only [Bool.false_eq_true, ite_false] at hc ⊢
    have hc0pos : 0 < c0 := hc
    have hc0R : (0 : ℝ) < c0 := by exact_mod_cast hc0pos
    have hI0 : exists_bet_strategy_of_card_le_I A n (x ++ [false]) =
        (n : ℝ) - ((x.length : ℝ) + 1) - Real.logb 2 (c0 : ℝ) := by
      unfold exists_bet_strategy_of_card_le_I
      simp [← hc0def, hc0pos.ne']
    rw [hIx, hI0, hSc]
    by_cases h1 : c1 = 0
    · have : c = c0 := by omega
      have hcc : (c : ℝ) = c0 := by exact_mod_cast this
      simp [h1, hcc]
      linarith
    · have hc1pos : 0 < c1 := Nat.pos_of_ne_zero h1
      have hc1R : (0 : ℝ) < c1 := by exact_mod_cast hc1pos
      simp only [h1, ite_false]
      have hL : Real.logb 2 (2 * (c1 : ℝ) / (c : ℝ)) = 1 + Real.logb 2 c1 - Real.logb 2 c := by
        rw [Real.logb_div (by positivity) hcR.ne', Real.logb_mul (by norm_num) hc1R.ne',
          Real.logb_self_eq_one (by norm_num)]
      have hm : Real.logb 2 (c0 : ℝ) ≤ Real.logb 2 c :=
        Real.logb_le_logb_of_le one_lt_two hc0R hle0
      have hAM : Real.logb 2 (4 * (c0 : ℝ) * c1) ≤ Real.logb 2 ((c : ℝ) ^ 2) :=
        Real.logb_le_logb_of_le one_lt_two (by positivity)
          (by rw [hsplitR]; nlinarith [sq_nonneg ((c0 : ℝ) - c1)])
      have h4 : Real.logb 2 (4 * (c0 : ℝ) * c1) = 2 + Real.logb 2 c0 + Real.logb 2 c1 := by
        rw [Real.logb_mul (by positivity) hc1R.ne', Real.logb_mul (by norm_num) hc0R.ne']
        have : Real.logb 2 (4 : ℝ) = 2 := by
          have : (4 : ℝ) = 2 ^ 2 := by norm_num
          rw [this, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
          norm_num
        rw [this]
      have h5 : Real.logb 2 ((c : ℝ) ^ 2) = 2 * Real.logb 2 c := by
        rw [Real.logb_pow]; norm_num
      have hmin : min 1 (max (-1) (Real.logb 2 (2 * (c1 : ℝ) / (c : ℝ)))) ≤
          max (-1) (Real.logb 2 (2 * (c1 : ℝ) / (c : ℝ))) := min_le_right _ _
      have hmax : max (-1) (Real.logb 2 (2 * (c1 : ℝ) / (c : ℝ))) ≤
          Real.logb 2 c - 1 - Real.logb 2 c0 := by
        apply max_le
        · linarith
        · rw [hL]; linarith
      linarith
  · -- b = true
    simp only [ite_true] at hc ⊢
    have hc1pos : 0 < c1 := hc
    have hc1R : (0 : ℝ) < c1 := by exact_mod_cast hc1pos
    have hI1 : exists_bet_strategy_of_card_le_I A n (x ++ [true]) =
        (n : ℝ) - ((x.length : ℝ) + 1) - Real.logb 2 (c1 : ℝ) := by
      unfold exists_bet_strategy_of_card_le_I
      simp [← hc1def, hc1pos.ne']
    rw [hIx, hI1, hSc]
    simp only [hc1pos.ne', ite_false]
    have hL : Real.logb 2 (2 * (c1 : ℝ) / (c : ℝ)) = 1 + Real.logb 2 c1 - Real.logb 2 c := by
      rw [Real.logb_div (by positivity) hcR.ne', Real.logb_mul (by norm_num) hc1R.ne',
        Real.logb_self_eq_one (by norm_num)]
    have hm : Real.logb 2 (c1 : ℝ) ≤ Real.logb 2 c :=
      Real.logb_le_logb_of_le one_lt_two hc1R hle1
    have hge : Real.logb 2 (2 * (c1 : ℝ) / (c : ℝ)) ≤
        min 1 (max (-1) (Real.logb 2 (2 * (c1 : ℝ) / (c : ℝ)))) := by
      apply le_min
      · rw [hL]; linarith
      · exact le_max_right _ _
    linarith

/-- Step 3(c) of the proof: telescoping along y.take k. -/
private lemma exists_bet_strategy_of_card_le_telescope (A : Finset BitString) (n : ℕ)
    (hlen : ∀ x ∈ A, x.length = n) (y : BitString) (hy : y ∈ A) :
    exists_bet_strategy_of_card_le_I A n [] ≤ exists_bet_strategy_of_card_le_I A n y + betGainOnOne
        (exists_bet_strategy_of_card_le_S A) y := by
  have hyn : y.length = n := hlen y hy
  have hgain : betGainOnOne (exists_bet_strategy_of_card_le_S A) y = ∑ i ∈ Finset.range y.length,
      exists_bet_strategy_of_card_le_S A (y.take i) * (if y.getD i false then 1 else -1) := by
    unfold betGainOnOne
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => exists_bet_strategy_of_card_le_S A (y.take i) * (if y.getD i false then 1 else -1))
          y.length]
    apply Finset.sum_congr rfl
    intro i _
    rw [List.getD_eq_getElem _ _ i.2]
    rfl
  have key : ∀ k, k ≤ y.length → exists_bet_strategy_of_card_le_I A n [] ≤
      exists_bet_strategy_of_card_le_I A n (y.take k) +
        ∑ i ∈ Finset.range k,
          exists_bet_strategy_of_card_le_S A (y.take i) * (if y.getD i false then 1 else -1) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k < y.length := hk
      have h1 := ih hk'.le
      have htake : y.take (k + 1) = y.take k ++ [y.getD k false] := by
        rw [List.take_add_one, List.getD_eq_getElem _ _ hk']
        simp [List.getElem?_eq_getElem hk']
      have hc : 0 < exists_bet_strategy_of_card_le_c A (y.take k ++ [y.getD k false]) := by
        rw [← htake]
        unfold exists_bet_strategy_of_card_le_c
        apply Finset.card_pos.mpr
        exact ⟨y, Finset.mem_filter.mpr ⟨hy, List.take_prefix _ _⟩⟩
      have hx : (y.take k).length < n := by
        rw [List.length_take]; omega
      have h2 := exists_bet_strategy_of_card_le_one_step A n hlen (y.take k) (y.getD k false)
          hx hc
      rw [← htake] at h2
      rw [Finset.sum_range_succ]
      linarith
  have := key y.length le_rfl
  rw [List.take_length] at this
  rw [hgain]
  exact this

/-- Step 4 of the proof of `exists_bet_strategy_of_card_le`: the final information capital
is at most 0. -/
private lemma exists_bet_strategy_of_card_le_end (A : Finset BitString) (n : ℕ)
    (hlen : ∀ x ∈ A, x.length = n) (y : BitString) (hy : y ∈ A) :
    exists_bet_strategy_of_card_le_I A n y ≤ 0 := by
  have hc : exists_bet_strategy_of_card_le_c A y = 1 := by
    unfold exists_bet_strategy_of_card_le_c
    rw [Finset.card_eq_one]
    refine ⟨y, ?_⟩
    ext z
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hp⟩
      exact (hp.eq_of_length ((hlen y hy).trans (hlen z hz).symm)).symm
    · rintro rfl
      exact ⟨hy, List.prefix_refl _⟩
  unfold exists_bet_strategy_of_card_le_I
  simp only [hc]
  have hl := hlen y hy
  simp [hl]

/-- **Lemma of SUV p. 294.**  If `A` is a set of `n`-bit strings with at most `2^s` elements,
`s < n`, there is a strategy with bets in `[-1, 1]` winning at least `n - s` on every element of
`A`. -/
theorem exists_bet_strategy_of_card_le {n : ℕ} {s : ℝ} (_hsn : s < n) {A : Finset BitString}
    (hlen : ∀ x ∈ A, x.length = n) (hcard : (A.card : ℝ) ≤ (2 : ℝ) ^ s) :
    ∃ S : BitString → ℝ, (∀ x, |S x| ≤ 1) ∧ ∀ x ∈ A, (n : ℝ) - s ≤ betGainOnOne S x := by
  use exists_bet_strategy_of_card_le_S A
  refine ⟨exists_bet_strategy_of_card_le_bound A, fun x hx => ?_⟩
  have hA : A.Nonempty := ⟨x, hx⟩
  have h1 := exists_bet_strategy_of_card_le_init n A hA hcard
  have h2 := exists_bet_strategy_of_card_le_telescope A n hlen x hx
  have h3 := exists_bet_strategy_of_card_le_end A n hlen x hx
  linarith

/-- The subsequence in residue class `r` modulo `2 ^ k`. -/
def not_isMisesKLRandom_of_plainK_lt_column
    (w : CantorSeq) (k r : ℕ) : CantorSeq := fun n => w (2 ^ k * n + r)

/-- The bits outside a dyadic column, with all positions in the column masked to zero. -/
def not_isMisesKLRandom_of_plainK_lt_background
    (w : CantorSeq) (k r : ℕ) : Set ℕ := {n | n % 2 ^ k ≠ r ∧ w n = true}

/-- Step 1 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
an oracle prefix description can encode an ordinary shortest plain program with a
self-delimiting description of its length. The overhead is logarithmic in that length. -/
private lemma not_isMisesKLRandom_of_plainK_lt_prefix_cost
    (A : Set ℕ) (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x : BitString,
      PointToSet.oracleComplexity A x ≤ (plainK V x).toNat +
        2 * (Nat.bits (plainK V x).toNat).length + c := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c₁, hc₁⟩ := (PointToSet.exists_optimalOraclePrefix_spec A).2.2 U
    ((PointToSet.isDecompressorIn_iff_partrecIn _ _).mpr hU.isDecompressor.partrecIn)
    hU.isPrefixMachine
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨c₃, hc₃⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c₁ + c₂ + c₃, fun x => ?_⟩
  have hfinite : plainK V x ≠ ⊤ := by
    obtain ⟨c, hc⟩ := plainK_le_length V hV
    exact ne_top_of_le_natCast_add (hc x)
  have hx : plainK V x = ((plainK V x).toNat : ℕ∞) :=
    (ENat.natCast_toNat hfinite).symm
  have h : KPPlain (PointToSet.optimalOraclePrefix A) x ≤
      (((plainK V x).toNat + 2 * (Nat.bits (plainK V x).toNat).length +
        (c₁ + c₂ + c₃) : ℕ) : ℕ∞) := by
    calc
      KPPlain (PointToSet.optimalOraclePrefix A) x ≤ KPPlain U x + c₁ := hc₁ x []
      _ ≤ ((plainK V x).toNat : ℕ∞) +
          KPPlain U (Nat.bits (plainK V x).toNat) + c₂ + c₁ := by
        gcongr
        exact hc₂ x _ hx
      _ ≤ ((plainK V x).toNat : ℕ∞) +
          (2 * ((Nat.bits (plainK V x).toNat).length : ℕ∞) + c₃) + c₂ + c₁ := by
        gcongr
        exact hc₃ _
      _ = _ := by push_cast; ring
  exact ENat.natCast_le_natCast.mp (by
    simpa only [PointToSet.oracleComplexity, PointToSet.oraclePrefixComplexity_coe,
      PointToSet.oraclePrefixComplexity, KPPlain] using h)

/-- Step 2 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
infinitely often plain compression bounds the lower prefix-complexity density, even
with an oracle; the logarithmic conversion cost in Step 1 vanishes after normalization. -/
lemma not_isMisesKLRandom_of_plainK_lt_low_dimension
    (A : Set ℕ) (V : Map) (hV : isOptimalConditional V) {α : ℝ} (hα : α < 1)
    {w : CantorSeq}
    (hC : ∃ᶠ n : ℕ in atTop, ((plainK V (cantorPrefix w n)).toNat : ℝ) < α * n) :
    Applications.oraclePrefixDim A w ≤ α := by
  obtain ⟨c, hc⟩ := not_isMisesKLRandom_of_plainK_lt_prefix_cost A V hV
  apply le_of_forall_gt_imp_ge_of_dense
  intro β hαβ
  have hs := PointToSet.normalized_additive_slack_logSlack (c + 2)
  have he : ∀ᶠ n : ℕ in atTop, (logSlack (c + 2) n : ℝ) / n < β - α :=
    hs.eventually (gt_mem_nhds (sub_pos.mpr hαβ))
  have hf : ∃ᶠ n : ℕ in atTop,
      (PointToSet.oracleComplexity A (cantorPrefix w n) : ℝ) / n ≤ β := by
    apply ((hC.and_eventually he).and_eventually (eventually_gt_atTop 0)).mono
    rintro n ⟨⟨hn, hslack⟩, hnpos⟩
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hk : (plainK V (cantorPrefix w n)).toNat ≤ n := by
      have hkn : ((plainK V (cantorPrefix w n)).toNat : ℝ) < n := by
        nlinarith
      exact_mod_cast hkn.le
    have hbits : (Nat.bits (plainK V (cantorPrefix w n)).toNat).length ≤
        (Nat.bits n).length := by
      simpa only [← Nat.size_eq_bits_len] using Nat.size_le_size hk
    have hover : 2 * (Nat.bits (plainK V (cantorPrefix w n)).toNat).length + c ≤
        logSlack (c + 2) n := by
      unfold logSlack
      nlinarith
    have hcost : (PointToSet.oracleComplexity A (cantorPrefix w n) : ℝ) ≤
        (plainK V (cantorPrefix w n)).toNat + (logSlack (c + 2) n : ℝ) := by
      have hcost := hc (cantorPrefix w n)
      have hcost' : PointToSet.oracleComplexity A (cantorPrefix w n) ≤
          (plainK V (cantorPrefix w n)).toNat + logSlack (c + 2) n := by omega
      exact_mod_cast hcost'
    apply (div_le_iff₀ hnR).mpr
    have hh := (div_lt_iff₀ hnR).mp hslack
    nlinarith
  exact liminf_le_of_frequently_le hf (isBoundedUnder_of ⟨0, fun n => by positivity⟩)

/-- Step 3 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
relative prefix-complexity densities are nonnegative. -/
lemma not_isMisesKLRandom_of_plainK_lt_nonneg
    (A : Set ℕ) (u : CantorSeq) : 0 ≤ Applications.oraclePrefixDim A u := by
  unfold Applications.oraclePrefixDim
  rw [Filter.liminf_eq]
  exact Real.sSup_nonneg' ⟨0, Filter.Eventually.of_forall (fun n => by positivity), le_rfl⟩

/-- Step 4 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
literal prefix descriptions bound the relative prefix complexity by twice the
length plus a constant, ensuring bounded normalized complexities. -/
private lemma not_isMisesKLRandom_of_plainK_lt_length_bound
    (A : Set ℕ) :
    ∃ c : ℕ, ∀ x : BitString, PointToSet.oracleComplexity A x ≤ 2 * x.length + c := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c₁, hc₁⟩ := (PointToSet.exists_optimalOraclePrefix_spec A).2.2 U
    ((PointToSet.isDecompressorIn_iff_partrecIn _ _).mpr hU.isDecompressor.partrecIn)
    hU.isPrefixMachine
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c₂ + c₁, fun x => ?_⟩
  have hb : KPPlain (PointToSet.optimalOraclePrefix A) x ≤
      ((2 * x.length + (c₂ + c₁) : ℕ) : ℕ∞) := by
    calc
      KPPlain (PointToSet.optimalOraclePrefix A) x ≤ KPPlain U x + c₁ := hc₁ x []
      _ ≤ (2 * (x.length : ℕ∞) + c₂) + c₁ := by gcongr; exact hc₂ x
      _ = _ := by push_cast; ring
  exact ENat.natCast_le_natCast.mp (by
    simpa only [PointToSet.oracleComplexity, PointToSet.oraclePrefixComplexity_coe,
      PointToSet.oraclePrefixComplexity, KPPlain] using hb)

/-- Step 4 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
normalized relative prefix complexities are bounded above, as needed for real
liminf arguments. -/
lemma not_isMisesKLRandom_of_plainK_lt_bounded
    (A : Set ℕ) (u : CantorSeq) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (PointToSet.oracleComplexity A (cantorPrefix u n) : ℝ) / n) := by
  obtain ⟨c, hc⟩ := not_isMisesKLRandom_of_plainK_lt_length_bound A
  refine ⟨2 + (c : ℝ), ?_⟩
  change ∀ᶠ n : ℕ in atTop,
    (PointToSet.oracleComplexity A (cantorPrefix u n) : ℝ) / n ≤ 2 + (c : ℝ)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcost : (PointToSet.oracleComplexity A (cantorPrefix u n) : ℝ) ≤ 2 * n + c := by
    have h := hc (cantorPrefix u n)
    rw [cantorPrefix_length] at h
    exact_mod_cast h
  apply (div_le_iff₀ hnR).mpr
  nlinarith [show (0 : ℝ) ≤ c by positivity]

/-- Step 4 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
normalizing a finite chain inequality and letting its logarithmic slack vanish
gives the corresponding lower-density inequality. -/
lemma not_isMisesKLRandom_of_plainK_lt_normalize
    (a b p : ℕ → ℕ) (c : ℕ)
    (hp : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (p n : ℝ) / n))
    (hfinite : ∀ n, a (n / 2) + b (n / 2) ≤ p n + logSlack c n) :
    ((liminf (fun n : ℕ => (a n : ℝ) / n) atTop) +
      liminf (fun n : ℕ => (b n : ℝ) / n) atTop) / 2 ≤
      liminf (fun n : ℕ => (p n : ℝ) / n) atTop := by
  have hhalf : Tendsto (fun n : ℕ => ((n / 2 : ℕ) : ℝ) / n) atTop (𝓝 (1 / 2)) := by
    have hmod := tendsto_mod_div_atTop_nhds_zero_nat (show 0 < (2 : ℕ) by omega)
    have heq : (fun n : ℕ => ((n / 2 : ℕ) : ℝ) / n) =ᶠ[atTop]
        (fun n : ℕ => (1 - ((n % 2 : ℕ) : ℝ) / n) / 2) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have h : ((n % 2 : ℕ) : ℝ) + 2 * ((n / 2 : ℕ) : ℝ) = n := by
        exact_mod_cast (Nat.mod_add_div n 2)
      field_simp
      nlinarith
    exact Tendsto.congr' heq.symm (by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hmod).div_const 2)
  let da := liminf (fun n : ℕ => (a n : ℝ) / n) atTop
  let db := liminf (fun n : ℕ => (b n : ℝ) / n) atTop
  let dp := liminf (fun n : ℕ => (p n : ℝ) / n) atTop
  have hbnd (v : ℕ → ℕ) : IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => (v n : ℝ) / n) := isBoundedUnder_of ⟨0, fun n => by positivity⟩
  have hlow (x y : ℝ) (hx : x < da) (hy : y < db) : (x + y) / 2 ≤ dp := by
    have ha := (Nat.tendsto_div_const_atTop (show 2 ≠ 0 by omega)).eventually
      (eventually_lt_of_lt_liminf hx (hbnd a))
    have hb := (Nat.tendsto_div_const_atTop (show 2 ≠ 0 by omega)).eventually
      (eventually_lt_of_lt_liminf hy (hbnd b))
    have ht : Tendsto (fun n : ℕ =>
        (x + y) * (((n / 2 : ℕ) : ℝ) / n) - (logSlack c n : ℝ) / n)
        atTop (𝓝 ((x + y) / 2)) := by
      simpa [div_eq_mul_inv] using (hhalf.const_mul (x + y)).sub
        (PointToSet.normalized_additive_slack_logSlack c)
    have he : ∀ᶠ n : ℕ in atTop,
        (x + y) * (((n / 2 : ℕ) : ℝ) / n) - (logSlack c n : ℝ) / n ≤ (p n : ℝ) / n := by
      filter_upwards [ha, hb, eventually_ge_atTop 2] with n han hbn hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hdivR : (0 : ℝ) < (n / 2 : ℕ) := by exact_mod_cast (show 0 < n / 2 by omega)
      have han' := (lt_div_iff₀ hdivR).mp han
      have hbn' := (lt_div_iff₀ hdivR).mp hbn
      have hfn : (a (n / 2) : ℝ) + (b (n / 2) : ℝ) ≤ p n + (logSlack c n : ℝ) := by
        exact_mod_cast hfinite n
      rw [← mul_div_assoc, ← sub_div, div_le_div_iff_of_pos_right hnR]
      nlinarith
    by_contra! hlt
    obtain ⟨z, hz₀, hz₁⟩ := exists_between hlt
    have hf := frequently_lt_of_liminf_lt hp.isCoboundedUnder_ge hz₀
    obtain ⟨n, ⟨hn, hne⟩, hnt⟩ :=
      ((hf.and_eventually he).and_eventually (ht.eventually (lt_mem_nhds hz₁))).exists
    linarith
  by_contra! hlt
  have hx : da - ((da + db) / 2 - dp) / 2 < da := by linarith
  have hy : db - ((da + db) / 2 - dp) / 2 < db := by linarith
  have h := hlow _ _ hx hy
  linarith

/-- Kraft's inequality for the relative prefix complexity on every finite set of strings. -/
private lemma not_isMisesKLRandom_of_plainK_lt_xside_kraft (A : Set ℕ)
    (Z : Finset BitString) :
    ∑ z ∈ Z, (2 : ℝ)⁻¹ ^ PointToSet.oracleComplexity A z ≤ 1 := by
  let U := PointToSet.optimalOraclePrefix A
  have hterm (x : BitString) : complexityWeight (KP U x []) =
      (2 : ENNReal)⁻¹ ^ PointToSet.oracleComplexity A x := by
    rw [← complexityWeight_coe, PointToSet.oracleComplexity,
      PointToSet.oraclePrefixComplexity_coe]
    rfl
  have hsum : (∑' x : BitString, complexityWeight (KP U x [])) ≤ 1 :=
    (ENNReal.tsum_le_tsum (fun x => complexityWeight_KP_le_aprioriMeasure U x [])).trans
      (tsum_aprioriMeasure_le_one U [] (PointToSet.exists_optimalOraclePrefix_spec A).2.1)
  have hfinite : ∀ x ∈ Z, complexityWeight (KP U x []) ≠ ⊤ := by
    intro x hx
    rw [hterm]
    exact ENNReal.pow_ne_top (by norm_num)
  have hreal := ENNReal.toReal_mono ENNReal.one_ne_top ((ENNReal.sum_le_tsum Z).trans hsum)
  rw [ENNReal.toReal_sum hfinite, ENNReal.toReal_one] at hreal
  simpa only [hterm, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat] using hreal

/-- At most `2 ^ m` strings have relative prefix complexity at most `m`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_xside_card_le (A : Set ℕ) (m : ℕ)
    (Z : Finset BitString) (hZ : ∀ z ∈ Z, PointToSet.oracleComplexity A z ≤ m) :
    Z.card ≤ 2 ^ m := by
  have hk := not_isMisesKLRandom_of_plainK_lt_xside_kraft A Z
  have h1 : ∑ z ∈ Z, ((2 : ℝ)⁻¹) ^ m ≤ ∑ z ∈ Z, (2 : ℝ)⁻¹ ^ PointToSet.oracleComplexity A z := by
    apply Finset.sum_le_sum
    intro z hz
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hZ z hz)
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : (Z.card : ℝ) * ((2 : ℝ)⁻¹) ^ m ≤ 1 := h1.trans hk
  have h3 : (Z.card : ℝ) ≤ 2 ^ m := by
    have hpos : (0 : ℝ) < 2 ^ m := by positivity
    have := mul_le_mul_of_nonneg_right h2 hpos.le
    rw [one_mul, mul_assoc, ← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow, mul_one] at this
    exact this
  exact_mod_cast h3

/-- If each of the strings `x` of a finite set has `2 ^ d` partners `y` with
`K^A(⟨x, y⟩) ≤ m`, then the finite set has at most `2 ^ (m - d)` elements. -/
private lemma not_isMisesKLRandom_of_plainK_lt_xside_fiber_card (A : Set ℕ) (m d : ℕ)
    (X : Finset BitString)
    (hX : ∀ x ∈ X, ∃ T : Finset BitString, T.card = 2 ^ d ∧
      ∀ y ∈ T, PointToSet.oracleComplexity A (pairCode x y) ≤ m) :
    X.card * 2 ^ d ≤ 2 ^ m := by
  classical
  choose! T hTcard hTK using hX
  let Z : Finset BitString := X.biUnion (fun x => (T x).image (fun y => pairCode x y))
  have hinj (x : BitString) : Function.Injective (fun y : BitString => pairCode x y) := by
    intro y y' h
    exact (Prod.mk.inj (pairCode_injective (a₁ := (x, y)) (a₂ := (x, y')) h)).2
  have hZcard : Z.card = X.card * 2 ^ d := by
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun x hx => by
        rw [Finset.card_image_of_injective _ (hinj x), hTcard x hx])]
      simp
    · intro x hx x' hx' hne
      rw [Function.onFun, Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y', hy', hyy⟩ := Finset.mem_image.mp hz'
      exact hne (Prod.mk.inj (pairCode_injective (a₁ := (x, y)) (a₂ := (x', y')) hyy.symm)).1
  have hZK : ∀ z ∈ Z, PointToSet.oracleComplexity A z ≤ m := by
    intro z hz
    obtain ⟨x, hx, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact hTK x hx y hy
  rw [← hZcard]
  exact not_isMisesKLRandom_of_plainK_lt_xside_card_le A m Z hZK

/-- The weights `4 ^ (-|bin m|)` have a finite sum. -/
private lemma not_isMisesKLRandom_of_plainK_lt_xside_tsum_weight_lt_top :
    (∑' m : ℕ, ((2 : ENNReal)⁻¹) ^ (2 * (natBits m).length)) < ⊤ := by
  have hsum : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h' := (summable_nat_add_iff 1).mpr h
    simpa [Nat.cast_add, Nat.cast_one] using h'
  have hle : ∀ m : ℕ, ((2 : ENNReal)⁻¹) ^ (2 * (natBits m).length) ≤
      ENNReal.ofReal (1 / ((m : ℝ) + 1) ^ 2) := by
    intro m
    have hlen : (natBits m).length = m.size := Nat.size_eq_bits_len m
    have hs : ((m : ℝ) + 1) ≤ 2 ^ (natBits m).length := by
      rw [hlen]
      have := Nat.lt_size_self m
      exact_mod_cast this
    have h2 : (1 : ℝ) / 2 ^ (2 * (natBits m).length) ≤ 1 / ((m : ℝ) + 1) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      calc ((m : ℝ) + 1) ^ 2 ≤ (2 ^ (natBits m).length) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hs 2
        _ = 2 ^ (2 * (natBits m).length) := by rw [← pow_mul, mul_comm]
    calc ((2 : ENNReal)⁻¹) ^ (2 * (natBits m).length)
        = ENNReal.ofReal (1 / 2 ^ (2 * (natBits m).length)) := by
          rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
            ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, one_div,
            ENNReal.inv_pow]
      _ ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1) ^ 2) := ENNReal.ofReal_le_ofReal h2
  calc (∑' m : ℕ, ((2 : ENNReal)⁻¹) ^ (2 * (natBits m).length))
      ≤ ∑' m : ℕ, ENNReal.ofReal (1 / ((m : ℝ) + 1) ^ 2) := ENNReal.tsum_le_tsum hle
    _ = ENNReal.ofReal (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The coding domain: `(m, d)` together with a string `x` having `2 ^ d` distinct partners `y`
with `K^A(⟨x, y⟩) ≤ m`. -/
private def not_isMisesKLRandom_of_plainK_lt_xside_dom (A : Set ℕ) (md : ℕ × ℕ)
    (x : BitString) : Prop :=
  ∃ T : Finset BitString, T.card = 2 ^ md.2 ∧
    ∀ y ∈ T, PointToSet.oracleComplexity A (pairCode x y) ≤ md.1

/-- The cost `m - d + 2 |bin m| + 2 |bin d| + 2`. -/
private noncomputable def not_isMisesKLRandom_of_plainK_lt_xside_cost (md : ℕ × ℕ) : ℝ :=
  ((md.1 + 2 * (natBits md.1).length + 2 * (natBits md.2).length + 2 : ℕ) : ℝ) - md.2

/-- The exponential mass of the cost over the coding domain is finite. -/
private lemma not_isMisesKLRandom_of_plainK_lt_xside_mass (A : Set ℕ) :
    (∑' z : {a : (ℕ × ℕ) × BitString //
        not_isMisesKLRandom_of_plainK_lt_xside_dom A a.1 a.2},
      (2 : ENNReal) ^ (-(not_isMisesKLRandom_of_plainK_lt_xside_cost z.val.1))) < ⊤ := by
  let u : ℕ → ENNReal := fun m => ((2 : ENNReal)⁻¹) ^ (2 * (natBits m).length)
  let c : ENNReal := ((2 : ENNReal)⁻¹) ^ 2
  let W : ℕ × ℕ → ENNReal := fun md => u md.1 * (u md.2 * c)
  have hpt : ∀ md : ℕ × ℕ,
      (2 : ENNReal) ^ (-(not_isMisesKLRandom_of_plainK_lt_xside_cost md)) =
        ((2 : ENNReal) ^ md.2 * ((2 : ENNReal)⁻¹) ^ md.1) * W md := by
    intro md
    have hexp : -(not_isMisesKLRandom_of_plainK_lt_xside_cost md) =
        (md.2 : ℝ) + (-((md.1 + 2 * (natBits md.1).length + 2 * (natBits md.2).length + 2 : ℕ) : ℝ))
            := by
      unfold not_isMisesKLRandom_of_plainK_lt_xside_cost
      ring
    have h1 : ∀ N : ℕ, (2 : ENNReal) ^ (-(N : ℝ)) = ((2 : ENNReal)⁻¹) ^ N := by
      intro N
      rw [ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.inv_pow]
    rw [hexp, ENNReal.rpow_add _ _ (by norm_num) (by norm_num), ENNReal.rpow_natCast, h1]
    simp only [W, u, c, pow_add]
    ring
  have hfiber : ∀ md : ℕ × ℕ,
      (∑' x : {x : BitString // not_isMisesKLRandom_of_plainK_lt_xside_dom A md x},
        (2 : ENNReal) ^ md.2 * ((2 : ENNReal)⁻¹) ^ md.1) ≤ 1 := by
    intro md
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le (fun s => ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    classical
    have hcard : s.card * 2 ^ md.2 ≤ 2 ^ md.1 := by
      have h := not_isMisesKLRandom_of_plainK_lt_xside_fiber_card A md.1 md.2
        (s.image Subtype.val) (fun x hx => by
          obtain ⟨⟨x', hx'⟩, _, rfl⟩ := Finset.mem_image.mp hx
          exact hx')
      rwa [Finset.card_image_of_injective _ Subtype.val_injective] at h
    calc (s.card : ENNReal) * ((2 : ENNReal) ^ md.2 * ((2 : ENNReal)⁻¹) ^ md.1)
        = ((s.card * 2 ^ md.2 : ℕ) : ENNReal) * ((2 : ENNReal)⁻¹) ^ md.1 := by
          push_cast; ring
      _ ≤ ((2 ^ md.1 : ℕ) : ENNReal) * ((2 : ENNReal)⁻¹) ^ md.1 := by
          gcongr
      _ = 1 := by
          push_cast
          rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  have heq : (∑' z : {a : (ℕ × ℕ) × BitString //
        not_isMisesKLRandom_of_plainK_lt_xside_dom A a.1 a.2},
      (2 : ENNReal) ^ (-(not_isMisesKLRandom_of_plainK_lt_xside_cost z.val.1))) =
      ∑' md : ℕ × ℕ, ∑' x : {x : BitString //
          not_isMisesKLRandom_of_plainK_lt_xside_dom A md x},
        (2 : ENNReal) ^ (-(not_isMisesKLRandom_of_plainK_lt_xside_cost md)) := by
    rw [← ENNReal.tsum_sigma]
    exact (Equiv.subtypeProdEquivSigmaSubtype
      (fun (md : ℕ × ℕ) (x : BitString) =>
        not_isMisesKLRandom_of_plainK_lt_xside_dom A md x)).tsum_eq
      (fun z => (2 : ENNReal) ^ (-(not_isMisesKLRandom_of_plainK_lt_xside_cost z.1)))
  rw [heq]
  calc (∑' md : ℕ × ℕ, ∑' x : {x : BitString //
          not_isMisesKLRandom_of_plainK_lt_xside_dom A md x},
        (2 : ENNReal) ^ (-(not_isMisesKLRandom_of_plainK_lt_xside_cost md)))
      = ∑' md : ℕ × ℕ, (∑' x : {x : BitString //
          not_isMisesKLRandom_of_plainK_lt_xside_dom A md x},
            (2 : ENNReal) ^ md.2 * ((2 : ENNReal)⁻¹) ^ md.1) * W md := by
        refine tsum_congr (fun md => ?_)
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr (fun x => hpt md)
    _ ≤ ∑' md : ℕ × ℕ, 1 * W md := ENNReal.tsum_le_tsum (fun md => by
        gcongr
        exact hfiber md)
    _ = (∑' m, u m) * ((∑' d, u d) * c) := by
        simp only [one_mul, W]
        refine (ENNReal.tsum_prod (f := fun m d => u m * (u d * c))).trans ?_
        simp only [ENNReal.tsum_mul_left]
        simp only [ENNReal.tsum_mul_right]
    _ < ⊤ := by
        have hu : (∑' m, u m) < ⊤ :=
          not_isMisesKLRandom_of_plainK_lt_xside_tsum_weight_lt_top
        have hc : c < ⊤ := ENNReal.pow_lt_top (by norm_num)
        exact ENNReal.mul_lt_top hu (ENNReal.mul_lt_top hu hc)

/-- The coding domain is relatively enumerable: by an injective enumeration of the relation
`K^A(⟨x, y⟩) ≤ m`, the domain is the set of `((m, d), x)` for which at some stage at least `2 ^ d`
triples `(m, x, y)` have been enumerated. -/
private lemma not_isMisesKLRandom_of_plainK_lt_xside_dom_isREIn (A : Set ℕ) :
    PointToSet.IsREIn A (fun a : (ℕ × ℕ) × BitString =>
      not_isMisesKLRandom_of_plainK_lt_xside_dom A a.1 a.2) := by
  classical
  let Q : ℕ × BitString × BitString → Prop := fun p =>
    PointToSet.oracleComplexity A (pairCode p.2.1 p.2.2) ≤ p.1
  have hf : ComputableIn {charOracle A} (fun p : ℕ × BitString × BitString =>
      (pairCode p.2.1 p.2.2, (((p.1 + 1 : ℕ) : ℚ)))) := by
    have h1 : Computable (fun p : ℕ × BitString × BitString => pairCode p.2.1 p.2.2) :=
      pairCode_computable.comp
        ((Computable.fst.comp Computable.snd).pair (Computable.snd.comp Computable.snd))
    have h2 : Computable (fun p : ℕ × BitString × BitString => (((p.1 + 1 : ℕ) : ℚ))) :=
      computable_nat_to_rat.comp (Computable.succ.comp Computable.fst)
    exact (h1.pair h2).computableIn
  have hQ : PointToSet.IsREIn A Q := by
    have h := (PointToSet.isREIn_oracleComplexity_lt A).comp hf
    have hQeq : Q = fun p : ℕ × BitString × BitString =>
        (PointToSet.oracleComplexity A (pairCode p.2.1 p.2.2) : ℝ) <
          ((((p.1 + 1 : ℕ) : ℚ) : ℝ)) := by
      funext p
      apply propext
      simp only [Q, Rat.cast_natCast]
      constructor
      · intro h
        exact_mod_cast Nat.lt_succ_of_le h
      · intro h
        exact Nat.le_of_lt_succ (by exact_mod_cast h)
    rw [hQeq]
    exact h
  obtain ⟨e, ⟨he, hrange⟩, hinj⟩ := PointToSet.relative_enumeration_injective A Q hQ
  let key : ℕ × BitString × BitString → ℕ × BitString := fun p => (p.1, p.2.1)
  let step : (ℕ × BitString) → ℕ × ℕ → ℕ := fun q p =>
    p.2 + (if (e p.1).map key = some q then 1 else 0)
  let cnt : (ℕ × BitString) × ℕ → ℕ := fun q =>
    Nat.rec 0 (fun s c => step q.1 (s, c)) q.2
  have hkey : Computable key :=
    Computable.fst.pair (Computable.fst.comp Computable.snd)
  have hstep : ComputableIn₂ {charOracle A}
      (fun (q : (ℕ × BitString) × ℕ) (p : ℕ × ℕ) => step q.1 p) := by
    have hmap : Computable (fun o : Option (ℕ × BitString × BitString) => o.map key) :=
      Computable.option_map Computable.id (hkey.comp Computable.snd).to₂
    have heqd : Computable
        (fun p : Option (ℕ × BitString) × Option (ℕ × BitString) => decide (p.1 = p.2)) :=
      (PrimrecRel.decide Primrec.eq).to_comp
    have hcond : Computable (fun b : Bool => cond b 1 0) :=
      Computable.cond Computable.id (Computable.const 1) (Computable.const 0)
    have hs : ComputableIn {charOracle A}
        (fun z : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) => z.2.1) :=
      ComputableIn.fst.comp ComputableIn.snd
    have he' : ComputableIn {charOracle A}
        (fun z : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) => e z.2.1) := he.comp hs
    have hmapped : ComputableIn {charOracle A}
        (fun z : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) => (e z.2.1).map key) :=
      hmap.computableIn.comp he'
    have hq : ComputableIn {charOracle A}
        (fun z : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) => some z.1.1) :=
      (Computable.option_some.comp (Computable.fst.comp Computable.fst)).computableIn
    have hdec : ComputableIn {charOracle A}
        (fun z : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) =>
          decide ((e z.2.1).map key = some z.1.1)) :=
      heqd.computableIn.comp (hmapped.pair hq)
    have hind : ComputableIn {charOracle A}
        (fun z : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) =>
          cond (decide ((e z.2.1).map key = some z.1.1)) 1 0) :=
      hcond.computableIn.comp hdec
    have h22 : ComputableIn {charOracle A}
        (fun z : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) => z.2.2) :=
      ComputableIn.snd.comp ComputableIn.snd
    have hplus : ComputableIn {charOracle A} (fun p : ℕ × ℕ => p.1 + p.2) :=
      Primrec.nat_add.computableIn
    have hadd0 := hplus.comp (h22.pair hind)
    have hadd : ComputableIn {charOracle A}
        (fun z : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) =>
          z.2.2 + cond (decide ((e z.2.1).map key = some z.1.1)) 1 0) := hadd0
    refine hadd.of_eq (fun z => ?_)
    simp only [step]
    split_ifs <;> simp_all
  have hcnt : ComputableIn {charOracle A} cnt :=
    ComputableIn.nat_rec (f := fun q : (ℕ × BitString) × ℕ => q.2) (g := fun _ => 0)
      (h := fun q p => step q.1 p) ComputableIn.snd (ComputableIn.const 0) hstep
  have hcnt_eq : ∀ (q : ℕ × BitString) (t : ℕ),
      cnt (q, t) = ((Finset.range t).filter (fun s => (e s).map key = some q)).card := by
    intro q t
    rw [Finset.card_filter]
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Finset.sum_range_succ, ← ih]
  have hDeq : ∀ a : (ℕ × ℕ) × BitString,
      not_isMisesKLRandom_of_plainK_lt_xside_dom A a.1 a.2 ↔
        ∃ t, 2 ^ a.1.2 ≤ cnt ((a.1.1, a.2), t) := by
    intro a
    constructor
    · rintro ⟨T, hTcard, hTK⟩
      have hs : ∀ y ∈ T, ∃ s, e s = some (a.1.1, a.2, y) :=
        fun y hy => (hrange _).mp (hTK y hy)
      choose! s hs using hs
      refine ⟨T.sup s + 1, ?_⟩
      have hle : T.card ≤ ((Finset.range (T.sup s + 1)).filter
          (fun s' => (e s').map key = some (a.1.1, a.2))).card := by
        refine Finset.card_le_card_of_injOn s ?_ ?_
        · intro y hy
          simp only [Finset.mem_coe, Finset.coe_filter, Finset.mem_range,
            Set.mem_ofPred_eq] at hy ⊢
          refine ⟨Nat.lt_succ_of_le (Finset.le_sup hy), ?_⟩
          rw [hs y hy]
          rfl
        · intro y hy y' hy' h
          have h1 := hs y hy
          have h2 := hs y' hy'
          rw [h, h2] at h1
          exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj h1)).2).2.symm
      calc 2 ^ a.1.2 = T.card := hTcard.symm
        _ ≤ _ := hle
        _ = cnt ((a.1.1, a.2), T.sup s + 1) := (hcnt_eq _ _).symm
    · rintro ⟨t, ht⟩
      rw [hcnt_eq (a.1.1, a.2) t] at ht
      set S := (Finset.range t).filter (fun s => (e s).map key = some (a.1.1, a.2)) with hS
      have hy : ∀ s ∈ S, ∃ y, e s = some (a.1.1, a.2, y) := by
        intro s hsS
        have h := (Finset.mem_filter.mp hsS).2
        cases hes : e s with
        | none => simp [hes] at h
        | some p =>
          rw [hes] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, key] at h
          refine ⟨p.2.2, ?_⟩
          rw [← h.1, ← h.2]
      choose! y hy using hy
      have hyinj : Set.InjOn y S := by
        intro s hs s' hs' h
        have h1 := hy s hs
        have h2 := hy s' hs'
        rw [h] at h1
        exact hinj s s' _ h1 h2
      have hQy : ∀ s ∈ S, Q (a.1.1, a.2, y s) := fun s hs => (hrange _).mpr ⟨s, hy s hs⟩
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
        (s := S.image y) (n := 2 ^ a.1.2) (by rw [Finset.card_image_of_injOn hyinj]; exact ht)
      refine ⟨T, hTcard, fun y' hy' => ?_⟩
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (hTsub hy')
      exact hQy s hs
  have hmat : PointToSet.IsREIn A
      (fun p : ((ℕ × ℕ) × BitString) × ℕ => 2 ^ p.1.1.2 ≤ cnt ((p.1.1.1, p.1.2), p.2)) := by
    let P : ((ℕ × ℕ) × BitString) × ℕ → Prop :=
      fun p => (2 : ℕ) ^ p.1.1.2 ≤ cnt ((p.1.1.1, p.1.2), p.2)
    refine @PointToSet.isREIn_of_computableIn_decide _ _ A P (fun p => Nat.decLe _ _) ?_
    have hpow2 : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec.nat_iff.mpr Nat.Primrec.pow
    have hpow2' : ComputableIn {charOracle A} (fun p : ℕ × ℕ => p.1 ^ p.2) :=
      hpow2.computableIn
    have hexp : ComputableIn {charOracle A}
        (fun p : ((ℕ × ℕ) × BitString) × ℕ => p.1.1.2) :=
      ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)
    have hpow0 := hpow2'.comp ((ComputableIn.const 2).pair hexp)
    have hpow : ComputableIn {charOracle A}
        (fun p : ((ℕ × ℕ) × BitString) × ℕ => 2 ^ p.1.1.2) := hpow0
    have hc : ComputableIn {charOracle A}
        (fun p : ((ℕ × ℕ) × BitString) × ℕ => cnt ((p.1.1.1, p.1.2), p.2)) :=
      hcnt.comp (((ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
        (ComputableIn.snd.comp ComputableIn.fst)).pair ComputableIn.snd)
    have hd := (PrimrecRel.decide Primrec.nat_le).to_comp.computableIn.comp (hpow.pair hc)
    exact hd
  have hex := PointToSet.IsREIn.exists hmat
  have hfun : (fun a : (ℕ × ℕ) × BitString =>
      not_isMisesKLRandom_of_plainK_lt_xside_dom A a.1 a.2) =
      fun a => ∃ t, 2 ^ a.1.2 ≤ cnt ((a.1.1, a.2), t) :=
    funext fun a => propext (hDeq a)
  rw [hfun]
  exact hex

/-- The cost is upper semicomputable on the coding domain. -/
private lemma not_isMisesKLRandom_of_plainK_lt_xside_upper (A : Set ℕ) :
    PointToSet.IsUpperSemicomputableOnIn A
      (fun a : (ℕ × ℕ) × BitString => not_isMisesKLRandom_of_plainK_lt_xside_dom A a.1 a.2)
      (fun a => not_isMisesKLRandom_of_plainK_lt_xside_cost a.val.1) := by
  have hdom := not_isMisesKLRandom_of_plainK_lt_xside_dom_isREIn A
  let N : ℕ × ℕ → ℕ := fun md =>
    md.1 + 2 * (natBits md.1).length + 2 * (natBits md.2).length + 2
  let costQ : ℕ × ℕ → ℚ := fun md => (N md : ℚ) - (md.2 : ℚ)
  have hcost : ∀ md : ℕ × ℕ,
      not_isMisesKLRandom_of_plainK_lt_xside_cost md = ((costQ md : ℚ) : ℝ) := by
    intro md
    simp only [not_isMisesKLRandom_of_plainK_lt_xside_cost, costQ, N]
    push_cast
    ring
  have hN : Computable N := by
    have hadd : Computable₂ (fun a b : ℕ => a + b) := Primrec.nat_add.to_comp
    have hmul : Computable₂ (fun a b : ℕ => a * b) := Primrec.nat_mul.to_comp
    have hl1 : Computable (fun md : ℕ × ℕ => (natBits md.1).length) :=
      Computable.list_length.comp (natBits_computable.comp Computable.fst)
    have hl2 : Computable (fun md : ℕ × ℕ => (natBits md.2).length) :=
      Computable.list_length.comp (natBits_computable.comp Computable.snd)
    have h2l1 : Computable (fun md : ℕ × ℕ => 2 * (natBits md.1).length) :=
      hmul.comp (Computable.const 2) hl1
    have h2l2 : Computable (fun md : ℕ × ℕ => 2 * (natBits md.2).length) :=
      hmul.comp (Computable.const 2) hl2
    exact hadd.comp (hadd.comp (hadd.comp Computable.fst h2l1) h2l2) (Computable.const 2)
  have hcostQ : Computable costQ :=
    ComputableReals.computable_ratSub.comp (computable_nat_to_rat.comp hN)
      (computable_nat_to_rat.comp Computable.snd)
  let U : ((ℕ × ℕ) × BitString) × ℚ → Prop := fun aq =>
    not_isMisesKLRandom_of_plainK_lt_xside_dom A aq.1.1 aq.1.2 ∧ costQ aq.1.1 < aq.2
  have hU : PointToSet.IsREIn A U := by
    apply PointToSet.IsREIn.and
    · exact hdom.comp (f := fun aq : ((ℕ × ℕ) × BitString) × ℚ => aq.1)
        Computable.fst.computableIn
    · apply PointToSet.isREIn_of_computable_decide
      exact (PrimrecRel.decide ComputableReals.primrec_ratLt).to_comp.comp
        (hcostQ.comp (Computable.fst.comp Computable.fst)) Computable.snd
  refine ⟨U, hU, ?_, ?_⟩
  · rintro a q ⟨hD, hlt⟩
    refine ⟨hD, ?_⟩
    have hlt' : costQ a.1 < q := hlt
    change not_isMisesKLRandom_of_plainK_lt_xside_cost a.1 < (q : ℝ)
    rw [hcost]
    exact_mod_cast hlt'
  · intro a ε hε
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn
      (lt_add_of_pos_right (not_isMisesKLRandom_of_plainK_lt_xside_cost a.val.1) hε)
    refine ⟨q, ⟨a.property, ?_⟩, hq₂⟩
    rw [hcost] at hq₁
    exact_mod_cast hq₁

/-- An effective encoding with a left inverse transports an upper semicomputable cost with
finite total mass to bit strings, where the relative coding theorem bounds the oracle complexity
of the code by the cost plus a constant. -/
private lemma not_isMisesKLRandom_of_plainK_lt_xside_coding
    {α : Type*} [Primcodable α] (A : Set ℕ) (D : α → Prop)
    (v : α → ℝ) (hv : PointToSet.IsUpperSemicomputableOnIn A D (fun a ↦ v a.val))
    (hmass : (∑' a : Subtype D, (2 : ENNReal) ^ (-v a.val)) < ⊤)
    (code : α → BitString) (decode : BitString → α)
    (hcode : Computable code) (hleft : Function.LeftInverse decode code) :
    ∃ c : ℕ, ∀ a, D a → (PointToSet.oracleComplexity A (code a) : ℝ) ≤ v a + c := by
  let F : BitString → Prop := fun w ↦ ∃ a, D a ∧ code a = w
  let g : Subtype F → ℝ := fun w ↦ v (decode w.val)
  obtain ⟨U, hU, hUsound, hUclose⟩ := hv
  let V : BitString × ℚ → Prop := fun wq ↦
    ∃ aq : α × ℚ, U aq ∧ (code aq.1, aq.2) = wq
  have hV : PointToSet.IsREIn A V := hU.image (g := fun aq : α × ℚ ↦ (code aq.1, aq.2))
    ((hcode.comp Computable.fst).pair Computable.snd)
  have hg : PointToSet.IsUpperSemicomputableOnIn A F g := by
    refine ⟨V, hV, ?_, ?_⟩
    · intro w q hw
      obtain ⟨⟨a, r⟩, ha, he⟩ := hw
      obtain ⟨haD, hav⟩ := hUsound a r ha
      have hwcode : code a = w := congrArg Prod.fst he
      have hrq : r = q := congrArg Prod.snd he
      refine ⟨⟨a, haD, hwcode⟩, ?_⟩
      simpa [g, ← hwcode, hleft a, hrq] using hav
    · intro w ε hε
      obtain ⟨a, haD, haw⟩ := w.property
      obtain ⟨q, hqU, hq⟩ := hUclose ⟨a, haD⟩ ε hε
      refine ⟨q, ⟨(a, q), hqU, ?_⟩, ?_⟩
      · exact Prod.ext haw rfl
      · simpa [g, ← haw, hleft a] using hq
  have hdecode (w : Subtype F) : D (decode w.val) := by
    obtain ⟨a, ha, haw⟩ := w.property
    simpa [← haw, hleft a] using ha
  let dec : Subtype F → Subtype D := fun w ↦ ⟨decode w.val, hdecode w⟩
  have hdecinj : Function.Injective dec := by
    intro w z he
    obtain ⟨a, haD, haw⟩ := w.property
    obtain ⟨b, hbD, hbz⟩ := z.property
    have hab : a = b := by
      have hd := congrArg (fun a : Subtype D ↦ a.val) he
      simpa [dec, ← haw, ← hbz, hleft a, hleft b] using hd
    exact Subtype.ext (haw.symm.trans ((congrArg code hab).trans hbz))
  have hgmass : (∑' w : Subtype F, (2 : ENNReal) ^ (-g w)) < ⊤ :=
    lt_of_le_of_lt (ENNReal.tsum_comp_le_tsum_of_injective hdecinj
      (fun a : Subtype D ↦ (2 : ENNReal) ^ (-v a.val))) hmass
  obtain ⟨c, hc⟩ := PointToSet.oracle_coding_finite_mass A F g hg _ le_rfl hgmass
  refine ⟨c, fun a ha ↦ ?_⟩
  have h := hc ⟨code a, ⟨a, ha, rfl⟩⟩
  simpa [g, hleft a] using h

/-- **X-side of the counting proof of relativized symmetry of information.** If a string `x` has
`2 ^ d` partners `y` with `K^A(⟨x, y⟩) ≤ m`, then `K^A(x) ≤ m - d + O(log m + log d)`. -/
lemma not_isMisesKLRandom_of_plainK_lt_xside (A : Set ℕ) :
    ∃ c : ℕ, ∀ (x : BitString) (m d : ℕ) (T : Finset BitString), T.card = 2 ^ d →
      (∀ y ∈ T, PointToSet.oracleComplexity A (pairCode x y) ≤ m) →
      PointToSet.oracleComplexity A x + d ≤ m + 2 * Nat.size m + 2 * Nat.size d + c := by
  let code : (ℕ × ℕ) × BitString → BitString := fun a =>
    pairCode (natBits a.1.1) (pairCode (natBits a.1.2) a.2)
  let decode : BitString → (ℕ × ℕ) × BitString := fun w =>
    ((decodeBits (decodeFirst w), decodeBits (decodeFirst (decodeSecond w))),
      decodeSecond (decodeSecond w))
  have hcode : Computable code := by
    have hpair : Computable (fun p : BitString × BitString => pairCode p.1 p.2) :=
      pairCode_computable
    have h1 : Computable (fun a : (ℕ × ℕ) × BitString => natBits a.1.1) :=
      natBits_computable.comp (Computable.fst.comp Computable.fst)
    have h2 : Computable (fun a : (ℕ × ℕ) × BitString => natBits a.1.2) :=
      natBits_computable.comp (Computable.snd.comp Computable.fst)
    have h3 := hpair.comp (h2.pair (Computable.snd : Computable (fun a : (ℕ × ℕ) × BitString =>
      a.2)))
    have h4 := hpair.comp (h1.pair h3)
    exact h4
  have hleft : Function.LeftInverse decode code := by
    intro a
    simp [code, decode, decodeFirst_pairCode, decodeSecond_pairCode, natBits,
      decodeBits_natBits]
  obtain ⟨c₁, hc₁⟩ := not_isMisesKLRandom_of_plainK_lt_xside_coding A
    (fun a : (ℕ × ℕ) × BitString =>
      not_isMisesKLRandom_of_plainK_lt_xside_dom A a.1 a.2)
    (fun a => not_isMisesKLRandom_of_plainK_lt_xside_cost a.1)
    (not_isMisesKLRandom_of_plainK_lt_xside_upper A)
    (not_isMisesKLRandom_of_plainK_lt_xside_mass A) code decode hcode hleft
  let F : List BitString →. BitString := fun xs =>
    Part.some (decodeSecond (decodeSecond xs.headI))
  have hF : PartrecIn {charOracle A} F :=
    (decodeSecond_computable.comp (decodeSecond_computable.comp
      Primrec.list_headI.to_comp)).computableIn.partrecIn
  obtain ⟨c₂, hc₂⟩ := PointToSet.oracle_tuple_bounds_composition A 1 F hF
  refine ⟨c₁ + c₂ + 2, fun x m d T hT hK => ?_⟩
  have hD : not_isMisesKLRandom_of_plainK_lt_xside_dom A (m, d) x := ⟨T, hT, hK⟩
  have h1 : (PointToSet.oracleComplexity A (code ((m, d), x)) : ℝ) ≤
      ((m + 2 * (natBits m).length + 2 * (natBits d).length + 2 : ℕ) : ℝ) - d + c₁ :=
    hc₁ ((m, d), x) hD
  have h2 : PointToSet.oracleComplexity A x ≤
      PointToSet.oracleComplexity A (code ((m, d), x)) + c₂ := by
    have h := hc₂ [code ((m, d), x)] x (by simp) (by
      simp [F, code, decodeSecond_pairCode])
    simpa using h
  have hlm : (natBits m).length = Nat.size m := Nat.size_eq_bits_len m
  have hld : (natBits d).length = Nat.size d := Nat.size_eq_bits_len d
  rw [hlm, hld] at h1
  have h1' : PointToSet.oracleComplexity A (code ((m, d), x)) + d ≤
      m + 2 * Nat.size m + 2 * Nat.size d + 2 + c₁ := by
    have : (PointToSet.oracleComplexity A (code ((m, d), x)) : ℝ) + d ≤
        ((m + 2 * Nat.size m + 2 * Nat.size d + 2 + c₁ : ℕ) : ℝ) := by
      push_cast at h1 ⊢
      linarith
    exact_mod_cast this
  omega

end Kolmogorov.FrequencyGames
