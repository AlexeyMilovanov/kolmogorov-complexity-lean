/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale.LogComplexityConstruction

/-!
# Martin Lof Separation

The uniform-measure separation of computable randomness from Martin-Löf randomness, together with
the fact that computable randomness implies Mises-Church randomness.

Main declarations:

* `exists_isComputablyRandom_not_isMartinLofRandom`: there is a computably random sequence that
  is not Martin-Löf random (SUV Theorem 182(b), p. 279).
* `isMisesChurchRandom_of_isComputablyRandom`: a computably random sequence is Mises-Church
  random, proved by a computable martingale that wins on every unbalanced sequence.

The module belongs to the chapter of Shen, Uspensky and Vereshchagin on randomness and
frequency games.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology ComputableReals

/-- Step 1 of the proof of `exists_isComputablyRandom_not_isMartinLofRandom`: a sequence
whose prefixes have logarithmic complexity is not Martin-Löf random. -/
private theorem exists_isComputablyRandom_not_isMartinLofRandom_step1
    (V : Map) (hV : isOptimalConditional V)
    {w : CantorSeq} {c : ℕ}
    (H : ∀ n : ℕ, plainK V (cantorPrefix w n) ≤ ((c * Nat.log 2 n + c : ℕ) : ℕ∞)) :
    ¬ IsMartinLofRandom uniformMeasure w := by
  intro hw
  have hconv : (∑' n : ℕ, (2 : ENNReal)⁻¹ ^ (2 * Nat.size n)) ≠ ⊤ := by
    have hterm : ∀ n : ℕ, (2 : ENNReal)⁻¹ ^ (2 * Nat.size n)
        ≤ ENNReal.ofReal (1 / (((n : ℝ) + 1) ^ 2)) := by
      intro n
      have h2 : (2 : ENNReal)⁻¹ =ENNReal.ofReal (1 / 2) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
        simp
      rw [h2, ← ENNReal.ofReal_pow (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have hlt : n < 2 ^ Nat.size n := Nat.lt_size_self n
      have hle : ((n : ℝ) + 1) ≤ 2 ^ Nat.size n := by exact_mod_cast hlt
      have hpos : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
      have h3 : ((n : ℝ) + 1) ^ 2 ≤ ((2 : ℝ) ^ Nat.size n) ^ 2 := by gcongr
      have h4 : (1 / 2 : ℝ) ^ (2 * Nat.size n) = 1 / ((2 : ℝ) ^ Nat.size n) ^ 2 := by
        rw [pow_mul', div_pow, one_pow, div_pow, one_pow]
      rw [h4]
      exact one_div_le_one_div_of_le (by positivity) h3
    have hsum : Summable (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2)) := by
      have := (summable_nat_add_iff 1).mpr
        ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
      simpa using this
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  obtain ⟨c', hc'⟩ := forall_computable_summable_le_plainK_of_isMartinLofRandom_uniform hV hw
    (fun n => 2 * Nat.size n)
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) computable_nat_size) hconv
  set a := c + 2 with ha
  set b := c + 2 + c' with hb
  set m := 2 * a + b + 1 with hm
  have key : ∀ K : ℕ, 2 ^ K ≤ a * K + b := by
    intro K
    have h1 := hc' (2 ^ K)
    have h2 := H (2 ^ K)
    have hs : Nat.size (2 ^ K) = K + 1 := Nat.size_pow
    have hl : Nat.log 2 (2 ^ K) = K := Nat.log_pow (by norm_num) K
    rw [hl] at h2
    have h3 : ((2 ^ K : ℕ) : ℕ∞) ≤ ((c * K + c : ℕ) : ℕ∞) + ((2 * Nat.size (2 ^ K) : ℕ) : ℕ∞)
        + (c' : ℕ∞) := h1.trans (by gcongr)
    rw [hs] at h3
    have h4 : 2 ^ K ≤ c * K + c + 2 * (K + 1) + c' := by exact_mod_cast h3
    nlinarith
  have h5 := key (2 * m)
  have h6 : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have h7 : (m + 1) * (m + 1) ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul h6 h6
  have h8 : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
  rw [h8] at h5
  nlinarith

/-- **SUV Theorem 182(b), p. 279, "so the previous statement cannot be reversed".**  There is a
computably random sequence that is not Martin-Löf random, for the uniform measure. -/
theorem exists_isComputablyRandom_not_isMartinLofRandom :
    ∃ w, IsComputablyRandom uniformMeasure w ∧ ¬ IsMartinLofRandom uniformMeasure w := by
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  have hpos : ∀ x, 0 < cantorMass uniformMeasure x := by
    intro x
    rw [cantorMass_uniformMeasure]
    exact ENNReal.pow_pos (by norm_num) _
  obtain ⟨w, hw1, c, hw2⟩ :=
    exists_isComputablyRandom_plainK_log isComputableMeasure_uniform hpos V hV
  exact ⟨w, hw1, exists_isComputablyRandom_not_isMartinLofRandom_step1 V hV hw2⟩


/-- The bet fraction `(-1)^i / 2^(i/2+1)` of the `i`-th bettor in the martingale that wins on
every unbalanced sequence. -/
private def mcr_unbalanced_aux_d (i : ℕ) : ℚ :=
    (-1)^i * (1/2 : ℚ)^(i/2+1)

/-- The sign of a bit: `1` for `true` and `-1` for `false`. -/
private def mcr_unbalanced_aux_s (b : Bool) : ℚ :=
    cond b 1 (-1)

/-- The capital of the `i`-th bettor on the word `x`, starting after position `i`. -/
private def mcr_unbalanced_aux_B (i : ℕ) (x : List Bool) : ℚ :=
    ((x.drop i).map
      (fun b => 1 + mcr_unbalanced_aux_d i * mcr_unbalanced_aux_s b)).prod

/-- The total computable rational martingale winning on every unbalanced sequence. -/
private def mcr_unbalanced_aux_M (x : List Bool) : ℚ :=
    ((List.range x.length).map
      (fun i => (1/2 : ℚ)^(i+1) * mcr_unbalanced_aux_B i x)).sum + (1/2 : ℚ)^x.length


/-- Step 1a of the proof of `mcr_unbalanced_aux`: computability of the martingale `M`. -/
private lemma mcr_comp :
  Computable mcr_unbalanced_aux_M := by
  have step1_pow : Computable (fun k : ℕ => (1/2 : ℚ)^k) := by
    apply computable_of_num_den (N := fun _ => 1) (D := fun k => 2^k) (Computable.const 1)
        (Kolmogorov.comp_pow)
    · intro x; positivity
    · intro x; push_cast; exact one_div_pow (2:ℚ) x
  have step2_d : Computable mcr_unbalanced_aux_d := by
    have H1 : Computable (fun i : ℕ => (1/2 : ℚ)^(i/2+1)) := Computable.comp step1_pow
        (Computable.comp (f := fun i => i + 1) (g := fun i => i / 2) (Primrec.nat_add.comp
        Primrec.id (Primrec.const 1)).to_comp (Primrec.nat_div.comp Primrec.id
        (Primrec.const 2)).to_comp)
    have H2 : Computable (fun i : ℕ => (-1 : ℚ)^i) := by
      have H2a := Computable.cond (c := fun i => decide (i % 2 = 0)) (f := fun i => (1:ℚ))
          (g := fun i => (-1:ℚ)) (PrimrecPred.decide (PrimrecRel.comp Primrec.eq
          (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0))).to_comp
          (Computable.const 1) (Computable.const (-1))
      refine H2a.of_eq (fun i => ?_)
      by_cases h : i % 2 = 0
      · have he : Even i := ⟨i / 2, by omega⟩
        rw [he.neg_one_pow]
        simp [h]
      · have ho : Odd i := ⟨i / 2, by omega⟩
        rw [ho.neg_one_pow]
        simp [h]
    apply (computable₂_ratMul.comp H2 H1).of_eq
    intro x; rfl
  have step3_s : Computable mcr_unbalanced_aux_s := by
    have := Computable.cond (c := fun i => i) (f := fun i => (1:ℚ)) (g := fun i => (-1:ℚ))
        Computable.id (Computable.const 1) (Computable.const (-1))
    apply this.of_eq
    intro b
    rfl
  have step4_B : Computable (fun p : ℕ × List Bool =>
    mcr_unbalanced_aux_B p.1 p.2) := by
    have H1 : Computable (fun p : ℕ × List Bool => p.2.drop p.1) :=
        (Primrec.list_drop (α := Bool)).comp Primrec.fst Primrec.snd |>.to_comp.of_eq (fun _ => rfl)
    have H2 : Computable₂ (fun (p : ℕ × List Bool) (sb : ℚ × Bool) =>
      sb.1 * (1 + mcr_unbalanced_aux_d p.1 *
      mcr_unbalanced_aux_s sb.2)) := by
      apply computable₂_ratMul.comp
      · exact (Computable.fst.comp (Computable.snd (α := ℕ × List Bool) (β := ℚ × Bool))).of_eq
          (fun _ => rfl)
      · apply computable₂_ratAdd.comp (Computable.const 1)
        apply computable₂_ratMul.comp
        · exact (Computable.comp step2_d (Computable.fst.comp (Computable.fst (α := ℕ × List Bool)
            (β := ℚ × Bool)))).of_eq (fun _ => rfl)
        · exact (Computable.comp step3_s (Computable.snd.comp (Computable.snd (α := ℕ × List Bool)
            (β := ℚ × Bool)))).of_eq (fun _ => rfl)
    have H3 := Computable.list_foldl (l := fun p : ℕ × List Bool => p.2.drop p.1) (g := fun p => 1)
        (h := fun p sb => sb.1 *
                            (1 + mcr_unbalanced_aux_d
                            p.1 * mcr_unbalanced_aux_s
                            sb.2)) H1 (Computable.const 1) H2
    apply H3.of_eq
    intro p
    dsimp [mcr_unbalanced_aux_B]
    rw [List.prod_eq_foldl, List.foldl_map]
  have H1 : Computable (fun (x : List Bool) => List.range x.length) :=
      (Primrec.list_range.comp Primrec.list_length).to_comp
  have H2 : Computable₂ (fun (x : List Bool) (is : ℚ × ℕ) =>
    is.1 + (1/2 : ℚ)^(is.2+1) * mcr_unbalanced_aux_B
    is.2 x) := by
    apply computable₂_ratAdd.comp
    · exact (Computable.fst.comp (Computable.snd (α := List Bool) (β := ℚ × ℕ))).of_eq
        (fun _ => rfl)
    · apply computable₂_ratMul.comp
      · have Hpow : Computable (fun (p : List Bool × ℚ × ℕ) => (1/2 : ℚ)^(p.2.2+1)) :=
          Computable.comp step1_pow (Computable.comp (f := fun i => i + 1) (g := fun p : List Bool ×
          ℚ × ℕ => p.2.2) (Primrec.nat_add.comp Primrec.id (Primrec.const 1)).to_comp
                     (Computable.snd.comp (Computable.snd (α := List Bool) (β := ℚ × ℕ))))
        exact Hpow.of_eq (fun _ => rfl)
      · have H_B : Computable (fun (p : List Bool × ℚ × ℕ) =>
          mcr_unbalanced_aux_B p.2.2 p.1) := by
          have H_B1 : Computable (fun (p : List Bool × ℚ × ℕ) => (p.2.2, p.1)) :=
              (Computable.pair (Computable.snd.comp (Computable.snd (α := List Bool) (β := ℚ × ℕ)))
              (Computable.fst (α := List Bool) (β := ℚ × ℕ))).of_eq (fun _ => rfl)
          exact (Computable.comp (f := fun p : ℕ × List Bool =>
            mcr_unbalanced_aux_B p.1 p.2) step4_B
            H_B1).of_eq (fun _ => rfl)
        exact H_B.of_eq (fun _ => rfl)
  have H3 := Computable.list_foldl (l := fun x : List Bool => List.range x.length) (g := fun x => 0)
      (h := fun x is => is.1 + (1/2 : ℚ)^(is.2+1) *
                          mcr_unbalanced_aux_B is.2 x)
                          H1 (Computable.const 0) H2
  apply (computable₂_ratAdd.comp H3 (Computable.comp step1_pow (Primrec.list_length.to_comp))).of_eq
  intro x
  dsimp [mcr_unbalanced_aux_M]
  congr 1
  rw [List.sum_eq_foldl, List.foldl_map]


private lemma mcr_mart_d_abs_le_half (i : ℕ) :
    |mcr_unbalanced_aux_d i| ≤ 1/2 := by
  dsimp [mcr_unbalanced_aux_d]
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have H : (1/2 : ℚ)^(i/2+1) ≤ 1/2 := by
    calc
      (1/2 : ℚ)^(i/2+1) ≤ (1/2 : ℚ)^1 := by
        apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
        omega
      _ = 1/2 := by norm_num
  have H2 : |(1/2 : ℚ)^(i/2+1)| = (1/2 : ℚ)^(i/2+1) := by
    apply abs_of_nonneg
    positivity
  rw [H2]
  exact H

private lemma mcr_mart_factor_nonneg (i : ℕ) (b : Bool) : 0 ≤
    1 + mcr_unbalanced_aux_d i *
    mcr_unbalanced_aux_s b := by
  have hd := mcr_mart_d_abs_le_half
      i
  have hs : |mcr_unbalanced_aux_s b| = 1 := by
    cases b <;> rfl
  have : |mcr_unbalanced_aux_d i *
      mcr_unbalanced_aux_s b| ≤ 1/2 := by
    rw [abs_mul, hs, mul_one]
    exact hd
  have H2: - (1/2 : ℚ) ≤ mcr_unbalanced_aux_d i *
      mcr_unbalanced_aux_s b := neg_le_of_abs_le this
  linarith

private lemma mcr_mart_B_nonneg
    (i : ℕ) (x : List Bool) : 0 ≤ mcr_unbalanced_aux_B i
    x := by
  dsimp [mcr_unbalanced_aux_B]
  apply List.prod_nonneg
  intro y hy
  rw [List.mem_map] at hy
  rcases hy with ⟨b, _, rfl⟩
  exact mcr_mart_factor_nonneg i b

private lemma mcr_mart_M_nonneg
    (x : List Bool) : 0 ≤ mcr_unbalanced_aux_M x := by
  dsimp [mcr_unbalanced_aux_M]
  apply add_nonneg
  · apply List.sum_nonneg
    intro y hy
    rw [List.mem_map] at hy
    rcases hy with ⟨i, _, rfl⟩
    apply mul_nonneg
    · positivity
    · exact mcr_mart_B_nonneg i x
  · positivity

private lemma mcr_mart_B_append
    (i : ℕ) (x : List Bool) (b : Bool) (hi : i ≤ x.length) :
    mcr_unbalanced_aux_B i (x ++ [b]) =
    mcr_unbalanced_aux_B i x *
    (1 + mcr_unbalanced_aux_d i *
    mcr_unbalanced_aux_s b) := by
  dsimp [mcr_unbalanced_aux_B]
  rw [List.drop_append_of_le_length hi]
  rw [List.map_append, List.prod_append]
  simp

private lemma mcr_mart_B_length_append (x : List Bool)
    (b : Bool) : mcr_unbalanced_aux_B x.length (x ++ [b]) =
    1 + mcr_unbalanced_aux_d x.length *
    mcr_unbalanced_aux_s b := by
  dsimp [mcr_unbalanced_aux_B]
  have : (x ++ [b]).drop x.length = [b] := by
    rw [List.drop_append_of_le_length (le_refl _)]
    rw [List.drop_length, List.nil_append]
  rw [this]
  simp

private lemma mcr_mart_M_append (x : List Bool) (b : Bool) :
    mcr_unbalanced_aux_M (x ++ [b]) =
      ((List.range x.length).map (fun i => (1/2 : ℚ)^(i+1) * mcr_unbalanced_aux_B i x *
        (1 + mcr_unbalanced_aux_d i * mcr_unbalanced_aux_s b))).sum +
      (1/2 : ℚ)^(x.length+1) * (1 + mcr_unbalanced_aux_d x.length * mcr_unbalanced_aux_s b) +
      (1/2 : ℚ)^(x.length+1) := by
  dsimp [mcr_unbalanced_aux_M]
  rw [List.length_append, List.length_singleton]
  have h1 : List.range (x.length + 1) = List.range x.length ++ [x.length] := List.range_succ
  rw [h1]
  rw [List.map_append]
  rw [List.sum_append]
  simp only [List.map_singleton, List.sum_singleton]
  have H1 : (List.map (fun i => (1 / 2 : ℚ) ^ (i + 1) *
                                  mcr_unbalanced_aux_B i (x ++
                                  [b])) (List.range x.length)).sum =
             (List.map (fun i => (1 / 2 : ℚ) ^ (i + 1) *
                                   mcr_unbalanced_aux_B i x *
                                   (1 + mcr_unbalanced_aux_d i
                                   * mcr_unbalanced_aux_s b))
                                   (List.range x.length)).sum := by
    have : (List.map (fun i => (1 / 2 : ℚ) ^ (i + 1) *
                                 mcr_unbalanced_aux_B i (x ++
                                 [b])) (List.range x.length)) =
           (List.map (fun i => (1 / 2 : ℚ) ^ (i + 1) * mcr_unbalanced_aux_B i x *
             (1 + mcr_unbalanced_aux_d i * mcr_unbalanced_aux_s b)) (List.range x.length)) := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      rw [mcr_mart_B_append i x b
          (le_of_lt hi)]
      ring
    rw [this]
  rw [H1]
  have H2 : (1 / 2 : ℚ) ^ (x.length + 1) *
      mcr_unbalanced_aux_B x.length (x ++ [b]) =
      (1 / 2 : ℚ) ^ (x.length + 1) * (1 +
      mcr_unbalanced_aux_d x.length *
      mcr_unbalanced_aux_s b) := by
    rw [mcr_mart_B_length_append]
  rw [H2]

/-- Step 1b of the proof of
`mcr_unbalanced_aux`: Nonnegativity and fairness. -/
private lemma mcr_mart :
  (∀ x, 0 ≤ mcr_unbalanced_aux_M x) ∧
  (∀ x, mcr_unbalanced_aux_M x =
      (mcr_unbalanced_aux_M (x ++ [false]) +
      mcr_unbalanced_aux_M (x ++ [true])) / 2) := by
  constructor
  · exact mcr_mart_M_nonneg
  · intro x
    have hf : mcr_unbalanced_aux_s false = -1 := rfl
    have ht : mcr_unbalanced_aux_s true = 1 := rfl
    have hsum : ((List.range x.length).map (fun i => (1/2 : ℚ)^(i+1) *
          mcr_unbalanced_aux_B i x *
          (1 + mcr_unbalanced_aux_d i * mcr_unbalanced_aux_s false))).sum +
        ((List.range x.length).map (fun i => (1/2 : ℚ)^(i+1) *
          mcr_unbalanced_aux_B i x *
          (1 + mcr_unbalanced_aux_d i * mcr_unbalanced_aux_s true))).sum =
        2 * ((List.range x.length).map
          (fun i => (1/2 : ℚ)^(i+1) * mcr_unbalanced_aux_B i x)).sum := by
      rw [← List.sum_map_add]
      have : (fun i => (1/2 : ℚ)^(i+1) *
                         mcr_unbalanced_aux_B i x *
                         (1 + mcr_unbalanced_aux_d i *
                         mcr_unbalanced_aux_s false) +
                         (1/2 : ℚ)^(i+1) *
                         mcr_unbalanced_aux_B i x *
                         (1 + mcr_unbalanced_aux_d i *
                         mcr_unbalanced_aux_s true)) =
             fun i => 2 * ((1/2 : ℚ)^(i+1) *
                        mcr_unbalanced_aux_B i x) := by
        funext i
        rw [hf, ht]
        ring
      rw [this]
      rw [List.sum_map_mul_left]
    have h2 : (1 / 2 : ℚ) ^ (x.length + 1) = (1 / 2 : ℚ) ^ x.length / 2 := by
      rw [pow_add, pow_one]
      ring
    have H3 : mcr_unbalanced_aux_M (x ++ [false]) +
        mcr_unbalanced_aux_M (x ++ [true]) = 2 *
        mcr_unbalanced_aux_M x := by
      rw [mcr_mart_M_append x false,
          mcr_mart_M_append x true]
      calc
        ((List.range x.length).map (fun i => (1/2 : ℚ)^(i+1) * mcr_unbalanced_aux_B i x *
          (1 + mcr_unbalanced_aux_d i * mcr_unbalanced_aux_s false))).sum +
        (1/2 : ℚ)^(x.length+1) *
            (1 + mcr_unbalanced_aux_d x.length *
            mcr_unbalanced_aux_s false) +
            (1/2 : ℚ)^(x.length+1) +
        (((List.range x.length).map (fun i => (1/2 : ℚ)^(i+1) * mcr_unbalanced_aux_B i x *
          (1 + mcr_unbalanced_aux_d i * mcr_unbalanced_aux_s true))).sum +
        (1/2 : ℚ)^(x.length+1) *
            (1 + mcr_unbalanced_aux_d x.length *
            mcr_unbalanced_aux_s true) +
            (1/2 : ℚ)^(x.length+1))
        _ = ((List.range x.length).map (fun i => (1/2 : ℚ)^(i+1) * mcr_unbalanced_aux_B i x *
              (1 + mcr_unbalanced_aux_d i * mcr_unbalanced_aux_s false))).sum +
            ((List.range x.length).map (fun i => (1/2 : ℚ)^(i+1) * mcr_unbalanced_aux_B i x *
              (1 + mcr_unbalanced_aux_d i * mcr_unbalanced_aux_s true))).sum +
            (1/2 : ℚ)^(x.length+1) *
                ((1 + mcr_unbalanced_aux_d x.length *
                mcr_unbalanced_aux_s false) +
                (1 + mcr_unbalanced_aux_d x.length *
                mcr_unbalanced_aux_s true)) +
            2 * (1/2 : ℚ)^(x.length+1) := by ring
        _ = 2 * ((List.range x.length).map
              (fun i => (1/2 : ℚ)^(i+1) * mcr_unbalanced_aux_B i x)).sum +
            (1/2 : ℚ)^(x.length+1) * 2 + 2 * (1/2 : ℚ)^(x.length+1) := by
          rw [hsum]
          congr 2
          rw [hf, ht]
          ring
        _ = 2 * mcr_unbalanced_aux_M x := by
          dsimp [mcr_unbalanced_aux_M]
          rw [h2]
          ring
    linarith

/-- Step 1 of the proof of
`mcr_wins`: Nonconvergence of the
frequency yields a fixed positive deviation toward ones or zeros infinitely often. -/
private lemma mcr_extraction (u : CantorSeq)
    (hu : ¬ HasLimitFreq (1/2) u) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/2 ∧
      ((∃ᶠ n : ℕ in Filter.atTop,
          (1 / 2 + ε) * n ≤ (List.count true (cantorPrefix u n) : ℝ)) ∨
       (∃ᶠ n : ℕ in Filter.atTop,
          (1 / 2 + ε) * n ≤ (n - List.count true (cantorPrefix u n) : ℝ))) := by
  unfold HasLimitFreq at hu
  rw [Metric.tendsto_atTop] at hu
  push Not at hu
  obtain ⟨ε', hε', hex⟩ := hu
  refine ⟨min ε' (1/2), lt_min hε' (by norm_num), min_le_right _ _, ?_⟩
  by_contra hcon
  rw [not_or, Filter.not_frequently, Filter.not_frequently] at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 h1
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 h2
  obtain ⟨n, hn, hdist⟩ := hex (max (max N1 N2) 1)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hf : ((freqOne u n : ℚ) : ℝ) = ((cantorPrefix u n).count true : ℝ) / n := by
    simp [freqOne]
  rw [Real.dist_eq, hf] at hdist
  have e1 := hN1 n hnN1
  have e2 := hN2 n hnN2
  have hmin : min ε' (1/2) ≤ ε' := min_le_left _ _
  have hcn : (((cantorPrefix u n).count true : ℕ) : ℝ) ≤ n := by
    have := List.count_le_length (a := true) (l := cantorPrefix u n)
    rw [cantorPrefix_length] at this
    exact_mod_cast this
  rcases le_abs'.1 hdist with h | h
  · -- c/n - 1/2 ≤ -ε'  : zeros dominate
    apply e2
    have h' : ((cantorPrefix u n).count true : ℝ) / n ≤ 1/2 - min ε' (1/2) := by linarith
    rw [div_le_iff₀ hnpos] at h'
    nlinarith
  · have h' : 1/2 + min ε' (1/2) ≤ ((cantorPrefix u n).count true : ℝ) / n := by linarith
    rw [le_div_iff₀ hnpos] at h'
    exact e1 h'

/-- Step 2 of the proof of
`mcr_wins`: Choose a positive
dyadic stake at most half the frequency deviation. -/
private lemma mcr_bettor
    {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, (2 : ℝ)⁻¹ ^ (k + 1) ≤ ε / 2 := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (2:ℝ)⁻¹ < 1)
  exact ⟨k, le_trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)) hk.le⟩

/-- Step 3 of the proof of
`mcr_wins`: Each active bettor,
multiplied by its positive account weight, is bounded by the mixture capital. -/
private lemma mcr_dom
    (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (1/2 : ℚ)^(i+1) * mcr_unbalanced_aux_B i x ≤
        mcr_unbalanced_aux_M x := by
  unfold mcr_unbalanced_aux_M
  have hmem : ((1/2 : ℚ)^(i+1) * mcr_unbalanced_aux_B i x) ∈
      (List.range x.length).map (fun i => (1/2 : ℚ)^(i+1) * mcr_unbalanced_aux_B i x) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have hnn : ∀ a ∈ (List.range x.length).map
      (fun i => (1/2 : ℚ)^(i+1) * mcr_unbalanced_aux_B i x), 0 ≤ a := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    exact mul_nonneg (by positivity)
        (mcr_mart_B_nonneg j x)
  have h1 := List.single_le_sum hnn _ hmem
  have h2 : (0:ℚ) ≤ (1/2)^x.length := by positivity
  linarith

/-- Step 4 of the proof of
`mcr_wins`: The counts of a bit and
its complement add to the length. -/
private lemma mcr_counts
    (l : List Bool) (b : Bool) : l.count b + l.count (!b) = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases a <;> cases b <;>
      simp only [Bool.not_true, Bool.not_false] at ih ⊢ <;>
      simp <;> omega

/-- Step 4 of the proof of
`mcr_wins`: For a bettor whose
signed stake favours the bit β, express its capital as powers indexed by the counts of β and its
complement. -/
private lemma mcr_prod_formula (i : ℕ) (β : Bool) (δ : ℝ)
    (hd : ((mcr_unbalanced_aux_d i : ℚ) : ℝ) = if β then
      δ else -δ) (y : List Bool) :
    (((y.map (fun b => 1 + mcr_unbalanced_aux_d i *
                         mcr_unbalanced_aux_s b)).prod :
                         ℚ) : ℝ)
      = (1 + δ)^(y.count β) * (1 - δ)^(y.count (!β)) := by
  induction y with
  | nil => simp
  | cons b y ih =>
    rw [List.map_cons, List.prod_cons, Rat.cast_mul, ih, Rat.cast_add, Rat.cast_one, Rat.cast_mul]
    cases β
    · simp only [Bool.false_eq_true, ite_false] at hd
      cases b <;> simp [mcr_unbalanced_aux_s, hd] <;>
          ring
    · simp only [ite_true] at hd
      cases b <;> simp [mcr_unbalanced_aux_s, hd] <;>
          ring

/-- Step 4 of the proof of
`mcr_wins`: Deleting the first i
bits loses at most a factor of 2^i for a bettor whose signed stake favours β. -/
private lemma mcr_one_bettor (x : List Bool) (i : ℕ)
    (β : Bool) (δ : ℝ) (hδ1 : 0 < δ) (hδ2 : δ ≤ 1)
    (hd : ((mcr_unbalanced_aux_d i : ℚ) : ℝ) = if β then
      δ else -δ) :
    (1 + δ)^(x.count β) * (1 - δ)^(x.count (!β)) ≤
      2^i * (mcr_unbalanced_aux_B i x : ℝ) := by
  have hB : (mcr_unbalanced_aux_B i x : ℝ) =
      (1 + δ)^((x.drop i).count β) * (1 - δ)^((x.drop i).count (!β)) := by
    unfold mcr_unbalanced_aux_B; exact
        mcr_prod_formula i β δ hd (x.drop i)
  rw [hB]
  have h1 : x.count β ≤ i + (x.drop i).count β := by
    have h0 : (x.take i ++ x.drop i).count β = (x.take i).count β + (x.drop i).count β :=
      List.count_append
    rw [List.take_append_drop] at h0
    have h2 : (x.take i).count β ≤ (x.take i).length := List.count_le_length
    have h3 : (x.take i).length ≤ i := List.length_take_le i x
    omega
  have h2 : (1 + δ)^(x.count β) ≤ 2^i * (1 + δ)^((x.drop i).count β) := by
    calc (1 + δ)^(x.count β) ≤ (1 + δ)^(i + (x.drop i).count β) :=
          pow_le_pow_right₀ (by linarith) h1
      _ = (1 + δ)^i * (1 + δ)^((x.drop i).count β) := pow_add _ _ _
      _ ≤ 2^i * (1 + δ)^((x.drop i).count β) := by
        gcongr
        linarith
  have h3 : (1 - δ)^(x.count (!β)) ≤ (1 - δ)^((x.drop i).count (!β)) :=
    pow_le_pow_of_le_one (by linarith) (by linarith) ((List.drop_sublist i x).count_le (!β))
  calc (1 + δ)^(x.count β) * (1 - δ)^(x.count (!β))
      ≤ (2^i * (1 + δ)^((x.drop i).count β)) * (1 - δ)^((x.drop i).count (!β)) := by
        apply mul_le_mul h2 h3 (pow_nonneg (by linarith) _) (by positivity)
    _ = 2^i * ((1 + δ)^((x.drop i).count β) * (1 - δ)^((x.drop i).count (!β))) := by ring

/-- Step 5 of the proof of
`mcr_wins`: A frequency deviation ε
and a positive stake δ at most ε/2 give exponential growth, by lower bounds on the logarithms of 1+δ
and 1-δ. -/
private lemma mcr_estimate (ε δ : ℝ) (hδ1 : 0 < δ)
    (hδ2 : δ ≤ ε / 2) (hε : ε ≤ 1 / 2)
    (c d : ℕ) (h_c_large : (1 / 2 + ε) * (c + d) ≤ c) :
    Real.exp (ε * δ * (c + d)) ≤ (1 + δ)^c * (1 - δ)^d := by
  have hδ : δ ≤ 1/4 := by linarith
  have hpos1 : 0 < 1 + δ := by linarith
  have hpos2 : 0 < 1 - δ := by linarith
  have h1 : δ - δ^2 ≤ Real.log (1 + δ) := by
    have h := Real.one_sub_inv_le_log_of_pos hpos1
    have h' : δ - δ^2 ≤ 1 - (1 + δ)⁻¹ := by
      have e : 1 - (1 + δ)⁻¹ - (δ - δ^2) = δ^3 / (1 + δ) := by field_simp; ring
      have : 0 ≤ δ^3 / (1 + δ) := by positivity
      linarith
    linarith
  have h2 : -δ - 2 * δ^2 ≤ Real.log (1 - δ) := by
    have h := Real.one_sub_inv_le_log_of_pos hpos2
    have h' : -δ - 2 * δ^2 ≤ 1 - (1 - δ)⁻¹ := by
      have e : 1 - (1 - δ)⁻¹ - (-δ - 2 * δ^2) = δ^2 * (1 - 2 * δ) / (1 - δ) := by
        field_simp; ring
      have : 0 ≤ δ^2 * (1 - 2 * δ) / (1 - δ) := by
        apply div_nonneg
        · apply mul_nonneg (by positivity); linarith
        · linarith
      linarith
    linarith
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn0 : (0 : ℝ) ≤ c + d := add_nonneg hc0 hd0
  have hlog : ε * δ * (c + d) ≤ Real.log ((1 + δ)^c * (1 - δ)^d) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have a1 : (c : ℝ) * (δ - δ^2) ≤ c * Real.log (1 + δ) := mul_le_mul_of_nonneg_left h1 hc0
    have a2 : (d : ℝ) * (-δ - 2 * δ^2) ≤ d * Real.log (1 - δ) :=
      mul_le_mul_of_nonneg_left h2 hd0
    have k1 : (c : ℝ) - d ≥ 2 * ε * (c + d) := by linarith
    nlinarith [mul_nonneg hδ1.le hn0, mul_nonneg hδ1.le (sub_nonneg.2 k1),
      mul_nonneg (mul_nonneg hδ1.le hδ1.le) hc0, mul_nonneg hδ1.le
          (mul_nonneg hn0 (sub_nonneg.2 hδ2))]
  calc Real.exp (ε * δ * (c + d)) ≤ Real.exp (Real.log ((1 + δ)^c * (1 - δ)^d)) :=
        Real.exp_le_exp.2 hlog
    _ = (1 + δ)^c * (1 - δ)^d := Real.exp_log (by positivity)

/-- Step 6 of the proof of
`mcr_wins`: Combine the mixture
bound, the loss from the first i bits, and the exponential estimate at every sufficiently long
biased prefix. -/
private lemma mcr_M_lower (x : List Bool) (i : ℕ) (β : Bool)
    (δ ε : ℝ) (hδ1 : 0 < δ) (hδ2 : δ ≤ ε / 2)
    (hε : ε ≤ 1 / 2) (hd : ((mcr_unbalanced_aux_d i : ℚ) :
        ℝ) = if β then δ else -δ)
    (hi : i < x.length) (hx : (1 / 2 + ε) * x.length ≤ (x.count β : ℝ)) :
    (1/2 : ℝ)^(2*i+1) * Real.exp (ε * δ * x.length) ≤
        (mcr_unbalanced_aux_M x : ℝ) := by
  have h3 : ((1/2 : ℝ))^(i+1) * (mcr_unbalanced_aux_B i
      x : ℝ) ≤ (mcr_unbalanced_aux_M x : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2
        (mcr_dom x i hi)
    push_cast at this
    exact this
  have hcount : (x.length : ℝ) = x.count β + x.count (!β) := by
    exact_mod_cast (mcr_counts x β).symm
  have hδ1' : δ ≤ 1 := by linarith
  have h4 := mcr_one_bettor x i β δ hδ1 hδ1' hd
  have h5 := mcr_estimate ε δ hδ1 hδ2 hε (x.count β) (x.count (!β))
      (by rw [← hcount]; exact hx)
  rw [← hcount] at h5
  have hpow : (1/2 : ℝ)^(2*i+1) * 2^i = (1/2)^(i+1) := by
    rw [show 2*i+1 = (i+1) + i by ring, pow_add, mul_assoc, ← mul_pow]
    norm_num
  calc (1/2 : ℝ)^(2*i+1) * Real.exp (ε * δ * x.length)
      ≤ (1/2 : ℝ)^(2*i+1) * (2^i * (mcr_unbalanced_aux_B
          i x : ℝ)) :=
        mul_le_mul_of_nonneg_left (h5.trans h4) (by positivity)
    _ = (1/2)^(i+1) * (mcr_unbalanced_aux_B i x : ℝ) :=
        by rw [← mul_assoc, hpow]
    _ ≤ mcr_unbalanced_aux_M x := h3

/-- Step 7 of the proof of
`mcr_wins`: Infinitely many biased
prefixes make the capital of a fixed suitable bettor, and hence the mixture, unbounded. -/
private lemma mcr_unbounded_of_bettor (u : CantorSeq) (i : ℕ)
    (β : Bool) (δ ε : ℝ) (hδ1 : 0 < δ)
    (hδ2 : δ ≤ ε / 2) (hε : ε ≤ 1 / 2) (hd :
        ((mcr_unbalanced_aux_d i : ℚ) : ℝ) = if β then
          δ else -δ)
    (hfreq : ∃ᶠ n : ℕ in Filter.atTop,
      (1 / 2 + ε) * n ≤ (((cantorPrefix u n).count β : ℕ) : ℝ)) :
    ¬ BddAbove (Set.range fun n =>
      ((mcr_unbalanced_aux_M (cantorPrefix u n) : ℚ) :
      ℝ)) := by
  rintro ⟨C, hC⟩
  have hε1 : 0 < ε := by linarith
  have hεδ : 0 < ε * δ := mul_pos hε1 hδ1
  obtain ⟨N, hN⟩ := exists_nat_gt (((|C| + 1) * 2^(2*i+1)) / (ε * δ))
  obtain ⟨n, hn, hn1⟩ := (Filter.frequently_atTop.1 hfreq) (max N (i+1))
  have hniN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnii : i + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hM := mcr_M_lower
      (cantorPrefix u n) i β δ ε hδ1 hδ2 hε hd
    (by rw [cantorPrefix_length]; omega) (by rw [cantorPrefix_length]; exact hn1)
  rw [cantorPrefix_length] at hM
  have hMC : ((mcr_unbalanced_aux_M (cantorPrefix u n) :
      ℚ) : ℝ) ≤ C := hC ⟨n, rfl⟩
  have hP : (0:ℝ) < 2^(2*i+1) := by positivity
  have hq : (1/2 : ℝ)^(2*i+1) * 2^(2*i+1) = 1 := by rw [← mul_pow]; norm_num
  have hbig : (|C| + 1) * 2^(2*i+1) < ε * δ * N := by
    have := (div_lt_iff₀ hεδ).1 hN
    linarith
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hniN
  have h1 : ε * δ * N ≤ ε * δ * n := mul_le_mul_of_nonneg_left hNn hεδ.le
  have hexp : ε * δ * n + 1 ≤ Real.exp (ε * δ * n) := by
    linarith [Real.add_one_le_exp (ε * δ * n)]
  have h2 : (1/2:ℝ)^(2*i+1) * (ε * δ * n + 1) ≤ C :=
    calc (1/2:ℝ)^(2*i+1) * (ε * δ * n + 1)
        ≤ (1/2:ℝ)^(2*i+1) * Real.exp (ε * δ * n) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ ((mcr_unbalanced_aux_M (cantorPrefix u n) : ℚ)
          : ℝ) := hM
      _ ≤ C := hMC
  have h3 : ε * δ * n + 1 ≤ 2^(2*i+1) * C := by
    have := mul_le_mul_of_nonneg_left h2 hP.le
    calc ε * δ * n + 1 = 2^(2*i+1) * ((1/2:ℝ)^(2*i+1) * (ε * δ * n + 1)) := by
          rw [← mul_assoc, mul_comm (2^(2*i+1) : ℝ), hq, one_mul]
      _ ≤ 2^(2*i+1) * C := this
  have h4 : (2:ℝ)^(2*i+1) * C ≤ 2^(2*i+1) * |C| :=
    mul_le_mul_of_nonneg_left (le_abs_self C) hP.le
  nlinarith [hbig, h1, h3, h4, hP]

/-- Step 8 of the proof of
`mcr_wins`: Select the even bettor
favouring ones or the odd bettor favouring zeros, according to the recurring deviation. -/
private lemma mcr_conclusion (u : CantorSeq) (ε : ℝ)
    (hε1 : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (h_freq : (∃ᶠ n : ℕ in Filter.atTop,
        (1 / 2 + ε) * n ≤ (List.count true (cantorPrefix u n) : ℝ)) ∨
      (∃ᶠ n : ℕ in Filter.atTop,
        (1 / 2 + ε) * n ≤ (n - List.count true (cantorPrefix u n) : ℝ))) :
    ¬ BddAbove (Set.range fun n =>
      ((mcr_unbalanced_aux_M (cantorPrefix u n) : ℚ) :
      ℝ)) := by
  obtain ⟨k, hk⟩ :=
      mcr_bettor hε1
  have hδ1 : 0 < (2:ℝ)⁻¹ ^ (k+1) := by positivity
  rcases h_freq with h | h
  · refine mcr_unbounded_of_bettor u (2*k) true
      ((2:ℝ)⁻¹ ^ (k+1)) ε hδ1 hk hε2 ?_ h
    have e : mcr_unbalanced_aux_d (2*k) =
        (1/2 : ℚ)^(k+1) := by
      unfold mcr_unbalanced_aux_d
      have h1 : (2*k)/2 = k := by omega
      rw [h1, pow_mul]; simp
    rw [e]; simp
  · refine mcr_unbounded_of_bettor u (2*k+1) false
      ((2:ℝ)⁻¹ ^ (k+1)) ε hδ1 hk hε2 ?_ ?_
    · have e : mcr_unbalanced_aux_d (2*k+1) =
        -(1/2 : ℚ)^(k+1) := by
        unfold mcr_unbalanced_aux_d
        have h1 : (2*k+1)/2 = k := by omega
        rw [h1, pow_succ, pow_mul]; simp
      rw [e]; simp
    · refine h.mono (fun n hn => ?_)
      have h0 : (cantorPrefix u n).count true + (cantorPrefix u n).count false
          = (cantorPrefix u n).length := mcr_counts
              (cantorPrefix u n) true
      rw [cantorPrefix_length] at h0
      have h0' : (((cantorPrefix u n).count true : ℕ) : ℝ) + (((cantorPrefix u n).count false : ℕ) :
          ℝ) = n := by
        exact_mod_cast h0
      linarith

/-- Step 1c of the proof of
`mcr_unbalanced_aux`: Winning estimate. -/
private lemma mcr_wins :
  ∀ u, ¬ HasLimitFreq (1/2) u → ¬ BddAbove (Set.range fun n =>
    ((mcr_unbalanced_aux_M (cantorPrefix u n) : ℚ) : ℝ))
    := by
  intro u hu
  obtain ⟨ε, hε1, hε2, h_freq⟩ := mcr_extraction u hu
  exact mcr_conclusion u
      ε hε1 hε2 h_freq

private lemma mcr_unbalanced_aux :
  ∃ M : BitString → ℚ,
    Computable M ∧
    (∀ x, 0 ≤ M x) ∧
    (∀ x, M x = (M (x ++ [false]) + M (x ++ [true])) / 2) ∧
    ∀ u, ¬ HasLimitFreq (1/2) u → ¬ BddAbove (Set.range fun n => ((M (cantorPrefix u n) : ℚ) : ℝ))
        := by
  refine ⟨mcr_unbalanced_aux_M,
          mcr_comp,
          mcr_mart.1,
          mcr_mart.2,
          mcr_wins⟩

/-- Step 1 of the proof of `isMisesChurchRandom_of_isComputablyRandom`: there is a
computable martingale that wins on all unbalanced sequences. -/
private lemma mcr_unbalanced :
    ∃ m : BitString → ℝ, IsFairCapital uniformMeasure m ∧ IsComputableOnStrings m ∧
      ∀ w : CantorSeq, ¬ HasLimitFreq (1 / 2) w → Wins m w := by
  obtain ⟨M, hcomp, hnn, hfair, hwins⟩ :=
      mcr_unbalanced_aux
  refine ⟨fun x => (M x : ℝ), ?_, isComputablyRandom_iff_rational_aux M hcomp, ?_⟩
  · rw [isFairCapital_uniform_iff]
    refine ⟨fun x => by exact_mod_cast hnn x, fun x => ?_⟩
    have h := hfair x
    have h' : ((M x : ℚ) : ℝ) = (((M (x ++ [false]) + M (x ++ [true])) / 2 : ℚ) : ℝ) := by
      exact_mod_cast h
    simpa using h'
  · intro w hw
    exact hwins w hw

/-- Auxiliary for step 2 of `isMisesChurchRandom_of_isComputablyRandom`: `selectedAux` as a left
fold with a Boolean test for `R`. -/
private lemma mcr_compose_foldl_eq (R : Set BitString)
    (f : BitString → Bool) (hf : ∀ a, f a = true ↔ a ∈ R) (y : BitString) :
    ∀ pre out : BitString,
      y.foldl (fun (s : BitString × BitString) (b : Bool) =>
          (s.1 ++ [b], cond (f s.1) (s.2 ++ [b]) s.2)) (pre, out)
        = (pre ++ y, out ++ selectedAux R pre y) := by
  induction y with
  | nil => intro pre out; simp [selectedAux]
  | cons b rest ih =>
    intro pre out
    simp only [List.foldl_cons]
    rw [ih]
    by_cases h : pre ∈ R
    · have hfp : f pre = true := (hf pre).2 h
      simp [selectedAux, h, hfp]
    · have hfp : f pre = false := by
        cases hfp' : f pre
        · rfl
        · exact absurd ((hf pre).1 hfp') h
      simp [selectedAux, h, hfp]

/-- Auxiliary for step 2 of `isMisesChurchRandom_of_isComputablyRandom`: for decidable `R` the
selected bits of a string are computable. -/
private lemma mcr_compose_computable_selectedBits
    {R : Set BitString} (hR : IsDecidableSet R) :
    Computable (fun y : BitString => selectedBits R y) := by
  obtain ⟨f, hf, hfR⟩ := hR
  have hs : Computable (fun q : BitString × ((BitString × BitString) × Bool) => q.2.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have ho : Computable (fun q : BitString × ((BitString × BitString) × Bool) => q.2.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.snd)
  have hb : Computable (fun q : BitString × ((BitString × BitString) × Bool) => q.2.2) :=
    Computable.snd.comp Computable.snd
  have h1 : Computable (fun q : BitString × ((BitString × BitString) × Bool) =>
      q.2.1.1 ++ [q.2.2]) := Computable.list_concat.comp hs hb
  have h2 : Computable (fun q : BitString × ((BitString × BitString) × Bool) =>
      q.2.1.2 ++ [q.2.2]) := Computable.list_concat.comp ho hb
  have h3 : Computable (fun q : BitString × ((BitString × BitString) × Bool) => f q.2.1.1) :=
    hf.comp hs
  have hstep : Computable₂ (fun (_ : BitString) (p : (BitString × BitString) × Bool) =>
      ((p.1.1 ++ [p.2], cond (f p.1.1) (p.1.2 ++ [p.2]) p.1.2) : BitString × BitString)) :=
    Computable.pair h1 (Computable.cond h3 h2 ho)
  have hfold := Computable.list_foldl (l := fun y : BitString => y)
    (g := fun _ : BitString => (([] : BitString), ([] : BitString)))
    (h := fun (_ : BitString) (p : (BitString × BitString) × Bool) =>
      ((p.1.1 ++ [p.2], cond (f p.1.1) (p.1.2 ++ [p.2]) p.1.2) : BitString × BitString))
    Computable.id (Computable.const _) hstep
  refine (Computable.snd.comp hfold).of_eq fun y => ?_
  simp only
  rw [mcr_compose_foldl_eq R f hfR y [] []]
  simp [selectedBits]

/-- Auxiliary for step 2 of `isMisesChurchRandom_of_isComputablyRandom`: every prefix of the
selected infinite sequence is a selected prefix of `w`. -/
private lemma mcr_compose_prefix_surj
    (R : Set BitString) (w u : CantorSeq) (hsw : selectStream R w = .infinite u) (n : ℕ) :
    ∃ t, cantorPrefix u n = selectedBits R (cantorPrefix w t) := by
  classical
  have hT := isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)
  have hsw' : BitStream.ofPrefixSet (chainPrefixSet (selectChain R w)) hT = .infinite u := hsw
  have hmem : cantorPrefix u n ∈ chainPrefixSet (selectChain R w) := by
    rw [← BitStream.finite_le_ofPrefixSet_iff hT, hsw']
    exact BitStream.finite_le_infinite_iff.mpr
      ((isCantorPrefix_iff_cantorPrefix_eq _ _).mpr (by simp))
  obtain ⟨t0, ht0⟩ := hmem
  have hlen0 : n ≤ (selectChain R w t0).length := by
    simpa using ht0.length_le
  have hstep : ∀ t, (selectChain R w (t + 1)).length ≤ (selectChain R w t).length + 1 := by
    intro t
    unfold selectChain
    rw [cantorPrefix_succ, selectedBits_append_singleton]
    split_ifs <;> simp
  have hex : ∃ t, n ≤ (selectChain R w t).length := ⟨t0, hlen0⟩
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ t0 := Nat.find_min' hex hlen0
  have hlen : (selectChain R w (Nat.find hex)).length = n := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0] at hspec ⊢
      simp [selectChain, selectedBits, selectedAux, cantorPrefix] at hspec ⊢
      omega
    · obtain ⟨s, hs⟩ : ∃ s, Nat.find hex = s + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hlt : ¬ n ≤ (selectChain R w s).length := Nat.find_min hex (by omega)
      have := hstep s
      rw [hs] at hspec ⊢
      omega
  have hpre : selectChain R w (Nat.find hex) <+: selectChain R w t0 :=
    chain_prefix_of_le (selectChain_prefix R w) hle
  refine ⟨Nat.find hex, ?_⟩
  have h1 : cantorPrefix u n <+: selectChain R w t0 := ht0
  have hlenu : (cantorPrefix u n).length = (selectChain R w (Nat.find hex)).length := by
    simp [hlen]
  exact (List.prefix_of_prefix_length_le h1 hpre hlenu.le).eq_of_length hlenu

/-- Step 2 of the proof of `isMisesChurchRandom_of_isComputablyRandom`: given a computable
martingale and a decidable selection rule, one can construct a computable martingale that plays the
original martingale on the selected subsequence. -/
private lemma mcr_compose
    (m : BitString → ℝ) (hfair : IsFairCapital uniformMeasure m)
    (hcomp : IsComputableOnStrings m)
    (R : Set BitString) (hR : IsDecidableSet R) :
    ∃ mR : BitString → ℝ, IsFairCapital uniformMeasure mR ∧ IsComputableOnStrings mR ∧
      ∀ w u : CantorSeq, selectStream R w = .infinite u → Wins m u → Wins mR w := by
  classical
  refine ⟨fun x => m (selectedBits R x), ?_, ?_, ?_⟩
  · obtain ⟨hnn, hf⟩ := (isFairCapital_uniform_iff m).mp hfair
    rw [isFairCapital_uniform_iff]
    refine ⟨fun x => hnn _, fun x => ?_⟩
    simp only [selectedBits_append_singleton]
    by_cases hx : x ∈ R
    · simp only [ite_eq_left hx]
      exact hf _
    · simp only [ite_eq_right hx, List.append_nil]
      ring
  · obtain ⟨q, hq, hbound⟩ := hcomp
    refine ⟨fun p => q (selectedBits R p.1, p.2), ?_, fun x s => hbound _ _⟩
    exact hq.comp (Computable.pair
      ((mcr_compose_computable_selectedBits hR).comp
        Computable.fst) Computable.snd)
  · intro w u hsw hwin hbdd
    apply hwin
    obtain ⟨B, hB⟩ := hbdd
    refine ⟨B, ?_⟩
    rintro _ ⟨n, rfl⟩
    obtain ⟨t, ht⟩ := mcr_compose_prefix_surj R w u hsw
        n
    change m (cantorPrefix u n) ≤ B
    rw [ht]
    exact hB ⟨t, rfl⟩

/-- **SUV Theorem 182(c), p. 279.**  Every computably random sequence is Mises-Church random, for
the uniform measure. -/
theorem isMisesChurchRandom_of_isComputablyRandom {w : CantorSeq}
    (hw : IsComputablyRandom uniformMeasure w) : IsMisesChurchRandom w := by
  intro R hR
  obtain ⟨m, hfair, hcomp, hwins⟩ := mcr_unbalanced
  obtain ⟨mR, hRfair, hRcomp, hRwins⟩ := mcr_compose m
      hfair hcomp R hR
  by_contra h_not
  have h_not_win_mR : ¬ Wins mR w := hw mR hRfair hRcomp
  have h_win_mR : Wins mR w := by
    dsimp [FiniteOrFreq] at h_not
    rcases hsw : selectStream R w with _ | u
    · simp [hsw] at h_not
    · have h_not_u : ¬ HasLimitFreq (1 / 2) u := by
        intro hu
        apply h_not
        rw [hsw]
        exact hu
      exact hRwins w u hsw (hwins u h_not_u)
  exact h_not_win_mR h_win_mR

end Kolmogorov.FrequencyGames
