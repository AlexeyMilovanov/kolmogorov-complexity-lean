/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch.NormalSequences

/-!
# Normal In Base

Normality of a real number in an integer base `b`, as in SUV Section 9.3 (p. 265).

The main declarations are `IsNormalInBase` and `IsAbsolutelyNormal`, defined through the
digits `baseDigit` of the fractional part and the occurrence frequencies `digitOccurrenceFreq`
of digit strings.  The module proves that normality in base `b` is equivalent to normality in
base `b ^ k` (`isNormalInBase_iff_pow`), that the class of reals normal in base `b` depends on
`b` (`exists_isNormalInBase_not_isNormalInBase`), that a sequence is normal exactly when the
orbit of its real under the doubling map is equidistributed
(`isNormal_iff_orbit_equidistributed`), and that normality is preserved by multiplication by a
non-zero integer (`isNormalInBase_mul`, `isNormalInBase_two_mul`) and by division by a non-zero
integer (`isNormalInBase_div_int`).
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-! ### Normal reals -/

/-- The `i`-th digit after the point of the fractional part of `α` in base `b`. -/
noncomputable def baseDigit (b : ℕ) (α : ℝ) (i : ℕ) : ℕ :=
  ⌊(b : ℝ) ^ (i + 1) * Int.fract α⌋₊ % b

/-- The digit string `U` occurs at position `k` of the base-`b` expansion of `α`. -/
def DigitOccursAt (b : ℕ) (α : ℝ) (U : List ℕ) (k : ℕ) : Prop :=
  ∀ j, (hj : j < U.length) → baseDigit b α (k + j) = U[j]

open Classical in
/-- The fraction of positions among the first `N` at which `U` occurs in base `b`. -/
noncomputable def digitOccurrenceFreq (b : ℕ) (α : ℝ) (U : List ℕ) (N : ℕ) : ℝ :=
  (((Finset.range N).filter fun k => DigitOccursAt b α U k).card : ℝ) / N

/-- **SUV p. 265.**  `α` is *normal in base `b`*: every digit string `U` occurs with limit
frequency `b^{-|U|}`. -/
def IsNormalInBase (b : ℕ) (α : ℝ) : Prop :=
  ∀ U : List ℕ, (∀ d ∈ U, d < b) →
    Tendsto (digitOccurrenceFreq b α U) atTop (𝓝 ((b : ℝ)⁻¹ ^ U.length))

/-- **SUV p. 265.**  *Absolutely normal*: normal in every base `b ≥ 2`.  The book says "for every
integer `b`"; bases below `2` have no expansion. -/
def IsAbsolutelyNormal (α : ℝ) : Prop := ∀ b : ℕ, 2 ≤ b → IsNormalInBase b α

/-- The real `0.ω_0 ω_1 …` in `[0, 1]` with binary digits `ω`. -/
noncomputable def binaryReal (w : CantorSeq) : ℝ :=
  ∑' i, if w i then (2 : ℝ)⁻¹ ^ (i + 1) else 0

private noncomputable def isNormalInBase_iff_pow_mp_W (b : ℕ) (α : ℝ) (l p : ℕ) : ℕ :=
  ⌊(b : ℝ) ^ (p + l) * Int.fract α⌋₊ % (b ^ l)

/-- Window lemma, Step 1 of both directions of `isNormalInBase_iff_pow`: a word `U` of length
`m` with digits `< c` occurs at position `p` of the base-`c` expansion of `α` exactly when the
length-`m` window at `p` is the base-`c` value of `U`. -/
private lemma isNormalInBase_iff_pow_window
    (c : ℕ) (hc : 2 ≤ c) (α : ℝ) (U : List ℕ) (m p : ℕ) (hU_len : U.length = m)
    (hU_lt : ∀ d ∈ U, d < c) :
    DigitOccursAt c α U p ↔
    isNormalInBase_iff_pow_mp_W c α m p = U.foldl (fun acc d => acc * c + d) 0 := by
  subst m
  have hc0 : 0 < c := by omega
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hfloor (n : ℕ) :
      ⌊(c : ℝ) ^ (p + (n + 1)) * Int.fract α⌋₊ / c =
        ⌊(c : ℝ) ^ (p + n) * Int.fract α⌋₊ := by
    rw [← Nat.floor_div_natCast]
    congr 1
    rw [← Nat.add_assoc, pow_succ]
    field_simp
  have hquot (n : ℕ) :
      isNormalInBase_iff_pow_mp_W c α (n + 1) p / c =
        isNormalInBase_iff_pow_mp_W c α n p := by
    unfold isNormalInBase_iff_pow_mp_W
    rw [pow_succ' c n, Nat.mod_mul_right_div_self, hfloor n]
  have hrem (n : ℕ) :
      isNormalInBase_iff_pow_mp_W c α (n + 1) p % c =
        baseDigit c α (p + n) := by
    unfold isNormalInBase_iff_pow_mp_W baseDigit
    rw [pow_succ' c n, Nat.mod_mul_right_mod]
    rfl
  revert hU_lt
  induction U using List.reverseRecOn with
  | nil =>
    intro _
    simp [DigitOccursAt, isNormalInBase_iff_pow_mp_W, Nat.mod_one]
  | append_singleton U d ih =>
    intro hU_lt
    have hd : d < c := hU_lt d (by simp)
    have hU' : ∀ e ∈ U, e < c := fun e he => hU_lt e (by simp [he])
    have ih' : DigitOccursAt c α U p ↔
        isNormalInBase_iff_pow_mp_W c α U.length p =
          U.foldl (fun acc e => acc * c + e) 0 := ih hU'
    have hlen : (U ++ [d]).length = U.length + 1 := by simp
    have hfold : (U ++ [d]).foldl (fun acc e => acc * c + e) 0 =
        U.foldl (fun acc e => acc * c + e) 0 * c + d := by
      simp [List.foldl_append]
    have hocc : DigitOccursAt c α (U ++ [d]) p ↔
        DigitOccursAt c α U p ∧ baseDigit c α (p + U.length) = d := by
      unfold DigitOccursAt
      constructor
      · intro h
        refine ⟨fun j hj => ?_, ?_⟩
        · have h' := h j (by simp; omega)
          simpa only [List.getElem_append_left hj] using h'
        · have h' := h U.length (by simp)
          simpa using h'
      · rintro ⟨h1, h2⟩ j hj
        by_cases hjU : j < U.length
        · rw [List.getElem_append_left hjU]
          exact h1 j hjU
        · have hj' : j = U.length := by simp at hj; omega
          subst j
          simpa using h2
    rw [hlen, hfold, hocc, ih', ← hquot U.length, ← hrem U.length]
    constructor
    · rintro ⟨h1, h2⟩
      have h := ((Nat.div_mod_unique hc0).mp ⟨h1, h2⟩).1
      rw [← h]
      ring
    · intro h
      exact (Nat.div_mod_unique hc0).mpr ⟨by rw [h]; ring, hd⟩

/-- Step 2 of the proof of `isNormalInBase_iff_pow_mp`: Windows nest. -/
private lemma isNormalInBase_iff_pow_nest
    (b : ℕ) (hb : 2 ≤ b) (α : ℝ) (k M L j q : ℕ) (hL : L ≤ M) (hj : j ≤ M - L) :
    isNormalInBase_iff_pow_mp_W b α (k * L) (k * q + k * j) =
    (isNormalInBase_iff_pow_mp_W b α (k * M) (k * q)) / b ^ (k * (M - L - j)) % (b ^ (k * L))
        := by
  have hsplit : k * (M - L - j) + (k * j + k * L) = k * M := by
    rw [← mul_add, ← mul_add]
    congr 1
    omega
  have hpow : b ^ (k * M) = b ^ (k * (M - L - j)) * b ^ (k * j + k * L) := by
    rw [← pow_add, hsplit]
  have hdiv : b ^ (k * L) ∣ b ^ (k * j + k * L) := pow_dvd_pow b (by omega)
  symm
  unfold isNormalInBase_iff_pow_mp_W
  rw [hpow, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdiv,
    ← Nat.floor_div_natCast]
  congr 2
  rw [Nat.cast_pow, div_eq_iff (by positivity : (b : ℝ) ^ (k * (M - L - j)) ≠ 0)]
  have he : k * q + k * M = (k * q + k * j + k * L) + k * (M - L - j) := by
    omega
  rw [he, pow_add]
  ring

/-- Step 1 of the proof of `isNormalInBase_iff_pow_counting`:
split a finite sum into blocks of a fixed size. -/
private lemma isNormalInBase_iff_pow_sum_blocks (b : ℕ) (F : ℕ → ℕ) :
    ∀ n : ℕ, ∑ m ∈ Finset.range (n * b), F m =
      ∑ q ∈ Finset.range n, ∑ d ∈ Finset.range b, F (q * b + d) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Step 2 of the proof of `isNormalInBase_iff_pow_counting`:
removing a prescribed middle block leaves an arbitrary function of the prefix,
with one copy for each possible suffix. -/
private lemma isNormalInBase_iff_pow_strip_window
    (a d n t : ℕ) (ha : 0 < a) (ht : t < d) (F : ℕ → ℕ) :
    (∑ z ∈ Finset.range (n * d * a),
      if z / a % d = t then F (z / (a * d)) else 0) =
        a * ∑ q ∈ Finset.range n, F q := by
  have hd : 0 < d := Nat.zero_lt_of_lt ht
  have hdiv (q r : ℕ) (hr : r < a) : (q * a + r) / a = q := by
    rw [add_comm, Nat.add_mul_div_right _ _ ha, Nat.div_eq_of_lt hr, zero_add]
  rw [isNormalInBase_iff_pow_sum_blocks]
  calc
    (∑ q ∈ Finset.range (n * d), ∑ r ∈ Finset.range a,
        if (q * a + r) / a % d = t then F ((q * a + r) / (a * d)) else 0) =
        ∑ q ∈ Finset.range (n * d), a * (if q % d = t then F (q / d) else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      have heq : ∀ r ∈ Finset.range a,
          (if (q * a + r) / a % d = t then F ((q * a + r) / (a * d)) else 0) =
            (if q % d = t then F (q / d) else 0) := by
        intro r hr
        rw [← Nat.div_div_eq_div_mul, hdiv q r (Finset.mem_range.mp hr)]
      rw [Finset.sum_congr rfl heq]
      simp
    _ = a * ∑ q ∈ Finset.range (n * d), if q % d = t then F (q / d) else 0 := by
      rw [Finset.mul_sum]
    _ = a * ∑ q ∈ Finset.range n, F q := by
      congr 1
      rw [isNormalInBase_iff_pow_sum_blocks]
      apply Finset.sum_congr rfl
      intro q hq
      have heq : ∀ r ∈ Finset.range d,
          (if (q * d + r) % d = t then F ((q * d + r) / d) else 0) =
            (if r = t then F q else 0) := by
        intro r hr
        have hr' := Finset.mem_range.mp hr
        have hqdiv : (q * d + r) / d = q := by
          rw [add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hr', zero_add]
        rw [hqdiv, add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr']
      rw [Finset.sum_congr rfl heq]
      simp [ht]

/-- Step 3 of the proof of `isNormalInBase_iff_pow_counting`:
a prescribed length-`L` window has exactly `B ^ (M - L)` realizations. -/
private lemma isNormalInBase_iff_pow_single_count
    (B L M s t : ℕ) (hB : 0 < B) (hs : s + L ≤ M) (ht : t < B ^ L) :
    ((Finset.range (B ^ M)).filter (fun z => z / B ^ s % B ^ L = t)).card =
      B ^ (M - L) := by
  have hfactor : B ^ M = B ^ (M - (s + L)) * B ^ L * B ^ s := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hstrip := isNormalInBase_iff_pow_strip_window
    (B ^ s) (B ^ L) (B ^ (M - (s + L))) t (pow_pos hB _) ht (fun _ => 1)
  rw [← hfactor] at hstrip
  calc
    ((Finset.range (B ^ M)).filter (fun z => z / B ^ s % B ^ L = t)).card =
        B ^ s * B ^ (M - (s + L)) := by
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, mul_one,
        ← Finset.card_filter] using hstrip
    _ = B ^ (M - L) := by
      rw [← pow_add]
      congr 1
      omega

/-- Step 4 of the proof of `isNormalInBase_iff_pow_counting`:
prescribing the word in two disjoint windows fixes exactly `2 * L` letters. -/
private lemma isNormalInBase_iff_pow_disjoint_count
    (B L M s s' t : ℕ) (hB : 0 < B) (hs : s' + L ≤ M) (hss : s + L ≤ s')
    (ht : t < B ^ L) :
    ((Finset.range (B ^ M)).filter (fun z =>
      z / B ^ s % B ^ L = t ∧ z / B ^ s' % B ^ L = t)).card =
        B ^ (M - 2 * L) := by
  have hfactor : B ^ M = B ^ (M - (s + L)) * B ^ L * B ^ s := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hgap : B ^ s * B ^ L * B ^ (s' - (s + L)) = B ^ s' := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hstrip := isNormalInBase_iff_pow_strip_window
    (B ^ s) (B ^ L) (B ^ (M - (s + L))) t (pow_pos hB _) ht
    (fun q => if q / B ^ (s' - (s + L)) % B ^ L = t then 1 else 0)
  rw [← hfactor] at hstrip
  simp only [Nat.div_div_eq_div_mul, hgap] at hstrip
  have hsingle := isNormalInBase_iff_pow_single_count
    B L (M - (s + L)) (s' - (s + L)) t hB (by omega) ht
  rw [Finset.card_filter] at hsingle
  rw [hsingle] at hstrip
  calc
    ((Finset.range (B ^ M)).filter (fun z =>
        z / B ^ s % B ^ L = t ∧ z / B ^ s' % B ^ L = t)).card =
        B ^ s * B ^ (M - (s + L) - L) := by
      simpa only [Finset.card_filter, ite_and] using hstrip
    _ = B ^ (M - 2 * L) := by
      rw [← pow_add]
      congr 1
      omega

/-- Step 5 of the proof of `isNormalInBase_iff_pow_counting`:
the second-moment Chebyshev bound for events independent at distance at least `k`. -/
private lemma isNormalInBase_iff_pow_chebyshev
    {ι : Type*} (Ω : Finset ι) (N k : ℕ) (hk : 1 ≤ k) (X : ℕ → ι → Prop)
    [∀ j x, Decidable (X j x)] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hsingle : ∀ j < N, ((Ω.filter (fun x => X j x)).card : ℝ) = p * Ω.card)
    (hpair : ∀ j < N, ∀ j' < N, j + k ≤ j' →
      ((Ω.filter (fun x => X j x ∧ X j' x)).card : ℝ) = p ^ 2 * Ω.card)
    (δ : ℝ) (hδ : 0 < δ) :
    ((Ω.filter (fun x =>
        δ ≤ |(((Finset.range N).filter (fun j => X j x)).card : ℝ) - N * p|)).card : ℝ)
      ≤ Ω.card * (2 * k * N / δ ^ 2) := by
  classical
  -- centred indicators
  let Y : ℕ → ι → ℝ := fun j x => (if X j x then (1 : ℝ) else 0) - p
  have hS : ∀ x, (((Finset.range N).filter (fun j => X j x)).card : ℝ) - N * p
      = ∑ j ∈ Finset.range N, Y j x := by
    intro x
    simp only [Y, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  let E : ℕ → ℕ → ℝ := fun j j' => ∑ x ∈ Ω, Y j x * Y j' x
  have hYabs : ∀ j x, |Y j x| ≤ 1 := by
    intro j x
    simp only [Y]
    split_ifs
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith
  -- far pairs are uncorrelated
  have hfar : ∀ j < N, ∀ j' < N, j + k ≤ j' → E j j' = 0 := by
    intro j hj j' hj' hjj'
    have h1 := hsingle j hj
    have h2 := hsingle j' hj'
    have h3 := hpair j hj j' hj' hjj'
    have hexp : ∀ x, Y j x * Y j' x
        = (if X j x ∧ X j' x then (1 : ℝ) else 0) - p * (if X j x then (1 : ℝ) else 0)
          - p * (if X j' x then (1 : ℝ) else 0) + p ^ 2 := by
      intro x
      simp only [Y]
      by_cases a : X j x <;> by_cases c : X j' x <;> simp [a, c] <;> ring
    simp only [E, hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_boole, Finset.sum_const, nsmul_eq_mul]
    rw [h1, h2, h3]
    ring
  have hnear : ∀ j j', E j j' ≤ Ω.card := by
    intro j j'
    calc E j j' ≤ ∑ x ∈ Ω, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro x _
          have h1 := hYabs j x
          have h2 := hYabs j' x
          calc Y j x * Y j' x ≤ |Y j x * Y j' x| := le_abs_self _
            _ = |Y j x| * |Y j' x| := abs_mul _ _
            _ ≤ 1 * 1 := by gcongr
            _ = 1 := by ring
      _ = Ω.card := by simp
  have hV : ∑ x ∈ Ω, (∑ j ∈ Finset.range N, Y j x) ^ 2
      = ∑ j ∈ Finset.range N, ∑ j' ∈ Finset.range N, E j j' := by
    simp only [E, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
  have hrow : ∀ j ∈ Finset.range N,
      ∑ j' ∈ Finset.range N, E j j' ≤ 2 * k * Ω.card := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    have hsub : ∑ j' ∈ Finset.range N, E j j'
        = ∑ j' ∈ (Finset.range N) ∩ Finset.Ico (j - k) (j + k), E j j' := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro j' hj'N hj'not
      have hj'N' : j' < N := Finset.mem_range.mp hj'N
      have hnot : ¬ (j' ∈ Finset.Ico (j - k) (j + k)) :=
        fun h => hj'not (Finset.mem_inter.mpr ⟨hj'N, h⟩)
      rw [Finset.mem_Ico] at hnot
      by_cases h1 : j + k ≤ j'
      · exact hfar j hjN j' hj'N' h1
      · have h2 : j' + k ≤ j := by omega
        have h4 := hfar j' hj'N' j hjN h2
        have h5 : E j j' = E j' j :=
          Finset.sum_congr rfl (fun x _ => mul_comm _ _)
        rw [h5]
        exact h4
    rw [hsub]
    calc ∑ j' ∈ (Finset.range N) ∩ Finset.Ico (j - k) (j + k), E j j'
        ≤ ∑ j' ∈ (Finset.range N) ∩ Finset.Ico (j - k) (j + k), (Ω.card : ℝ) :=
          Finset.sum_le_sum (fun j' _ => hnear j j')
      _ = (((Finset.range N) ∩ Finset.Ico (j - k) (j + k)).card : ℝ) * Ω.card := by
          simp [Finset.sum_const]
      _ ≤ (2 * k : ℝ) * Ω.card := by
          have h1 : ((Finset.range N) ∩ Finset.Ico (j - k) (j + k)).card
              ≤ (Finset.Ico (j - k) (j + k)).card :=
            Finset.card_le_card Finset.inter_subset_right
          have h2 : (Finset.Ico (j - k) (j + k)).card ≤ 2 * k := by
            rw [Nat.card_Ico]; omega
          have h3 : ((((Finset.range N) ∩ Finset.Ico (j - k) (j + k)).card : ℕ) : ℝ)
              ≤ (2 * k : ℝ) := by
            exact_mod_cast h1.trans h2
          exact mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
  have hVle : ∑ x ∈ Ω, (∑ j ∈ Finset.range N, Y j x) ^ 2 ≤ N * (2 * k * Ω.card) := by
    rw [hV]
    calc ∑ j ∈ Finset.range N, ∑ j' ∈ Finset.range N, E j j'
        ≤ ∑ j ∈ Finset.range N, (2 * k * Ω.card : ℝ) := Finset.sum_le_sum hrow
      _ = N * (2 * k * Ω.card) := by simp
  -- Chebyshev
  have hcheb : ((Ω.filter (fun x =>
        δ ≤ |(((Finset.range N).filter (fun j => X j x)).card : ℝ) - N * p|)).card : ℝ) * δ ^ 2
      ≤ ∑ x ∈ Ω, (∑ j ∈ Finset.range N, Y j x) ^ 2 := by
    calc ((Ω.filter (fun x =>
        δ ≤ |(((Finset.range N).filter (fun j => X j x)).card : ℝ) - N * p|)).card : ℝ) * δ ^ 2
        = ∑ x ∈ Ω.filter (fun x =>
        δ ≤ |(((Finset.range N).filter (fun j => X j x)).card : ℝ) - N * p|), δ ^ 2 := by
          simp [Finset.sum_const]
      _ ≤ ∑ x ∈ Ω.filter (fun x =>
        δ ≤ |(((Finset.range N).filter (fun j => X j x)).card : ℝ) - N * p|),
          (∑ j ∈ Finset.range N, Y j x) ^ 2 := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Finset.mem_filter] at hx
          have hx2 := hx.2
          rw [hS x] at hx2
          calc δ ^ 2 ≤ |∑ j ∈ Finset.range N, Y j x| ^ 2 := by
                have h0 : 0 ≤ δ := hδ.le
                gcongr
            _ = (∑ j ∈ Finset.range N, Y j x) ^ 2 := sq_abs _
      _ ≤ ∑ x ∈ Ω, (∑ j ∈ Finset.range N, Y j x) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro x _ _
            positivity
  have hδ2 : 0 < δ ^ 2 := by positivity
  rw [← mul_div_assoc, le_div_iff₀ hδ2]
  calc ((Ω.filter (fun x =>
        δ ≤ |(((Finset.range N).filter (fun j => X j x)).card : ℝ) - N * p|)).card : ℝ) * δ ^ 2
      ≤ ∑ x ∈ Ω, (∑ j ∈ Finset.range N, Y j x) ^ 2 := hcheb
    _ ≤ N * (2 * k * Ω.card) := hVle
    _ = Ω.card * (2 * k * N) := by ring

/-- Step 3 of the proof of `isNormalInBase_iff_pow_mp`: Counting lemma. -/
private lemma isNormalInBase_iff_pow_counting
    (b k L M t : ℕ) (hb : 2 ≤ b) (_hk : 1 ≤ k) (hL : 1 ≤ L) (hM : 2 * L ≤ M)
    (ht : t < (b ^ k) ^ L) (ε : ℝ) (hε : 0 < ε) :
    (((Finset.range (b ^ (k * M))).filter (fun z =>
      |(((Finset.Icc 0 (M - L)).filter (fun j =>
        z / (b ^ (k * (M - L - j))) % (b ^ (k * L)) = t)).card : ℝ) -
        ((M - L + 1) : ℝ) * ((b ^ k : ℝ)⁻¹ ^ L)| ≥ ε * M)).card : ℝ)
    ≤ 2 * (L : ℝ) * (b ^ (k * M) : ℝ) / (ε ^ 2 * M) := by
  classical
  let B : ℕ := b ^ k
  let N : ℕ := M - L + 1
  let p : ℝ := (B : ℝ)⁻¹ ^ L
  let Ω := Finset.range (B ^ M)
  let X : ℕ → ℕ → Prop := fun j z => z / B ^ (M - L - j) % B ^ L = t
  have hB : 0 < B := pow_pos (by omega) _
  have hBR : 0 < (B : ℝ) := Nat.cast_pos.mpr hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hLM : L ≤ M := by omega
  have hMR : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hB1)
  have hweight (d : ℕ) (hd : d ≤ M) :
      ((B ^ (M - d) : ℕ) : ℝ) = (B : ℝ)⁻¹ ^ d * (B ^ M : ℕ) := by
    push_cast
    have he : (B : ℝ) ^ M = (B : ℝ) ^ d * (B : ℝ) ^ (M - d) := by
      rw [← pow_add]
      congr 1
      omega
    rw [he, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hBR.ne'), one_mul]
  have hsingle : ∀ j < N, ((Ω.filter (fun z => X j z)).card : ℝ) = p * Ω.card := by
    intro j hj
    have hs : M - L - j + L ≤ M := by omega
    dsimp [Ω, X]
    rw [isNormalInBase_iff_pow_single_count
      B L M (M - L - j) t hB hs ht, hweight L hLM, Finset.card_range]
  have hpair : ∀ j < N, ∀ j' < N, j + L ≤ j' →
      ((Ω.filter (fun z => X j z ∧ X j' z)).card : ℝ) = p ^ 2 * Ω.card := by
    intro j hj j' hj' hjj'
    have hs : M - L - j + L ≤ M := by omega
    have hss : M - L - j' + L ≤ M - L - j := by dsimp [N] at *; omega
    have hc := isNormalInBase_iff_pow_disjoint_count
      B L M (M - L - j') (M - L - j) t hB hs hss ht
    have hcard : (Ω.filter (fun z => X j z ∧ X j' z)).card = B ^ (M - 2 * L) := by
      simpa only [Ω, X, and_comm] using hc
    rw [hcard, hweight (2 * L) hM]
    dsimp [p, Ω]
    rw [Finset.card_range, mul_comm 2 L, pow_mul]
  have hc := isNormalInBase_iff_pow_chebyshev
    Ω N L hL X p hp0 hp1 hsingle hpair (ε * M) (mul_pos hε hMR)
  have hNM : (N : ℝ) ≤ M := by
    dsimp [N]
    exact_mod_cast (show M - L + 1 ≤ M by omega)
  have hbound : (Ω.card : ℝ) * (2 * L * N / (ε * M) ^ 2) ≤
      2 * (L : ℝ) * (B ^ M : ℕ) / (ε ^ 2 * M) := by
    dsimp [Ω]
    rw [Finset.card_range]
    calc
      (B ^ M : ℕ) * (2 * (L : ℝ) * N / (ε * M) ^ 2) ≤
          (B ^ M : ℕ) * (2 * (L : ℝ) * M / (ε * M) ^ 2) := by gcongr
      _ = 2 * (L : ℝ) * (B ^ M : ℕ) / (ε ^ 2 * M) := by
        field_simp
  simpa only [Ω, N, X, p, B, ← pow_mul, Nat.cast_pow, Nat.range_succ_eq_Icc_zero,
    Nat.cast_add, Nat.cast_one, Nat.cast_sub hLM]
    using hc.trans hbound

/-- Every numeral below `c ^ L` has a length-`L` digit list, including leading zeroes
(a private copy of `isNormalInBase_iff_pow_freq_r_digits`, which comes later). -/
private lemma isNormalInBase_iff_pow_assembly_digits
    (c : ℕ) (hc : 2 ≤ c) (L t : ℕ) (ht : t < c ^ L) :
    ∃ U : List ℕ, U.length = L ∧ (∀ d ∈ U, d < c) ∧
      U.foldl (fun acc d => acc * c + d) 0 = t := by
  have hc0 : 0 < c := by omega
  induction L generalizing t with
  | zero =>
    have ht0 : t = 0 := by simpa using ht
    exact ⟨[], rfl, by simp, by simp [ht0]⟩
  | succ L ih =>
    have hquot : t / c < c ^ L := by
      rw [Nat.div_lt_iff_lt_mul hc0]
      simpa only [pow_succ] using ht
    obtain ⟨U, hlen, hU, hval⟩ := ih (t / c) hquot
    refine ⟨U ++ [t % c], by simp [hlen], ?_, ?_⟩
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hU d hd
      · rw [List.mem_singleton] at hd
        exact hd ▸ Nat.mod_lt t hc0
    · simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil, hval]
        using Nat.div_add_mod' t c

/-- The value of a digit list is below `c ^ length`. -/
private lemma isNormalInBase_iff_pow_assembly_val_lt
    (c : ℕ) (U : List ℕ) (hU : ∀ d ∈ U, d < c) :
    U.foldl (fun acc d => acc * c + d) 0 < c ^ U.length := by
  induction U using List.reverseRecOn with
  | nil => simp
  | append_singleton U d ih =>
    have hd : d < c := hU d (by simp)
    have ih' := ih (fun e he => hU e (by simp [he]))
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton, pow_succ]
    calc U.foldl (fun acc d => acc * c + d) 0 * c + d
        < U.foldl (fun acc d => acc * c + d) 0 * c + c := Nat.add_lt_add_left hd _
      _ = (U.foldl (fun acc d => acc * c + d) 0 + 1) * c := by ring
      _ ≤ c ^ U.length * c := Nat.mul_le_mul_right _ ih'

/-- In a normal base-`b` expansion every length-`m` window value has frequency `b ^ (-m)`. -/
private lemma isNormalInBase_iff_pow_assembly_wfreq
    {b : ℕ} (hb : 2 ≤ b) (α : ℝ) (h_norm : IsNormalInBase b α) (m z : ℕ) (hz : z < b ^ m) :
    Tendsto (fun P : ℕ => (((Finset.range P).filter (fun p =>
      isNormalInBase_iff_pow_mp_W b α m p = z)).card : ℝ) / P)
      atTop (𝓝 ((b : ℝ)⁻¹ ^ m)) := by
  classical
  obtain ⟨U, hlen, hU, hval⟩ :=
    isNormalInBase_iff_pow_assembly_digits b hb m z hz
  have heq (P : ℕ) : digitOccurrenceFreq b α U P =
      (((Finset.range P).filter (fun p =>
        isNormalInBase_iff_pow_mp_W b α m p = z)).card : ℝ) / P := by
    unfold digitOccurrenceFreq
    congr 2
    congr 1
    apply Finset.filter_congr
    intro p _
    rw [isNormalInBase_iff_pow_window b hb α U m p hlen hU, hval]
  simpa only [hlen] using (h_norm U hU).congr heq

/-- In a normal base-`b` expansion the windows of length `m` falling into a finite set `S` of
values below `b ^ m` have frequency `|S| * b ^ (-m)`. -/
private lemma isNormalInBase_iff_pow_assembly_setfreq
    {b : ℕ} (hb : 2 ≤ b) (α : ℝ) (h_norm : IsNormalInBase b α) (m : ℕ) (S : Finset ℕ)
    (hS : ∀ z ∈ S, z < b ^ m) :
    Tendsto (fun P : ℕ => (((Finset.range P).filter (fun p =>
      isNormalInBase_iff_pow_mp_W b α m p ∈ S)).card : ℝ) / P)
      atTop (𝓝 (S.card * (b : ℝ)⁻¹ ^ m)) := by
  classical
  have hlim := tendsto_finsetSum S (fun z hz =>
    isNormalInBase_iff_pow_assembly_wfreq hb α h_norm m z (hS z hz))
  have hcount (P : ℕ) : ((Finset.range P).filter (fun p =>
      isNormalInBase_iff_pow_mp_W b α m p ∈ S)).card =
      ∑ z ∈ S, ((Finset.range P).filter (fun p =>
        isNormalInBase_iff_pow_mp_W b α m p = z)).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun p => isNormalInBase_iff_pow_mp_W b α m p)
      (s := (Finset.range P).filter (fun p => isNormalInBase_iff_pow_mp_W b α m p ∈ S))
      (t := S) (fun p hp => (Finset.mem_filter.mp hp).2)]
    apply Finset.sum_congr rfl
    intro z hz
    congr 1
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hp, _⟩, hpz⟩
      exact ⟨hp, hpz⟩
    · rintro ⟨hp, hpz⟩
      exact ⟨⟨hp, hpz ▸ hz⟩, hpz⟩
  rw [Finset.sum_const, nsmul_eq_mul] at hlim
  refine hlim.congr (fun P => ?_)
  rw [hcount P, Nat.cast_sum, Finset.sum_div]

/-- Abstract double counting: if every length-`n` block sum of a `[0, 1]`-valued sequence is
`n * μ` up to `E`, except at "bad" starting points, then its averages are `μ` up to explicit
error terms. -/
private lemma isNormalInBase_iff_pow_assembly_abstract
    (occ bad : ℕ → ℝ) (hocc0 : ∀ s, 0 ≤ occ s) (hocc1 : ∀ s, occ s ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (μ E : ℝ)
    (hq : ∀ q, |∑ j ∈ Finset.range n, occ (q + j) - n * μ| ≤ E + n * bad q)
    (N : ℕ) (hN : 1 ≤ N) :
    |(∑ s ∈ Finset.range N, occ s) / N - μ| ≤
      n / N + E / n + (∑ q ∈ Finset.range N, bad q) / N := by
  have hshift : ∀ j : ℕ, |∑ q ∈ Finset.range N, occ (q + j) -
      ∑ q ∈ Finset.range N, occ q| ≤ j := by
    intro j
    have h1 := Finset.sum_range_add occ j N
    have h2 := Finset.sum_range_add occ N j
    have h3 : ∑ q ∈ Finset.range N, occ (q + j) = ∑ x ∈ Finset.range N, occ (j + x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [add_comm]
    rw [add_comm j N] at h1
    have ha0 : 0 ≤ ∑ x ∈ Finset.range j, occ x := Finset.sum_nonneg (fun x _ => hocc0 x)
    have ha1 : ∑ x ∈ Finset.range j, occ x ≤ j := by
      calc ∑ x ∈ Finset.range j, occ x ≤ ∑ x ∈ Finset.range j, (1 : ℝ) :=
            Finset.sum_le_sum (fun x _ => hocc1 x)
        _ = j := by simp
    have hb0 : 0 ≤ ∑ x ∈ Finset.range j, occ (N + x) :=
      Finset.sum_nonneg (fun x _ => hocc0 _)
    have hb1 : ∑ x ∈ Finset.range j, occ (N + x) ≤ j := by
      calc ∑ x ∈ Finset.range j, occ (N + x) ≤ ∑ x ∈ Finset.range j, (1 : ℝ) :=
            Finset.sum_le_sum (fun x _ => hocc1 _)
        _ = j := by simp
    rw [h3, abs_le]
    constructor <;> linarith
  have hdc : |∑ q ∈ Finset.range N, ∑ j ∈ Finset.range n, occ (q + j) -
      n * ∑ s ∈ Finset.range N, occ s| ≤ n * n := by
    rw [Finset.sum_comm]
    have he : ∑ j ∈ Finset.range n, ∑ q ∈ Finset.range N, occ (q + j) -
        n * ∑ s ∈ Finset.range N, occ s =
        ∑ j ∈ Finset.range n, (∑ q ∈ Finset.range N, occ (q + j) -
          ∑ q ∈ Finset.range N, occ q) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [he]
    calc |∑ j ∈ Finset.range n, (∑ q ∈ Finset.range N, occ (q + j) -
          ∑ q ∈ Finset.range N, occ q)|
        ≤ ∑ j ∈ Finset.range n, |∑ q ∈ Finset.range N, occ (q + j) -
          ∑ q ∈ Finset.range N, occ q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range n, (n : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        refine (hshift j).trans ?_
        exact_mod_cast (Finset.mem_range.mp hj).le
      _ = n * n := by simp
  have hsumq : |∑ q ∈ Finset.range N, ∑ j ∈ Finset.range n, occ (q + j) - N * (n * μ)| ≤
      N * E + n * ∑ q ∈ Finset.range N, bad q := by
    have he : ∑ q ∈ Finset.range N, ∑ j ∈ Finset.range n, occ (q + j) - N * (n * μ) =
        ∑ q ∈ Finset.range N, (∑ j ∈ Finset.range n, occ (q + j) - n * μ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [he]
    calc |∑ q ∈ Finset.range N, (∑ j ∈ Finset.range n, occ (q + j) - n * μ)|
        ≤ ∑ q ∈ Finset.range N, |∑ j ∈ Finset.range n, occ (q + j) - n * μ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Finset.range N, (E + n * bad q) := Finset.sum_le_sum (fun q _ => hq q)
      _ = N * E + n * ∑ q ∈ Finset.range N, bad q := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Finset.mul_sum]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have key : |n * ∑ s ∈ Finset.range N, occ s - N * (n * μ)| ≤
      n * n + (N * E + n * ∑ q ∈ Finset.range N, bad q) := by
    have h := abs_sub_le (n * ∑ s ∈ Finset.range N, occ s)
      (∑ q ∈ Finset.range N, ∑ j ∈ Finset.range n, occ (q + j)) (N * (n * μ))
    have h2 := abs_sub_comm (n * ∑ s ∈ Finset.range N, occ s)
      (∑ q ∈ Finset.range N, ∑ j ∈ Finset.range n, occ (q + j))
    linarith
  have hrw : (∑ s ∈ Finset.range N, occ s) / N - μ =
      (n * ∑ s ∈ Finset.range N, occ s - N * (n * μ)) / (n * N) := by
    field_simp
  rw [hrw, abs_div, abs_of_pos (by positivity : (0 : ℝ) < n * N), div_le_iff₀ (by positivity)]
  calc |n * ∑ s ∈ Finset.range N, occ s - N * (n * μ)|
      ≤ n * n + (N * E + n * ∑ q ∈ Finset.range N, bad q) := key
    _ = (n / N + E / n + (∑ q ∈ Finset.range N, bad q) / N) * (n * N) := by
      field_simp
      ring

/-- For fixed `M ≥ 2L` and `ε, δ > 0`: the frequency of the length-`k * L` base-`b` windows with
value `t` at the positions `k * s` is eventually within
`δ + ε * M / (M - L + 1) + 2 * k * L / (ε ^ 2 * M)` of `b ^ (-k * L)`. -/
private lemma isNormalInBase_iff_pow_assembly_fixedM
    {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (α : ℝ) (h_norm : IsNormalInBase b α)
    (L M t : ℕ) (hL : 1 ≤ L) (hM : 2 * L ≤ M) (ht : t < (b ^ k) ^ L)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      |(∑ s ∈ Finset.range N, if isNormalInBase_iff_pow_mp_W b α (k * L) (k * s) = t
          then (1 : ℝ) else 0) / N - ((b : ℝ) ^ k)⁻¹ ^ L| ≤
        δ + ε * M / ((M - L + 1 : ℕ) : ℝ) + 2 * k * L / (ε ^ 2 * M) := by
  classical
  have hb0 : 0 < b := by omega
  have hLM : L ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  let n : ℕ := M - L + 1
  let μ : ℝ := ((b : ℝ) ^ k)⁻¹ ^ L
  let occ : ℕ → ℝ := fun s =>
    if isNormalInBase_iff_pow_mp_W b α (k * L) (k * s) = t then (1 : ℝ) else 0
  let Z : ℕ → ℕ := fun q => isNormalInBase_iff_pow_mp_W b α (k * M) (k * q)
  let C : ℕ → ℝ := fun z => (((Finset.Icc 0 (M - L)).filter (fun j =>
    z / (b ^ (k * (M - L - j))) % (b ^ (k * L)) = t)).card : ℝ)
  let Bad : Finset ℕ := (Finset.range (b ^ (k * M))).filter (fun z =>
    |C z - ((M - L + 1) : ℝ) * ((b ^ k : ℝ)⁻¹ ^ L)| ≥ ε * M)
  have hBad_card : (Bad.card : ℝ) ≤ 2 * (L : ℝ) * (b ^ (k * M) : ℝ) / (ε ^ 2 * M) :=
    isNormalInBase_iff_pow_counting b k L M t hb hk hL hM ht ε hε
  have hn1 : 1 ≤ n := by omega
  have hnR : (n : ℝ) = (M : ℝ) - L + 1 := by
    simp only [n]
    rw [Nat.cast_add, Nat.cast_sub hLM, Nat.cast_one]
  have hμ0 : 0 ≤ μ := by simp only [μ]; positivity
  have hμ1 : μ ≤ 1 := by
    have hb1 : (1 : ℝ) ≤ (b : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hb0)
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hb1)
  have hocc0 : ∀ s, 0 ≤ occ s := fun s => by simp only [occ]; split_ifs <;> norm_num
  have hocc1 : ∀ s, occ s ≤ 1 := fun s => by simp only [occ]; split_ifs <;> norm_num
  -- block sums are window counts
  have hblock : ∀ q, ∑ j ∈ Finset.range n, occ (q + j) = C (Z q) := by
    intro q
    have hfilt : (Finset.range n).filter (fun j =>
        isNormalInBase_iff_pow_mp_W b α (k * L) (k * (q + j)) = t) =
        (Finset.Icc 0 (M - L)).filter (fun j =>
          Z q / b ^ (k * (M - L - j)) % b ^ (k * L) = t) := by
      rw [show n = M - L + 1 from rfl, Nat.range_succ_eq_Icc_zero]
      apply Finset.filter_congr
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [mul_add, isNormalInBase_iff_pow_nest b hb α k M L j q hLM hj.2]
    simp only [occ, C, Finset.sum_boole]
    rw [hfilt]
  have hq : ∀ q, |∑ j ∈ Finset.range n, occ (q + j) - n * μ| ≤
      ε * M + n * (if Z q ∈ Bad then (1 : ℝ) else 0) := by
    intro q
    rw [hblock q]
    have hnμ : ((M - L + 1) : ℝ) * ((b ^ k : ℝ)⁻¹ ^ L) = n * μ := by rw [hnR]
    by_cases hbad : Z q ∈ Bad
    · rw [ite_eq_left hbad, mul_one]
      have hC0 : 0 ≤ C (Z q) := Nat.cast_nonneg _
      have hCn : C (Z q) ≤ n := by
        have h1 : ((Finset.Icc 0 (M - L)).filter (fun j =>
            Z q / (b ^ (k * (M - L - j))) % (b ^ (k * L)) = t)).card ≤ n := by
          refine (Finset.card_filter_le _ _).trans ?_
          simp [n]
        have h2 : (((Finset.Icc 0 (M - L)).filter (fun j =>
            Z q / (b ^ (k * (M - L - j))) % (b ^ (k * L)) = t)).card : ℝ) ≤ n := by
          exact_mod_cast h1
        exact h2
      have hnμ1 : n * μ ≤ n := mul_le_of_le_one_right (Nat.cast_nonneg _) hμ1
      have hnμ0 : 0 ≤ n * μ := mul_nonneg (Nat.cast_nonneg _) hμ0
      have hεM : 0 ≤ ε * M := by positivity
      rw [abs_le]
      constructor <;> linarith
    · rw [ite_eq_right hbad, mul_zero, add_zero]
      have hZlt : Z q < b ^ (k * M) := Nat.mod_lt _ (by positivity)
      have hnot : ¬ (|C (Z q) - ((M - L + 1) : ℝ) * ((b ^ k : ℝ)⁻¹ ^ L)| ≥ ε * M) := by
        intro h
        exact hbad (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hZlt, h⟩)
      rw [hnμ] at hnot
      exact (not_le.mp hnot).le
  -- the bad windows at the positions `k * q` are rare
  have hG := (isNormalInBase_iff_pow_assembly_setfreq hb α h_norm (k * M) Bad
    (fun z hz => Finset.mem_range.mp (Finset.mem_filter.mp hz).1)).comp
    (tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hk) tendsto_id)
  have hD : ∀ N, ((Finset.range N).filter (fun q => Z q ∈ Bad)).card ≤
      ((Finset.range (k * N)).filter (fun p =>
        isNormalInBase_iff_pow_mp_W b α (k * M) p ∈ Bad)).card := by
    intro N
    apply Finset.card_le_card_of_injOn (fun q => k * q)
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hq ⊢
      exact ⟨Nat.mul_lt_mul_of_pos_left hq.1 (by omega), hq.2⟩
    · intro q1 _ q2 _ h
      exact Nat.eq_of_mul_eq_mul_left (by omega) h
  have hlimval : (k : ℝ) * (Bad.card * (b : ℝ)⁻¹ ^ (k * M)) ≤ 2 * k * L / (ε ^ 2 * M) := by
    have hbpow : (b : ℝ) ^ (k * M) * (b : ℝ)⁻¹ ^ (k * M) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
    have h1 : (Bad.card : ℝ) * (b : ℝ)⁻¹ ^ (k * M) ≤ 2 * (L : ℝ) / (ε ^ 2 * M) := by
      calc (Bad.card : ℝ) * (b : ℝ)⁻¹ ^ (k * M)
          ≤ 2 * (L : ℝ) * (b ^ (k * M) : ℝ) / (ε ^ 2 * M) * (b : ℝ)⁻¹ ^ (k * M) :=
            mul_le_mul_of_nonneg_right hBad_card (by positivity)
        _ = 2 * (L : ℝ) / (ε ^ 2 * M) := by
            rw [div_mul_eq_mul_div, mul_assoc, hbpow, mul_one]
    calc (k : ℝ) * (Bad.card * (b : ℝ)⁻¹ ^ (k * M)) ≤ k * (2 * (L : ℝ) / (ε ^ 2 * M)) :=
          mul_le_mul_of_nonneg_left h1 hkpos.le
      _ = 2 * k * L / (ε ^ 2 * M) := by ring
  have hδk : 0 < δ / (2 * k) := div_pos hδ (mul_pos two_pos hkpos)
  have hev1 : ∀ᶠ N : ℕ in atTop,
      (((Finset.range (k * N)).filter (fun p =>
        isNormalInBase_iff_pow_mp_W b α (k * M) p ∈ Bad)).card : ℝ) / ((k * N : ℕ) : ℝ) <
        Bad.card * (b : ℝ)⁻¹ ^ (k * M) + δ / (2 * k) :=
    (tendsto_order.1 hG).2 _ (by linarith)
  have hev2 : ∀ᶠ N : ℕ in atTop, (n : ℝ) / N < δ / 2 :=
    (tendsto_order.1 (tendsto_const_div_atTop_nhds_zero_nat (n : ℝ))).2 _ (half_pos hδ)
  filter_upwards [hev1, hev2, eventually_ge_atTop 1] with N hN1 hN2 hN3
  have habs := isNormalInBase_iff_pow_assembly_abstract occ
    (fun q => if Z q ∈ Bad then (1 : ℝ) else 0) hocc0 hocc1 n hn1 μ (ε * M) hq N hN3
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN3
  have hbadsum : (∑ q ∈ Finset.range N, (if Z q ∈ Bad then (1 : ℝ) else 0)) / N ≤
      δ / 2 + 2 * k * L / (ε ^ 2 * M) := by
    rw [Finset.sum_boole]
    have h1 : (((Finset.range N).filter (fun q => Z q ∈ Bad)).card : ℝ) ≤
        (((Finset.range (k * N)).filter (fun p =>
          isNormalInBase_iff_pow_mp_W b α (k * M) p ∈ Bad)).card : ℝ) := by
      exact_mod_cast hD N
    have hkN : ((k * N : ℕ) : ℝ) = k * N := by push_cast; ring
    rw [hkN, div_lt_iff₀ (by positivity)] at hN1
    rw [div_le_iff₀ hNpos]
    have h3 : (k : ℝ) * (Bad.card * (b : ℝ)⁻¹ ^ (k * M)) * N ≤ 2 * k * L / (ε ^ 2 * M) * N :=
      mul_le_mul_of_nonneg_right hlimval hNpos.le
    have h4 : (Bad.card * (b : ℝ)⁻¹ ^ (k * M) + δ / (2 * k)) * (k * N) =
        (k : ℝ) * (Bad.card * (b : ℝ)⁻¹ ^ (k * M)) * N + δ / 2 * N := by
      field_simp
    linarith
  have hfinal : (n : ℝ) / N + ε * M / n +
      (∑ q ∈ Finset.range N, (if Z q ∈ Bad then (1 : ℝ) else 0)) / N ≤
      δ + ε * M / n + 2 * k * L / (ε ^ 2 * M) := by
    linarith
  exact habs.trans hfinal

/-- Step 4 of the proof of `isNormalInBase_iff_pow_mp`: Assembly. -/
private lemma isNormalInBase_iff_pow_assembly
    {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (α : ℝ) (h_norm : IsNormalInBase b α)
    (ha_window : ∀ (c : ℕ), 2 ≤ c → ∀ (α : ℝ) (U : List ℕ) (m p : ℕ), U.length = m →
      (∀ d ∈ U, d < c) →
      (DigitOccursAt c α U p ↔
      isNormalInBase_iff_pow_mp_W c α m p = U.foldl (fun acc d => acc * c + d) 0)) :
    IsNormalInBase (b ^ k) α := by
  classical
  intro V hV_lt
  have hb0 : 0 < b := by omega
  have hB2 : 2 ≤ b ^ k := hb.trans (by simpa using Nat.pow_le_pow_right hb0 hk)
  rcases Nat.eq_zero_or_pos V.length with hL0 | hLpos
  · -- the empty word occurs at every position
    have hV0 : V = [] := List.length_eq_zero_iff.mp hL0
    subst hV0
    have hfreq1 : ∀ N : ℕ, 1 ≤ N → digitOccurrenceFreq (b ^ k) α [] N = 1 := by
      intro N hN
      unfold digitOccurrenceFreq
      have hfilt : ((Finset.range N).filter fun q => DigitOccursAt (b ^ k) α [] q) =
          Finset.range N := by
        apply Finset.filter_true_of_mem
        intro q _ j hj
        exact absurd hj (by simp)
      rw [hfilt, Finset.card_range]
      have hN' : (N : ℝ) ≠ 0 := by
        have : 0 < N := hN
        positivity
      exact div_self hN'
    simp only [List.length_nil, pow_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hfreq1 N hN).symm
  · -- a nonempty word of length `L` with value `t`
    set L := V.length with hL_def
    have hL : 1 ≤ L := hLpos
    set t := V.foldl (fun acc d => acc * (b ^ k) + d) 0 with ht_def
    have ht : t < (b ^ k) ^ L :=
      isNormalInBase_iff_pow_assembly_val_lt (b ^ k) V hV_lt
    have hfreq : ∀ N : ℕ, digitOccurrenceFreq (b ^ k) α V N =
        (∑ s ∈ Finset.range N, if isNormalInBase_iff_pow_mp_W b α (k * L) (k * s) = t
          then (1 : ℝ) else 0) / N := by
      intro N
      unfold digitOccurrenceFreq
      rw [Finset.sum_boole]
      congr 2
      congr 1
      apply Finset.filter_congr
      intro q _
      have hw : isNormalInBase_iff_pow_mp_W (b ^ k) α L q =
          isNormalInBase_iff_pow_mp_W b α (k * L) (k * q) := by
        simp only [isNormalInBase_iff_pow_mp_W, Nat.cast_pow, ← pow_mul, Nat.mul_add]
      rw [ha_window (b ^ k) hB2 α V L q rfl hV_lt, hw, ht_def]
    have hμ : (((b ^ k : ℕ) : ℝ))⁻¹ ^ L = ((b : ℝ) ^ k)⁻¹ ^ L := by rw [Nat.cast_pow]
    rw [hμ, Metric.tendsto_atTop]
    intro η hη
    set ε : ℝ := η / 8 with hε_def
    have hε : 0 < ε := by positivity
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    obtain ⟨M0, hM0⟩ := exists_nat_gt (8 * k * L / (ε ^ 2 * η))
    set M : ℕ := M0 + 2 * L with hM_def
    have hM : 2 * L ≤ M := by omega
    have hMR : (M0 : ℝ) ≤ M := by exact_mod_cast (show M0 ≤ M by omega)
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hev := isNormalInBase_iff_pow_assembly_fixedM hb hk α h_norm L M t hL hM
      ht ε (η / 8) hε (by positivity)
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N0, fun N hN => ?_⟩
    rw [Real.dist_eq, hfreq N]
    have h1 : ε * M / ((M - L + 1 : ℕ) : ℝ) ≤ 2 * ε := by
      have hn : (M : ℝ) ≤ 2 * ((M - L + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show M ≤ 2 * (M - L + 1) by omega)
      have hnpos : (0 : ℝ) < ((M - L + 1 : ℕ) : ℝ) := by positivity
      rw [div_le_iff₀ hnpos]
      nlinarith
    have h2 : 2 * k * L / (ε ^ 2 * M) < η / 4 := by
      have hM0' : 8 * k * L / (ε ^ 2 * η) < M := lt_of_lt_of_le hM0 hMR
      rw [div_lt_iff₀ (by positivity)] at hM0'
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have h3 := hN0 N hN
    linarith

/-- Step 1 of the proof of `isNormalInBase_iff_pow`: normal in base `b` implies normal in
base `b^k`. -/
private theorem isNormalInBase_iff_pow_mp {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (α : ℝ) :
    IsNormalInBase b α → IsNormalInBase (b ^ k) α := by
  intro h_norm
  exact isNormalInBase_iff_pow_assembly hb hk α h_norm isNormalInBase_iff_pow_window

/-- Step 2 of the proof of `isNormalInBase_iff_pow_mpr`: Windows nest. -/
private lemma isNormalInBase_iff_pow_mpr_nest
    (b : ℕ) (hb : 2 ≤ b) (α : ℝ) (k L m r q u : ℕ) (_hr : r < k) (hm : r + m ≤ k * L)
    (hU_val : u = isNormalInBase_iff_pow_mp_W b α m (k * q + r)) :
    isNormalInBase_iff_pow_mp_W b α (k * L) (k * q) / b ^ (k * L - r - m) % b ^ m = u := by
  subst hU_val
  have hpow : b ^ (k * L) = b ^ (k * L - r - m) * b ^ (r + m) := by
    rw [← pow_add]; congr 1; omega
  have hdiv : b ^ m ∣ b ^ (r + m) := pow_dvd_pow b (by omega)
  unfold isNormalInBase_iff_pow_mp_W
  rw [hpow, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdiv,
    ← Nat.floor_div_natCast]
  congr 2
  rw [Nat.cast_pow, div_eq_iff (by positivity : (b : ℝ) ^ (k * L - r - m) ≠ 0)]
  have he : k * q + k * L = (k * q + r + m) + (k * L - r - m) := by omega
  rw [he, pow_add]
  ring

/-- Step 3 of the proof of `isNormalInBase_iff_pow_mpr`: Count $S_r$. -/
private lemma isNormalInBase_iff_pow_count
    (b k L m r u : ℕ) (hb : 2 ≤ b) (hm : r + m ≤ k * L) (_hr : r < k) (hu : u < b ^ m) :
    (Finset.filter (fun t => t / b ^ (k * L - r - m) % b ^ m = u) (Finset.range (b ^ (k * L)))).card
        = b ^ (k * L - m) := by
  have hb0 : 0 < b := by omega
  obtain ⟨e, he⟩ : ∃ e, k * L = r + m + e := ⟨k * L - r - m, by omega⟩
  have he' : k * L - r - m = e := by omega
  have he'' : k * L - m = r + e := by omega
  rw [he', he'', he]
  have hbe : 0 < b ^ e := pow_pos hb0 e
  have hbm : 0 < b ^ m := pow_pos hb0 m
  have hd : ∀ h l : ℕ, l < b ^ e → ((h * b ^ m + u) * b ^ e + l) / b ^ e = h * b ^ m + u := by
    intro h l hl
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hbe, Nat.div_eq_of_lt hl, zero_add]
  have hmod : ∀ h l : ℕ, l < b ^ e → ((h * b ^ m + u) * b ^ e + l) % b ^ e = l := by
    intro h l hl
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  have key : ((Finset.range (b ^ r)) ×ˢ (Finset.range (b ^ e))).card =
      (Finset.filter (fun t => t / b ^ e % b ^ m = u) (Finset.range (b ^ (r + m + e)))).card := by
    apply Finset.card_bij (fun (x : ℕ × ℕ) _ => (x.1 * b ^ m + u) * b ^ e + x.2)
    · rintro ⟨h, l⟩ hx
      simp only [Finset.mem_product, Finset.mem_range] at hx
      simp only [Finset.mem_filter, Finset.mem_range]
      obtain ⟨h1, h2⟩ := hx
      refine ⟨?_, ?_⟩
      · have : h * b ^ m + u < b ^ (r + m) := by
          rw [pow_add]
          calc h * b ^ m + u < h * b ^ m + b ^ m := by omega
            _ = (h + 1) * b ^ m := by ring
            _ ≤ b ^ r * b ^ m := Nat.mul_le_mul_right _ h1
        calc (h * b ^ m + u) * b ^ e + l < (h * b ^ m + u) * b ^ e + b ^ e := by omega
          _ = (h * b ^ m + u + 1) * b ^ e := by ring
          _ ≤ b ^ (r + m) * b ^ e := Nat.mul_le_mul_right _ this
          _ = b ^ (r + m + e) := (pow_add b (r + m) e).symm
      · rw [hd h l h2, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
    · rintro ⟨h, l⟩ hx ⟨h', l'⟩ hx' heq
      simp only [Finset.mem_product, Finset.mem_range] at hx hx'
      simp only at heq
      have h1 := hd h l hx.2
      have h2 := hd h' l' hx'.2
      have h3 := hmod h l hx.2
      have h4 := hmod h' l' hx'.2
      rw [heq] at h1 h3
      have hh : h * b ^ m = h' * b ^ m := by omega
      have : h = h' := Nat.eq_of_mul_eq_mul_right hbm hh
      ext
      · exact this
      · simp only; omega
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      obtain ⟨ht1, ht2⟩ := ht
      have hlt : t / b ^ e < b ^ (r + m) := by
        rw [Nat.div_lt_iff_lt_mul hbe, ← pow_add]; exact ht1
      refine ⟨(t / b ^ e / b ^ m, t % b ^ e), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_range]
        refine ⟨?_, Nat.mod_lt _ hbe⟩
        rw [Nat.div_lt_iff_lt_mul hbm, ← pow_add]; exact hlt
      · simp only
        have h5 : t / b ^ e / b ^ m * b ^ m + u = t / b ^ e := by
          rw [← ht2]; exact Nat.div_add_mod' _ _
        rw [h5]
        exact Nat.div_add_mod' t (b ^ e)
  rw [← key, Finset.card_product, Finset.card_range, Finset.card_range, pow_add]

/-- Every numeral below `c ^ L` has a length-`L` digit list, including leading zeroes. -/
private lemma isNormalInBase_iff_pow_freq_r_digits
    (c : ℕ) (hc : 2 ≤ c) (L t : ℕ) (ht : t < c ^ L) :
    ∃ U : List ℕ, U.length = L ∧ (∀ d ∈ U, d < c) ∧
      U.foldl (fun acc d => acc * c + d) 0 = t := by
  have hc0 : 0 < c := by omega
  induction L generalizing t with
  | zero =>
    have ht0 : t = 0 := by simpa using ht
    exact ⟨[], rfl, by simp, by simp [ht0]⟩
  | succ L ih =>
    have hquot : t / c < c ^ L := by
      rw [Nat.div_lt_iff_lt_mul hc0]
      simpa only [pow_succ] using ht
    obtain ⟨U, hlen, hU, hval⟩ := ih (t / c) hquot
    refine ⟨U ++ [t % c], by simp [hlen], ?_, ?_⟩
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hU d hd
      · rw [List.mem_singleton] at hd
        exact hd ▸ Nat.mod_lt t hc0
    · simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil, hval]
        using Nat.div_add_mod' t c

/-- A base-`b ^ k` word gives the frequency of the corresponding length-`k * L` window. -/
private lemma isNormalInBase_iff_pow_freq_r_window_freq
    (b k L t : ℕ) (α : ℝ) (hb : 2 ≤ b) (hk : 1 ≤ k)
    (h_norm : IsNormalInBase (b ^ k) α) (ht : t < b ^ (k * L)) :
    Tendsto (fun N => ((Finset.range N).filter (fun q =>
      isNormalInBase_iff_pow_mp_W b α (k * L) (k * q) = t)).card / (N : ℝ))
      atTop (𝓝 (((b ^ k : ℕ) : ℝ)⁻¹ ^ L)) := by
  classical
  have hB : 2 ≤ b ^ k := by
    exact hb.trans (by simpa using Nat.pow_le_pow_right (by omega : 0 < b) hk)
  obtain ⟨U, hlen, hU, hval⟩ :=
    isNormalInBase_iff_pow_freq_r_digits (b ^ k) hB L t
      (by simpa only [← pow_mul] using ht)
  have hwindow (q : ℕ) :
      isNormalInBase_iff_pow_mp_W (b ^ k) α L q =
        isNormalInBase_iff_pow_mp_W b α (k * L) (k * q) := by
    simp only [isNormalInBase_iff_pow_mp_W, Nat.cast_pow, ← pow_mul,
      Nat.mul_add]
  have heq (N : ℕ) : digitOccurrenceFreq (b ^ k) α U N =
      ((Finset.range N).filter (fun q =>
        isNormalInBase_iff_pow_mp_W b α (k * L) (k * q) = t)).card / (N : ℝ) := by
    unfold digitOccurrenceFreq
    congr 2
    congr 1
    apply Finset.filter_congr
    intro q _
    rw [isNormalInBase_iff_pow_window (b ^ k) hB α U L q hlen hU,
      hval, hwindow]
  simpa only [hlen] using (h_norm U hU).congr heq

/-- Floor division extracts a short window from a longer one containing it. -/
private lemma isNormalInBase_iff_pow_freq_r_extract
    (b m r n p : ℕ) (α : ℝ) (hb : 2 ≤ b) (hm : r + m ≤ n) :
    isNormalInBase_iff_pow_mp_W b α n p / b ^ (n - r - m) % b ^ m =
      isNormalInBase_iff_pow_mp_W b α m (p + r) := by
  have hpow : b ^ n = b ^ (n - r - m) * b ^ (r + m) := by
    rw [← pow_add]
    congr 1
    omega
  have hdiv : b ^ m ∣ b ^ (r + m) := pow_dvd_pow b (by omega)
  unfold isNormalInBase_iff_pow_mp_W
  rw [hpow, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdiv,
    ← Nat.floor_div_natCast]
  congr 2
  rw [Nat.cast_pow, div_eq_iff (by positivity : (b : ℝ) ^ (n - r - m) ≠ 0)]
  have he : p + n = (p + r + m) + (n - r - m) := by omega
  rw [he, pow_add]
  ring

/-- Step 4 of the proof of `isNormalInBase_iff_pow_mpr`: Frequency for fixed $r$. -/
private lemma isNormalInBase_iff_pow_freq_r
    (b k m r u : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k) (hr : r < k) (_hu : u < b ^ m) (α : ℝ)
    (h_norm : IsNormalInBase (b ^ k) α)
    (_H_nest : ∀ L q, r + m ≤ k * L → u = isNormalInBase_iff_pow_mp_W b α m (k * q + r) →
        isNormalInBase_iff_pow_mp_W b α (k * L) (k * q) / b ^ (k * L - r - m) % b ^ m = u)
    (H_count : ∀ L, r + m ≤ k * L → (Finset.filter (fun t => t / b ^ (k * L - r - m) % b ^ m = u)
        (Finset.range (b ^ (k * L)))).card = b ^ (k * L - m)) :
    Tendsto (fun N => ((Finset.range N).filter (fun q =>
      isNormalInBase_iff_pow_mp_W b α m (k * q + r) = u)).card / (N : ℝ))
    atTop (𝓝 ((b : ℝ)⁻¹ ^ m)) := by
  classical
  let L := m + 1
  have hL : r + m ≤ k * L := by
    have hm : m ≤ k * m := Nat.le_mul_of_pos_left _ hk
    dsimp [L]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  let T := fun q => isNormalInBase_iff_pow_mp_W b α (k * L) (k * q)
  let S := (Finset.range (b ^ (k * L))).filter
    (fun t => t / b ^ (k * L - r - m) % b ^ m = u)
  have hmem (q : ℕ) : T q ∈ S ↔
      isNormalInBase_iff_pow_mp_W b α m (k * q + r) = u := by
    have hlt : T q < b ^ (k * L) := Nat.mod_lt _ (by positivity)
    simp only [S, Finset.mem_filter, Finset.mem_range, hlt, true_and]
    rw [isNormalInBase_iff_pow_freq_r_extract b m r (k * L)
      (k * q) α hb hL]
  have hcount (N : ℕ) :
      ((Finset.range N).filter (fun q =>
        isNormalInBase_iff_pow_mp_W b α m (k * q + r) = u)).card =
      ∑ t ∈ S, ((Finset.range N).filter (fun q => T q = t)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := T) (t := S)
      (fun q hq => (hmem q).mpr (Finset.mem_filter.mp hq).2)]
    apply Finset.sum_congr rfl
    intro t ht
    congr 1
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq, _⟩, hqt⟩
      exact ⟨hq, hqt⟩
    · rintro ⟨hq, hqt⟩
      refine ⟨⟨hq, (hmem q).mp ?_⟩, hqt⟩
      rwa [hqt]
  have hlim := tendsto_finsetSum S (fun t ht =>
    isNormalInBase_iff_pow_freq_r_window_freq b k L t α hb hk h_norm
      (Finset.mem_range.mp (Finset.mem_filter.mp ht).1))
  have hval : (∑ _t ∈ S, (((b ^ k : ℕ) : ℝ)⁻¹ ^ L)) = (b : ℝ)⁻¹ ^ m := by
    have hcard : S.card = b ^ (k * L - m) := H_count L hL
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    simp only [Nat.cast_pow, inv_pow, ← pow_mul]
    have he : (b : ℝ) ^ (k * L) = (b : ℝ) ^ (k * L - m) * (b : ℝ) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : m ≤ k * L)]
    rw [he, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have heq : (fun N : ℕ => ((Finset.range N).filter (fun q =>
      isNormalInBase_iff_pow_mp_W b α m (k * q + r) = u)).card / (N : ℝ)) =
      (fun N => ∑ t ∈ S, (((Finset.range N).filter (fun q => T q = t)).card : ℝ) / N) := by
    funext N
    rw [← Finset.sum_div, ← Nat.cast_sum, ← hcount N]
  rw [heq, ← hval]
  exact hlim

/-- Auxiliary counting: residue-class decomposition of a filter over `range (k * N)`. -/
private lemma isNormalInBase_iff_pow_freq_kN_aux_count (k : ℕ) (P : ℕ → Prop)
    [DecidablePred P] (N : ℕ) :
    ((Finset.range (k * N)).filter P).card =
      ∑ r ∈ Finset.range k, ((Finset.range N).filter (fun q => P (k * q + r))).card := by
  induction N with
  | zero => simp
  | succ n ih =>
    have e1 : k * (n + 1) = k * n + k := by ring
    rw [e1, Finset.card_filter, Finset.sum_range_add, ← Finset.card_filter, ih]
    simp only [Finset.card_filter, Finset.sum_range_succ, Finset.sum_add_distrib]

/-- Step 5 of the proof of `isNormalInBase_iff_pow_mpr`: Frequency up to $kN$. -/
private lemma isNormalInBase_iff_pow_freq_kN
    (b k m u : ℕ) (_hb : 2 ≤ b) (hk : 1 ≤ k) (_hu : u < b ^ m) (α : ℝ)
    (h_freq_r : ∀ r < k, Tendsto (fun N => ((Finset.range N).filter (fun q =>
      isNormalInBase_iff_pow_mp_W b α m (k * q + r) = u)).card / (N : ℝ))
      atTop (𝓝 ((b : ℝ)⁻¹ ^ m))) :
    Tendsto (fun N => ((Finset.range (k * N)).filter (fun p =>
      isNormalInBase_iff_pow_mp_W b α m p = u)).card / (k * N : ℝ))
    atTop (𝓝 ((b : ℝ)⁻¹ ^ m)) := by
  classical
  have hcount := fun N => isNormalInBase_iff_pow_freq_kN_aux_count k
    (fun p => isNormalInBase_iff_pow_mp_W b α m p = u) N
  have hlim : Tendsto (fun N : ℕ => ∑ r ∈ Finset.range k,
      (((Finset.range N).filter (fun q =>
        isNormalInBase_iff_pow_mp_W b α m (k * q + r) = u)).card : ℝ) / (N : ℝ)) atTop
      (𝓝 (∑ _r ∈ Finset.range k, (b : ℝ)⁻¹ ^ m)) :=
    tendsto_finsetSum _ (fun r hr => h_freq_r r (Finset.mem_range.mp hr))
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have h2 := hlim.const_mul ((k : ℝ)⁻¹)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hk0,
    one_mul] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  rw [hcount N]
  push_cast
  rw [← Finset.sum_div]
  field_simp

/-- Generic form of Step 6 of the proof of
`isNormalInBase_iff_pow_freq_n`: frequency along multiples of `k` extends to all
cutoffs. -/
private lemma isNormalInBase_iff_pow_freq_n_aux
    (P : ℕ → Prop) [DecidablePred P] (k : ℕ) (hk : 1 ≤ k) (c : ℝ)
    (h : Tendsto (fun N => ((Finset.range (k * N)).filter P).card / (k * N : ℝ))
      atTop (𝓝 c)) :
    Tendsto (fun n => ((Finset.range n).filter P).card / (n : ℝ)) atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop] at h ⊢
  intro ε hε
  obtain ⟨N0, hN0⟩ := h (ε / 2) (by linarith)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hC : (0 : ℝ) < k * (1 + |c|) := by positivity
  obtain ⟨n1, hn1⟩ := exists_nat_gt (2 * (k * (1 + |c|)) / ε)
  refine ⟨max (k * (N0 + 1)) (n1 + 1), fun n hn => ?_⟩
  have hn_ge : k * (N0 + 1) ≤ n := le_trans (le_max_left _ _) hn
  have hn_ge2 : n1 + 1 ≤ n := le_trans (le_max_right _ _) hn
  set N := n / k with hNdef
  have hkN : k * N ≤ n := Nat.mul_div_le n k
  have hnk : n < k * N + k := by
    have := Nat.lt_mul_div_succ n (show 0 < k by omega)
    rw [hNdef]; nlinarith [this]
  have hN0le : N0 + 1 ≤ N := by
    rw [hNdef]; exact (Nat.le_div_iff_mul_le (by omega)).2 (by linarith [mul_comm k (N0+1)])
  have hNpos : 0 < N := by omega
  have hmain := hN0 N (by omega)
  rw [Real.dist_eq] at hmain
  set a : ℕ := ((Finset.range (k * N)).filter P).card with ha
  set A : ℕ := ((Finset.range n).filter P).card with hA
  have hlo : a ≤ A := Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hkN))
  have hhi : A ≤ a + k := by
    have hsub : (Finset.range n).filter P ⊆
        (Finset.range (k * N)).filter P ∪ Finset.Ico (k * N) n := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico] at hx ⊢
      by_cases hx2 : x < k * N
      · exact Or.inl ⟨hx2, hx.2⟩
      · exact Or.inr ⟨by omega, hx.1⟩
    calc A ≤ ((Finset.range (k * N)).filter P ∪ Finset.Ico (k * N) n).card :=
          Finset.card_le_card hsub
      _ ≤ a + (Finset.Ico (k * N) n).card := Finset.card_union_le _ _
      _ ≤ a + k := by rw [Nat.card_Ico]; omega
  have hkNpos : (0 : ℝ) < (k * N : ℕ) := by exact_mod_cast Nat.mul_pos hk hNpos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hkNle : ((k * N : ℕ) : ℝ) ≤ n := by exact_mod_cast hkN
  have hnlt : (n : ℝ) < ((k * N : ℕ) : ℝ) + k := by exact_mod_cast hnk
  have hlo' : (a : ℝ) ≤ A := by exact_mod_cast hlo
  have hhi' : (A : ℝ) ≤ a + k := by exact_mod_cast hhi
  push_cast at hmain hkNpos hkNle hnlt
  have h1 : |(a : ℝ) - c * (k * N)| < ε / 2 * (k * N) := by
    have : (a : ℝ) / (k * N) - c = ((a : ℝ) - c * (k * N)) / (k * N) := by
      field_simp
    rw [this, abs_div, abs_of_pos hkNpos, div_lt_iff₀ hkNpos] at hmain
    exact hmain
  have hrn : (n : ℝ) - k * N < k := by linarith
  have hrn0 : (0 : ℝ) ≤ (n : ℝ) - k * N := by linarith
  have h2 : |(A : ℝ) - c * n| < ε / 2 * n + k * (1 + |c|) := by
    have e : (A : ℝ) - c * n = ((a : ℝ) - c * (k * N)) + ((A : ℝ) - a) - c * ((n : ℝ) - k * N) := by
      ring
    have hAa : |(A : ℝ) - a| ≤ k := by
      rw [abs_of_nonneg (by linarith)]; linarith
    have hcr : |c * ((n : ℝ) - k * N)| ≤ |c| * k := by
      rw [abs_mul, abs_of_nonneg hrn0]
      exact mul_le_mul_of_nonneg_left hrn.le (abs_nonneg c)
    rw [e]
    calc |((a : ℝ) - c * (k * N)) + ((A : ℝ) - a) - c * ((n : ℝ) - k * N)|
        ≤ |((a : ℝ) - c * (k * N)) + ((A : ℝ) - a)| + |c * ((n : ℝ) - k * N)| :=
          abs_sub _ _
      _ ≤ |(a : ℝ) - c * (k * N)| + |(A : ℝ) - a| + |c * ((n : ℝ) - k * N)| := by
          gcongr; exact abs_add_le _ _
      _ < ε / 2 * (k * N) + k + |c| * k := by linarith
      _ ≤ ε / 2 * n + k * (1 + |c|) := by nlinarith
  rw [Real.dist_eq]
  have : (A : ℝ) / n - c = ((A : ℝ) - c * n) / n := by field_simp
  rw [this, abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos]
  have hn1' : 2 * (k * (1 + |c|)) / ε < n := by
    have : (n1 : ℝ) + 1 ≤ n := by exact_mod_cast hn_ge2
    linarith
  rw [div_lt_iff₀ hε] at hn1'
  nlinarith

/-- Step 6 of the proof of `isNormalInBase_iff_pow_mpr`: Frequency along all $n$. -/
private lemma isNormalInBase_iff_pow_freq_n
    (b k m u : ℕ) (hk : 1 ≤ k) (α : ℝ)
    (h_freq_kN : Tendsto (fun N => ((Finset.range (k * N)).filter (fun p =>
      isNormalInBase_iff_pow_mp_W b α m p = u)).card / (k * N : ℝ))
      atTop (𝓝 ((b : ℝ)⁻¹ ^ m))) :
    Tendsto (fun n => ((Finset.range n).filter (fun p =>
      isNormalInBase_iff_pow_mp_W b α m p = u)).card / (n : ℝ))
    atTop (𝓝 ((b : ℝ)⁻¹ ^ m)) := by
  exact isNormalInBase_iff_pow_freq_n_aux _ k hk _ h_freq_kN

private lemma isNormalInBase_iff_pow_assembly_foldl_lt
    {b : ℕ} (_hb : 2 ≤ b) (U : List ℕ) (hU : ∀ d ∈ U, d < b) :
    ∀ (s acc : ℕ), acc < b ^ s →
      U.foldl (fun acc d => acc * b + d) acc < b ^ (s + U.length) := by
  induction U with
  | nil => intro s acc h; simpa using h
  | cons d U ih =>
    intro s acc h
    have hd : d < b := hU d (by simp)
    have h1 : acc * b + d < b ^ (s + 1) := by
      rw [pow_succ]
      calc acc * b + d < acc * b + b := by omega
        _ = (acc + 1) * b := by ring
        _ ≤ b ^ s * b := Nat.mul_le_mul_right _ h
    have := ih (fun e he => hU e (by simp [he])) (s + 1) _ h1
    simpa [List.foldl, Nat.add_assoc, Nat.add_comm 1 U.length, Nat.add_left_comm] using this

/-- Step 7 of the proof of `isNormalInBase_iff_pow_mpr`: Assembly. -/
private lemma isNormalInBase_iff_pow_mpr_assembly
    {b k : ℕ} (hb : 2 ≤ b) (_hk : 1 ≤ k) (α : ℝ) (_h_norm : IsNormalInBase (b ^ k) α)
    (h_window : ∀ (c : ℕ), 2 ≤ c → ∀ (α : ℝ) (U : List ℕ) (m p : ℕ), U.length = m →
      (∀ d ∈ U, d < c) →
      (DigitOccursAt c α U p ↔
      isNormalInBase_iff_pow_mp_W c α m p = U.foldl (fun acc d => acc * c + d) 0))
    (h_freq : ∀ (m u : ℕ), 0 < m → u < b ^ m →
      Tendsto (fun n => ((Finset.range n).filter (fun p =>
        isNormalInBase_iff_pow_mp_W b α m p = u)).card / (n : ℝ))
      atTop (𝓝 ((b : ℝ)⁻¹ ^ m))) :
    IsNormalInBase b α := by
  classical
  intro U hU
  by_cases hnil : U = []
  · subst hnil
    have hocc : ∀ N, 1 ≤ N → digitOccurrenceFreq b α [] N = 1 := by
      intro N hN
      unfold digitOccurrenceFreq
      have : ((Finset.range N).filter fun k => DigitOccursAt b α [] k) = Finset.range N := by
        apply Finset.filter_true_of_mem
        intro k _ j hj
        simp at hj
      rw [this]
      have : (N : ℝ) ≠ 0 := by positivity
      simp [this]
    simp only [List.length_nil, pow_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (hocc N hN).symm
  · have hm : 0 < U.length := List.length_pos_iff.mpr hnil
    have hlt := isNormalInBase_iff_pow_assembly_foldl_lt hb U hU 0 0
      (by simp)
    simp only [zero_add] at hlt
    have hf := h_freq U.length (U.foldl (fun acc d => acc * b + d) 0) hm hlt
    refine hf.congr' ?_
    refine Filter.Eventually.of_forall fun N => ?_
    unfold digitOccurrenceFreq
    have hc : ((Finset.range N).filter (fun p =>
        isNormalInBase_iff_pow_mp_W b α U.length p =
          U.foldl (fun acc d => acc * b + d) 0)).card =
        ((Finset.range N).filter fun k => DigitOccursAt b α U k).card := by
      congr 1
      ext p
      simp only [Finset.mem_filter]
      rw [h_window b hb α U U.length p rfl hU]
    change (((Finset.range N).filter (fun p =>
        isNormalInBase_iff_pow_mp_W b α U.length p =
          U.foldl (fun acc d => acc * b + d) 0)).card : ℝ) / (N : ℝ) = _
    rw [hc]

/-- Step 2 of the proof of `isNormalInBase_iff_pow`: normal in base `b^k` implies normal
in base `b`. -/
private theorem isNormalInBase_iff_pow_mpr {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (α : ℝ) :
    IsNormalInBase (b ^ k) α → IsNormalInBase b α := by
  intro h_norm
  exact isNormalInBase_iff_pow_mpr_assembly hb hk α h_norm
    isNormalInBase_iff_pow_window
    (fun m u hm hu => isNormalInBase_iff_pow_freq_n b k m u hk α
      (isNormalInBase_iff_pow_freq_kN b k m u hb hk hu α
        (fun r hr => isNormalInBase_iff_pow_freq_r b k m r u hb hk hr hu α h_norm
          (fun L q hL hval => isNormalInBase_iff_pow_mpr_nest b hb α k L m r q u hr hL
                                hval)
          (fun L hL => isNormalInBase_iff_pow_count b k L m r u hb hL hr hu))))


/-- **SUV Problem 256, p. 265.**  A real is normal in base `b` exactly when it is normal in base
`b^k`.  The book leaves `b ≥ 2` and `k ≥ 1` implicit. -/
theorem isNormalInBase_iff_pow {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (α : ℝ) :
    IsNormalInBase b α ↔ IsNormalInBase (b ^ k) α :=
  ⟨isNormalInBase_iff_pow_mp hb hk α, isNormalInBase_iff_pow_mpr hb hk α⟩

/-- Auxiliary for `exists_isNormalInBase_not_isNormalInBase`: the real number
`∑_j 2 w_j 3^{-(j+1)}` whose ternary digits are `2 w_j ∈ {0, 2}` (a point of the Cantor set). -/
private noncomputable def exists_isNormalInBase_not_isNormalInBase_cantorReal (w : CantorSeq) : ℝ :=
  ∑' j, if w j then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) else 0

/-- Auxiliary for `exists_isNormalInBase_not_isNormalInBase`: the character `e(y) = exp(2πiy)`. -/
private noncomputable def exists_isNormalInBase_not_isNormalInBase_e (y : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (y : ℂ))

/-- Auxiliary for `exists_isNormalInBase_not_isNormalInBase`: the Weyl average
`(1/N) ∑_{n<N} e(h y_n)` of the sequence `y`. -/
private noncomputable def exists_isNormalInBase_not_isNormalInBase_weylAvg (y : ℕ → ℝ) (h : ℤ)
    (N : ℕ) : ℂ :=
  (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * y n)

/-- Auxiliary for `exists_isNormalInBase_not_isNormalInBase`: `G k z = ∏_{j=1}^k |cos(2π z / 3^j)|`,
the bound for the absolute value of the Fourier transform of the Cantor measure at the integer `z`.
-/
private noncomputable def exists_isNormalInBase_not_isNormalInBase_G (k : ℕ) (z : ℤ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 k, |Real.cos (2 * Real.pi * (z : ℝ) / 3 ^ j)|

/-- Auxiliary for `exists_isNormalInBase_not_isNormalInBase`: the absolute value of the Fourier
transform at the integer `t` of the law of `∑ 2 w_j 3^{-(j+1)}` under the uniform measure. -/
private noncomputable def exists_isNormalInBase_not_isNormalInBase_chf (t : ℤ) : ℝ :=
  ‖∫ w, exists_isNormalInBase_not_isNormalInBase_e
      ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_cantorReal w) ∂uniformMeasure‖

private lemma exists_isNormalInBase_not_isNormalInBase_s1a_e_cont :
    Continuous exists_isNormalInBase_not_isNormalInBase_e := by
  unfold exists_isNormalInBase_not_isNormalInBase_e
  fun_prop

/-- Weyl averages of a trigonometric polynomial converge to its constant coefficient. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s1a_trigpoly (y : ℕ → ℝ)
    (hy : ∀ h : ℤ, h ≠ 0 →
      Tendsto (exists_isNormalInBase_not_isNormalInBase_weylAvg y h) atTop (𝓝 0))
    (S : Finset ℤ) (c : ℤ → ℂ) :
    Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, ∑ h ∈ S,
        c h * exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * y n))
      atTop (𝓝 (∑ h ∈ S, if h = 0 then c h else 0)) := by
  have key : ∀ N : ℕ, (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, ∑ h ∈ S,
        c h * exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * y n)
      = ∑ h ∈ S, c h * exists_isNormalInBase_not_isNormalInBase_weylAvg y h N := by
    intro N
    simp only [exists_isNormalInBase_not_isNormalInBase_weylAvg]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.mul_sum]
    ring
  simp_rw [key]
  refine tendsto_finsetSum _ fun h _ => ?_
  by_cases h0 : h = 0
  · subst h0
    simp only [ite_true]
    have hev : ∀ᶠ N : ℕ in atTop,
        (1 : ℂ) = exists_isNormalInBase_not_isNormalInBase_weylAvg y 0 N := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      simp only [exists_isNormalInBase_not_isNormalInBase_weylAvg,
        exists_isNormalInBase_not_isNormalInBase_e]
      simp [hN']
    have h1 : Tendsto (fun N => exists_isNormalInBase_not_isNormalInBase_weylAvg y 0 N) atTop
        (𝓝 1) := tendsto_const_nhds.congr' hev
    simpa using h1.const_mul (c 0)
  · simp only [h0, ite_false]
    simpa using (hy h h0).const_mul (c h)

/-- Integral of a trigonometric polynomial over a period. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s1a_integral_trigpoly (S : Finset ℤ)
    (c : ℤ → ℂ) :
    ∫ x in (0 : ℝ)..1, ∑ h ∈ S, c h * exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * x)
      = ∑ h ∈ S, if h = 0 then c h else 0 := by
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun h _ => ?_
    rw [intervalIntegral.integral_const_mul]
    by_cases h0 : h = 0
    · subst h0
      simp [exists_isNormalInBase_not_isNormalInBase_e]
    · have hne : (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) ≠ 0 := by
        have : (h : ℂ) ≠ 0 := Int.cast_ne_zero.2 h0
        simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
      have hfun : ∀ x : ℝ, exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * x)
          = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) * (x : ℂ)) := by
        intro x
        simp only [exists_isNormalInBase_not_isNormalInBase_e]
        congr 1
        push_cast
        ring
      simp_rw [hfun]
      rw [integral_exp_mul_complex hne]
      have h1 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) * ((1 : ℝ) : ℂ)) = 1 := by
        have := Complex.exp_int_mul_two_pi_mul_I h
        rw [← this]
        congr 1
        push_cast
        ring
      rw [h1]
      simp [h0]
  · intro h _
    exact (continuous_const.mul
      (exists_isNormalInBase_not_isNormalInBase_s1a_e_cont.comp
        (continuous_const.mul continuous_id))).intervalIntegrable _ _

/-- Uniform approximation of a continuous `1`-periodic function by a trigonometric polynomial. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s1a_approx (ψ : ℝ → ℝ)
    (hc : Continuous ψ) (hp : Function.Periodic ψ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℤ →₀ ℂ, ∀ x : ℝ, ‖(ψ x : ℂ) -
      ∑ h ∈ c.support, c h * exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * x)‖ ≤ ε := by
  have : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have hpc : Function.Periodic (fun x : ℝ => (ψ x : ℂ)) 1 := fun x => by simp [hp x]
  let F : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨hpc.lift, continuous_coinduced_dom.mpr (Complex.continuous_ofReal.comp hc)⟩
  have hF : F ∈ (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  have hF' : F ∈ closure ((Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) :
      Set C(AddCircle (1 : ℝ), ℂ)) := hF
  obtain ⟨P, hP, hdist⟩ := Metric.mem_closure_iff.1 hF' ε hε
  obtain ⟨c, hcP⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hP
  refine ⟨c, fun x => ?_⟩
  have h1 : dist (F (x : AddCircle (1 : ℝ))) (P (x : AddCircle (1 : ℝ))) ≤ dist F P :=
    ContinuousMap.dist_apply_le_dist _
  have h2 : F (x : AddCircle (1 : ℝ)) = (ψ x : ℂ) := by
    simp [F, Function.Periodic.lift_coe]
  have h3 : P (x : AddCircle (1 : ℝ)) =
      ∑ h ∈ c.support, c h * exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * x) := by
    rw [← hcP]
    simp only [Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [fourier_coe_apply]
    simp only [exists_isNormalInBase_not_isNormalInBase_e]
    congr 2
    push_cast
    ring
  rw [h2, h3, dist_eq_norm] at h1
  exact h1.trans hdist.le

/-- Weyl's criterion for continuous `1`-periodic functions. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s1a_cont (y : ℕ → ℝ)
    (hy : ∀ h : ℤ, h ≠ 0 →
      Tendsto (exists_isNormalInBase_not_isNormalInBase_weylAvg y h) atTop (𝓝 0))
    (ψ : ℝ → ℝ) (hc : Continuous ψ) (hp : Function.Periodic ψ 1) :
    Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, ψ (y n)) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, ψ x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨c, hc'⟩ := exists_isNormalInBase_not_isNormalInBase_s1a_approx ψ hc hp
    (ε := ε / 4) (by positivity)
  have hT := exists_isNormalInBase_not_isNormalInBase_s1a_trigpoly y hy c.support c
  have hI : ‖(∑ h ∈ c.support, if h = 0 then c h else 0) - ((∫ x in (0 : ℝ)..1, ψ x : ℝ) : ℂ)‖
      ≤ ε / 4 := by
    rw [← exists_isNormalInBase_not_isNormalInBase_s1a_integral_trigpoly c.support c,
      ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_sub]
    · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (C := ε / 4)
        (f := fun x => (∑ h ∈ c.support, c h *
          exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * x)) - (ψ x : ℂ))
        (fun x _ => by rw [norm_sub_rev]; exact hc' x)
      simpa using this
    · exact (continuous_finsetSum _ fun h _ => continuous_const.mul
        (exists_isNormalInBase_not_isNormalInBase_s1a_e_cont.comp
          (continuous_const.mul continuous_id))).intervalIntegrable _ _
    · exact (Complex.continuous_ofReal.comp hc).intervalIntegrable _ _
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 hT (ε / 4) (by positivity)
  refine ⟨max N0 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0' : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hA := hN0 N hN0'
  rw [dist_eq_norm] at hA
  -- the error term
  have hE : ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, ((ψ (y n) : ℂ) -
      ∑ h ∈ c.support, c h * exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * y n))‖
        ≤ ε / 4 := by
    rw [norm_mul]
    have h1 : ‖∑ n ∈ Finset.range N, ((ψ (y n) : ℂ) -
        ∑ h ∈ c.support, c h * exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * y n))‖
          ≤ N * (ε / 4) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ n ∈ Finset.range N, ‖(ψ (y n) : ℂ) -
            ∑ h ∈ c.support, c h * exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * y n)‖
          ≤ ∑ n ∈ Finset.range N, ε / 4 := Finset.sum_le_sum fun n _ => hc' (y n)
        _ = N * (ε / 4) := by simp
    have h2 : ‖(1 / (N : ℂ))‖ = 1 / (N : ℝ) := by
      rw [norm_div, norm_one, Complex.norm_natCast]
    rw [h2]
    calc 1 / (N : ℝ) * ‖∑ n ∈ Finset.range N, ((ψ (y n) : ℂ) -
        ∑ h ∈ c.support, c h * exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * y n))‖
        ≤ 1 / (N : ℝ) * (N * (ε / 4)) := by gcongr
      _ = ε / 4 := by field_simp
  have hsplit : (((1 / (N : ℝ)) * ∑ n ∈ Finset.range N, ψ (y n) : ℝ) : ℂ) -
        ((∫ x in (0 : ℝ)..1, ψ x : ℝ) : ℂ)
      = (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, ((ψ (y n) : ℂ) -
          ∑ h ∈ c.support, c h * exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * y n))
        + ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N, ∑ h ∈ c.support,
            c h * exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * y n)
          - ∑ h ∈ c.support, if h = 0 then c h else 0)
        + ((∑ h ∈ c.support, if h = 0 then c h else 0) - ((∫ x in (0 : ℝ)..1, ψ x : ℝ) : ℂ)) := by
    push_cast
    rw [Finset.sum_sub_distrib]
    ring
  rw [Real.dist_eq]
  have hnorm : ‖(((1 / (N : ℝ)) * ∑ n ∈ Finset.range N, ψ (y n) : ℝ) : ℂ) -
      ((∫ x in (0 : ℝ)..1, ψ x : ℝ) : ℂ)‖ < ε := by
    rw [hsplit]
    refine lt_of_le_of_lt norm_add₃_le ?_
    linarith [hE, hA, hI]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hnorm
  exact hnorm

/-- The trapezoid minorant of the indicator of the arc `[a, b)`, `0 < a < b < 1`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s1a_trapezoid {a b : ℝ} (ha : 0 < a)
    (_hab : a < b) (hb : b < 1) {δ : ℝ} (hδ : 0 < δ) (hδab : 2 * δ ≤ b - a) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ Function.Periodic ψ 1 ∧
      (∀ x, ψ x ≤ if a ≤ Int.fract x ∧ Int.fract x < b then 1 else 0) ∧
      b - a - 2 * δ ≤ ∫ x in (0 : ℝ)..1, ψ x := by
  set φ : ℝ → ℝ := fun t => max 0 (min 1 (min ((t - a) / δ) ((b - t) / δ))) with hφ
  have hφc : Continuous φ := by
    simp only [hφ]
    fun_prop
  have hφ0 : ∀ t, t ≤ a ∨ b ≤ t → φ t = 0 := by
    intro t ht
    simp only [hφ]
    apply max_eq_left
    rcases ht with ht | ht
    · exact (min_le_right _ _).trans ((min_le_left _ _).trans
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le))
  have hφ1 : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1 := by
    intro t
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hφ2 : ∀ t, a + δ ≤ t → t ≤ b - δ → φ t = 1 := by
    intro t h1 h2
    simp only [hφ]
    have hA : 1 ≤ (t - a) / δ := by rw [le_div_iff₀ hδ]; linarith
    have hB : 1 ≤ (b - t) / δ := by rw [le_div_iff₀ hδ]; linarith
    rw [min_eq_left (le_min hA hB), max_eq_right zero_le_one]
  have hψc : Continuous fun x => φ (Int.fract x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : Int.fract x = 0
    · have hxn : x = (⌊x⌋ : ℝ) := by
        have := Int.self_sub_floor x
        linarith
      have hev : (fun y => φ (Int.fract y)) =ᶠ[𝓝 x] fun _ => 0 := by
        have hmem : Set.Ioo (x - (1 - b)) (x + a) ∈ 𝓝 x := Ioo_mem_nhds (by linarith) (by linarith)
        filter_upwards [hmem] with y hy
        rcases le_or_gt x y with hxy | hxy
        · have hf : Int.fract y = y - x := by
            rw [Int.fract_eq_iff]
            refine ⟨by linarith, by linarith [hy.2], ⌊x⌋, ?_⟩
            linarith
          change φ (Int.fract y) = 0
          rw [hf]
          exact hφ0 _ (Or.inl (by linarith [hy.2]))
        · have hf : Int.fract y = y - (x - 1) := by
            rw [Int.fract_eq_iff]
            refine ⟨by linarith [hy.1], by linarith, ⌊x⌋ - 1, ?_⟩
            push_cast
            linarith
          change φ (Int.fract y) = 0
          rw [hf]
          exact hφ0 _ (Or.inr (by linarith [hy.1]))
      exact continuousAt_const.congr hev.symm
    · have hlt : (⌊x⌋ : ℝ) < x := by
        rcases (Int.floor_le x).lt_or_eq with h | h
        · exact h
        · exfalso
          apply hx
          have := Int.self_sub_floor x
          linarith
      have hmem : Set.Ico (⌊x⌋ : ℝ) (⌊x⌋ + 1) ∈ 𝓝 x := Ico_mem_nhds hlt (Int.lt_floor_add_one x)
      exact hφc.continuousAt.comp ((continuousOn_fract ⌊x⌋).continuousAt hmem)
  refine ⟨fun x => φ (Int.fract x), hψc, ?_, ?_, ?_⟩
  · intro x
    change φ (Int.fract (x + 1)) = φ (Int.fract x)
    rw [Int.fract_add_one]
  · intro x
    by_cases hc : a ≤ Int.fract x ∧ Int.fract x < b
    · rw [ite_eq_left hc]
      exact (hφ1 _).2
    · rw [ite_eq_right hc]
      apply le_of_eq
      rcases not_and_or.1 hc with h | h
      · exact hφ0 _ (Or.inl (le_of_lt (not_le.1 h)))
      · exact hφ0 _ (Or.inr (not_lt.1 h))
  · have h1 : ∫ x in (a + δ)..(b - δ), φ (Int.fract x) = b - a - 2 * δ := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
      · simp
        ring
      · intro x hx
        rw [Set.uIcc_of_le (by linarith)] at hx
        have hf : Int.fract x = x := Int.fract_eq_self.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
        change φ (Int.fract x) = 1
        rw [hf]
        exact hφ2 x hx.1 hx.2
    rw [← h1]
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
    · exact Filter.Eventually.of_forall fun x => (hφ1 _).1
    · exact hψc.intervalIntegrable _ _

open Classical in
/-- Lower frequency bound for an arc strictly inside `(0, 1)`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s1a_lower_interior (y : ℕ → ℝ)
    (hy : ∀ h : ℤ, h ≠ 0 →
      Tendsto (exists_isNormalInBase_not_isNormalInBase_weylAvg y h) atTop (𝓝 0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, b - a - η ≤
      (((Finset.range N).filter fun n => a ≤ Int.fract (y n) ∧ Int.fract (y n) < b).card : ℝ)
        / N := by
  set δ : ℝ := min (η / 4) ((b - a) / 2) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by linarith)
  have hδ1 : 2 * δ ≤ b - a := by
    have := min_le_right (η / 4) ((b - a) / 2)
    linarith
  have hδ2 : δ ≤ η / 4 := min_le_left _ _
  obtain ⟨ψ, hψc, hψp, hψle, hψint⟩ :=
    exists_isNormalInBase_not_isNormalInBase_s1a_trapezoid ha hab hb hδpos hδ1
  have hlim := exists_isNormalInBase_not_isNormalInBase_s1a_cont y hy ψ hψc hψp
  have hev : ∀ᶠ N : ℕ in atTop, (∫ x in (0 : ℝ)..1, ψ x) - η / 2 <
      (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, ψ (y n) :=
    hlim.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcard : (((Finset.range N).filter fun n => a ≤ Int.fract (y n) ∧
      Int.fract (y n) < b).card : ℝ) =
        ∑ n ∈ Finset.range N, if a ≤ Int.fract (y n) ∧ Int.fract (y n) < b then (1 : ℝ) else 0 := by
    rw [Finset.card_filter]
    push_cast
    rfl
  have hsum : ∑ n ∈ Finset.range N, ψ (y n) ≤
      (((Finset.range N).filter fun n => a ≤ Int.fract (y n) ∧ Int.fract (y n) < b).card : ℝ) := by
    rw [hcard]
    exact Finset.sum_le_sum fun n _ => hψle (y n)
  have hle : (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, ψ (y n) ≤
      (((Finset.range N).filter fun n => a ≤ Int.fract (y n) ∧ Int.fract (y n) < b).card : ℝ)
        / N := by
    rw [one_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hsum hNpos.le
  linarith

open Classical in
/-- Lower frequency bound for an arbitrary arc `[a, b) ⊆ [0, 1)`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s1a_lower (y : ℕ → ℝ)
    (hy : ∀ h : ℤ, h ≠ 0 →
      Tendsto (exists_isNormalInBase_not_isNormalInBase_weylAvg y h) atTop (𝓝 0))
    {a b : ℝ} (ha : 0 ≤ a) (_hab : a ≤ b) (hb : b ≤ 1) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, b - a - η ≤
      (((Finset.range N).filter fun n => a ≤ Int.fract (y n) ∧ Int.fract (y n) < b).card : ℝ)
        / N := by
  by_cases hsmall : b - a ≤ η
  · refine Filter.Eventually.of_forall fun N => ?_
    have : (0 : ℝ) ≤ (((Finset.range N).filter fun n => a ≤ Int.fract (y n) ∧
        Int.fract (y n) < b).card : ℝ) / N := by positivity
    linarith
  · push Not at hsmall
    have h := exists_isNormalInBase_not_isNormalInBase_s1a_lower_interior y hy
      (a := a + η / 3) (b := b - η / 3) (by linarith) (by linarith) (by linarith)
      (η := η / 3) (by positivity)
    filter_upwards [h] with N hN
    have hmono : (((Finset.range N).filter fun n => a + η / 3 ≤ Int.fract (y n) ∧
        Int.fract (y n) < b - η / 3).card : ℝ) / N ≤
        (((Finset.range N).filter fun n => a ≤ Int.fract (y n) ∧ Int.fract (y n) < b).card : ℝ)
          / N := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      refine Nat.cast_le.2 (Finset.card_le_card ?_)
      intro n hn
      simp only [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, by linarith [hn.2.1], by linarith [hn.2.2]⟩
    linarith

open Classical in
/-- Step 1a of the proof of `exists_isNormalInBase_not_isNormalInBase`: Weyl's criterion
for arcs.  If all the Weyl averages `(1/N) ∑_{n<N} e(h y_n)`, `h ≠ 0`, tend to `0`, then the
fractional parts of `y_n` equidistribute on every arc `[a, b) ⊆ [0, 1]`. -/
private theorem exists_isNormalInBase_not_isNormalInBase_weyl_arcs (y : ℕ → ℝ)
    (hy : ∀ h : ℤ, h ≠ 0 →
      Tendsto (exists_isNormalInBase_not_isNormalInBase_weylAvg y h) atTop (𝓝 0))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun n => a ≤ Int.fract (y n) ∧ Int.fract (y n) < b).card : ℝ) / N)
      atTop (𝓝 (b - a)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hη : 0 < ε / 3 := by positivity
  have h1 := exists_isNormalInBase_not_isNormalInBase_s1a_lower y hy ha hab hb hη
  have h2 := exists_isNormalInBase_not_isNormalInBase_s1a_lower y hy (a := 0) (b := a)
    le_rfl ha (hab.trans hb) hη
  have h3 := exists_isNormalInBase_not_isNormalInBase_s1a_lower y hy (a := b) (b := 1)
    (ha.trans hab) hb le_rfl hη
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (h1.and (h2.and (h3.and (eventually_ge_atTop 1))))
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hA, hB, hC, hN1⟩ := hN0 N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpart : (((Finset.range N).filter fun n => 0 ≤ Int.fract (y n) ∧
        Int.fract (y n) < a).card : ℝ) / N +
      (((Finset.range N).filter fun n => a ≤ Int.fract (y n) ∧ Int.fract (y n) < b).card : ℝ) / N +
      (((Finset.range N).filter fun n => b ≤ Int.fract (y n) ∧ Int.fract (y n) < 1).card : ℝ) / N
        = 1 := by
    rw [← add_div, ← add_div, div_eq_one_iff_eq hNpos.ne']
    simp only [Finset.card_filter]
    push_cast
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have : ∀ n ∈ Finset.range N, ((if 0 ≤ Int.fract (y n) ∧ Int.fract (y n) < a then (1 : ℝ) else 0)
        +
        (if a ≤ Int.fract (y n) ∧ Int.fract (y n) < b then (1 : ℝ) else 0) +
        (if b ≤ Int.fract (y n) ∧ Int.fract (y n) < 1 then (1 : ℝ) else 0)) = 1 := by
      intro n _
      have h0 := Int.fract_nonneg (y n)
      have h1 := Int.fract_lt_one (y n)
      by_cases c1 : Int.fract (y n) < a
      · have c2 : ¬ (a ≤ Int.fract (y n)) := not_le.2 c1
        have c3 : ¬ (b ≤ Int.fract (y n)) := not_le.2 (lt_of_lt_of_le c1 hab)
        simp [h0, c1, c2, c3]
      · push Not at c1
        by_cases c2 : Int.fract (y n) < b
        · have c3 : ¬ (b ≤ Int.fract (y n)) := not_le.2 c2
          have c4 : ¬ (Int.fract (y n) < a) := not_lt.2 c1
          simp [h0, c1, c2, c3, c4]
        · push Not at c2
          have c4 : ¬ (Int.fract (y n) < a) := not_lt.2 (le_trans hab c2)
          have c5 : ¬ (Int.fract (y n) < b) := not_lt.2 c2
          simp [h1, c2, c4, c5]
    rw [Finset.sum_congr rfl this]
    simp
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith
/-- Single-digit identity: digit `k + j` of `α` is digit `j` of the orbit point `fract (b^k α)`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s1b_digit_shift (b : ℕ) (hb : 2 ≤ b)
    (α : ℝ) (k j : ℕ) :
    baseDigit b α (k + j) = ⌊(b : ℝ) ^ (j + 1) * Int.fract ((b : ℝ) ^ k * α)⌋₊ % b := by
  unfold baseDigit
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hx0 : 0 ≤ Int.fract α := Int.fract_nonneg α
  have h1 : Int.fract ((b : ℝ) ^ k * α) = Int.fract ((b : ℝ) ^ k * Int.fract α) := by
    have e : (b : ℝ) ^ k * α = (b : ℝ) ^ k * Int.fract α + (((b : ℤ) ^ k * ⌊α⌋ : ℤ) : ℝ) := by
      push_cast
      have hα : α = (⌊α⌋ : ℝ) + Int.fract α := (Int.floor_add_fract α).symm
      conv_lhs => rw [hα]
      ring
    rw [e, Int.fract_add_intCast]
  rw [h1]
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = (b : ℝ) ^ k * Int.fract α := ⟨_, rfl⟩
  rw [← hz]
  have hz0 : 0 ≤ z := by rw [hz]; exact mul_nonneg (by positivity) hx0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊z⌋₊ := ⟨_, rfl⟩
  have hn1 : (n : ℝ) ≤ z := by rw [hn]; exact Nat.floor_le hz0
  have hn2 : z < n + 1 := by rw [hn]; exact Nat.lt_floor_add_one z
  have hfr : Int.fract z = z - n := by
    rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, n, by push_cast; ring⟩
  rw [hfr]
  have e2 : (b : ℝ) ^ (k + j + 1) * Int.fract α
      = (b : ℝ) ^ (j + 1) * (z - n) + ((b ^ (j + 1) * n : ℕ) : ℝ) := by
    push_cast
    rw [hz]
    ring
  have hw : 0 ≤ (b : ℝ) ^ (j + 1) * (z - n) := mul_nonneg (by positivity) (by linarith)
  rw [e2, Nat.floor_add_natCast hw]
  have e3 : b ^ (j + 1) * n = b * (b ^ j * n) := by ring
  rw [e3, Nat.add_mul_mod_self_left]

/-- `⌊b^(m+1) y⌋₊ / b = ⌊b^m y⌋₊`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s1b_floor_succ_div (b : ℕ) (hb : 2 ≤ b)
    (y : ℝ) (m : ℕ) :
    ⌊(b : ℝ) ^ (m + 1) * y⌋₊ / b = ⌊(b : ℝ) ^ m * y⌋₊ := by
  have hb0 : (b : ℝ) ≠ 0 := by
    have : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    exact this.ne'
  rw [← Nat.floor_div_natCast]
  congr 1
  rw [pow_succ]
  field_simp

/-- Window lemma: the word `U` occurs at position `k` iff `⌊b^|U| fract (b^k α)⌋₊` is the value of
`U` read as a base-`b` numeral. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s1b_window (b : ℕ) (hb : 2 ≤ b) (α : ℝ)
    (U : List ℕ) (hU : ∀ d ∈ U, d < b) (k : ℕ) :
    DigitOccursAt b α U k ↔
      ⌊(b : ℝ) ^ U.length * Int.fract ((b : ℝ) ^ k * α)⌋₊ = U.foldl (fun acc d => acc * b + d) 0 :=
          by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Int.fract ((b : ℝ) ^ k * α) := ⟨_, rfl⟩
  rw [← hy]
  have hy0 : 0 ≤ y := by rw [hy]; exact Int.fract_nonneg _
  have hy1 : y < 1 := by rw [hy]; exact Int.fract_lt_one _
  have hdig : ∀ j, baseDigit b α (k + j) = ⌊(b : ℝ) ^ (j + 1) * y⌋₊ % b := by
    intro j; rw [hy]; exact exists_isNormalInBase_not_isNormalInBase_s1b_digit_shift b hb α k j
  clear hy
  revert hU
  induction U using List.reverseRecOn with
  | nil =>
    intro _
    simp only [List.length_nil, pow_zero, one_mul, List.foldl_nil]
    constructor
    · intro _; exact Nat.floor_eq_zero.mpr hy1
    · intro _ j hj; simp at hj
  | append_singleton U d ih =>
    intro hU
    have hd : d < b := hU d (by simp)
    have hU' : ∀ e ∈ U, e < b := fun e he => hU e (by simp [he])
    have ih' : DigitOccursAt b α U k ↔
        ⌊(b : ℝ) ^ U.length * y⌋₊ = U.foldl (fun acc e => acc * b + e) 0 := ih hU'
    have hlen : (U ++ [d]).length = U.length + 1 := by simp
    have hfold : (U ++ [d]).foldl (fun acc e => acc * b + e) 0
        = U.foldl (fun acc e => acc * b + e) 0 * b + d := by
      simp [List.foldl_append]
    rw [hlen, hfold]
    have hocc : DigitOccursAt b α (U ++ [d]) k ↔
        DigitOccursAt b α U k ∧ baseDigit b α (k + U.length) = d := by
      unfold DigitOccursAt
      constructor
      · intro h
        refine ⟨fun j hj => ?_, ?_⟩
        · have := h j (by simp; omega)
          simpa [List.getElem_append_left hj] using this
        · have := h U.length (by simp)
          simpa using this
      · rintro ⟨h1, h2⟩ j hj
        by_cases hjU : j < U.length
        · rw [List.getElem_append_left hjU]
          exact h1 j hjU
        · have hj' : j = U.length := by simp at hj; omega
          subst hj'
          simpa using h2
    rw [hocc, ih', hdig U.length]
    have hdiv := exists_isNormalInBase_not_isNormalInBase_s1b_floor_succ_div b hb y U.length
    generalize ⌊(b : ℝ) ^ (U.length + 1) * y⌋₊ = F1 at hdiv ⊢
    rw [← hdiv]
    generalize U.foldl (fun acc e => acc * b + e) 0 = V
    have hb0 : 0 < b := by omega
    constructor
    · rintro ⟨h1, h2⟩
      have := (Nat.div_mod_unique hb0).mp ⟨h1, h2⟩
      rw [← this.1]; ring
    · intro h
      exact (Nat.div_mod_unique hb0).mpr ⟨by rw [h]; ring, hd⟩

/-- The value of a binary word is below `2 ^ length`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s1b_foldl_lt (U : List ℕ)
    (hU : ∀ d ∈ U, d < 2) :
    U.foldl (fun acc d => acc * 2 + d) 0 < 2 ^ U.length := by
  induction U using List.reverseRecOn with
  | nil => simp
  | append_singleton U d ih =>
    have hd : d < 2 := hU d (by simp)
    have hU' : ∀ e ∈ U, e < 2 := fun e he => hU e (by simp [he])
    have h1 := ih hU'
    have hfold : (U ++ [d]).foldl (fun acc e => acc * 2 + e) 0
        = U.foldl (fun acc e => acc * 2 + e) 0 * 2 + d := by
      simp [List.foldl_append]
    have hlen : (U ++ [d]).length = U.length + 1 := by simp
    rw [hfold, hlen, pow_succ]
    generalize U.foldl (fun acc e => acc * 2 + e) 0 = V at h1 ⊢
    generalize 2 ^ U.length = P at h1 ⊢
    omega

open Classical in
/-- Step 1b of the proof of `exists_isNormalInBase_not_isNormalInBase`: if the fractional
parts of `2^n x` equidistribute on every arc `[a, b) ⊆ [0, 1]`, then `x` is normal in base `2`
(the digit window `U` occurs at `n` iff `{2^n x}` lies in the dyadic arc of the word `U`). -/
private theorem exists_isNormalInBase_not_isNormalInBase_arcs_normal (x : ℝ)
    (hx : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n =>
          a ≤ Int.fract ((2 : ℝ) ^ n * x) ∧ Int.fract ((2 : ℝ) ^ n * x) < b).card : ℝ) / N)
        atTop (𝓝 (b - a))) :
    IsNormalInBase 2 x := by
  intro U hU
  have hvlt := exists_isNormalInBase_not_isNormalInBase_s1b_foldl_lt U hU
  have hwin : ∀ n, DigitOccursAt 2 x U n ↔
      ⌊(2 : ℝ) ^ U.length * Int.fract ((2 : ℝ) ^ n * x)⌋₊
        = U.foldl (fun acc d => acc * 2 + d) 0 := by
    intro n
    have := exists_isNormalInBase_not_isNormalInBase_s1b_window 2 le_rfl x U hU n
    simpa using this
  obtain ⟨v, hv⟩ : ∃ v, v = U.foldl (fun acc d => acc * 2 + d) 0 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = U.length := ⟨_, rfl⟩
  rw [← hv, ← hL] at hvlt
  simp only [← hv, ← hL] at hwin
  rw [← hL]
  have hpos : (0 : ℝ) < 2 ^ L := by positivity
  have hv1 : v + 1 ≤ 2 ^ L := hvlt
  have hvR : (v : ℝ) + 1 ≤ 2 ^ L := by exact_mod_cast hv1
  have hab : (v : ℝ) / 2 ^ L ≤ ((v : ℝ) + 1) / 2 ^ L := by
    rw [← sub_nonneg]
    have : ((v : ℝ) + 1) / 2 ^ L - (v : ℝ) / 2 ^ L = 1 / 2 ^ L := by ring
    rw [this]; positivity
  have h := hx ((v : ℝ) / 2 ^ L) (((v : ℝ) + 1) / 2 ^ L) (by positivity) hab
    ((div_le_one hpos).mpr hvR)
  have hlim : (((v : ℝ) + 1) / 2 ^ L - (v : ℝ) / 2 ^ L) = ((2 : ℕ) : ℝ)⁻¹ ^ L := by
    have h1 : (((v : ℝ) + 1) / 2 ^ L - (v : ℝ) / 2 ^ L) = 1 / 2 ^ L := by ring
    rw [h1]
    push_cast
    rw [inv_pow, one_div]
  have key : ∀ y : ℝ, 0 ≤ y →
      (⌊(2 : ℝ) ^ L * y⌋₊ = v ↔ (v : ℝ) / 2 ^ L ≤ y ∧ y < ((v : ℝ) + 1) / 2 ^ L) := by
    intro y hy
    rw [Nat.floor_eq_iff (by positivity), div_le_iff₀ hpos, lt_div_iff₀ hpos]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith [mul_comm y ((2 : ℝ) ^ L)], by linarith [mul_comm y ((2 : ℝ) ^ L)]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith [mul_comm y ((2 : ℝ) ^ L)], by linarith [mul_comm y ((2 : ℝ) ^ L)]⟩
  rw [← hlim]
  refine Tendsto.congr (fun N => ?_) h
  unfold digitOccurrenceFreq
  apply congrArg (fun s : Finset ℕ => ((s.card : ℕ) : ℝ) / (N : ℝ))
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  rw [hwin n, key _ (Int.fract_nonneg _)]

private lemma exists_isNormalInBase_not_isNormalInBase_s234_pow_mul_inv_pow (i j : ℕ) (hj : j ≤ i) :
    (3 : ℝ) ^ (i + 1) * (3 : ℝ)⁻¹ ^ (j + 1) = 3 ^ (i - j) := by
  have h : i + 1 = (i - j) + (j + 1) := by omega
  rw [h, pow_add, mul_assoc, inv_pow, mul_inv_cancel₀ (by positivity), mul_one]

private lemma exists_isNormalInBase_not_isNormalInBase_s234_pow_mul_inv_pow_tail (i j : ℕ) :
    (3 : ℝ) ^ (i + 1) * (3 : ℝ)⁻¹ ^ (j + (i + 1) + 1) = (3 : ℝ)⁻¹ ^ (j + 1) := by
  have h : j + (i + 1) + 1 = (j + 1) + (i + 1) := by omega
  have h3 : (3 : ℝ) ^ (i + 1) * (3 : ℝ)⁻¹ ^ (i + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
  calc (3 : ℝ) ^ (i + 1) * (3 : ℝ)⁻¹ ^ (j + (i + 1) + 1)
      = ((3 : ℝ) ^ (i + 1) * (3 : ℝ)⁻¹ ^ (i + 1)) * (3 : ℝ)⁻¹ ^ (j + 1) := by
        rw [h, pow_add]; ring
    _ = (3 : ℝ)⁻¹ ^ (j + 1) := by rw [h3, one_mul]

private lemma exists_isNormalInBase_not_isNormalInBase_s234_summable (v : ℕ → Bool) :
    Summable (fun j : ℕ => if v j then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) else 0) := by
  have hg : Summable (fun j : ℕ => (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1)) := by
    have := (summable_geometric_of_lt_one (r := (3 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_left
      (2 * 3⁻¹)
    refine this.congr fun j => ?_
    ring
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hg
  · split_ifs <;> positivity
  · split_ifs
    · exact le_rfl
    · positivity

private lemma exists_isNormalInBase_not_isNormalInBase_s234_geom_lt (v : ℕ → Bool)
    (hv : ∃ j, v j = false) :
    0 ≤ ∑' j : ℕ, (if v j then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) else 0) ∧
      ∑' j : ℕ, (if v j then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) else 0) < 1 := by
  have hgeo : ∑' j : ℕ, (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) = 1 := by
    have h1 : ∑' j : ℕ, (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) = 2 * 3⁻¹ * ∑' j : ℕ, (3 : ℝ)⁻¹ ^ j := by
      rw [← tsum_mul_left]
      refine tsum_congr fun j => ?_
      ring
    rw [h1, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hg : Summable (fun j : ℕ => (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1)) := by
    have := (summable_geometric_of_lt_one (r := (3 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_left
      (2 * 3⁻¹)
    refine this.congr fun j => ?_
    ring
  refine ⟨tsum_nonneg fun j => by split_ifs <;> positivity, ?_⟩
  obtain ⟨j0, hj0⟩ := hv
  rw [← hgeo]
  refine Summable.tsum_lt_tsum_of_nonneg (i := j0) (fun j => ?_) (fun j => ?_) ?_ hg
  · split_ifs <;> positivity
  · split_ifs
    · exact le_rfl
    · positivity
  · simp only [hj0, Bool.false_eq_true, ite_false]
    positivity

private lemma exists_isNormalInBase_not_isNormalInBase_s234_nat_mod (w : CantorSeq) (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), if w j then 2 * 3 ^ (i - j) else 0) % 3
      = if w i then 2 else 0 := by
  rw [Finset.sum_range_succ]
  have hdvd : 3 ∣ ∑ j ∈ Finset.range i, if w j then 2 * 3 ^ (i - j) else 0 := by
    refine Finset.dvd_sum fun j hj => ?_
    have hji : j < i := Finset.mem_range.1 hj
    split_ifs
    · exact Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) 2
    · exact dvd_zero 3
  obtain ⟨K, hK⟩ := hdvd
  rw [hK]
  simp only [Nat.sub_self, pow_zero, mul_one]
  split_ifs <;> omega

private lemma exists_isNormalInBase_not_isNormalInBase_s234_baseDigit (w : CantorSeq)
    (hw : ¬ ∀ᶠ j in atTop, w j = true) (i : ℕ) :
    baseDigit 3 (exists_isNormalInBase_not_isNormalInBase_cantorReal w) i
      = if w i then 2 else 0 := by
  have hfalse : ∀ n0 : ℕ, ∃ j, w (j + n0) = false := by
    intro n0
    obtain ⟨j, hj, hwj⟩ := Filter.frequently_atTop.1 (Filter.not_eventually.1 hw) n0
    refine ⟨j - n0, ?_⟩
    rw [Nat.sub_add_cancel hj]
    simpa using hwj
  have hX := exists_isNormalInBase_not_isNormalInBase_s234_geom_lt w (hfalse 0 |>.imp fun j hj =>
    by simpa using hj)
  set X := exists_isNormalInBase_not_isNormalInBase_cantorReal w with hXdef
  have hfract : Int.fract X = X := Int.fract_eq_self.2 hX
  have hsumm := exists_isNormalInBase_not_isNormalInBase_s234_summable w
  have hsplit := hsumm.sum_add_tsum_nat_add (i + 1)
  have ht := exists_isNormalInBase_not_isNormalInBase_s234_geom_lt (fun j => w (j + (i + 1)))
    (hfalse (i + 1))
  -- head part
  have hhead : (3 : ℝ) ^ (i + 1) * ∑ j ∈ Finset.range (i + 1),
      (if w j then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) else 0)
      = ((∑ j ∈ Finset.range (i + 1), if w j then 2 * 3 ^ (i - j) else 0 : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    split_ifs
    · rw [← mul_assoc, mul_comm ((3 : ℝ) ^ (i + 1)) 2, mul_assoc,
        exists_isNormalInBase_not_isNormalInBase_s234_pow_mul_inv_pow i j hji]
    · simp
  -- tail part
  have htail : (3 : ℝ) ^ (i + 1) * ∑' j : ℕ,
      (if w (j + (i + 1)) then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + (i + 1) + 1) else 0)
      = ∑' j : ℕ, (if w (j + (i + 1)) then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) else 0) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    split_ifs
    · rw [← mul_assoc, mul_comm ((3 : ℝ) ^ (i + 1)) 2, mul_assoc,
        exists_isNormalInBase_not_isNormalInBase_s234_pow_mul_inv_pow_tail i j]
    · simp
  set N : ℕ := ∑ j ∈ Finset.range (i + 1), if w j then 2 * 3 ^ (i - j) else 0 with hN
  set t : ℝ := ∑' j : ℕ, (if w (j + (i + 1)) then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) else 0) with ht_def
  have hXeq : (3 : ℝ) ^ (i + 1) * X = (N : ℝ) + t := by
    have : X = (∑ j ∈ Finset.range (i + 1),
        (if w j then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) else 0)) +
        ∑' j : ℕ, (if w (j + (i + 1)) then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + (i + 1) + 1) else 0) :=
      hsplit.symm
    rw [this, mul_add, hhead, htail]
  have hfloor : ⌊(3 : ℝ) ^ (i + 1) * X⌋₊ = N := by
    rw [Nat.floor_eq_iff (by rw [hXeq]; exact add_nonneg (Nat.cast_nonneg _) ht.1), hXeq]
    exact ⟨le_add_of_nonneg_right ht.1, by linarith [ht.2]⟩
  unfold baseDigit
  rw [hfract]
  simp only [Nat.cast_ofNat]
  rw [hfloor, hN]
  exact exists_isNormalInBase_not_isNormalInBase_s234_nat_mod w i

open Classical in
private lemma exists_isNormalInBase_not_isNormalInBase_s234_freq_zero (w : CantorSeq)
    (hw : ¬ ∀ᶠ j in atTop, w j = true) (N : ℕ) :
    digitOccurrenceFreq 3 (exists_isNormalInBase_not_isNormalInBase_cantorReal w) [1] N = 0 := by
  unfold digitOccurrenceFreq
  have : (Finset.range N).filter (fun k => DigitOccursAt 3
      (exists_isNormalInBase_not_isNormalInBase_cantorReal w) [1] k) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun k _ hk => ?_
    have h0 := hk 0 (by simp)
    rw [Nat.add_zero, exists_isNormalInBase_not_isNormalInBase_s234_baseDigit w hw k] at h0
    split_ifs at h0 <;> simp at h0
  rw [this]
  simp

/-- Step 2 of the proof of `exists_isNormalInBase_not_isNormalInBase`: a Cantor point
`∑ 2 w_j 3^{-(j+1)}` whose digit sequence is not eventually `true` has ternary digits only in
`{0, 2}` (so no digit `1`), hence is not normal in base `3`. -/
private theorem exists_isNormalInBase_not_isNormalInBase_cantor_not_normal3 (w : CantorSeq)
    (hw : ¬ ∀ᶠ j in atTop, w j = true) :
    ¬ IsNormalInBase 3 (exists_isNormalInBase_not_isNormalInBase_cantorReal w) := by
  intro hN
  have h1 := hN [1] (by simp)
  have h2 : Tendsto (digitOccurrenceFreq 3 (exists_isNormalInBase_not_isNormalInBase_cantorReal w)
      [1]) atTop (𝓝 0) := by
    have : digitOccurrenceFreq 3 (exists_isNormalInBase_not_isNormalInBase_cantorReal w) [1]
        = fun _ => 0 := funext (exists_isNormalInBase_not_isNormalInBase_s234_freq_zero w hw)
    rw [this]
    exact tendsto_const_nhds
  have := tendsto_nhds_unique h1 h2
  norm_num at this

private lemma exists_isNormalInBase_not_isNormalInBase_s234_pi_true (m n : ℕ) :
    uniformMeasure (Set.pi (↑(Finset.Ico m (m + n)) : Set ℕ) (fun _ => ({true} : Set Bool)))
      = (2 : ENNReal)⁻¹ ^ n := by
  unfold uniformMeasure bernoulliMeasure
  rw [Measure.infinitePi_pi (fun (_ : ℕ) =>
      ProbabilityTheory.bernoulliMeasure true false
        ⟨((1 / 2 : NNReal) : ℝ), (1 / 2 : NNReal).2, NNReal.coe_le_one.mpr (by norm_num)⟩)
      (fun i _ => measurableSet_singleton true)]
  have hmass : ProbabilityTheory.bernoulliMeasure true false
      (⟨((1 / 2 : NNReal) : ℝ), (1 / 2 : NNReal).2, NNReal.coe_le_one.mpr (by norm_num)⟩ :
        unitInterval) {true} = (2 : ENNReal)⁻¹ := by
    have hcoe : unitInterval.toNNReal
        ⟨((1 / 2 : NNReal) : ℝ), (1 / 2 : NNReal).2, NNReal.coe_le_one.mpr (by norm_num)⟩
        = 1 / 2 := rfl
    rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _)
      rfl (by simp), hcoe]
    have : ((1 / 2 : NNReal) : ENNReal) = (1 : ENNReal) / (2 : ENNReal) :=
      ENNReal.coe_div (by norm_num)
    rw [this, div_eq_mul_inv, one_mul]
  rw [Finset.prod_congr rfl (fun i _ => hmass), Finset.prod_const, Nat.card_Ico,
    Nat.add_sub_cancel_left]

/-- Step 3 of the proof of `exists_isNormalInBase_not_isNormalInBase`: the set of
sequences that are eventually `true` is null for the uniform measure. -/
private theorem exists_isNormalInBase_not_isNormalInBase_eventually_true_null :
    uniformMeasure {w : CantorSeq | ∀ᶠ j in atTop, w j = true} = 0 := by
  have hset : {w : CantorSeq | ∀ᶠ j in atTop, w j = true}
      = ⋃ m : ℕ, {w : CantorSeq | ∀ j, m ≤ j → w j = true} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Filter.eventually_atTop]
  rw [hset]
  refine measure_iUnion_null fun m => ?_
  have hle : ∀ n : ℕ, uniformMeasure {w : CantorSeq | ∀ j, m ≤ j → w j = true}
      ≤ (2 : ENNReal)⁻¹ ^ n := by
    intro n
    rw [← exists_isNormalInBase_not_isNormalInBase_s234_pi_true m n]
    refine measure_mono fun w hw i hi => ?_
    have hi' : i ∈ Finset.Ico m (m + n) := hi
    exact hw i (Finset.mem_Ico.1 hi').1
  refine le_antisymm ?_ zero_le
  exact ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
    (Filter.Eventually.of_forall hle)

private lemma exists_isNormalInBase_not_isNormalInBase_s234_cos_sq_sum (θ : ℝ) :
    ∑ s ∈ Finset.range 3, Real.cos (θ + 2 * Real.pi * (s : ℝ) / 3) ^ 2 = 3 / 2 := by
  have hc : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have hs : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e1 : θ + 2 * Real.pi * ((1 : ℕ) : ℝ) / 3 = (θ + Real.pi) - Real.pi / 3 := by
    push_cast; ring
  have e2 : θ + 2 * Real.pi * ((2 : ℕ) : ℝ) / 3 = (θ + Real.pi) + Real.pi / 3 := by
    push_cast; ring
  have h0 : Real.cos (θ + 2 * Real.pi * ((0 : ℕ) : ℝ) / 3) = Real.cos θ := by simp
  have h1 : Real.cos (θ + 2 * Real.pi * ((1 : ℕ) : ℝ) / 3)
      = -(Real.cos θ / 2) - Real.sin θ * (Real.sqrt 3 / 2) := by
    rw [e1, Real.cos_sub, Real.cos_add_pi, Real.sin_add_pi, hc, hs]; ring
  have h2 : Real.cos (θ + 2 * Real.pi * ((2 : ℕ) : ℝ) / 3)
      = -(Real.cos θ / 2) + Real.sin θ * (Real.sqrt 3 / 2) := by
    rw [e2, Real.cos_add, Real.cos_add_pi, Real.sin_add_pi, hc, hs]; ring
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2]
  linear_combination (3 / 2) * Real.sin_sq_add_cos_sq θ + (Real.sin θ ^ 2 / 2) * h3

private lemma exists_isNormalInBase_not_isNormalInBase_s234_cos_period (j k : ℕ) (hj : j ≤ k)
    (r s : ℕ) :
    Real.cos (2 * Real.pi * ((r + 3 ^ k * s : ℕ) : ℝ) / 3 ^ j)
      = Real.cos (2 * Real.pi * (r : ℝ) / 3 ^ j) := by
  have key : (3 : ℝ) ^ k / 3 ^ j = 3 ^ (k - j) := by
    rw [div_eq_iff (by positivity), ← pow_add]
    congr 1
    omega
  have h : 2 * Real.pi * ((r + 3 ^ k * s : ℕ) : ℝ) / 3 ^ j
      = 2 * Real.pi * (r : ℝ) / 3 ^ j + ((3 ^ (k - j) * s : ℕ) : ℝ) * (2 * Real.pi) := by
    calc 2 * Real.pi * ((r + 3 ^ k * s : ℕ) : ℝ) / 3 ^ j
        = 2 * Real.pi * (r : ℝ) / 3 ^ j + ((3 : ℝ) ^ k / 3 ^ j) * (s : ℝ) * (2 * Real.pi) := by
          push_cast; ring
      _ = 2 * Real.pi * (r : ℝ) / 3 ^ j + ((3 ^ (k - j) * s : ℕ) : ℝ) * (2 * Real.pi) := by
          rw [key]; push_cast; ring
  rw [h, Real.cos_add_nat_mul_two_pi]

/-- Step 4 of the proof of `exists_isNormalInBase_not_isNormalInBase`: the Parseval
identity on `ℤ/3^k` for the Cantor measure,
`∑_{r mod 3^k} ∏_{j=1}^k cos²(2π r / 3^j) = (3/2)^k`. -/
private theorem exists_isNormalInBase_not_isNormalInBase_parseval (k : ℕ) :
    ∑ r ∈ Finset.range (3 ^ k), ∏ j ∈ Finset.Icc 1 k, Real.cos (2 * Real.pi * (r : ℝ) / 3 ^ j) ^ 2
      = (3 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : ∀ f : ℕ → ℝ, ∑ r ∈ Finset.range (3 ^ (k + 1)), f r
        = ∑ r ∈ Finset.range (3 ^ k), ∑ s ∈ Finset.range 3, f (r + 3 ^ k * s) := by
      intro f
      have h3 : 3 ^ (k + 1) = 3 ^ k + 3 ^ k + 3 ^ k := by ring
      rw [h3, Finset.sum_range_add, Finset.sum_range_add, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      have e1 : 3 ^ k + r = r + 3 ^ k * 1 := by ring
      have e2 : 3 ^ k + 3 ^ k + r = r + 3 ^ k * 2 := by ring
      rw [e1, e2]
      simp [Finset.sum_range_succ]
    rw [hsplit]
    have hterm : ∀ r ∈ Finset.range (3 ^ k), ∑ s ∈ Finset.range 3,
        ∏ j ∈ Finset.Icc 1 (k + 1), Real.cos (2 * Real.pi * ((r + 3 ^ k * s : ℕ) : ℝ) / 3 ^ j) ^ 2
        = (3 / 2) * ∏ j ∈ Finset.Icc 1 k, Real.cos (2 * Real.pi * (r : ℝ) / 3 ^ j) ^ 2 := by
      intro r _
      have hprod : ∀ s : ℕ, ∏ j ∈ Finset.Icc 1 (k + 1),
          Real.cos (2 * Real.pi * ((r + 3 ^ k * s : ℕ) : ℝ) / 3 ^ j) ^ 2
          = (∏ j ∈ Finset.Icc 1 k, Real.cos (2 * Real.pi * (r : ℝ) / 3 ^ j) ^ 2) *
            Real.cos (2 * Real.pi * (r : ℝ) / 3 ^ (k + 1) + 2 * Real.pi * (s : ℝ) / 3) ^ 2 := by
        intro s
        rw [Finset.prod_Icc_succ_top (by omega)]
        congr 1
        · refine Finset.prod_congr rfl fun j hj => ?_
          rw [exists_isNormalInBase_not_isNormalInBase_s234_cos_period j k (Finset.mem_Icc.1 hj).2
            r s]
        · congr 2
          push_cast
          rw [pow_succ]
          field_simp
      simp_rw [hprod]
      rw [← Finset.mul_sum,
        exists_isNormalInBase_not_isNormalInBase_s234_cos_sq_sum
          (2 * Real.pi * (r : ℝ) / 3 ^ (k + 1))]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ih]
    ring
/-- `3^k ∣ 2^(2·3^(k-1)) - 1` (lifting the exponent for the prime `3`). -/
private lemma exists_isNormalInBase_not_isNormalInBase_s5_dvd (k : ℕ) (hk : 1 ≤ k) :
    3 ^ k ∣ 2 ^ (2 * 3 ^ (k - 1)) - 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h4 : (2 : ℕ) ^ (2 * 3 ^ (k - 1)) = 4 ^ (3 ^ (k - 1)) := by
    rw [pow_mul]; norm_num
  have hpos : 4 ^ (3 ^ (k - 1)) - 1 ^ (3 ^ (k - 1)) ≠ 0 := by
    have : 1 < 4 ^ (3 ^ (k - 1)) := Nat.one_lt_pow (by positivity) (by norm_num)
    simp only [one_pow]; omega
  have hlte : padicValNat 3 (4 ^ (3 ^ (k - 1)) - 1 ^ (3 ^ (k - 1)))
      = padicValNat 3 (4 - 1) + padicValNat 3 (3 ^ (k - 1)) :=
    padicValNat.pow_sub_pow ⟨1, rfl⟩ (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have e1 : padicValNat 3 (4 - 1) = 1 := by
    norm_num [padicValNat_self]
  have e2 : padicValNat 3 (3 ^ (k - 1)) = k - 1 := padicValNat.prime_pow _
  have h1 : (4 : ℕ) ^ (3 ^ (k - 1)) - 1 = 4 ^ (3 ^ (k - 1)) - 1 ^ (3 ^ (k - 1)) := by simp
  rw [h4, h1, padicValNat_dvd_iff_le hpos, hlte, e1, e2]
  omega

/-- `2^n = 1` in `ZMod (3^k)` exactly when `2·3^(k-1) ∣ n`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s5_core (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    (2 : ZMod (3 ^ k)) ^ n = 1 ↔ 2 * 3 ^ (k - 1) ∣ n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : (2 : ZMod (3 ^ k)) ^ n = 1 ↔ 3 ^ k ∣ 2 ^ n - 1 := by
    have h := ZMod.natCast_eq_natCast_iff (2 ^ n) 1 (3 ^ k)
    push_cast at h
    rw [h, Nat.ModEq.comm, Nat.modEq_iff_dvd' Nat.one_le_two_pow]
  rw [h1]
  constructor
  · intro hdiv
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact dvd_zero _
    have hodd : ¬ Odd n := by
      rintro ⟨m, rfl⟩
      have h3 : 3 ∣ 2 ^ (2 * m + 1) - 1 := (dvd_pow_self 3 (by omega : k ≠ 0)).trans hdiv
      have h4 : 4 ^ m % 3 = 1 := by
        rw [Nat.pow_mod]; norm_num
      have h5 : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
        rw [pow_succ, pow_mul]; norm_num [mul_comm]
      rw [h5] at h3
      omega
    obtain ⟨m, rfl⟩ := Nat.not_odd_iff_even.1 hodd
    have hm : m ≠ 0 := by omega
    have h4m : 2 ^ (m + m) - 1 = 4 ^ m - 1 ^ m := by
      rw [← two_mul, pow_mul]; norm_num
    have hpos : 4 ^ m - 1 ^ m ≠ 0 := by
      have : 1 < 4 ^ m := Nat.one_lt_pow hm (by norm_num)
      simp only [one_pow]; omega
    have hlte : padicValNat 3 (4 ^ m - 1 ^ m) = padicValNat 3 (4 - 1) + padicValNat 3 m :=
      padicValNat.pow_sub_pow ⟨1, rfl⟩ (by norm_num) (by norm_num) (by norm_num) hm
    have e1 : padicValNat 3 (4 - 1) = 1 := by
      norm_num [padicValNat_self]
    rw [h4m, padicValNat_dvd_iff_le hpos, hlte, e1] at hdiv
    have h3m : 3 ^ (k - 1) ∣ m := by
      rw [padicValNat_dvd_iff_le hm]; omega
    obtain ⟨t, ht⟩ := h3m
    exact ⟨t, by rw [ht]; ring⟩
  · rintro ⟨t, rfl⟩
    have h0 := exists_isNormalInBase_not_isNormalInBase_s5_dvd k hk
    have h2 : 2 ^ (2 * 3 ^ (k - 1)) - 1 ∣ 2 ^ (2 * 3 ^ (k - 1) * t) - 1 := by
      have := Nat.sub_dvd_pow_sub_pow (2 ^ (2 * 3 ^ (k - 1))) 1 t
      simpa [pow_mul] using this
    exact h0.trans h2

/-- Step 5 of the proof of `exists_isNormalInBase_not_isNormalInBase`: `2` has order
`2 · 3^(k-1)` in `ℤ/3^k` (it is a primitive root modulo every power of `3`). -/
private theorem exists_isNormalInBase_not_isNormalInBase_order (k : ℕ) (hk : 1 ≤ k) :
    orderOf (2 : ZMod (3 ^ k)) = 2 * 3 ^ (k - 1) := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one
      ((exists_isNormalInBase_not_isNormalInBase_s5_core k hk _).2 dvd_rfl)
  · exact (exists_isNormalInBase_not_isNormalInBase_s5_core k hk _).1 (pow_orderOf_eq_one _)
private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_summable :
    Summable (fun j : ℕ => (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1)) := by
  have := (summable_geometric_of_lt_one (r := (3 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_left
    (2 * (3 : ℝ)⁻¹)
  refine this.congr fun j => ?_
  ring

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_continuous_cantorReal :
    Continuous exists_isNormalInBase_not_isNormalInBase_cantorReal := by
  unfold exists_isNormalInBase_not_isNormalInBase_cantorReal
  refine continuous_tsum (u := fun j : ℕ => (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1)) (fun j => ?_)
    exists_isNormalInBase_not_isNormalInBase_s6a6c_summable (fun j w => ?_)
  · exact (continuous_of_discreteTopology
      (f := fun b : Bool => if b then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) else 0)).comp
      (continuous_apply j)
  · split_ifs
    · rw [Real.norm_of_nonneg (by positivity)]
    · rw [norm_zero]; positivity

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_continuous_e :
    Continuous exists_isNormalInBase_not_isNormalInBase_e := by
  unfold exists_isNormalInBase_not_isNormalInBase_e
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_norm_e (y : ℝ) :
    ‖exists_isNormalInBase_not_isNormalInBase_e y‖ = 1 := by
  unfold exists_isNormalInBase_not_isNormalInBase_e
  have : (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) = ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_e_mul_conj (a b : ℝ) :
    exists_isNormalInBase_not_isNormalInBase_e a *
        (starRingEnd ℂ) (exists_isNormalInBase_not_isNormalInBase_e b)
      = exists_isNormalInBase_not_isNormalInBase_e (a - b) := by
  unfold exists_isNormalInBase_not_isNormalInBase_e
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_integrable_e
    (g : CantorSeq → ℝ) (hg : Continuous g) :
    Integrable (fun w : CantorSeq => exists_isNormalInBase_not_isNormalInBase_e (g w))
      uniformMeasure := by
  have hc : Continuous (fun w : CantorSeq => exists_isNormalInBase_not_isNormalInBase_e (g w)) :=
    exists_isNormalInBase_not_isNormalInBase_s6a6c_continuous_e.comp hg
  refine (integrable_const (1 : ℝ)).mono' hc.measurable.aestronglyMeasurable
    (ae_of_all _ fun w => ?_)
  rw [exists_isNormalInBase_not_isNormalInBase_s6a6c_norm_e]

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_pointwise (h : ℤ) (N : ℕ)
    (w : CantorSeq) :
    ((‖(N : ℂ) * exists_isNormalInBase_not_isNormalInBase_weylAvg
        (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖ ^ 2
        : ℝ) : ℂ)
      = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          exists_isNormalInBase_not_isNormalInBase_e
            (((h * (2 ^ n - 2 ^ m) : ℤ) : ℝ) *
              exists_isNormalInBase_not_isNormalInBase_cantorReal w) := by
  have hS : (N : ℂ) * exists_isNormalInBase_not_isNormalInBase_weylAvg
        (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N
      = ∑ n ∈ Finset.range N, exists_isNormalInBase_not_isNormalInBase_e
          ((h : ℝ) * ((2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w)) := by
    unfold exists_isNormalInBase_not_isNormalInBase_weylAvg
    by_cases hN : N = 0
    · subst hN; simp
    · have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
      rw [← mul_assoc, mul_one_div_cancel this, one_mul]
  have key : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := fun z => by
    rw [Complex.mul_conj']
    push_cast
    rfl
  rw [hS, key, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [exists_isNormalInBase_not_isNormalInBase_s6a6c_e_mul_conj]
  congr 1
  push_cast
  ring

/-- The finite truncation `∑_{j<m} 2 w_j 3^{-(j+1)}` of the Cantor real. -/
private noncomputable def exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc (m : ℕ)
    (w : CantorSeq) : ℝ :=
  ∑ j ∈ Finset.range m, if w j then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) else 0

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_continuous_trunc (m : ℕ) :
    Continuous (exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m) := by
  unfold exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc
  refine continuous_finsetSum _ fun j _ => ?_
  exact (continuous_of_discreteTopology
      (f := fun b : Bool => if b then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) else 0)).comp
      (continuous_apply j)

/-- The truncation approximates the Cantor real to within `3^{-m}`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc_close (m : ℕ) (w : CantorSeq) :
    0 ≤ exists_isNormalInBase_not_isNormalInBase_cantorReal w
        - exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w ∧
      exists_isNormalInBase_not_isNormalInBase_cantorReal w
        - exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w ≤ (3 : ℝ)⁻¹ ^ m := by
  set f : ℕ → ℝ := fun j => if w j then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) else 0 with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => by
    simp only [hf]; split_ifs <;> positivity
  have hfle : ∀ j, f j ≤ (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) := fun j => by
    simp only [hf]; split_ifs <;> first | exact le_rfl | positivity
  have hsum : Summable f :=
    Summable.of_nonneg_of_le hf0 hfle exists_isNormalInBase_not_isNormalInBase_s6a6c_summable
  have hsum' : Summable (fun i => f (i + m)) := (summable_nat_add_iff m).2 hsum
  have hsplit : exists_isNormalInBase_not_isNormalInBase_cantorReal w
      = exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w + ∑' i, f (i + m) := by
    unfold exists_isNormalInBase_not_isNormalInBase_cantorReal
      exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc
    exact hsum'.sum_add_tsum_nat_add'.symm
  have hgeom : ∑' i : ℕ, (2 : ℝ) * (3 : ℝ)⁻¹ ^ (i + m + 1) = (3 : ℝ)⁻¹ ^ m := by
    have h1 : ∀ i : ℕ, (2 : ℝ) * (3 : ℝ)⁻¹ ^ (i + m + 1)
        = (2 * (3 : ℝ)⁻¹ ^ (m + 1)) * (3 : ℝ)⁻¹ ^ i := fun i => by ring
    simp_rw [h1]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
    ring
  have hsum2 : Summable (fun i : ℕ => (2 : ℝ) * (3 : ℝ)⁻¹ ^ (i + m + 1)) := by
    have := (summable_nat_add_iff m).2
      exists_isNormalInBase_not_isNormalInBase_s6a6c_summable
    exact this.congr fun i => by ring_nf
  rw [hsplit]
  refine ⟨?_, ?_⟩
  · simp only [add_sub_cancel_left]
    exact tsum_nonneg fun i => hf0 _
  · simp only [add_sub_cancel_left]
    calc ∑' i, f (i + m) ≤ ∑' i : ℕ, (2 : ℝ) * (3 : ℝ)⁻¹ ^ (i + m + 1) :=
          hsum'.tsum_le_tsum (fun i => hfle (i + m)) hsum2
      _ = (3 : ℝ)⁻¹ ^ m := hgeom

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_norm_e_sub (a b : ℝ) :
    ‖exists_isNormalInBase_not_isNormalInBase_e a - exists_isNormalInBase_not_isNormalInBase_e b‖
      ≤ 2 * Real.pi * |a - b| := by
  have h1 : exists_isNormalInBase_not_isNormalInBase_e a
      - exists_isNormalInBase_not_isNormalInBase_e b
      = exists_isNormalInBase_not_isNormalInBase_e b *
        (Complex.exp (Complex.I * ((2 * Real.pi * (a - b) : ℝ) : ℂ)) - 1) := by
    unfold exists_isNormalInBase_not_isNormalInBase_e
    have : (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ))
        + Complex.I * ((2 * Real.pi * (a - b) : ℝ) : ℂ)
        = 2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) := by push_cast; ring
    rw [mul_sub, ← Complex.exp_add, this, mul_one]
  rw [h1, norm_mul, exists_isNormalInBase_not_isNormalInBase_s6a6c_norm_e, one_mul]
  calc _ ≤ ‖(2 * Real.pi * (a - b) : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |a - b| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_e_sum {ι : Type*} (s : Finset ι)
    (g : ι → ℝ) :
    exists_isNormalInBase_not_isNormalInBase_e (∑ i ∈ s, g i)
      = ∏ i ∈ s, exists_isNormalInBase_not_isNormalInBase_e (g i) := by
  unfold exists_isNormalInBase_not_isNormalInBase_e
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_e_zero :
    exists_isNormalInBase_not_isNormalInBase_e 0 = 1 := by
  unfold exists_isNormalInBase_not_isNormalInBase_e
  simp

/-- The fair coin on `Bool`: the law of one coordinate of `uniformMeasure`. -/
private noncomputable abbrev exists_isNormalInBase_not_isNormalInBase_s6a6c_coin : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false
    (⟨((1 / 2 : NNReal) : ℝ), (1 / 2 : NNReal).2, NNReal.coe_le_one.mpr (by norm_num)⟩ :
      unitInterval)

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_integral_coin (g : Bool → ℂ) :
    ∫ b, g b ∂exists_isNormalInBase_not_isNormalInBase_s6a6c_coin = (g true + g false) / 2 := by
  have h1 : exists_isNormalInBase_not_isNormalInBase_s6a6c_coin.real {true} = 1 / 2 := by
    unfold exists_isNormalInBase_not_isNormalInBase_s6a6c_coin
    rw [ProbabilityTheory.bernoulliMeasure_real_apply_of_mem_of_notMem _
      (measurableSet_singleton true) (Set.mem_singleton true) (by simp)]
    norm_num
  have h2 : exists_isNormalInBase_not_isNormalInBase_s6a6c_coin.real {false} = 1 / 2 := by
    unfold exists_isNormalInBase_not_isNormalInBase_s6a6c_coin
    rw [ProbabilityTheory.bernoulliMeasure_real_apply_of_notMem_of_mem _
      (measurableSet_singleton false) (by simp) (Set.mem_singleton false)]
    norm_num
  rw [integral_fintype Integrable.of_finite, Fintype.sum_bool, h1, h2]
  simp only [Complex.real_smul]
  push_cast
  ring

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_integral_trunc (t : ℤ) (m : ℕ) :
    ∫ w, exists_isNormalInBase_not_isNormalInBase_e
        ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w) ∂uniformMeasure
      = ∏ j ∈ Finset.range m, ((exists_isNormalInBase_not_isNormalInBase_e
          ((t : ℝ) * ((2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1))) + 1) / 2) := by
  classical
  have hU : uniformMeasure = Measure.infinitePi
      (fun _ : ℕ => exists_isNormalInBase_not_isNormalInBase_s6a6c_coin) := rfl
  set s : Finset ℕ := Finset.range m with hs
  let f : (Π i : s, Bool) → ℂ := fun y => ∏ i : s, exists_isNormalInBase_not_isNormalInBase_e
      ((t : ℝ) * (if y i then (2 : ℝ) * (3 : ℝ)⁻¹ ^ ((i : ℕ) + 1) else 0))
  have hpt : ∀ w : CantorSeq, exists_isNormalInBase_not_isNormalInBase_e
      ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w) = f (s.restrict w) :=
    fun w => by
    change _ = ∏ i : s, exists_isNormalInBase_not_isNormalInBase_e
      ((t : ℝ) * (if w (i : ℕ) then (2 : ℝ) * (3 : ℝ)⁻¹ ^ ((i : ℕ) + 1) else 0))
    rw [Finset.prod_coe_sort s (fun j => exists_isNormalInBase_not_isNormalInBase_e
      ((t : ℝ) * (if w j then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) else 0)))]
    rw [← exists_isNormalInBase_not_isNormalInBase_s6a6c_e_sum]
    unfold exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc
    rw [Finset.mul_sum]
  have hf : AEStronglyMeasurable f (Measure.pi (fun i : s =>
      exists_isNormalInBase_not_isNormalInBase_s6a6c_coin)) :=
    Measurable.of_discrete.aestronglyMeasurable
  calc ∫ w, exists_isNormalInBase_not_isNormalInBase_e
        ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w) ∂uniformMeasure
      = ∫ w, f (s.restrict w) ∂(Measure.infinitePi
          (fun _ : ℕ => exists_isNormalInBase_not_isNormalInBase_s6a6c_coin)) := by
        rw [hU]; simp_rw [hpt]
    _ = ∫ y, f y ∂(Measure.pi (fun i : s =>
          exists_isNormalInBase_not_isNormalInBase_s6a6c_coin)) :=
        integral_restrict_infinitePi (μ := fun _ : ℕ =>
          exists_isNormalInBase_not_isNormalInBase_s6a6c_coin) hf
    _ = ∏ i : s, ∫ b, exists_isNormalInBase_not_isNormalInBase_e
          ((t : ℝ) * (if b then (2 : ℝ) * (3 : ℝ)⁻¹ ^ ((i : ℕ) + 1) else 0))
          ∂exists_isNormalInBase_not_isNormalInBase_s6a6c_coin :=
        integral_fintype_prod_eq_prod (fun (i : s) (b : Bool) =>
          exists_isNormalInBase_not_isNormalInBase_e
            ((t : ℝ) * (if b then (2 : ℝ) * (3 : ℝ)⁻¹ ^ ((i : ℕ) + 1) else 0)))
    _ = ∏ i : s, ((exists_isNormalInBase_not_isNormalInBase_e
          ((t : ℝ) * ((2 : ℝ) * (3 : ℝ)⁻¹ ^ ((i : ℕ) + 1))) + 1) / 2) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [exists_isNormalInBase_not_isNormalInBase_s6a6c_integral_coin]
        simp only [ite_true, Bool.false_eq_true, ite_false, mul_zero,
          exists_isNormalInBase_not_isNormalInBase_s6a6c_e_zero]
    _ = ∏ j ∈ Finset.range m, ((exists_isNormalInBase_not_isNormalInBase_e
          ((t : ℝ) * ((2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1))) + 1) / 2) :=
        Finset.prod_coe_sort s (fun j => (exists_isNormalInBase_not_isNormalInBase_e
          ((t : ℝ) * ((2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1))) + 1) / 2)

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_e_eq (y : ℝ) :
    exists_isNormalInBase_not_isNormalInBase_e y
      = Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) := by
  unfold exists_isNormalInBase_not_isNormalInBase_e
  congr 1
  push_cast
  ring

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_norm_e_add_one_div (θ : ℝ) :
    ‖(exists_isNormalInBase_not_isNormalInBase_e θ + 1) / 2‖ = |Real.cos (Real.pi * θ)| := by
  have hsq : ‖(exists_isNormalInBase_not_isNormalInBase_e θ + 1) / 2‖ ^ 2
      = Real.cos (Real.pi * θ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply,
      exists_isNormalInBase_not_isNormalInBase_s6a6c_e_eq]
    simp only [Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      add_zero]
    have hc : Real.cos (2 * Real.pi * θ) = 2 * Real.cos (Real.pi * θ) ^ 2 - 1 := by
      rw [show 2 * Real.pi * θ = 2 * (Real.pi * θ) by ring, Real.cos_two_mul]
    have hsc := Real.sin_sq_add_cos_sq (2 * Real.pi * θ)
    linear_combination (1 / 4) * hsc + (1 / 2) * hc
  have := (sq_eq_sq_iff_abs_eq_abs _ _).1 hsq
  rwa [abs_of_nonneg (norm_nonneg _)] at this

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_norm_integral_trunc (t : ℤ) (m : ℕ) :
    ‖∫ w, exists_isNormalInBase_not_isNormalInBase_e
        ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w) ∂uniformMeasure‖
      = ∏ j ∈ Finset.range m, |Real.cos (2 * Real.pi * (t : ℝ) / 3 ^ (j + 1))| := by
  rw [exists_isNormalInBase_not_isNormalInBase_s6a6c_integral_trunc, norm_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [exists_isNormalInBase_not_isNormalInBase_s6a6c_norm_e_add_one_div]
  congr 2
  rw [inv_pow]
  ring

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_prod_Icc (g : ℕ → ℝ) (k : ℕ) :
    ∏ j ∈ Finset.Icc 1 k, g j = ∏ j ∈ Finset.range k, g (j + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

private lemma exists_isNormalInBase_not_isNormalInBase_s6a6c_prod_range_le (a : ℕ → ℝ)
    (h0 : ∀ j, 0 ≤ a j) (h1 : ∀ j, a j ≤ 1) {k m : ℕ} (hkm : k ≤ m) :
    ∏ j ∈ Finset.range m, a j ≤ ∏ j ∈ Finset.range k, a j := by
  rw [← Finset.prod_range_mul_prod_Ico a hkm]
  have h2 : ∏ j ∈ Finset.Ico k m, a j ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => h0 j) (fun j _ => h1 j)
  have hp : 0 ≤ ∏ j ∈ Finset.range k, a j := Finset.prod_nonneg fun j _ => h0 j
  nlinarith

/-- Step 6a of the proof of `exists_isNormalInBase_not_isNormalInBase`: the Fourier
transform of the Cantor measure is bounded by the partial product, `|ν̂(t)| ≤ ∏_{j≤k} |cos(2π
t/3^j)|`
for every integer `t` and every `k` (independence of the digits `w_j`; the tail has modulus ≤ 1). -/
private theorem exists_isNormalInBase_not_isNormalInBase_chf_le (t : ℤ) (k : ℕ) :
    exists_isNormalInBase_not_isNormalInBase_chf t ≤ exists_isNormalInBase_not_isNormalInBase_G k
        t := by
  have key : ∀ m : ℕ, k ≤ m → exists_isNormalInBase_not_isNormalInBase_chf t ≤
      exists_isNormalInBase_not_isNormalInBase_G k t + 2 * Real.pi * |(t : ℝ)| * (3 : ℝ)⁻¹ ^ m := by
    intro m hkm
    have hA : Integrable (fun w : CantorSeq => exists_isNormalInBase_not_isNormalInBase_e
        ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_cantorReal w)) uniformMeasure :=
      exists_isNormalInBase_not_isNormalInBase_s6a6c_integrable_e _
        (continuous_const.mul exists_isNormalInBase_not_isNormalInBase_s6a6c_continuous_cantorReal)
    have hB : Integrable (fun w : CantorSeq => exists_isNormalInBase_not_isNormalInBase_e
        ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w)) uniformMeasure :=
      exists_isNormalInBase_not_isNormalInBase_s6a6c_integrable_e _
        (continuous_const.mul (exists_isNormalInBase_not_isNormalInBase_s6a6c_continuous_trunc m))
    have h1 : exists_isNormalInBase_not_isNormalInBase_chf t ≤
        ‖∫ w, exists_isNormalInBase_not_isNormalInBase_e
          ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w) ∂uniformMeasure‖
        + ‖∫ w, (exists_isNormalInBase_not_isNormalInBase_e
            ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_cantorReal w)
          - exists_isNormalInBase_not_isNormalInBase_e
            ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w)) ∂uniformMeasure‖
                := by
      rw [integral_sub hA hB]
      unfold exists_isNormalInBase_not_isNormalInBase_chf
      calc _ = ‖(∫ w, exists_isNormalInBase_not_isNormalInBase_e
            ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w) ∂uniformMeasure)
          + ((∫ w, exists_isNormalInBase_not_isNormalInBase_e
            ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_cantorReal w) ∂uniformMeasure)
          - ∫ w, exists_isNormalInBase_not_isNormalInBase_e
            ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w) ∂uniformMeasure)‖
                := by
            congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖∫ w, (exists_isNormalInBase_not_isNormalInBase_e
            ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_cantorReal w)
          - exists_isNormalInBase_not_isNormalInBase_e
            ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w)) ∂uniformMeasure‖
        ≤ 2 * Real.pi * |(t : ℝ)| * (3 : ℝ)⁻¹ ^ m := by
      have := norm_integral_le_of_norm_le_const (μ := uniformMeasure)
        (f := fun w => exists_isNormalInBase_not_isNormalInBase_e
            ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_cantorReal w)
          - exists_isNormalInBase_not_isNormalInBase_e
            ((t : ℝ) * exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w))
        (C := 2 * Real.pi * |(t : ℝ)| * (3 : ℝ)⁻¹ ^ m) (ae_of_all _ fun w => ?_)
      · simpa using this
      · refine (exists_isNormalInBase_not_isNormalInBase_s6a6c_norm_e_sub _ _).trans ?_
        obtain ⟨hc0, hc1⟩ := exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc_close m w
        have habs : |(t : ℝ) * exists_isNormalInBase_not_isNormalInBase_cantorReal w
            - (t : ℝ) * exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w|
            = |(t : ℝ)| * (exists_isNormalInBase_not_isNormalInBase_cantorReal w
              - exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w) := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hc0]
        rw [habs]
        calc 2 * Real.pi * (|(t : ℝ)| * (exists_isNormalInBase_not_isNormalInBase_cantorReal w
              - exists_isNormalInBase_not_isNormalInBase_s6a6c_trunc m w))
            ≤ 2 * Real.pi * (|(t : ℝ)| * (3 : ℝ)⁻¹ ^ m) := by gcongr
          _ = 2 * Real.pi * |(t : ℝ)| * (3 : ℝ)⁻¹ ^ m := by ring
    have h3 := exists_isNormalInBase_not_isNormalInBase_s6a6c_norm_integral_trunc t m
    have h4 : ∏ j ∈ Finset.range m, |Real.cos (2 * Real.pi * (t : ℝ) / 3 ^ (j + 1))|
        ≤ exists_isNormalInBase_not_isNormalInBase_G k t := by
      unfold exists_isNormalInBase_not_isNormalInBase_G
      rw [exists_isNormalInBase_not_isNormalInBase_s6a6c_prod_Icc
        (fun j => |Real.cos (2 * Real.pi * (t : ℝ) / 3 ^ j)|)]
      exact exists_isNormalInBase_not_isNormalInBase_s6a6c_prod_range_le
        (fun j => |Real.cos (2 * Real.pi * (t : ℝ) / 3 ^ (j + 1))|)
        (fun j => abs_nonneg _) (fun j => Real.abs_cos_le_one _) hkm
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hc : 0 ≤ 2 * Real.pi * |(t : ℝ)| := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show 0 < ε / (2 * Real.pi * |(t : ℝ)| + 1) by positivity) (by norm_num : (3 : ℝ)⁻¹ < 1)
  have h5 : (3 : ℝ)⁻¹ ^ (n + k) ≤ (3 : ℝ)⁻¹ ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right n k)
  have h6 : (3 : ℝ)⁻¹ ^ n * (2 * Real.pi * |(t : ℝ)| + 1) < ε := by
    rwa [lt_div_iff₀ (by positivity)] at hn
  have h7 := key (n + k) (by omega)
  have h8 : 0 ≤ (3 : ℝ)⁻¹ ^ n := by positivity
  nlinarith

/-- Step 6c of the proof of `exists_isNormalInBase_not_isNormalInBase`: the second moment
of the (non-normalised) Weyl sum is the double sum of Fourier coefficients,
`E |∑_{n<N} e(h 2^n X)|² ≤ ∑_{n,m<N} |ν̂(h (2^n - 2^m))|`. -/
private theorem exists_isNormalInBase_not_isNormalInBase_second_moment (h : ℤ) (N : ℕ) :
    ∫⁻ w, ENNReal.ofReal (‖(N : ℂ) * exists_isNormalInBase_not_isNormalInBase_weylAvg
        (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖ ^ 2)
        ∂uniformMeasure
      ≤ ENNReal.ofReal (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          exists_isNormalInBase_not_isNormalInBase_chf (h * (2 ^ n - 2 ^ m))) := by
  set F : CantorSeq → ℂ := fun w => ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
    exists_isNormalInBase_not_isNormalInBase_e
      (((h * (2 ^ n - 2 ^ m) : ℤ) : ℝ) * exists_isNormalInBase_not_isNormalInBase_cantorReal w)
    with hF
  have hpt : ∀ w, ‖(N : ℂ) * exists_isNormalInBase_not_isNormalInBase_weylAvg
        (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖ ^ 2
      = (F w).re := fun w => by
    have := congrArg Complex.re
      (exists_isNormalInBase_not_isNormalInBase_s6a6c_pointwise h N w)
    rw [Complex.ofReal_re] at this
    exact this
  have hterm : ∀ n m : ℕ, Integrable (fun w : CantorSeq =>
      exists_isNormalInBase_not_isNormalInBase_e
        (((h * (2 ^ n - 2 ^ m) : ℤ) : ℝ) * exists_isNormalInBase_not_isNormalInBase_cantorReal w))
      uniformMeasure := fun n m =>
    exists_isNormalInBase_not_isNormalInBase_s6a6c_integrable_e _
      (continuous_const.mul exists_isNormalInBase_not_isNormalInBase_s6a6c_continuous_cantorReal)
  have hFint : Integrable F uniformMeasure :=
    integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hterm n m
  have hre : Integrable (fun w => (F w).re) uniformMeasure := by
    simpa using hFint.re
  have hnn : ∀ w, 0 ≤ (F w).re := fun w => by rw [← hpt]; positivity
  have h2 : ∫ w, F w ∂uniformMeasure = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      ∫ w, exists_isNormalInBase_not_isNormalInBase_e
        (((h * (2 ^ n - 2 ^ m) : ℤ) : ℝ) * exists_isNormalInBase_not_isNormalInBase_cantorReal w)
          ∂uniformMeasure := by
    rw [hF]
    simp only []
    rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _ (fun m _ => hterm n m))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_finsetSum _ (fun m _ => hterm n m)]
  have h1 : ∫ w, (F w).re ∂uniformMeasure = (∫ w, F w ∂uniformMeasure).re := by
    have := integral_re hFint
    simpa using this
  have hbound : ∫ w, (F w).re ∂uniformMeasure ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      exists_isNormalInBase_not_isNormalInBase_chf (h * (2 ^ n - 2 ^ m)) := by
    calc ∫ w, (F w).re ∂uniformMeasure = (∫ w, F w ∂uniformMeasure).re := h1
      _ ≤ ‖∫ w, F w ∂uniformMeasure‖ := Complex.re_le_norm _
      _ = ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          ∫ w, exists_isNormalInBase_not_isNormalInBase_e
            (((h * (2 ^ n - 2 ^ m) : ℤ) : ℝ) *
              exists_isNormalInBase_not_isNormalInBase_cantorReal w) ∂uniformMeasure‖ := by
          rw [h2]
      _ ≤ ∑ n ∈ Finset.range N, ‖∑ m ∈ Finset.range N,
          ∫ w, exists_isNormalInBase_not_isNormalInBase_e
            (((h * (2 ^ n - 2 ^ m) : ℤ) : ℝ) *
              exists_isNormalInBase_not_isNormalInBase_cantorReal w) ∂uniformMeasure‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          ‖∫ w, exists_isNormalInBase_not_isNormalInBase_e
            (((h * (2 ^ n - 2 ^ m) : ℤ) : ℝ) *
              exists_isNormalInBase_not_isNormalInBase_cantorReal w) ∂uniformMeasure‖ :=
          Finset.sum_le_sum fun n _ => norm_sum_le _ _
      _ = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          exists_isNormalInBase_not_isNormalInBase_chf (h * (2 ^ n - 2 ^ m)) := rfl
  calc ∫⁻ w, ENNReal.ofReal (‖(N : ℂ) * exists_isNormalInBase_not_isNormalInBase_weylAvg
        (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖ ^ 2)
        ∂uniformMeasure
      = ∫⁻ w, ENNReal.ofReal ((F w).re) ∂uniformMeasure := by simp_rw [hpt]
    _ = ENNReal.ofReal (∫ w, (F w).re ∂uniformMeasure) :=
        (ofReal_integral_eq_lintegral_ofReal hre (ae_of_all _ hnn)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound
/-- `G k z` as a product over `Finset.range`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s6b_G_eq_prod_range (k : ℕ) (z : ℤ) :
    exists_isNormalInBase_not_isNormalInBase_G k z =
      ∏ i ∈ Finset.range k, |Real.cos (2 * Real.pi * (z : ℝ) / 3 ^ (i + 1))| := by
  unfold exists_isNormalInBase_not_isNormalInBase_G
  induction k with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1), ih, Finset.prod_range_succ]

/-- Stripping one factor `3`: `G (m+1) (3 w) = G m w`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s6b_G_mul_three (m : ℕ) (w : ℤ) :
    exists_isNormalInBase_not_isNormalInBase_G (m + 1) (3 * w) =
      exists_isNormalInBase_not_isNormalInBase_G m w := by
  rw [exists_isNormalInBase_not_isNormalInBase_s6b_G_eq_prod_range,
    exists_isNormalInBase_not_isNormalInBase_s6b_G_eq_prod_range, Finset.prod_range_succ']
  have h0 : |Real.cos (2 * Real.pi * ((3 * w : ℤ) : ℝ) / 3 ^ (0 + 1))| = 1 := by
    have : 2 * Real.pi * ((3 * w : ℤ) : ℝ) / 3 ^ (0 + 1) = (w : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [this, Real.cos_int_mul_two_pi]; simp
  have h1 : ∀ i ∈ Finset.range m,
      |Real.cos (2 * Real.pi * ((3 * w : ℤ) : ℝ) / 3 ^ (i + 1 + 1))| =
        |Real.cos (2 * Real.pi * (w : ℝ) / 3 ^ (i + 1))| := by
    intro i _
    congr 2
    push_cast
    rw [pow_succ (3 : ℝ) (i + 1)]
    field_simp
  change (∏ i ∈ Finset.range m, |Real.cos (2 * Real.pi * ((3 * w : ℤ) : ℝ) / 3 ^ (i + 1 + 1))|) *
      |Real.cos (2 * Real.pi * ((3 * w : ℤ) : ℝ) / 3 ^ (0 + 1))| =
    ∏ i ∈ Finset.range m, |Real.cos (2 * Real.pi * (w : ℝ) / 3 ^ (i + 1))|
  rw [h0, mul_one]
  exact Finset.prod_congr rfl h1

/-- Stripping `v` factors `3`: `G (k+v) (3^v z) = G k z`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s6b_G_shift (v k : ℕ) (z : ℤ) :
    exists_isNormalInBase_not_isNormalInBase_G (k + v) (3 ^ v * z) =
      exists_isNormalInBase_not_isNormalInBase_G k z := by
  induction v with
  | zero => simp
  | succ v ih =>
    have h1 : k + (v + 1) = (k + v) + 1 := by omega
    have h2 : (3 : ℤ) ^ (v + 1) * z = 3 * (3 ^ v * z) := by ring
    rw [h1, h2, exists_isNormalInBase_not_isNormalInBase_s6b_G_mul_three, ih]

/-- `G k` is `3^k`-periodic. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s6b_G_add_mul (k : ℕ) (z m : ℤ) :
    exists_isNormalInBase_not_isNormalInBase_G k (z + 3 ^ k * m) =
      exists_isNormalInBase_not_isNormalInBase_G k z := by
  unfold exists_isNormalInBase_not_isNormalInBase_G
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  have hk' : (3 : ℝ) ^ k = 3 ^ j * 3 ^ (k - j) := by
    rw [← pow_add]; congr 1; omega
  have h3 : (3 : ℝ) ^ j ≠ 0 := by positivity
  have : 2 * Real.pi * ((z + 3 ^ k * m : ℤ) : ℝ) / 3 ^ j =
      2 * Real.pi * (z : ℝ) / 3 ^ j + ((3 ^ (k - j) * m : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    rw [hk']
    field_simp
  rw [this, Real.cos_add_int_mul_two_pi]

/-- `G k z` depends only on `z % 3^k`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s6b_G_emod (k : ℕ) (z : ℤ) :
    exists_isNormalInBase_not_isNormalInBase_G k (z % 3 ^ k) =
      exists_isNormalInBase_not_isNormalInBase_G k z := by
  have := exists_isNormalInBase_not_isNormalInBase_s6b_G_add_mul k (z % 3 ^ k) (z / 3 ^ k)
  have hz : z % 3 ^ k + 3 ^ k * (z / 3 ^ k) = z := Int.emod_add_mul_ediv z (3 ^ k)
  rw [hz] at this
  exact this.symm

private lemma exists_isNormalInBase_not_isNormalInBase_s6b_G_nonneg (k : ℕ) (z : ℤ) :
    0 ≤ exists_isNormalInBase_not_isNormalInBase_G k z := by
  unfold exists_isNormalInBase_not_isNormalInBase_G
  exact Finset.prod_nonneg fun _ _ => abs_nonneg _

/-- Splitting off the `3`-part of a non-zero integer (induction on `natAbs`). -/
private lemma exists_isNormalInBase_not_isNormalInBase_s6b_three_part_aux :
    ∀ (n : ℕ) (s : ℤ), s ≠ 0 → s.natAbs = n →
      ∃ (v : ℕ) (u : ℤ), ¬ (3 : ℤ) ∣ u ∧ s = 3 ^ v * u := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hn
    by_cases h3 : (3 : ℤ) ∣ s
    · obtain ⟨t, rfl⟩ := h3
      have ht : t ≠ 0 := by
        rintro rfl
        simp at hs
      have hlt : t.natAbs < n := by
        rw [← hn, Int.natAbs_mul]
        have h0 : 0 < t.natAbs := Int.natAbs_pos.2 ht
        have h3' : (3 : ℤ).natAbs = 3 := rfl
        rw [h3']
        omega
      obtain ⟨v, u, hu, htu⟩ := ih t.natAbs hlt t ht rfl
      exact ⟨v + 1, u, hu, by rw [htu]; ring⟩
    · exact ⟨0, s, h3, by simp⟩

private lemma exists_isNormalInBase_not_isNormalInBase_s6b_three_part (s : ℤ) (hs : s ≠ 0) :
    ∃ (v : ℕ) (u : ℤ), ¬ (3 : ℤ) ∣ u ∧ s = 3 ^ v * u :=
  exists_isNormalInBase_not_isNormalInBase_s6b_three_part_aux s.natAbs s hs rfl

/-- The residues `2^(a+r1) u` and `2^(a+r2) u` modulo `3^k` differ for `r1 < r2 < 2·3^(k-1)`
(`2` has order `2·3^(k-1)` modulo `3^k`, `3 ∤ u`). -/
private lemma exists_isNormalInBase_not_isNormalInBase_s6b_not_modEq (k : ℕ) (hk : 1 ≤ k) (u : ℤ)
    (hu : ¬ (3 : ℤ) ∣ u) (a r1 r2 : ℕ) (h12 : r1 < r2) (h2 : r2 < 2 * 3 ^ (k - 1)) :
    (2 ^ (a + r1) * u) % (3 ^ k : ℤ) ≠ (2 ^ (a + r2) * u) % (3 ^ k : ℤ) := by
  intro hmod
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h12
  have hdvd : (3 ^ k : ℤ) ∣ 2 ^ (a + (r1 + d + 1)) * u - 2 ^ (a + r1) * u :=
    Int.modEq_iff_dvd.1 hmod
  have hfac : (2 : ℤ) ^ (a + (r1 + d + 1)) * u - 2 ^ (a + r1) * u =
      2 ^ (a + r1) * ((2 ^ (d + 1) - 1) * u) := by ring
  rw [hfac] at hdvd
  have h32 : IsCoprime (3 : ℤ) 2 := ⟨1, -1, by norm_num⟩
  have hc2 : IsCoprime ((3 : ℤ) ^ k) (2 ^ (a + r1)) := h32.pow
  have hcu : IsCoprime ((3 : ℤ) ^ k) u := (Int.prime_three.coprime_iff_not_dvd.2 hu).pow_left
  have h3 : (3 : ℤ) ^ k ∣ 2 ^ (d + 1) - 1 :=
    hcu.dvd_of_dvd_mul_right (hc2.dvd_of_dvd_mul_left hdvd)
  have hz : ((2 ^ (d + 1) - 1 : ℤ) : ZMod (3 ^ k)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact h3
  push_cast at hz
  have hz' : (2 : ZMod (3 ^ k)) ^ (d + 1) = 1 := sub_eq_zero.1 hz
  have hord := exists_isNormalInBase_not_isNormalInBase_order k hk
  exact pow_ne_one_of_lt_orderOf (Nat.succ_ne_zero d) (by rw [hord]; omega) hz'

/-- A full period `2·3^(k-1)` of the orbit `2^n u` visits distinct residues, so the sum of `G k`
over it is at most the sum of `G k` over all residues. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s6b_block (k : ℕ) (hk : 1 ≤ k) (u : ℤ)
    (hu : ¬ (3 : ℤ) ∣ u) (a : ℕ) :
    ∑ r ∈ Finset.range (2 * 3 ^ (k - 1)),
        exists_isNormalInBase_not_isNormalInBase_G k (2 ^ (a + r) * u) ≤
      ∑ i ∈ Finset.range (3 ^ k), exists_isNormalInBase_not_isNormalInBase_G k (i : ℤ) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, ∀ r, ((g r : ℕ) : ℤ) = (2 ^ (a + r) * u) % (3 ^ k : ℤ) :=
    ⟨fun r => ((2 ^ (a + r) * u) % (3 ^ k : ℤ)).toNat,
      fun r => Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))⟩
  have hGg : ∀ r, exists_isNormalInBase_not_isNormalInBase_G k (2 ^ (a + r) * u) =
      exists_isNormalInBase_not_isNormalInBase_G k ((g r : ℕ) : ℤ) := fun r => by
    rw [hg r, exists_isNormalInBase_not_isNormalInBase_s6b_G_emod]
  have hinj : Set.InjOn g (Finset.range (2 * 3 ^ (k - 1)) : Set ℕ) := by
    intro r1 hr1 r2 hr2 h12
    simp only [Finset.coe_range, Set.mem_Iio] at hr1 hr2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact exists_isNormalInBase_not_isNormalInBase_s6b_not_modEq k hk u hu a r1 r2 hlt hr2
        (by rw [← hg r1, ← hg r2, h12])
    · exact exists_isNormalInBase_not_isNormalInBase_s6b_not_modEq k hk u hu a r2 r1 hlt hr1
        (by rw [← hg r1, ← hg r2, h12])
  calc ∑ r ∈ Finset.range (2 * 3 ^ (k - 1)),
          exists_isNormalInBase_not_isNormalInBase_G k (2 ^ (a + r) * u)
      = ∑ r ∈ Finset.range (2 * 3 ^ (k - 1)),
          exists_isNormalInBase_not_isNormalInBase_G k ((g r : ℕ) : ℤ) :=
        Finset.sum_congr rfl fun r _ => hGg r
    _ = ∑ i ∈ (Finset.range (2 * 3 ^ (k - 1))).image g,
          exists_isNormalInBase_not_isNormalInBase_G k (i : ℤ) :=
        (Finset.sum_image (f := fun i : ℕ => exists_isNormalInBase_not_isNormalInBase_G k (i : ℤ))
          hinj).symm
    _ ≤ ∑ i ∈ Finset.range (3 ^ k), exists_isNormalInBase_not_isNormalInBase_G k (i : ℤ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ =>
          exists_isNormalInBase_not_isNormalInBase_s6b_G_nonneg k i
        intro i hi
        obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 hi
        rw [Finset.mem_range]
        have h2 : ((g r : ℕ) : ℤ) < 3 ^ k := by
          rw [hg r]; exact Int.emod_lt_of_pos _ (by positivity)
        exact_mod_cast h2

/-- Sum over `Q` consecutive blocks of length `P`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s6b_sum_blocks (f : ℕ → ℝ) (P : ℕ) (S : ℝ)
    (hblock : ∀ a, ∑ r ∈ Finset.range P, f (a + r) ≤ S) (Q : ℕ) :
    ∑ n ∈ Finset.range (Q * P), f n ≤ Q * S := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Nat.add_mul, Nat.one_mul, Finset.sum_range_add]
    push_cast
    linarith [hblock (Q * P)]

/-- Sum over `range M` bounded by `(M/P + 1)` blocks. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s6b_sum_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (P : ℕ) (hP : 0 < P) (S : ℝ) (hS : 0 ≤ S)
    (hblock : ∀ a, ∑ r ∈ Finset.range P, f (a + r) ≤ S) (M : ℕ) :
    ∑ n ∈ Finset.range M, f n ≤ ((M : ℝ) / P + 1) * S := by
  have hM : M ≤ (M / P + 1) * P := by
    have h1 : M = P * (M / P) + M % P := (Nat.div_add_mod M P).symm
    have h2 : M % P < P := Nat.mod_lt M hP
    calc M = P * (M / P) + M % P := h1
      _ ≤ P * (M / P) + P := by omega
      _ = (M / P + 1) * P := by ring
  calc ∑ n ∈ Finset.range M, f n ≤ ∑ n ∈ Finset.range ((M / P + 1) * P), f n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hM) fun n _ _ => hf n
    _ ≤ ((M / P + 1 : ℕ) : ℝ) * S :=
        exists_isNormalInBase_not_isNormalInBase_s6b_sum_blocks f P S hblock (M / P + 1)
    _ ≤ ((M : ℝ) / P + 1) * S := by
        apply mul_le_mul_of_nonneg_right _ hS
        push_cast
        have := (Nat.cast_div_le (α := ℝ) (m := M) (n := P))
        linarith

/-- Parseval for `G`: `∑_{r<3^k} G(k,r)^2 = (3/2)^k`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s6b_sum_G_sq (k : ℕ) :
    ∑ r ∈ Finset.range (3 ^ k), (exists_isNormalInBase_not_isNormalInBase_G k (r : ℤ)) ^ 2 =
      (3 / 2 : ℝ) ^ k := by
  rw [← exists_isNormalInBase_not_isNormalInBase_parseval k]
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold exists_isNormalInBase_not_isNormalInBase_G
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [sq_abs, Int.cast_natCast]

/-- Cauchy-Schwarz: `∑_{r<3^k} G(k,r) ≤ (9/2)^(k/2)`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s6b_sum_G_le (k : ℕ) :
    ∑ r ∈ Finset.range (3 ^ k), exists_isNormalInBase_not_isNormalInBase_G k (r : ℤ) ≤
      Real.sqrt ((9 / 2 : ℝ) ^ k) := by
  have hcs : (∑ r ∈ Finset.range (3 ^ k), exists_isNormalInBase_not_isNormalInBase_G k (r : ℤ)) ^ 2
      ≤
      ((Finset.range (3 ^ k)).card : ℝ) *
        ∑ r ∈ Finset.range (3 ^ k), (exists_isNormalInBase_not_isNormalInBase_G k (r : ℤ)) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [exists_isNormalInBase_not_isNormalInBase_s6b_sum_G_sq, Finset.card_range] at hcs
  have h9 : ((3 ^ k : ℕ) : ℝ) * (3 / 2 : ℝ) ^ k = (9 / 2 : ℝ) ^ k := by
    push_cast
    rw [← mul_pow]
    norm_num
  rw [h9] at hcs
  exact (le_abs_self _).trans (Real.abs_le_sqrt hcs)

/-- Step 6b of the proof of `exists_isNormalInBase_not_isNormalInBase`: the orbit-sum
bound for the Cantor measure.  For `s ≠ 0`, `k ≥ 1`, and `M`,
`∑_{n<M} |ν̂(2^n s)| ≤ (M / (2·3^(k-1)) + 1) · (9/2)^(k/2)`. (Strip the `3`-part `s = 3^v u` with
`3 ∤ u`, `|ν̂(3^v z)| ≤ G(k, z)` by step 6a; `2` is a primitive root mod `3^k` (step 5), so over a
period `2·3^(k-1)` the residues `2^n u` run over distinct units; Cauchy-Schwarz and Parseval
(step 4) bound the sum over all residues by `(9/2)^(k/2)`.) -/
private theorem exists_isNormalInBase_not_isNormalInBase_orbit_sum (s : ℤ) (hs : s ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (M : ℕ) :
    ∑ n ∈ Finset.range M, exists_isNormalInBase_not_isNormalInBase_chf (2 ^ n * s)
      ≤ ((M : ℝ) / (2 * 3 ^ (k - 1)) + 1) * Real.sqrt ((9 / 2 : ℝ) ^ k) := by
  obtain ⟨v, u, hu, rfl⟩ := exists_isNormalInBase_not_isNormalInBase_s6b_three_part s hs
  have hpt : ∀ n : ℕ, exists_isNormalInBase_not_isNormalInBase_chf (2 ^ n * (3 ^ v * u)) ≤
      exists_isNormalInBase_not_isNormalInBase_G k (2 ^ n * u) := by
    intro n
    have h2 : (2 : ℤ) ^ n * (3 ^ v * u) = 3 ^ v * (2 ^ n * u) := by ring
    have h1 := exists_isNormalInBase_not_isNormalInBase_chf_le (3 ^ v * (2 ^ n * u)) (k + v)
    rw [exists_isNormalInBase_not_isNormalInBase_s6b_G_shift] at h1
    rw [h2]
    exact h1
  have hS : 0 ≤ ∑ i ∈ Finset.range (3 ^ k), exists_isNormalInBase_not_isNormalInBase_G k (i : ℤ) :=
    Finset.sum_nonneg fun i _ => exists_isNormalInBase_not_isNormalInBase_s6b_G_nonneg k i
  have hP : 0 < 2 * 3 ^ (k - 1) := by positivity
  calc ∑ n ∈ Finset.range M, exists_isNormalInBase_not_isNormalInBase_chf (2 ^ n * (3 ^ v * u))
      ≤ ∑ n ∈ Finset.range M, exists_isNormalInBase_not_isNormalInBase_G k (2 ^ n * u) :=
        Finset.sum_le_sum fun n _ => hpt n
    _ ≤ ((M : ℝ) / ((2 * 3 ^ (k - 1) : ℕ) : ℝ) + 1) *
          ∑ i ∈ Finset.range (3 ^ k), exists_isNormalInBase_not_isNormalInBase_G k (i : ℤ) :=
        exists_isNormalInBase_not_isNormalInBase_s6b_sum_le
          (fun n => exists_isNormalInBase_not_isNormalInBase_G k (2 ^ n * u))
          (fun n => exists_isNormalInBase_not_isNormalInBase_s6b_G_nonneg k _)
          (2 * 3 ^ (k - 1)) hP _ hS
          (fun a => exists_isNormalInBase_not_isNormalInBase_s6b_block k hk u hu a) M
    _ ≤ ((M : ℝ) / (2 * 3 ^ (k - 1)) + 1) * Real.sqrt ((9 / 2 : ℝ) ^ k) := by
        push_cast
        exact mul_le_mul_of_nonneg_left
          (exists_isNormalInBase_not_isNormalInBase_s6b_sum_G_le k) (by positivity)
private lemma exists_isNormalInBase_not_isNormalInBase_s6_chf_nonneg (t : ℤ) :
    0 ≤ exists_isNormalInBase_not_isNormalInBase_chf t :=
  norm_nonneg _

private lemma exists_isNormalInBase_not_isNormalInBase_s6_chf_le_one (t : ℤ) :
    exists_isNormalInBase_not_isNormalInBase_chf t ≤ 1 := by
  have := exists_isNormalInBase_not_isNormalInBase_chf_le t 0
  simpa [exists_isNormalInBase_not_isNormalInBase_G] using this

private lemma exists_isNormalInBase_not_isNormalInBase_s6_decomp (f : ℕ → ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, f n m
      = ∑ n ∈ Finset.range N, f n n + ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range n, f n m
        + ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range n, f m n := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    rw [ih]
    ring

private lemma exists_isNormalInBase_not_isNormalInBase_s6_upper_sum (N : ℕ) (g : ℕ → ℕ → ℝ)
    (hg : ∀ d p, 0 ≤ g d p) :
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range n, g (n - m) m
      ≤ ∑ d ∈ Finset.Icc 1 (N - 1), ∑ p ∈ Finset.range N, g d p := by
  have h1 : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range n, g (n - m) m
      = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.Ioo m N, g (n - m) m := by
    apply Finset.sum_comm'
    intro n m
    simp only [Finset.mem_range, Finset.mem_Ioo]
    omega
  rw [h1]
  calc ∑ m ∈ Finset.range N, ∑ n ∈ Finset.Ioo m N, g (n - m) m
      ≤ ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Icc 1 (N - 1), g d m := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hinj : Set.InjOn (fun n => n - m) (Finset.Ioo m N : Set ℕ) := by
          intro a ha b hb hab
          simp only [Finset.coe_Ioo, Set.mem_Ioo] at ha hb
          simp only at hab
          omega
        rw [← Finset.sum_image (f := fun d => g d m) hinj]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => hg d m
        intro d hd
        simp only [Finset.mem_image, Finset.mem_Ioo] at hd
        obtain ⟨n, ⟨hn1, hn2⟩, rfl⟩ := hd
        simp only [Finset.mem_Icc]
        omega
    _ = ∑ d ∈ Finset.Icc 1 (N - 1), ∑ p ∈ Finset.range N, g d p := Finset.sum_comm

private lemma exists_isNormalInBase_not_isNormalInBase_s6_double_sum (h : ℤ) (hh : h ≠ 0)
    (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) :
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        exists_isNormalInBase_not_isNormalInBase_chf (h * (2 ^ n - 2 ^ m))
      ≤ N + 2 * (((N : ℝ) - 1) * (((N : ℝ) / (2 * 3 ^ (k - 1)) + 1) * Real.sqrt ((9 / 2 : ℝ) ^ k)))
          := by
  rw [exists_isNormalInBase_not_isNormalInBase_s6_decomp]
  have hdiag : ∑ n ∈ Finset.range N,
      exists_isNormalInBase_not_isNormalInBase_chf (h * (2 ^ n - 2 ^ n)) ≤ N := by
    calc ∑ n ∈ Finset.range N, exists_isNormalInBase_not_isNormalInBase_chf (h * (2 ^ n - 2 ^ n))
        ≤ ∑ n ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => exists_isNormalInBase_not_isNormalInBase_s6_chf_le_one _
      _ = N := by simp
  set Bnd : ℝ := ((N : ℝ) / (2 * 3 ^ (k - 1)) + 1) * Real.sqrt ((9 / 2 : ℝ) ^ k) with hBnd
  have hcard : ((Finset.Icc 1 (N - 1)).card : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.card_Icc]
    have : N - 1 + 1 - 1 = N - 1 := by omega
    rw [this]
    rw [Nat.cast_sub hN]
    simp
  have hfix : ∀ s : ℤ, s ≠ 0 →
      ∑ d ∈ Finset.Icc 1 (N - 1), ∑ p ∈ Finset.range N, (fun (d : ℕ) (p : ℕ) =>
        exists_isNormalInBase_not_isNormalInBase_chf (2 ^ p * (s * (2 ^ d - 1)))) d p
        ≤ ((N : ℝ) - 1) * Bnd := by
    intro s hs
    calc _ ≤ ∑ d ∈ Finset.Icc 1 (N - 1), Bnd := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hne : s * (2 ^ d - 1) ≠ 0 := by
            refine mul_ne_zero hs ?_
            have : (1 : ℤ) < 2 ^ d := one_lt_pow₀ (by norm_num) (by omega)
            omega
          exact exists_isNormalInBase_not_isNormalInBase_orbit_sum _ hne k hk N
      _ = ((N : ℝ) - 1) * Bnd := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hU : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range n,
      exists_isNormalInBase_not_isNormalInBase_chf (h * (2 ^ n - 2 ^ m))
      ≤ ((N : ℝ) - 1) * Bnd := by
    calc _ = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range n,
          (fun (d : ℕ) (p : ℕ) => exists_isNormalInBase_not_isNormalInBase_chf
            (2 ^ p * (h * (2 ^ d - 1)))) (n - m) m := by
          refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m hm => ?_
          have hmn : m < n := Finset.mem_range.mp hm
          change _ = exists_isNormalInBase_not_isNormalInBase_chf
            (2 ^ m * (h * (2 ^ (n - m) - 1)))
          congr 1
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmn
          have e0 : m + d + 1 - m = d + 1 := by omega
          have e1 : (2 : ℤ) ^ (m + d + 1) = 2 ^ m * 2 ^ (d + 1) := by ring
          rw [e0, e1]
          ring
      _ ≤ _ := by
          refine (exists_isNormalInBase_not_isNormalInBase_s6_upper_sum N _ ?_).trans (hfix h hh)
          intro d p
          exact exists_isNormalInBase_not_isNormalInBase_s6_chf_nonneg _
  have hL : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range n,
      exists_isNormalInBase_not_isNormalInBase_chf (h * (2 ^ m - 2 ^ n))
      ≤ ((N : ℝ) - 1) * Bnd := by
    calc _ = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range n,
          (fun (d : ℕ) (p : ℕ) => exists_isNormalInBase_not_isNormalInBase_chf
            (2 ^ p * ((-h) * (2 ^ d - 1)))) (n - m) m := by
          refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m hm => ?_
          have hmn : m < n := Finset.mem_range.mp hm
          change _ = exists_isNormalInBase_not_isNormalInBase_chf
            (2 ^ m * ((-h) * (2 ^ (n - m) - 1)))
          congr 1
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmn
          have e0 : m + d + 1 - m = d + 1 := by omega
          have e1 : (2 : ℤ) ^ (m + d + 1) = 2 ^ m * 2 ^ (d + 1) := by ring
          rw [e0, e1]
          ring
      _ ≤ _ := by
          refine (exists_isNormalInBase_not_isNormalInBase_s6_upper_sum N _ ?_).trans
            (hfix (-h) (neg_ne_zero.mpr hh))
          intro d p
          exact exists_isNormalInBase_not_isNormalInBase_s6_chf_nonneg _
  have e2 : (2 : ℝ) * (((N : ℝ) - 1) * Bnd) = ((N : ℝ) - 1) * Bnd + ((N : ℝ) - 1) * Bnd := by ring
  linarith

private lemma exists_isNormalInBase_not_isNormalInBase_s6_normalize (h : ℤ) (N : ℕ) (hN : 1 ≤ N) :
    ∫⁻ w, ENNReal.ofReal (‖exists_isNormalInBase_not_isNormalInBase_weylAvg
          (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖ ^
              2)
          ∂uniformMeasure
      ≤ ENNReal.ofReal ((∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          exists_isNormalInBase_not_isNormalInBase_chf (h * (2 ^ n - 2 ^ m))) / (N : ℝ) ^ 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h6c := exists_isNormalInBase_not_isNormalInBase_second_moment h N
  have key : ∀ w, ENNReal.ofReal (‖exists_isNormalInBase_not_isNormalInBase_weylAvg
          (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖ ^
              2)
      = ENNReal.ofReal (1 / (N : ℝ) ^ 2) * ENNReal.ofReal (‖(N : ℂ) *
          exists_isNormalInBase_not_isNormalInBase_weylAvg
          (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖ ^
              2) := by
    intro w
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [norm_mul, Complex.norm_natCast, mul_pow]
    generalize ‖exists_isNormalInBase_not_isNormalInBase_weylAvg
          (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖ =
              c
    field_simp
  simp_rw [key]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc _ ≤ ENNReal.ofReal (1 / (N : ℝ) ^ 2) * ENNReal.ofReal (∑ n ∈ Finset.range N,
          ∑ m ∈ Finset.range N,
          exists_isNormalInBase_not_isNormalInBase_chf (h * (2 ^ n - 2 ^ m))) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

private lemma exists_isNormalInBase_not_isNormalInBase_s6_numeric (N : ℕ) (hN : 3 ≤ N) (D : ℝ)
    (hD : D ≤ N + 2 * (((N : ℝ) - 1) * (((N : ℝ) / (2 * 3 ^ (Nat.log 3 N - 1)) + 1) *
      Real.sqrt ((9 / 2 : ℝ) ^ (Nat.log 3 N))))) :
    D / (N : ℝ) ^ 2 ≤ 23 * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
  set k := Nat.log 3 N with hk
  have hk1 : 1 ≤ k := Nat.log_pos (by norm_num) hN
  have hk_le : 3 ^ k ≤ N := Nat.pow_log_le_self 3 (by omega)
  have hk_lt : N < 3 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have ha : (3 : ℝ) ^ k ≤ N := by exact_mod_cast hk_le
  have hb : (N : ℝ) < 3 * 3 ^ k := by
    have : (N : ℝ) < 3 ^ (k + 1) := by exact_mod_cast hk_lt
    rwa [pow_succ, mul_comm] at this
  have h3 : (3 : ℝ) ^ k = 3 * 3 ^ (k - 1) := by
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel, pow_succ]; ring
  have hx : (N : ℝ) / (2 * 3 ^ (k - 1)) + 1 ≤ 11 / 2 := by
    have : (N : ℝ) / (2 * 3 ^ (k - 1)) ≤ 9 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  set T := Real.sqrt ((9 / 2 : ℝ) ^ k) with hT
  set s := Real.sqrt ((2 : ℝ) ^ k) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hTnn : 0 ≤ T := Real.sqrt_nonneg _
  have hTs : T * s = 3 ^ k := by
    rw [hT, hs, ← Real.sqrt_mul (by positivity)]
    have : ((9 / 2 : ℝ) ^ k) * 2 ^ k = (3 ^ k) ^ 2 := by
      calc ((9 / 2 : ℝ) ^ k) * 2 ^ k = ((9 / 2) * 2) ^ k := (mul_pow _ _ _).symm
        _ = (3 ^ 2) ^ k := by norm_num
        _ = (3 ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [this, Real.sqrt_sq (by positivity)]
  have hT_le : T ≤ N / s := by
    rw [le_div_iff₀ hspos, hTs]; exact ha
  set r := (N : ℝ) ^ (1 / 4 : ℝ) with hr
  have hr4 : r ^ 4 = N := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hrpos : 0 < r := Real.rpow_pos_of_pos hNpos _
  have hr1 : 1 ≤ r := Real.one_le_rpow (by linarith) (by norm_num)
  have hr_le : r ≤ N := by
    calc r ≤ r ^ 4 := le_self_pow₀ hr1 (by norm_num)
      _ = N := hr4
  have hs2 : s ^ 2 = 2 ^ k := Real.sq_sqrt (by positivity)
  have h2s : r ≤ 2 * s := by
    by_contra hcon
    push Not at hcon
    have h4 : (2 * s) ^ 4 < r ^ 4 := pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
    have h3k : (3 : ℝ) ^ k ≤ (2 ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
    have e4 : (2 * s) ^ 4 = 16 * (2 ^ k) ^ 2 := by
      have : (2 * s) ^ 4 = 16 * (s ^ 2) ^ 2 := by ring
      rw [this, hs2]
    have hpos : (0 : ℝ) ≤ (2 ^ k) ^ 2 := by positivity
    rw [e4, hr4] at h4
    linarith
  have hD1 : D ≤ N + 11 * N * (N / s) := by
    refine hD.trans ?_
    have h1 : ((N : ℝ) - 1) * (((N : ℝ) / (2 * 3 ^ (k - 1)) + 1) * T) ≤ N * ((11 / 2) * T) :=
      mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right hx hTnn) (by positivity) (by positivity)
    have h2 : (N : ℝ) * ((11 / 2) * T) ≤ N * ((11 / 2) * (N / s)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT_le (by norm_num)) hNpos.le
    nlinarith
  have hD2 : D / (N : ℝ) ^ 2 ≤ 1 / N + 11 / s := by
    calc D / (N : ℝ) ^ 2 ≤ (N + 11 * N * (N / s)) / (N : ℝ) ^ 2 := by gcongr
      _ = 1 / N + 11 / s := by field_simp
  have hN1 : 1 / (N : ℝ) ≤ 1 / r := one_div_le_one_div_of_le hrpos hr_le
  have hs1 : 11 / s ≤ 22 / r := by
    have : 11 / s = 22 / (2 * s) := by field_simp; ring
    rw [this]
    exact div_le_div_of_nonneg_left (by norm_num) hrpos h2s
  have hrw : (N : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / r := by
    rw [Real.rpow_neg hNpos.le]
    exact (one_div r).symm
  rw [hrw]
  calc D / (N : ℝ) ^ 2 ≤ 1 / N + 11 / s := hD2
    _ ≤ 1 / r + 22 / r := add_le_add hN1 hs1
    _ = 23 * (1 / r) := by ring

private theorem exists_isNormalInBase_not_isNormalInBase_s6_variance_bound :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℤ, h ≠ 0 → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∫⁻ w, ENNReal.ofReal (‖exists_isNormalInBase_not_isNormalInBase_weylAvg
          (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖ ^
              2)
          ∂uniformMeasure
        ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-δ)) := by
  refine ⟨1 / 4, by norm_num, fun h hh => ⟨23, fun N hN => ?_⟩⟩
  refine (exists_isNormalInBase_not_isNormalInBase_s6_normalize h N hN).trans ?_
  apply ENNReal.ofReal_le_ofReal
  by_cases h3 : 3 ≤ N
  · exact exists_isNormalInBase_not_isNormalInBase_s6_numeric N h3 _
      (exists_isNormalInBase_not_isNormalInBase_s6_double_sum h hh N _ hN
        (Nat.log_pos (by norm_num) h3))
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hN2 : (N : ℝ) ≤ 2 := by
      have : N ≤ 2 := by omega
      exact_mod_cast this
    have hD : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        exists_isNormalInBase_not_isNormalInBase_chf (h * (2 ^ n - 2 ^ m)) ≤ (N : ℝ) ^ 2 := by
      calc _ ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ =>
              exists_isNormalInBase_not_isNormalInBase_s6_chf_le_one _
        _ = (N : ℝ) ^ 2 := by simp [sq]
    have h1 : (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        exists_isNormalInBase_not_isNormalInBase_chf (h * (2 ^ n - 2 ^ m))) / (N : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hD
    set r := (N : ℝ) ^ (1 / 4 : ℝ) with hr
    have hr4 : r ^ 4 = N := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    have hrpos : 0 < r := Real.rpow_pos_of_pos hNpos _
    have hr2 : r ≤ 2 := by
      by_contra hcon
      push Not at hcon
      have h4 : (2 : ℝ) ^ 4 < r ^ 4 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
      rw [hr4] at h4
      norm_num at h4
      linarith
    have hrw : (N : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / r := by
      rw [Real.rpow_neg hNpos.le]
      exact (one_div r).symm
    rw [hrw]
    refine h1.trans ?_
    rw [mul_one_div, le_div_iff₀ hrpos]
    linarith

/-- Step 6 of the proof of `exists_isNormalInBase_not_isNormalInBase`: the variance bound
`E |(1/N) ∑_{n<N} e(h 2^n X)|² ≤ C_h N^{-δ}` with a uniform exponent `δ > 0` (assembled from steps
6a-6c: `∑_{n,m<N} |ν̂(h(2^n-2^m))| ≤ N + 2 ∑_{d=1}^{N-1} ∑_{n<N-d} |ν̂(2^n h (2^d-1))|`, apply
step 6b to `s = h(2^d-1) ≠ 0` with `k ≈ log_3 N`). -/
private theorem exists_isNormalInBase_not_isNormalInBase_variance_bound :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℤ, h ≠ 0 → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∫⁻ w, ENNReal.ofReal (‖exists_isNormalInBase_not_isNormalInBase_weylAvg
          (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖ ^
              2)
          ∂uniformMeasure
        ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-δ)) := by
  refine ⟨1 / 4, by norm_num, fun h hh => ⟨23, fun N hN => ?_⟩⟩
  refine (exists_isNormalInBase_not_isNormalInBase_s6_normalize h N hN).trans ?_
  apply ENNReal.ofReal_le_ofReal
  by_cases h3 : 3 ≤ N
  · exact exists_isNormalInBase_not_isNormalInBase_s6_numeric N h3 _
      (exists_isNormalInBase_not_isNormalInBase_s6_double_sum h hh N _ hN
        (Nat.log_pos (by norm_num) h3))
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hN2 : (N : ℝ) ≤ 2 := by
      have : N ≤ 2 := by omega
      exact_mod_cast this
    have hD : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        exists_isNormalInBase_not_isNormalInBase_chf (h * (2 ^ n - 2 ^ m)) ≤ (N : ℝ) ^ 2 := by
      calc _ ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ =>
              exists_isNormalInBase_not_isNormalInBase_s6_chf_le_one _
        _ = (N : ℝ) ^ 2 := by simp [sq]
    have h1 : (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        exists_isNormalInBase_not_isNormalInBase_chf (h * (2 ^ n - 2 ^ m))) / (N : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hD
    set r := (N : ℝ) ^ (1 / 4 : ℝ) with hr
    have hr4 : r ^ 4 = N := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    have hrpos : 0 < r := Real.rpow_pos_of_pos hNpos _
    have hr2 : r ≤ 2 := by
      by_contra hcon
      push Not at hcon
      have h4 : (2 : ℝ) ^ 4 < r ^ 4 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
      rw [hr4] at h4
      norm_num at h4
      linarith
    have hrw : (N : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / r := by
      rw [Real.rpow_neg hNpos.le]
      exact (one_div r).symm
    rw [hrw]
    refine h1.trans ?_
    rw [mul_one_div, le_div_iff₀ hrpos]
    linarith

/-- `cantorReal` is continuous on Cantor space. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s7_cantorReal_continuous :
    Continuous exists_isNormalInBase_not_isNormalInBase_cantorReal := by
  unfold exists_isNormalInBase_not_isNormalInBase_cantorReal
  refine continuous_tsum (u := fun j : ℕ => (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1)) ?_ ?_ ?_
  · intro j
    exact (continuous_of_discreteTopology
      (f := fun b : Bool => if b = true then (2 : ℝ) * (3 : ℝ)⁻¹ ^ (j + 1) else 0)).comp
      (continuous_apply j)
  · have h1 : Summable (fun j : ℕ => ((3 : ℝ)⁻¹) ^ j) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine (h1.mul_left (2 * (3 : ℝ)⁻¹)).congr (fun j => ?_)
    ring
  · intro j w
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · simp only [norm_zero]
      positivity

/-- The Weyl averages of the Cantor point are continuous functions of the sequence. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s7_weylAvg_continuous (h : ℤ) (N : ℕ) :
    Continuous fun w : CantorSeq => exists_isNormalInBase_not_isNormalInBase_weylAvg
      (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N := by
  have hX := exists_isNormalInBase_not_isNormalInBase_s7_cantorReal_continuous
  unfold exists_isNormalInBase_not_isNormalInBase_weylAvg exists_isNormalInBase_not_isNormalInBase_e
  fun_prop

private lemma exists_isNormalInBase_not_isNormalInBase_s7_measurable (h : ℤ) (N : ℕ) :
    Measurable fun w : CantorSeq => ENNReal.ofReal
                                      (‖exists_isNormalInBase_not_isNormalInBase_weylAvg
      (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖ ^
          2) := by
  have hc := exists_isNormalInBase_not_isNormalInBase_s7_weylAvg_continuous h N
  exact ENNReal.measurable_ofReal.comp ((hc.norm.pow 2).measurable)

/-- Chebyshev's inequality for the Weyl averages. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s7_cheb {δ : ℝ} {h : ℤ} {C : ℝ}
    (hv : ∀ N : ℕ, 1 ≤ N →
      ∫⁻ w, ENNReal.ofReal (‖exists_isNormalInBase_not_isNormalInBase_weylAvg
          (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖ ^
              2)
          ∂uniformMeasure
        ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-δ)))
    {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 1 ≤ N) :
    uniformMeasure {w | ε ≤ ‖exists_isNormalInBase_not_isNormalInBase_weylAvg
      (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖}
      ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-δ)) / ENNReal.ofReal (ε ^ 2) := by
  have hmeas := exists_isNormalInBase_not_isNormalInBase_s7_measurable h N
  have hε2 : ENNReal.ofReal (ε ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  calc uniformMeasure {w | ε ≤ ‖exists_isNormalInBase_not_isNormalInBase_weylAvg
        (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖}
      ≤ uniformMeasure {w | ENNReal.ofReal (ε ^ 2) ≤ ENNReal.ofReal
          (‖exists_isNormalInBase_not_isNormalInBase_weylAvg
            (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w)
              h N‖ ^ 2)} := by
        apply measure_mono
        intro w hw
        exact ENNReal.ofReal_le_ofReal (by gcongr; exact hw)
    _ ≤ (∫⁻ w, ENNReal.ofReal (‖exists_isNormalInBase_not_isNormalInBase_weylAvg
          (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w)
            h N‖ ^ 2) ∂uniformMeasure) / ENNReal.ofReal (ε ^ 2) :=
        meas_ge_le_lintegral_div hmeas.aemeasurable hε2 ENNReal.ofReal_ne_top
    _ ≤ _ := by
        gcongr
        exact hv N hN

/-- Interpolation: convergence of the Weyl averages along `N = (m+1)^c` gives convergence along
all `N` (every term has modulus one). -/
private lemma exists_isNormalInBase_not_isNormalInBase_s7_interp (y : ℕ → ℝ) (h : ℤ) {c : ℕ}
    (hc : 1 ≤ c)
    (hlim : Tendsto (fun m : ℕ => exists_isNormalInBase_not_isNormalInBase_weylAvg y h
                                    ((m + 1) ^ c))
      atTop (𝓝 0)) :
    Tendsto (exists_isNormalInBase_not_isNormalInBase_weylAvg y h) atTop (𝓝 0) := by
  classical
  set u : ℕ → ℂ := fun n => exists_isNormalInBase_not_isNormalInBase_e ((h : ℝ) * y n) with hu_def
  have hu : ∀ n, ‖u n‖ ≤ 1 := by
    intro n
    have : u n = Complex.exp (((2 * Real.pi * ((h : ℝ) * y n) : ℝ) : ℂ) * Complex.I) := by
      simp only [hu_def, exists_isNormalInBase_not_isNormalInBase_e]
      push_cast
      ring_nf
    rw [this, Complex.norm_exp_ofReal_mul_I]
  set S : ℕ → ℂ := fun N => ∑ n ∈ Finset.range N, u n with hS
  have hW : ∀ N : ℕ, exists_isNormalInBase_not_isNormalInBase_weylAvg y h N
      = (1 / (N : ℂ)) * S N := fun N => rfl
  set B : ℕ → ℕ := fun m => (m + 1) ^ c with hB
  have hBge : ∀ m, m + 1 ≤ B m := fun m => Nat.le_self_pow (by omega) (m + 1)
  set J : ℕ → ℕ := fun N => Nat.findGreatest (fun j => (j + 1) ^ c ≤ N) N with hJ
  have hJ_spec : ∀ N, 1 ≤ N → B (J N) ≤ N ∧ N < B (J N + 1) := by
    intro N hN
    have hP0 : (fun j => (j + 1) ^ c ≤ N) 0 := by simpa using hN
    have h1 : (J N + 1) ^ c ≤ N :=
      Nat.findGreatest_spec (P := fun j => (j + 1) ^ c ≤ N) (Nat.zero_le N) hP0
    refine ⟨h1, ?_⟩
    by_contra hcon
    replace hcon := not_lt.1 hcon
    have hle : J N + 1 ≤ N := by
      have := hBge (J N + 1)
      simp only [hB] at this hcon
      omega
    have := Nat.le_findGreatest (P := fun j => (j + 1) ^ c ≤ N) hle
      (show (J N + 1 + 1) ^ c ≤ N from hcon)
    simp only [hJ] at *
    omega
  have hJ_tendsto : Tendsto J atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    refine ⟨B M, fun N hN => ?_⟩
    have hMN : M ≤ N := le_trans (by have := hBge M; omega) hN
    exact Nat.le_findGreatest (P := fun j => (j + 1) ^ c ≤ N) hMN (show (M + 1) ^ c ≤ N from hN)
  -- the ratio term
  set r : ℕ → ℝ := fun j => (((j : ℝ) + 2) ^ c - ((j : ℝ) + 1) ^ c) / ((j : ℝ) + 1) ^ c with hr
  have hr_eq : ∀ j : ℕ, r j = (1 + 1 / ((j : ℝ) + 1)) ^ c - 1 := by
    intro j
    have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have : (1 + 1 / ((j : ℝ) + 1)) = ((j : ℝ) + 2) / ((j : ℝ) + 1) := by
      field_simp
      ring
    simp only [hr]
    rw [this, div_pow]
    field_simp
  have hr_tendsto : Tendsto r atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun j : ℕ => (1 + 1 / ((j : ℝ) + 1)) ^ c - 1) atTop (𝓝 ((1 + 0) ^ c - 1)) :=
      ((tendsto_const_nhds.add h1).pow c).sub_const 1
    simp only [add_zero, one_pow, sub_self] at h2
    exact h2.congr (fun j => (hr_eq j).symm)
  -- the pointwise bound
  have hbound : ∀ N : ℕ, 1 ≤ N →
      ‖(1 / (N : ℂ)) * S N‖ ≤ ‖(1 / ((B (J N) : ℕ) : ℂ)) * S (B (J N))‖ + r (J N) := by
    intro N hN
    obtain ⟨hMN, hNM⟩ := hJ_spec N hN
    set j := J N with hj
    set M := B j with hMdef
    have hMpos : (0 : ℝ) < (M : ℝ) := by
      have : 1 ≤ M := le_trans (by omega) (hBge j)
      exact_mod_cast this
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hdiff : ‖S N - S M‖ ≤ (N : ℝ) - M := by
      have h1 : S N - S M = ∑ n ∈ Finset.Ico M N, u n := by
        simp only [hS]
        rw [← Finset.sum_range_add_sum_Ico u hMN]
        ring
      rw [h1]
      calc ‖∑ n ∈ Finset.Ico M N, u n‖ ≤ ∑ n ∈ Finset.Ico M N, ‖u n‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Ico M N, (1 : ℝ) := Finset.sum_le_sum fun n _ => hu n
        _ = (N : ℝ) - M := by simp [Nat.cast_sub hMN]
    have hMNr : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hNMr : (N : ℝ) ≤ ((B (j + 1) : ℕ) : ℝ) := by exact_mod_cast hNM.le
    have hBj1 : ((B (j + 1) : ℕ) : ℝ) = ((j : ℝ) + 2) ^ c := by
      simp only [hB]
      push_cast
      ring_nf
    have hMr : (M : ℝ) = ((j : ℝ) + 1) ^ c := by
      simp only [hMdef, hB]
      push_cast
      ring
    have hSN : ‖S N‖ ≤ ‖S M‖ + ((N : ℝ) - M) := by
      calc ‖S N‖ = ‖S M + (S N - S M)‖ := by ring_nf
        _ ≤ ‖S M‖ + ‖S N - S M‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have hnormN : ‖(1 / (N : ℂ)) * S N‖ = ‖S N‖ / N := by
      rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
      ring
    have hnormM : ‖(1 / ((M : ℕ) : ℂ)) * S M‖ = ‖S M‖ / M := by
      rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
      ring
    rw [hnormN, hnormM]
    have hrj : r j = ((B (j + 1) : ℕ) - (M : ℝ)) / M := by
      simp only [hr]
      rw [hBj1, hMr]
    rw [hrj]
    -- ‖S N‖ / N ≤ ‖S M‖ / M + (B(j+1) - M) / M
    have e1 : ‖S M‖ / N ≤ ‖S M‖ / M := by
      apply div_le_div_of_nonneg_left (norm_nonneg _) hMpos hMNr
    have e2 : ((N : ℝ) - M) / N ≤ (((B (j + 1) : ℕ) : ℝ) - M) / M := by
      calc ((N : ℝ) - M) / N ≤ ((N : ℝ) - M) / M :=
            div_le_div_of_nonneg_left (by linarith) hMpos hMNr
        _ ≤ (((B (j + 1) : ℕ) : ℝ) - M) / M := by
            apply div_le_div_of_nonneg_right _ hMpos.le
            linarith
    calc ‖S N‖ / N ≤ (‖S M‖ + ((N : ℝ) - M)) / N := by
          apply div_le_div_of_nonneg_right hSN hNpos.le
      _ = ‖S M‖ / N + ((N : ℝ) - M) / N := by ring
      _ ≤ _ := by linarith
  -- conclude
  have hnorm : Tendsto (fun m : ℕ => ‖(1 / ((B m : ℕ) : ℂ)) * S (B m)‖) atTop (𝓝 0) := by
    have h1 := hlim.norm
    rw [norm_zero] at h1
    exact Tendsto.congr (fun m => rfl) h1
  have hg : Tendsto (fun j : ℕ => ‖(1 / ((B j : ℕ) : ℂ)) * S (B j)‖ + r j) atTop (𝓝 0) := by
    simpa using hnorm.add hr_tendsto
  have hgJ := hg.comp hJ_tendsto
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hgJ
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact hbound N hN

/-- Borel-Cantelli along `N = (m+1)^c`. -/
private lemma exists_isNormalInBase_not_isNormalInBase_s7_bc {δ : ℝ} {h : ℤ} {C : ℝ}
    (hv : ∀ N : ℕ, 1 ≤ N →
      ∫⁻ w, ENNReal.ofReal (‖exists_isNormalInBase_not_isNormalInBase_weylAvg
          (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖ ^
              2)
          ∂uniformMeasure
        ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-δ)))
    {c : ℕ} (hcδ : 1 < (c : ℝ) * δ) :
    ∀ᵐ w ∂uniformMeasure, Tendsto (fun m : ℕ => exists_isNormalInBase_not_isNormalInBase_weylAvg
      (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h
        ((m + 1) ^ c)) atTop (𝓝 0) := by
  have key : ∀ ε : ℝ, 0 < ε → ∀ᵐ w ∂uniformMeasure, ∀ᶠ m : ℕ in atTop,
      ‖exists_isNormalInBase_not_isNormalInBase_weylAvg
        (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h
          ((m + 1) ^ c)‖ < ε := by
    intro ε hε
    set s : ℕ → Set CantorSeq := fun m => {w | ε ≤ ‖exists_isNormalInBase_not_isNormalInBase_weylAvg
      (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h
        ((m + 1) ^ c)‖} with hs
    have hb : ∀ m : ℕ, uniformMeasure (s m) ≤
        ENNReal.ofReal (|C| * ((m : ℝ) + 1) ^ (-((c : ℝ) * δ))) / ENNReal.ofReal (ε ^ 2) := by
      intro m
      have hN : 1 ≤ (m + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos m)
      refine (exists_isNormalInBase_not_isNormalInBase_s7_cheb hv hε hN).trans
        (ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal ?_) _)
      have h1 : ((((m + 1) ^ c : ℕ) : ℝ)) ^ (-δ) = ((m : ℝ) + 1) ^ (-((c : ℝ) * δ)) := by
        push_cast
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have hsumm : Summable (fun m : ℕ => |C| * ((m : ℝ) + 1) ^ (-((c : ℝ) * δ))) := by
      have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-((c : ℝ) * δ))) :=
        Real.summable_nat_rpow.2 (by linarith)
      have h2 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-((c : ℝ) * δ))) :=
        (summable_nat_add_iff 1).2 h1
      refine (h2.mul_left |C|).congr (fun m => ?_)
      push_cast
      ring
    have hsum : ∑' m, uniformMeasure (s m) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
      simp_rw [div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right]
      refine ENNReal.mul_ne_top ?_ (ENNReal.inv_ne_top.2 ?_)
      · rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsumm]
        exact ENNReal.ofReal_ne_top
      · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        positivity
    filter_upwards [ae_eventually_notMem hsum] with w hw
    filter_upwards [hw] with m hm
    exact not_le.1 hm
  have key' : ∀ k : ℕ, ∀ᵐ w ∂uniformMeasure, ∀ᶠ m : ℕ in atTop,
      ‖exists_isNormalInBase_not_isNormalInBase_weylAvg
        (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h
          ((m + 1) ^ c)‖ < 1 / ((k : ℝ) + 1) := fun k => key _ (by positivity)
  filter_upwards [ae_all_iff.2 key'] with w hw
  refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  exact (hw k).mono fun m hm => hm.trans hk

/-- Step 7 of the proof of `exists_isNormalInBase_not_isNormalInBase`: Chebyshev and
Borel-Cantelli along `N_j = j^c` (`c δ > 1`).  If `E |A_N|² ≤ C N^{-δ}` for all `N ≥ 1`, where
`A_N = (1/N) ∑_{n<N} e(h 2^n X(w))`, then `A_N → 0` for almost every `w`. -/
private theorem exists_isNormalInBase_not_isNormalInBase_borel_cantelli {δ : ℝ} (hδ : 0 < δ)
    {h : ℤ} {C : ℝ}
    (hv : ∀ N : ℕ, 1 ≤ N →
      ∫⁻ w, ENNReal.ofReal (‖exists_isNormalInBase_not_isNormalInBase_weylAvg
          (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h N‖ ^
              2)
          ∂uniformMeasure
        ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-δ))) :
    ∀ᵐ w ∂uniformMeasure, Tendsto (exists_isNormalInBase_not_isNormalInBase_weylAvg
      (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h)
      atTop (𝓝 0) := by
  obtain ⟨c, hc, hcδ⟩ : ∃ c : ℕ, 1 ≤ c ∧ 1 < (c : ℝ) * δ := by
    refine ⟨⌈1 / δ⌉₊ + 1, by omega, ?_⟩
    have h1 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : 1 ≤ (⌈1 / δ⌉₊ : ℝ) * δ := by
      calc (1 : ℝ) = (1 / δ) * δ := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 hδ.le
    push_cast
    nlinarith
  filter_upwards [exists_isNormalInBase_not_isNormalInBase_s7_bc hv hcδ] with w hw
  exact exists_isNormalInBase_not_isNormalInBase_s7_interp _ h hc hw

/-- **SUV Section 9.3, p. 265**, the unnumbered assertion after Problem 256: "the class of
normal in base `b` reals depends on `b`".  This is an external result [160].  It asserts that
some two bases distinguish a real; it does not assert this for every pair of distinct bases. -/
theorem exists_isNormalInBase_not_isNormalInBase :
    ∃ b c : ℕ, 2 ≤ b ∧ 2 ≤ c ∧ ∃ α : ℝ, IsNormalInBase b α ∧ ¬ IsNormalInBase c α := by
  obtain ⟨δ, hδ, hv⟩ := exists_isNormalInBase_not_isNormalInBase_variance_bound
  have h7 : ∀ᵐ w ∂uniformMeasure, ∀ h : ℤ, h ≠ 0 → Tendsto
      (exists_isNormalInBase_not_isNormalInBase_weylAvg
        (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) h)
      atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro h
    by_cases hh : h = 0
    · exact Filter.Eventually.of_forall fun w hh' => absurd hh hh'
    · obtain ⟨C, hC⟩ := hv h hh
      filter_upwards [exists_isNormalInBase_not_isNormalInBase_borel_cantelli hδ hC] with w hw
        _ using hw
  have h3 := exists_isNormalInBase_not_isNormalInBase_eventually_true_null
  obtain ⟨w, hw7, hw3⟩ := (h7.and (measure_eq_zero_iff_ae_notMem.1 h3)).exists
  refine ⟨2, 3, by decide, by decide, exists_isNormalInBase_not_isNormalInBase_cantorReal w, ?_, ?_⟩
  · exact exists_isNormalInBase_not_isNormalInBase_arcs_normal _ fun a b ha hab hb =>
      exists_isNormalInBase_not_isNormalInBase_weyl_arcs
        (fun n : ℕ => (2 : ℝ) ^ n * exists_isNormalInBase_not_isNormalInBase_cantorReal w) hw7
        ha hab hb
  · exact exists_isNormalInBase_not_isNormalInBase_cantor_not_normal3 w hw3

/-- The doubling map `x ↦ {2x}` of **SUV Problem 257**. -/
noncomputable def doublingMap (x : ℝ) : ℝ := Int.fract (2 * x)

open Classical in
/-- The fraction of the first `N` points of the orbit of `x` under doubling lying in `[a, b)`. -/
noncomputable def orbitFreq (x a b : ℝ) (N : ℕ) : ℝ :=
  (((Finset.range N).filter fun i => a ≤ doublingMap^[i] x ∧ doublingMap^[i] x < b).card : ℝ) / N

private def isNormal_iff_orbit_equidistributed_dyadic_sh (w : CantorSeq) (i : ℕ) :
    CantorSeq :=
  fun j => w (i + j)

private def isNormal_iff_orbit_equidistributed_dyadic_M (w : CantorSeq) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, i => (if w i then 2 ^ k else 0) + isNormal_iff_orbit_equidistributed_dyadic_M w k
                  (i + 1)

private lemma isNormal_iff_orbit_equidistributed_dyadic_geom_summ :
    Summable (fun i : ℕ => (2 : ℝ)⁻¹ ^ (i + 1)) := by
  simp_rw [pow_succ]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _

private lemma isNormal_iff_orbit_equidistributed_dyadic_geom_sum :
    ∑' i : ℕ, (2 : ℝ)⁻¹ ^ (i + 1) = 1 := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

private lemma isNormal_iff_orbit_equidistributed_dyadic_summ (v : CantorSeq) :
    Summable (fun i : ℕ => if v i then (2 : ℝ)⁻¹ ^ (i + 1) else 0) :=
  Summable.of_nonneg_of_le (fun i => by split_ifs <;> positivity)
    (fun i => by split_ifs <;> simp)
    isNormal_iff_orbit_equidistributed_dyadic_geom_summ

private lemma isNormal_iff_orbit_equidistributed_dyadic_nonneg (v : CantorSeq) :
    0 ≤ binaryReal v :=
  tsum_nonneg (fun i => by split_ifs <;> positivity)

private lemma isNormal_iff_orbit_equidistributed_dyadic_lt_one (v : CantorSeq)
    (h : ∃ j, v j = false) : binaryReal v < 1 := by
  obtain ⟨j, hj⟩ := h
  rw [← isNormal_iff_orbit_equidistributed_dyadic_geom_sum]
  refine Summable.tsum_lt_tsum (i := j) (fun i => ?_) ?_
    (isNormal_iff_orbit_equidistributed_dyadic_summ v)
    isNormal_iff_orbit_equidistributed_dyadic_geom_summ
  · split_ifs <;> simp
  · simp [hj]

private lemma isNormal_iff_orbit_equidistributed_dyadic_M_lt (w : CantorSeq) :
    ∀ k i, isNormal_iff_orbit_equidistributed_dyadic_M w k i < 2 ^ k := by
  intro k
  induction k with
  | zero => intro i; simp [isNormal_iff_orbit_equidistributed_dyadic_M]
  | succ k ih =>
    intro i
    have := ih (i + 1)
    simp only [isNormal_iff_orbit_equidistributed_dyadic_M, pow_succ]
    split_ifs <;> omega

private lemma isNormal_iff_orbit_equidistributed_dyadic_succ (v : CantorSeq) :
    binaryReal v = (if v 0 then (2 : ℝ)⁻¹ else 0) + binaryReal (fun j => v (j + 1)) / 2 := by
  unfold binaryReal
  rw [Summable.tsum_eq_zero_add (isNormal_iff_orbit_equidistributed_dyadic_summ v)]
  congr 1
  · simp
  · rw [← tsum_div_const]
    congr 1
    funext j
    split_ifs <;> simp [pow_succ]
    ring

private lemma isNormal_iff_orbit_equidistributed_dyadic_pow (w : CantorSeq) :
    ∀ k i, (2 : ℝ) ^ k * binaryReal (isNormal_iff_orbit_equidistributed_dyadic_sh w i) =
      (isNormal_iff_orbit_equidistributed_dyadic_M w k i : ℝ) +
        binaryReal (isNormal_iff_orbit_equidistributed_dyadic_sh w (i + k)) := by
  intro k
  induction k with
  | zero => intro i; simp [isNormal_iff_orbit_equidistributed_dyadic_M]
  | succ k ih =>
    intro i
    have h1 := isNormal_iff_orbit_equidistributed_dyadic_succ
      (isNormal_iff_orbit_equidistributed_dyadic_sh w i)
    have e : (fun j => isNormal_iff_orbit_equidistributed_dyadic_sh w i (j + 1)) =
        isNormal_iff_orbit_equidistributed_dyadic_sh w (i + 1) := by
      funext j
      simp only [isNormal_iff_orbit_equidistributed_dyadic_sh]
      congr 1; omega
    rw [e] at h1
    have h2 := ih (i + 1)
    have e2 : i + 1 + k = i + (k + 1) := by omega
    rw [e2] at h2
    rw [h1]
    simp only [isNormal_iff_orbit_equidistributed_dyadic_M,
        isNormal_iff_orbit_equidistributed_dyadic_sh,
      add_zero] at *
    push_cast
    split_ifs
    · rw [pow_succ]; linear_combination h2
    · rw [pow_succ]; linear_combination h2

private lemma isNormal_iff_orbit_equidistributed_dyadic_orbit (w : CantorSeq)
    (hf : ∀ i, ∃ j, w (i + j) = false) :
    ∀ i, doublingMap^[i] (binaryReal w) =
      binaryReal (isNormal_iff_orbit_equidistributed_dyadic_sh w i) := by
  intro i
  induction i with
  | zero =>
    have : isNormal_iff_orbit_equidistributed_dyadic_sh w 0 = w := by
      funext j; simp [isNormal_iff_orbit_equidistributed_dyadic_sh]
    simp [this]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    have h1 := isNormal_iff_orbit_equidistributed_dyadic_succ
      (isNormal_iff_orbit_equidistributed_dyadic_sh w i)
    have e : (fun j => isNormal_iff_orbit_equidistributed_dyadic_sh w i (j + 1)) =
        isNormal_iff_orbit_equidistributed_dyadic_sh w (i + 1) := by
      funext j
      simp only [isNormal_iff_orbit_equidistributed_dyadic_sh]
      congr 1; omega
    rw [e] at h1
    have hlt := isNormal_iff_orbit_equidistributed_dyadic_lt_one
      (isNormal_iff_orbit_equidistributed_dyadic_sh w (i + 1)) (by
        obtain ⟨j, hj⟩ := hf (i + 1)
        exact ⟨j, by simpa [isNormal_iff_orbit_equidistributed_dyadic_sh] using hj⟩)
    have hge := isNormal_iff_orbit_equidistributed_dyadic_nonneg
      (isNormal_iff_orbit_equidistributed_dyadic_sh w (i + 1))
    unfold doublingMap
    have e2 : 2 * binaryReal (isNormal_iff_orbit_equidistributed_dyadic_sh w i) =
        (if w i then 1 else 0) + binaryReal (isNormal_iff_orbit_equidistributed_dyadic_sh w
            (i + 1)) := by
      rw [h1]
      simp only [isNormal_iff_orbit_equidistributed_dyadic_sh, add_zero]
      split_ifs <;> ring
    rw [e2]
    split_ifs
    · rw [add_comm, Int.fract_add_one]; exact Int.fract_eq_self.2 ⟨hge, hlt⟩
    · rw [zero_add]; exact Int.fract_eq_self.2 ⟨hge, hlt⟩

open Classical in
private lemma isNormal_iff_orbit_equidistributed_dyadic_false (w : CantorSeq)
    (hn : IsNormal w) :
    ∀ i, ∃ j, w (i + j) = false := by
  intro i
  by_contra hcon
  push Not at hcon
  have h1 := hn [false]
  have h2 : Tendsto (fun N : ℕ => (i : ℝ) / N) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat
      _
  have h3 : ∀ N, occurrenceFreq [false] w N ≤ (i : ℝ) / N := by
    intro N
    unfold occurrenceFreq
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have : (Finset.range N).filter (fun k => OccursAt [false] w k) ⊆ Finset.range i := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      by_contra hki
      have := hk.2 0 (by simp)
      have h5 := hcon (k - i)
      have : w (i + (k - i)) = w k := by congr 1; omega
      simp_all
    have := Finset.card_le_card this
    simpa using (Nat.cast_le (α := ℝ)).2 this
  have := le_of_tendsto_of_tendsto' h1 h2 h3
  norm_num at this

private lemma isNormal_iff_orbit_equidistributed_dyadic_occ_cons (b : Bool) (U : BitString)
    (w : CantorSeq) (i : ℕ) :
    OccursAt (b :: U) w i ↔ w i = b ∧ OccursAt U w (i + 1) := by
  constructor
  · intro h
    refine ⟨h 0 (by simp), fun j hj => ?_⟩
    have := h (j + 1) (by simpa using hj)
    simpa [show i + (j + 1) = i + 1 + j by omega] using this
  · rintro ⟨h1, h2⟩ j hj
    cases j with
    | zero => simpa using h1
    | succ j =>
      have := h2 j (by simpa using hj)
      simpa [show i + (j + 1) = i + 1 + j by omega] using this

private lemma isNormal_iff_orbit_equidistributed_dyadic_string :
    ∀ k m : ℕ, m < 2 ^ k → ∃ U : BitString, U.length = k ∧ ∀ (w : CantorSeq) (i : ℕ),
      (OccursAt U w i ↔ isNormal_iff_orbit_equidistributed_dyadic_M w k i = m) := by
  intro k
  induction k with
  | zero =>
    intro m hm
    refine ⟨[], rfl, fun w i => ?_⟩
    simp only [pow_zero, Nat.lt_one_iff] at hm
    subst hm
    simp [OccursAt, isNormal_iff_orbit_equidistributed_dyadic_M]
  | succ k ih =>
    intro m hm
    by_cases h : 2 ^ k ≤ m
    · obtain ⟨U, hU, hUi⟩ := ih (m - 2 ^ k) (by rw [pow_succ] at hm; omega)
      refine ⟨true :: U, by simp [hU], fun w i => ?_⟩
      rw [isNormal_iff_orbit_equidistributed_dyadic_occ_cons, hUi]
      have := isNormal_iff_orbit_equidistributed_dyadic_M_lt w k (i + 1)
      simp only [isNormal_iff_orbit_equidistributed_dyadic_M]
      cases hwi : w i <;> simp <;> omega
    · obtain ⟨U, hU, hUi⟩ := ih m (by omega)
      refine ⟨false :: U, by simp [hU], fun w i => ?_⟩
      rw [isNormal_iff_orbit_equidistributed_dyadic_occ_cons, hUi]
      have := isNormal_iff_orbit_equidistributed_dyadic_M_lt w k (i + 1)
      simp only [isNormal_iff_orbit_equidistributed_dyadic_M]
      cases hwi : w i <;> simp
      omega

open Classical in
private lemma isNormal_iff_orbit_equidistributed_dyadic_iff (w : CantorSeq)
    (hf : ∀ i, ∃ j, w (i + j) = false) (c d k i : ℕ) :
    ((c : ℝ) / 2 ^ k ≤ doublingMap^[i] (binaryReal w) ∧
      doublingMap^[i] (binaryReal w) < (d : ℝ) / 2 ^ k) ↔
    (c ≤ isNormal_iff_orbit_equidistributed_dyadic_M w k i ∧
      isNormal_iff_orbit_equidistributed_dyadic_M w k i < d) := by
  rw [isNormal_iff_orbit_equidistributed_dyadic_orbit w hf i]
  have h1 := isNormal_iff_orbit_equidistributed_dyadic_pow w k i
  have hlt := isNormal_iff_orbit_equidistributed_dyadic_lt_one
    (isNormal_iff_orbit_equidistributed_dyadic_sh w (i + k)) (by
      obtain ⟨j, hj⟩ := hf (i + k)
      exact ⟨j, by simpa [isNormal_iff_orbit_equidistributed_dyadic_sh] using hj⟩)
  have hge := isNormal_iff_orbit_equidistributed_dyadic_nonneg
    (isNormal_iff_orbit_equidistributed_dyadic_sh w (i + k))
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  set B := binaryReal (isNormal_iff_orbit_equidistributed_dyadic_sh w i)
  set r := binaryReal (isNormal_iff_orbit_equidistributed_dyadic_sh w (i + k))
  set M := isNormal_iff_orbit_equidistributed_dyadic_M w k i
  rw [div_le_iff₀ hp, lt_div_iff₀ hp]
  rw [mul_comm] at h1
  constructor
  · rintro ⟨a, b⟩
    constructor
    · by_contra hc
      have : (M : ℝ) + 1 ≤ c := by exact_mod_cast (by omega : M + 1 ≤ c)
      linarith
    · by_contra hc
      have : (d : ℝ) ≤ M := by exact_mod_cast (by omega : d ≤ M)
      linarith
  · rintro ⟨a, b⟩
    constructor
    · have : (c : ℝ) ≤ M := by exact_mod_cast a
      linarith
    · have : (M : ℝ) + 1 ≤ d := by exact_mod_cast (by omega : M + 1 ≤ d)
      linarith

open Classical in
/-- Step 1 of the proof of `isNormal_iff_orbit_equidistributed`: if a sequence is normal,
then its orbit is equidistributed for intervals of the form `[c/2^k, d/2^k)`. -/
private lemma isNormal_iff_orbit_equidistributed_dyadic (w : CantorSeq) :
    IsNormal w → ∀ c d k : ℕ, c ≤ d → d ≤ 2^k →
      Tendsto (orbitFreq (binaryReal w) (c / 2^k) (d / 2^k)) atTop (𝓝 ((d - c) / 2^k)) := by
  intro hn c d k hcd hd
  have hf := isNormal_iff_orbit_equidistributed_dyadic_false w hn
  have hex : ∀ m : ℕ, ∃ U : BitString, m < 2 ^ k → (U.length = k ∧ ∀ i : ℕ,
      (OccursAt U w i ↔ isNormal_iff_orbit_equidistributed_dyadic_M w k i = m)) := by
    intro m
    by_cases h : m < 2 ^ k
    · obtain ⟨U, hU, hUi⟩ := isNormal_iff_orbit_equidistributed_dyadic_string k m h
      exact ⟨U, fun _ => ⟨hU, fun i => hUi w i⟩⟩
    · exact ⟨[], fun h' => absurd h' h⟩
  choose U hU using hex
  have hsum : ∀ N : ℕ, orbitFreq (binaryReal w) (c / 2 ^ k) (d / 2 ^ k) N =
      ∑ m ∈ Finset.Ico c d, occurrenceFreq (U m) w N := by
    intro N
    unfold orbitFreq occurrenceFreq
    rw [← Finset.sum_div]
    congr 1
    have hs : ((Finset.range N).filter fun i => (c : ℝ) / 2 ^ k ≤ doublingMap^[i] (binaryReal w) ∧
        doublingMap^[i] (binaryReal w) < (d : ℝ) / 2 ^ k) =
        (Finset.range N).filter fun i => c ≤ isNormal_iff_orbit_equidistributed_dyadic_M w k i
                                           ∧
          isNormal_iff_orbit_equidistributed_dyadic_M w k i < d := by
      apply Finset.filter_congr
      intro i _
      exact isNormal_iff_orbit_equidistributed_dyadic_iff w hf c d k i
    rw [hs, Finset.card_eq_sum_card_fiberwise
      (f := fun i => isNormal_iff_orbit_equidistributed_dyadic_M w k i) (t := Finset.Ico c d)
      (fun i hi => by
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hi
        simp only [Finset.coe_Ico, Set.mem_Ico]
        exact hi.2)]
    push_cast
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm' : m < 2 ^ k := lt_of_lt_of_le (Finset.mem_Ico.1 hm).2 hd
    congr 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [(hU m hm').2 i]
    constructor
    · rintro ⟨⟨a, _⟩, b⟩; exact ⟨a, b⟩
    · rintro ⟨a, b⟩
      refine ⟨⟨a, ?_⟩, b⟩
      have := Finset.mem_Ico.1 hm
      omega
  have hlim : Tendsto (fun N : ℕ => ∑ m ∈ Finset.Ico c d, occurrenceFreq (U m) w N) atTop
      (𝓝 (∑ m ∈ Finset.Ico c d, ((2 : ℝ)⁻¹) ^ k)) := by
    refine tendsto_finsetSum _ (fun m hm => ?_)
    have hm' : m < 2 ^ k := lt_of_lt_of_le (Finset.mem_Ico.1 hm).2 hd
    have := hn (U m)
    rwa [(hU m hm').1] at this
  have hval : (∑ m ∈ Finset.Ico c d, ((2 : ℝ)⁻¹) ^ k) = ((d : ℝ) - c) / 2 ^ k := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hcd, inv_pow]
    ring
  rw [hval] at hlim
  exact hlim.congr (fun N => (hsum N).symm)

open Classical in
private lemma isNormal_iff_orbit_equidistributed_arbitrary_mono (x a b a' b' : ℝ)
    (ha : a' ≤ a) (hb : b ≤ b') (N : ℕ) :
    orbitFreq x a b N ≤ orbitFreq x a' b' N := by
  unfold orbitFreq
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (fun i hi => by
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, le_trans ha hi.2.1, lt_of_lt_of_le hi.2.2 hb⟩)

private lemma isNormal_iff_orbit_equidistributed_arbitrary_nonneg (x a b : ℝ) (N : ℕ) :
    0 ≤ orbitFreq x a b N := by
  unfold orbitFreq
  positivity

private lemma isNormal_iff_orbit_equidistributed_arbitrary_real (x : ℝ)
    (h : ∀ c d k : ℕ, c ≤ d → d ≤ 2^k →
      Tendsto (orbitFreq x (c / 2^k) (d / 2^k)) atTop (𝓝 ((d - c) / 2^k)))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (orbitFreq x a b) atTop (𝓝 (b - a)) := by
  rw [tendsto_order]
  have key : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, 4 < ε * 2 ^ k := by
    intro ε hε
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (4 / ε) (by norm_num : (1:ℝ) < 2)
    refine ⟨k, ?_⟩
    rwa [div_lt_iff₀ hε, mul_comm] at hk
  constructor
  · intro r hr
    by_cases hr0 : r < 0
    · exact Filter.Eventually.of_forall fun N =>
        lt_of_lt_of_le hr0 (isNormal_iff_orbit_equidistributed_arbitrary_nonneg x a b N)
    push Not at hr0
    obtain ⟨k, hk⟩ := key (b - a - r) (by linarith)
    have hP : (0:ℝ) < 2 ^ k := by positivity
    have hP1 : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    obtain ⟨c, hc⟩ : ∃ c : ℕ, c = ⌈a * 2 ^ k⌉₊ := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ⌊b * 2 ^ k⌋₊ := ⟨_, rfl⟩
    have h1 : a * 2 ^ k ≤ c := by rw [hc]; exact Nat.le_ceil _
    have h2 : (c : ℝ) < a * 2 ^ k + 1 := by
      rw [hc]; exact Nat.ceil_lt_add_one (by positivity)
    have h3 : (d : ℝ) ≤ b * 2 ^ k := by
      rw [hd]; exact Nat.floor_le (mul_nonneg (ha.trans hab) hP.le)
    have h4 : b * 2 ^ k < d + 1 := by rw [hd]; exact Nat.lt_floor_add_one _
    have hrP : 0 ≤ r * 2 ^ k := mul_nonneg hr0 hP.le
    have hcd : c ≤ d := by
      by_contra hcd
      push Not at hcd
      have : (d : ℝ) + 1 ≤ c := by exact_mod_cast hcd
      nlinarith
    have hd2 : d ≤ 2 ^ k := by
      have : (d : ℝ) ≤ 2 ^ k := by nlinarith
      exact_mod_cast this
    have hT := h c d k hcd hd2
    have hlt : r + (b - a - r) / 2 < ((d : ℝ) - c) / 2 ^ k := by
      rw [lt_div_iff₀ hP]; nlinarith
    have hev := Filter.Tendsto.eventually_const_lt
      (show ((d : ℝ) - c) / 2 ^ k - (b - a - r) / 2 < ((d : ℝ) - c) / 2 ^ k by linarith) hT
    filter_upwards [hev] with N hN
    have hmono := isNormal_iff_orbit_equidistributed_arbitrary_mono x (c / 2 ^ k) (d / 2 ^ k)
      a b (by rw [le_div_iff₀ hP]; exact h1) (by rw [div_le_iff₀ hP]; exact h3) N
    linarith
  · intro r hr
    obtain ⟨k, hk⟩ := key (r - (b - a)) (by linarith)
    have hP : (0:ℝ) < 2 ^ k := by positivity
    obtain ⟨c, hc⟩ : ∃ c : ℕ, c = ⌊a * 2 ^ k⌋₊ := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ⌈b * 2 ^ k⌉₊ := ⟨_, rfl⟩
    have h1 : (c : ℝ) ≤ a * 2 ^ k := by rw [hc]; exact Nat.floor_le (by positivity)
    have h2 : a * 2 ^ k < c + 1 := by rw [hc]; exact Nat.lt_floor_add_one _
    have h3 : b * 2 ^ k ≤ d := by rw [hd]; exact Nat.le_ceil _
    have h4 : (d : ℝ) < b * 2 ^ k + 1 := by
      rw [hd]; exact Nat.ceil_lt_add_one (mul_nonneg (ha.trans hab) hP.le)
    have hcd : c ≤ d := by
      have : (c : ℝ) ≤ d := by nlinarith
      exact_mod_cast this
    have hd2 : d ≤ 2 ^ k := by
      rw [hd]
      refine Nat.ceil_le.2 ?_
      push_cast
      nlinarith
    have hT := h c d k hcd hd2
    have hlt : ((d : ℝ) - c) / 2 ^ k + (r - (b - a)) / 2 < r := by
      have : ((d : ℝ) - c) / 2 ^ k < r - (r - (b - a)) / 2 := by
        rw [div_lt_iff₀ hP]; nlinarith
      linarith
    have hev := Filter.Tendsto.eventually_lt_const
      (show ((d : ℝ) - c) / 2 ^ k < ((d : ℝ) - c) / 2 ^ k + (r - (b - a)) / 2 by linarith) hT
    filter_upwards [hev] with N hN
    have hmono := isNormal_iff_orbit_equidistributed_arbitrary_mono x a b (c / 2 ^ k)
      (d / 2 ^ k) (by rw [div_le_iff₀ hP]; exact h1) (by rw [le_div_iff₀ hP]; exact h3) N
    linarith

/-- Step 2 of the proof of `isNormal_iff_orbit_equidistributed`: using the dyadic
equidistribution, we can approximate any interval `[a, b)` and show equidistribution for all
intervals. -/
private lemma isNormal_iff_orbit_equidistributed_arbitrary (w : CantorSeq) :
    (∀ c d k : ℕ, c ≤ d → d ≤ 2^k →
      Tendsto (orbitFreq (binaryReal w) (c / 2^k) (d / 2^k)) atTop (𝓝 ((d - c) / 2^k))) →
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      Tendsto (orbitFreq (binaryReal w) a b) atTop (𝓝 (b - a)) := by
  intro h a b ha hab hb
  exact isNormal_iff_orbit_equidistributed_arbitrary_real _ h a b ha hab hb

private lemma isNormal_iff_orbit_equidistributed_mpr_summable (v : CantorSeq) :
    Summable (fun i : ℕ => if v i then (2 : ℝ)⁻¹ ^ (i + 1) else 0) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    ((summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_right
      (2 : ℝ)⁻¹)
  · split_ifs <;> positivity
  · rw [pow_succ]
    split_ifs
    · exact le_refl _
    · positivity

private lemma isNormal_iff_orbit_equidistributed_mpr_bounds (v : CantorSeq) :
    0 ≤ binaryReal v ∧ binaryReal v ≤ 1 := by
  refine ⟨tsum_nonneg (fun i => by split_ifs <;> positivity), ?_⟩
  have hg : Summable (fun i : ℕ => (2 : ℝ)⁻¹ ^ (i + 1)) := by
    simpa [pow_succ] using
      (summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_right
        (2 : ℝ)⁻¹
  have h1 : ∑' i : ℕ, (2 : ℝ)⁻¹ ^ (i + 1) = 1 := by
    simp only [pow_succ, tsum_mul_right, tsum_geometric_of_lt_one (r := (2 : ℝ)⁻¹)
      (by norm_num) (by norm_num)]
    norm_num
  calc binaryReal v ≤ ∑' i : ℕ, (2 : ℝ)⁻¹ ^ (i + 1) :=
        Summable.tsum_le_tsum (fun i => by split_ifs <;> simp)
          (isNormal_iff_orbit_equidistributed_mpr_summable v) hg
    _ = 1 := h1

private lemma isNormal_iff_orbit_equidistributed_mpr_rec (v : CantorSeq) :
    binaryReal v = (if v 0 then (2 : ℝ)⁻¹ else 0) + binaryReal (fun j => v (j + 1)) / 2 := by
  unfold binaryReal
  rw [(isNormal_iff_orbit_equidistributed_mpr_summable v).tsum_eq_zero_add]
  have : ∀ i : ℕ, (if v (i + 1) then (2 : ℝ)⁻¹ ^ (i + 1 + 1) else 0)
      = (if v (i + 1) then (2 : ℝ)⁻¹ ^ (i + 1) else 0) / 2 := by
    intro i
    split_ifs
    · rw [pow_succ]; ring
    · simp
  simp_rw [this]
  rw [tsum_div_const]
  simp

private noncomputable def isNormal_iff_orbit_equidistributed_mpr_y (w : CantorSeq) (i : ℕ) :
    ℝ :=
  binaryReal (fun j => w (i + j))

private lemma isNormal_iff_orbit_equidistributed_mpr_y_zero (w : CantorSeq) :
    isNormal_iff_orbit_equidistributed_mpr_y w 0 = binaryReal w := by
  simp [isNormal_iff_orbit_equidistributed_mpr_y]

private lemma isNormal_iff_orbit_equidistributed_mpr_y_rec (w : CantorSeq) (i : ℕ) :
    isNormal_iff_orbit_equidistributed_mpr_y w i
      = (if w i then (2 : ℝ)⁻¹ else 0)
        + isNormal_iff_orbit_equidistributed_mpr_y w (i + 1) / 2 := by
  unfold isNormal_iff_orbit_equidistributed_mpr_y
  rw [isNormal_iff_orbit_equidistributed_mpr_rec]
  have : (fun j => w (i + (j + 1))) = fun j => w (i + 1 + j) := by
    funext j; congr 1; omega
  simp [this]

private lemma isNormal_iff_orbit_equidistributed_mpr_y_bounds (w : CantorSeq) (i : ℕ) :
    0 ≤ isNormal_iff_orbit_equidistributed_mpr_y w i ∧
      isNormal_iff_orbit_equidistributed_mpr_y w i ≤ 1 :=
  isNormal_iff_orbit_equidistributed_mpr_bounds _

private lemma isNormal_iff_orbit_equidistributed_mpr_y_one (w : CantorSeq) (i : ℕ)
    (h : isNormal_iff_orbit_equidistributed_mpr_y w i = 1) :
    isNormal_iff_orbit_equidistributed_mpr_y w (i + 1) = 1 := by
  have h1 := isNormal_iff_orbit_equidistributed_mpr_y_rec w i
  have h2 := isNormal_iff_orbit_equidistributed_mpr_y_bounds w (i + 1)
  split_ifs at h1 <;> linarith [h2.1, h2.2]

private lemma isNormal_iff_orbit_equidistributed_mpr_inv (w : CantorSeq) (i : ℕ) :
    doublingMap^[i] (binaryReal w) = isNormal_iff_orbit_equidistributed_mpr_y w i ∨
      (doublingMap^[i] (binaryReal w) = 0 ∧
        isNormal_iff_orbit_equidistributed_mpr_y w i = 1) := by
  induction i with
  | zero =>
    left
    simp [isNormal_iff_orbit_equidistributed_mpr_y_zero]
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have e : ∀ x : ℝ, doublingMap x = Int.fract (2 * x) := fun x => rfl
    rw [e]
    have hrec := isNormal_iff_orbit_equidistributed_mpr_y_rec w i
    have hb := isNormal_iff_orbit_equidistributed_mpr_y_bounds w (i + 1)
    rcases ih with h | ⟨h0, h1⟩
    · rw [h]
      set k : ℤ := if w i then 1 else 0 with hk
      have hy : 2 * isNormal_iff_orbit_equidistributed_mpr_y w i
          = isNormal_iff_orbit_equidistributed_mpr_y w (i + 1) + (k : ℝ) := by
        rw [hrec, hk]; split_ifs <;> push_cast <;> ring
      rw [hy, Int.fract_add_intCast]
      rcases hb.2.lt_or_eq with hlt | heq
      · left
        exact Int.fract_eq_self.2 ⟨hb.1, hlt⟩
      · right
        rw [heq]
        exact ⟨by simp, rfl⟩
    · right
      refine ⟨by rw [h0]; simp, ?_⟩
      exact isNormal_iff_orbit_equidistributed_mpr_y_one w i h1

private def isNormal_iff_orbit_equidistributed_mpr_val : List Bool → ℕ
  | [] => 0
  | b :: U => (if b then 2 ^ U.length else 0) + isNormal_iff_orbit_equidistributed_mpr_val U

private lemma isNormal_iff_orbit_equidistributed_mpr_val_lt (U : List Bool) :
    isNormal_iff_orbit_equidistributed_mpr_val U < 2 ^ U.length := by
  induction U with
  | nil => simp [isNormal_iff_orbit_equidistributed_mpr_val]
  | cons b U ih =>
    simp only [isNormal_iff_orbit_equidistributed_mpr_val, List.length_cons, pow_succ]
    split_ifs <;> omega

private lemma isNormal_iff_orbit_equidistributed_mpr_occ_cons (w : CantorSeq) (b : Bool)
    (U : List Bool) (i : ℕ) :
    OccursAt (b :: U) w i ↔ w i = b ∧ OccursAt U w (i + 1) := by
  unfold OccursAt
  constructor
  · intro h
    refine ⟨?_, fun j hj => ?_⟩
    · have h0 := h 0 (by simp)
      rw [Nat.add_zero] at h0
      exact h0
    have := h (j + 1) (by simpa using hj)
    simpa [show i + (j + 1) = i + 1 + j by omega] using this
  · rintro ⟨h0, h1⟩ j hj
    cases j with
    | zero => simpa using h0
    | succ j =>
      have := h1 j (by simpa using hj)
      simpa [show i + (j + 1) = i + 1 + j by omega] using this

private lemma isNormal_iff_orbit_equidistributed_mpr_occ_iff (w : CantorSeq)
    (hy : ∀ i, isNormal_iff_orbit_equidistributed_mpr_y w i < 1) (U : List Bool) :
    ∀ i, OccursAt U w i ↔
      ((isNormal_iff_orbit_equidistributed_mpr_val U : ℕ) : ℝ)
          ≤ 2 ^ U.length * isNormal_iff_orbit_equidistributed_mpr_y w i ∧
        2 ^ U.length * isNormal_iff_orbit_equidistributed_mpr_y w i
          < (isNormal_iff_orbit_equidistributed_mpr_val U : ℕ) + 1 := by
  induction U with
  | nil =>
    intro i
    have h0 := (isNormal_iff_orbit_equidistributed_mpr_y_bounds w i).1
    have h1 := hy i
    simp [OccursAt, isNormal_iff_orbit_equidistributed_mpr_val, h0, h1]
  | cons b U ih =>
    intro i
    rw [isNormal_iff_orbit_equidistributed_mpr_occ_cons, ih (i + 1)]
    have hrec := isNormal_iff_orbit_equidistributed_mpr_y_rec w i
    have hb0 := (isNormal_iff_orbit_equidistributed_mpr_y_bounds w (i + 1)).1
    have hb1 := hy (i + 1)
    have hv : ((isNormal_iff_orbit_equidistributed_mpr_val U : ℕ) : ℝ) + 1
        ≤ 2 ^ U.length := by
      exact_mod_cast isNormal_iff_orbit_equidistributed_mpr_val_lt U
    set n := U.length with hn
    set t := (2 : ℝ) ^ n * isNormal_iff_orbit_equidistributed_mpr_y w (i + 1) with ht
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t < 2 ^ n := by
      rw [ht]
      calc (2 : ℝ) ^ n * isNormal_iff_orbit_equidistributed_mpr_y w (i + 1)
          < 2 ^ n * 1 := by gcongr
        _ = 2 ^ n := by ring
    have hy2 : (2 : ℝ) ^ (n + 1) * isNormal_iff_orbit_equidistributed_mpr_y w i
        = 2 ^ n * (if w i then 1 else 0) + t := by
      rw [hrec, ht, pow_succ]
      split_ifs <;> ring
    simp only [isNormal_iff_orbit_equidistributed_mpr_val, List.length_cons]
    rw [hy2, ← hn]
    cases hb : b <;> cases hw : w i <;>
      simp only [true_and, Bool.false_eq_true, ↓reduceIte, zero_add, mul_zero, mul_one,
        Bool.true_eq_false, false_and, false_iff, not_and, not_lt, Nat.cast_add, Nat.cast_pow,
        Nat.cast_ofNat] <;>
      first
      | (intro h; linarith [Nat.cast_nonneg (α := ℝ)
          (isNormal_iff_orbit_equidistributed_mpr_val U)])
      | (constructor <;> intro h <;> constructor <;> linarith [h.1, h.2])

open Classical in
private lemma isNormal_iff_orbit_equidistributed_mpr_caseA (w : CantorSeq)
    (h : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      Tendsto (orbitFreq (binaryReal w) a b) atTop (𝓝 (b - a)))
    (n : ℕ) (hn : isNormal_iff_orbit_equidistributed_mpr_y w n = 1) : False := by
  have hall : ∀ i, n ≤ i → isNormal_iff_orbit_equidistributed_mpr_y w i = 1 := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => exact hn
    | succ i _ ih => exact isNormal_iff_orbit_equidistributed_mpr_y_one w i ih
  have h1 := h (1 / 2) 1 (by norm_num) (by norm_num) le_rfl
  have hbound : ∀ N : ℕ, orbitFreq (binaryReal w) (1 / 2) 1 N ≤ (n : ℝ) / N := by
    intro N
    unfold orbitFreq
    have hsub : (Finset.range N).filter (fun i => (1 / 2 : ℝ) ≤ doublingMap^[i] (binaryReal w) ∧
        doublingMap^[i] (binaryReal w) < 1) ⊆ Finset.range n := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_range]
      by_contra hni
      have hy := hall i (not_lt.1 hni)
      rcases isNormal_iff_orbit_equidistributed_mpr_inv w i with hz | ⟨hz, _⟩
      · rw [hy] at hz
        linarith [hi.2.2]
      · linarith [hi.2.1]
    have hc := Finset.card_le_card hsub
    rw [Finset.card_range] at hc
    gcongr
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (n : ℝ)
  have := le_of_tendsto_of_tendsto' h1 h2 hbound
  norm_num at this

open Classical in
private lemma isNormal_iff_orbit_equidistributed_mpr_caseB (w : CantorSeq)
    (h : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      Tendsto (orbitFreq (binaryReal w) a b) atTop (𝓝 (b - a)))
    (hy : ∀ i, isNormal_iff_orbit_equidistributed_mpr_y w i < 1) : IsNormal w := by
  intro U
  set k := U.length with hk
  set c := isNormal_iff_orbit_equidistributed_mpr_val U with hc
  have hck : (c : ℝ) + 1 ≤ 2 ^ k := by
    exact_mod_cast isNormal_iff_orbit_equidistributed_mpr_val_lt U
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have h1 := h ((c : ℝ) / 2 ^ k) (((c : ℝ) + 1) / 2 ^ k) (by positivity)
    (by gcongr; linarith) (by rw [div_le_one hpos]; exact hck)
  have hfun : orbitFreq (binaryReal w) ((c : ℝ) / 2 ^ k) (((c : ℝ) + 1) / 2 ^ k)
      = occurrenceFreq U w := by
    funext N
    unfold orbitFreq occurrenceFreq
    have : (Finset.range N).filter (fun i => (c : ℝ) / 2 ^ k ≤ doublingMap^[i] (binaryReal w) ∧
        doublingMap^[i] (binaryReal w) < ((c : ℝ) + 1) / 2 ^ k)
        = (Finset.range N).filter (fun i => OccursAt U w i) := by
      apply Finset.filter_congr
      intro i _
      have hz : doublingMap^[i] (binaryReal w)
          = isNormal_iff_orbit_equidistributed_mpr_y w i := by
        rcases isNormal_iff_orbit_equidistributed_mpr_inv w i with hz | ⟨_, hz⟩
        · exact hz
        · exact absurd hz (hy i).ne
      rw [hz, isNormal_iff_orbit_equidistributed_mpr_occ_iff w hy U i,
        div_le_iff₀ hpos, lt_div_iff₀ hpos, mul_comm _ (2 ^ k : ℝ)]
    rw [this]
  rw [hfun, ← sub_div, add_sub_cancel_left, one_div, ← inv_pow] at h1
  exact h1

/-- Step 3 of the proof of `isNormal_iff_orbit_equidistributed`: if the orbit is
equidistributed for all intervals, then the sequence is normal by applying it to dyadic intervals
corresponding to cylinders. -/
private lemma isNormal_iff_orbit_equidistributed_mpr (w : CantorSeq) :
    (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      Tendsto (orbitFreq (binaryReal w) a b) atTop (𝓝 (b - a))) → IsNormal w := by
  intro h
  by_cases hA : ∃ n, isNormal_iff_orbit_equidistributed_mpr_y w n = 1
  · obtain ⟨n, hn⟩ := hA
    exact (isNormal_iff_orbit_equidistributed_mpr_caseA w h n hn).elim
  · push Not at hA
    exact isNormal_iff_orbit_equidistributed_mpr_caseB w h
      (fun i => lt_of_le_of_ne (isNormal_iff_orbit_equidistributed_mpr_y_bounds w i).2 (hA i))

/-- **SUV Problem 257, p. 265.**  `ω` is normal exactly when the orbit of its real under
`x ↦ {2x}` is uniformly distributed in `[0, 1]`.  Half-open intervals are used; the point `1` is
the only real of `[0, 1]` that is not in the range of the fractional part. -/
theorem isNormal_iff_orbit_equidistributed (w : CantorSeq) :
    IsNormal w ↔ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      Tendsto (orbitFreq (binaryReal w) a b) atTop (𝓝 (b - a)) :=
  ⟨fun hw => isNormal_iff_orbit_equidistributed_arbitrary w
               (isNormal_iff_orbit_equidistributed_dyadic w hw),
               isNormal_iff_orbit_equidistributed_mpr w⟩

open Classical in
private def FractEquidist (y : ℕ → ℝ) : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ 1 →
    Tendsto (fun N : ℕ => (((Finset.range N).filter fun i =>
                            a ≤ Int.fract (y i) ∧ Int.fract (y i) < c).card : ℝ) / N) atTop
                            (𝓝 (c - a))

/-- Every `v < b ^ m` is the value of a digit string of length `m` with digits `< b`. -/
private theorem isNormalInBase_mul_exists (b : ℕ) (hb : 2 ≤ b) (m : ℕ) :
    ∀ v : ℕ, v < b ^ m → ∃ U : List ℕ, U.length = m ∧ (∀ d ∈ U, d < b) ∧
      U.foldl (fun acc d => acc * b + d) 0 = v := by
  induction m with
  | zero =>
    intro v hv
    refine ⟨[], rfl, by simp, ?_⟩
    simp at hv
    simp [hv]
  | succ m ih =>
    intro v hv
    have hb0 : 0 < b := by omega
    have hlt : v / b < b ^ m := by
      rw [Nat.div_lt_iff_lt_mul hb0]
      rw [pow_succ] at hv
      exact hv
    obtain ⟨U, h1, h2, h3⟩ := ih (v / b) hlt
    refine ⟨U ++ [v % b], by simp [h1], ?_, ?_⟩
    · intro d hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | hd
      · exact h2 d hd
      · rw [hd]; exact Nat.mod_lt _ hb0
    · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, h3]
      exact Nat.div_add_mod' v b

private theorem isNormalInBase_mul_step1a {b : ℕ} (hb : 2 ≤ b) {α : ℝ} (hα : IsNormalInBase b α)
    (m : ℕ) (v : ℕ) (hv : v < b ^ m) :
    Tendsto (fun N : ℕ => (((Finset.range N).filter fun i =>
                            (v : ℝ) / (b:ℝ)^m ≤ Int.fract ((b:ℝ)^i * α) ∧ Int.fract ((b:ℝ)^i * α) <
                            ((v : ℝ) + 1) / (b:ℝ)^m).card : ℝ) / N) atTop (𝓝 ((b:ℝ)⁻¹^m)) := by
  classical
  obtain ⟨U, hUl, hUb, hUv⟩ := isNormalInBase_mul_exists b hb m v hv
  have hbR : (0 : ℝ) < (b : ℝ) ^ m := by
    have : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    positivity
  have h := hα U hUb
  rw [hUl] at h
  refine Filter.Tendsto.congr (fun N => ?_) h
  unfold digitOccurrenceFreq
  have hfilt : ((Finset.range N).filter fun k => DigitOccursAt b α U k) =
      (Finset.range N).filter fun i => (v : ℝ) / (b:ℝ)^m ≤ Int.fract ((b:ℝ)^i * α) ∧
        Int.fract ((b:ℝ)^i * α) < ((v : ℝ) + 1) / (b:ℝ)^m := by
    ext i
    simp only [Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    rw [exists_isNormalInBase_not_isNormalInBase_s1b_window b hb α U hUb i, hUv, hUl,
      Nat.floor_eq_iff (mul_nonneg hbR.le (Int.fract_nonneg _)),
      div_le_iff₀ hbR, lt_div_iff₀ hbR, mul_comm]
  rw [hfilt]

open Classical in
private lemma isNormalInBase_mul_lower (f : ℕ → ℝ) (B a c : ℝ) (hB : 0 < B) (A C N : ℕ)
    (hA : a ≤ (A : ℝ) / B) (hC : (C : ℝ) / B ≤ c) :
    ∑ v ∈ Finset.Ico A C, (((Finset.range N).filter fun i =>
        (v : ℝ) / B ≤ f i ∧ f i < ((v : ℝ) + 1) / B).card)
      ≤ ((Finset.range N).filter fun i => a ≤ f i ∧ f i < c).card := by
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Ico] at hi ⊢
    obtain ⟨v, ⟨hv1, hv2⟩, hi, h1, h2⟩ := hi
    refine ⟨hi, ?_, ?_⟩
    · have : (A : ℝ) ≤ v := by exact_mod_cast hv1
      have : (A : ℝ) / B ≤ v / B := by gcongr
      linarith
    · have : (v : ℝ) + 1 ≤ C := by exact_mod_cast hv2
      have : ((v : ℝ) + 1) / B ≤ C / B := by gcongr
      linarith
  · intro v _ w _ hvw
    rw [Function.onFun, Finset.disjoint_left]
    intro i hv hw
    simp only [Finset.mem_filter] at hv hw
    rcases lt_or_gt_of_ne hvw with h | h
    · have : (v : ℝ) + 1 ≤ w := by exact_mod_cast h
      have : ((v : ℝ) + 1) / B ≤ w / B := by gcongr
      linarith [hv.2.2, hw.2.1]
    · have : (w : ℝ) + 1 ≤ v := by exact_mod_cast h
      have : ((w : ℝ) + 1) / B ≤ v / B := by gcongr
      linarith [hw.2.2, hv.2.1]

open Classical in
private lemma isNormalInBase_mul_upper (f : ℕ → ℝ) (B a c : ℝ) (hB : 0 < B) (A C N : ℕ)
    (hA : (A : ℝ) / B ≤ a) (hC : c ≤ (C : ℝ) / B) :
    ((Finset.range N).filter fun i => a ≤ f i ∧ f i < c).card
      ≤ ∑ v ∈ Finset.Ico A C, (((Finset.range N).filter fun i =>
        (v : ℝ) / B ≤ f i ∧ f i < ((v : ℝ) + 1) / B).card) := by
  refine le_trans ?_ Finset.card_biUnion_le
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi
  obtain ⟨hi, h1, h2⟩ := hi
  have hf0 : 0 ≤ f i * B := by
    have : 0 ≤ (A : ℝ) / B := by positivity
    have : (0:ℝ) ≤ a := le_trans this hA
    have := le_trans this h1
    positivity
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⌊f i * B⌋₊, ⟨?_, ?_⟩, hi, ?_, ?_⟩
  · apply Nat.le_floor
    rw [div_le_iff₀ hB] at hA
    nlinarith
  · rw [Nat.floor_lt hf0]
    rw [le_div_iff₀ hB] at hC
    nlinarith
  · rw [div_le_iff₀ hB]
    exact Nat.floor_le hf0
  · rw [lt_div_iff₀ hB]
    exact Nat.lt_floor_add_one _

private theorem isNormalInBase_mul_step1b {b : ℕ} (hb : 2 ≤ b) (y : ℕ → ℝ)
    (h_b_adic : ∀ (m v : ℕ), v < b ^ m → Tendsto
        (fun N : ℕ => (((Finset.range N).filter fun i => (v : ℝ) / (b:ℝ)^m ≤ Int.fract (y i) ∧
                                                           Int.fract (y i) < ((v : ℝ) + 1) /
                                                           (b:ℝ)^m).card : ℝ) / N) atTop
                                                           (𝓝 ((b:ℝ)⁻¹^m))) :
    FractEquidist y := by
  intro a c ha hac hc1
  have hb0 : (0:ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1:ℝ) < b := by exact_mod_cast hb
  have hinv0 : (0:ℝ) ≤ (b:ℝ)⁻¹ := by positivity
  have hinv1 : (b:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb1
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hinv0 hinv1
  have hm : ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, 2 * ((b:ℝ)⁻¹ ^ m) < ε := by
    intro ε hε
    obtain ⟨m, hm⟩ := (hpow.eventually (gt_mem_nhds (half_pos hε))).exists
    exact ⟨m, by linarith⟩
  rw [tendsto_order]
  constructor
  · intro a' ha'
    obtain ⟨m, hm⟩ := hm (c - a - a') (by linarith)
    have hB : (0:ℝ) < (b:ℝ)^m := by positivity
    have hr : (0:ℝ) < (b:ℝ)⁻¹ ^ m := by positivity
    have hBr : (b:ℝ)^m * ((b:ℝ)⁻¹ ^ m) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hb0.ne', one_pow]
    have hc0 : 0 ≤ c := le_trans ha hac
    have hcB : 0 ≤ c * (b:ℝ)^m := by positivity
    have haB : 0 ≤ a * (b:ℝ)^m := by positivity
    have hCB : ⌊c * (b:ℝ)^m⌋₊ ≤ b^m := by
      apply Nat.floor_le_of_le
      push_cast
      nlinarith
    have hA : a ≤ ((⌈a * (b:ℝ)^m⌉₊ : ℕ) : ℝ) / (b:ℝ)^m := by
      rw [le_div_iff₀ hB]; exact Nat.le_ceil _
    have hC : ((⌊c * (b:ℝ)^m⌋₊ : ℕ) : ℝ) / (b:ℝ)^m ≤ c := by
      rw [div_le_iff₀ hB]; exact Nat.floor_le hcB
    have hlim : Tendsto (fun N : ℕ => ∑ v ∈ Finset.Ico ⌈a * (b:ℝ)^m⌉₊ ⌊c * (b:ℝ)^m⌋₊,
        (((Finset.range N).filter fun i => (v : ℝ) / (b:ℝ)^m ≤ Int.fract (y i) ∧
          Int.fract (y i) < ((v : ℝ) + 1) / (b:ℝ)^m).card : ℝ) / N) atTop
        (𝓝 (∑ v ∈ Finset.Ico ⌈a * (b:ℝ)^m⌉₊ ⌊c * (b:ℝ)^m⌋₊, (b:ℝ)⁻¹ ^ m)) :=
      tendsto_finsetSum _ (fun v hv => h_b_adic m v
        (lt_of_lt_of_le (Finset.mem_Ico.1 hv).2 hCB))
    have hval : a' < ∑ v ∈ Finset.Ico ⌈a * (b:ℝ)^m⌉₊ ⌊c * (b:ℝ)^m⌋₊, (b:ℝ)⁻¹ ^ m := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have h1 := Nat.lt_floor_add_one (c * (b:ℝ)^m)
      have h2 := Nat.ceil_lt_add_one haB
      have hk : (c - a) * (b:ℝ)^m - 2 ≤
          (((⌊c * (b:ℝ)^m⌋₊ - ⌈a * (b:ℝ)^m⌉₊ : ℕ)) : ℝ) := by
        rcases le_total ⌈a * (b:ℝ)^m⌉₊ ⌊c * (b:ℝ)^m⌋₊ with h | h
        · rw [Nat.cast_sub h]; nlinarith
        · rw [Nat.sub_eq_zero_of_le h]
          have : ((⌊c * (b:ℝ)^m⌋₊ : ℕ) : ℝ) ≤ ((⌈a * (b:ℝ)^m⌉₊ : ℕ) : ℝ) := by
            exact_mod_cast h
          push_cast
          nlinarith
      have h3 := mul_le_mul_of_nonneg_right hk hr.le
      have h4 : ((c - a) * (b:ℝ)^m - 2) * ((b:ℝ)⁻¹ ^ m) = (c - a) - 2 * ((b:ℝ)⁻¹ ^ m) := by
        linear_combination (c - a) * hBr
      linarith
    filter_upwards [hlim.eventually (lt_mem_nhds hval)] with N hN
    refine lt_of_lt_of_le hN ?_
    rw [← Finset.sum_div, ← Nat.cast_sum]
    have hcmp := isNormalInBase_mul_lower (fun i => Int.fract (y i)) _ a c hB _ _ N hA hC
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcmp) (Nat.cast_nonneg N)
  · intro a' ha'
    obtain ⟨m, hm⟩ := hm (a' - (c - a)) (by linarith)
    have hB : (0:ℝ) < (b:ℝ)^m := by positivity
    have hr : (0:ℝ) < (b:ℝ)⁻¹ ^ m := by positivity
    have hBr : (b:ℝ)^m * ((b:ℝ)⁻¹ ^ m) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hb0.ne', one_pow]
    have hc0 : 0 ≤ c := le_trans ha hac
    have hcB : 0 ≤ c * (b:ℝ)^m := by positivity
    have haB : 0 ≤ a * (b:ℝ)^m := by positivity
    have hCB : ⌈c * (b:ℝ)^m⌉₊ ≤ b^m := by
      apply Nat.ceil_le.2
      push_cast
      nlinarith
    have hA : ((⌊a * (b:ℝ)^m⌋₊ : ℕ) : ℝ) / (b:ℝ)^m ≤ a := by
      rw [div_le_iff₀ hB]; exact Nat.floor_le haB
    have hC : c ≤ ((⌈c * (b:ℝ)^m⌉₊ : ℕ) : ℝ) / (b:ℝ)^m := by
      rw [le_div_iff₀ hB]; exact Nat.le_ceil _
    have hlim : Tendsto (fun N : ℕ => ∑ v ∈ Finset.Ico ⌊a * (b:ℝ)^m⌋₊ ⌈c * (b:ℝ)^m⌉₊,
        (((Finset.range N).filter fun i => (v : ℝ) / (b:ℝ)^m ≤ Int.fract (y i) ∧
          Int.fract (y i) < ((v : ℝ) + 1) / (b:ℝ)^m).card : ℝ) / N) atTop
        (𝓝 (∑ v ∈ Finset.Ico ⌊a * (b:ℝ)^m⌋₊ ⌈c * (b:ℝ)^m⌉₊, (b:ℝ)⁻¹ ^ m)) :=
      tendsto_finsetSum _ (fun v hv => h_b_adic m v
        (lt_of_lt_of_le (Finset.mem_Ico.1 hv).2 hCB))
    have hval : ∑ v ∈ Finset.Ico ⌊a * (b:ℝ)^m⌋₊ ⌈c * (b:ℝ)^m⌉₊, (b:ℝ)⁻¹ ^ m < a' := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have h1 := Nat.lt_floor_add_one (a * (b:ℝ)^m)
      have h2 := Nat.ceil_lt_add_one hcB
      have hk : (((⌈c * (b:ℝ)^m⌉₊ - ⌊a * (b:ℝ)^m⌋₊ : ℕ)) : ℝ) ≤
          (c - a) * (b:ℝ)^m + 2 := by
        rcases le_total ⌊a * (b:ℝ)^m⌋₊ ⌈c * (b:ℝ)^m⌉₊ with h | h
        · rw [Nat.cast_sub h]; nlinarith
        · rw [Nat.sub_eq_zero_of_le h]
          push_cast
          nlinarith
      have h3 := mul_le_mul_of_nonneg_right hk hr.le
      have h4 : ((c - a) * (b:ℝ)^m + 2) * ((b:ℝ)⁻¹ ^ m) = (c - a) + 2 * ((b:ℝ)⁻¹ ^ m) := by
        linear_combination (c - a) * hBr
      linarith
    filter_upwards [hlim.eventually (gt_mem_nhds hval)] with N hN
    refine lt_of_le_of_lt ?_ hN
    rw [← Finset.sum_div, ← Nat.cast_sum]
    have hcmp := isNormalInBase_mul_upper (fun i => Int.fract (y i)) _ a c hB _ _ N hA hC
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcmp) (Nat.cast_nonneg N)

private theorem isNormalInBase_mul_step1 {b : ℕ} (hb : 2 ≤ b) {α : ℝ} :
    IsNormalInBase b α → FractEquidist (fun i => (b:ℝ)^i * α) :=
  fun h => isNormalInBase_mul_step1b hb _ (fun m v hv => isNormalInBase_mul_step1a hb h m v hv)

private lemma isNormalInBase_mul_fract (n : ℕ) (y : ℝ) :
    Int.fract ((n:ℝ) * y) = (n:ℝ) * Int.fract y - (⌊(n:ℝ) * Int.fract y⌋₊ : ℝ) := by
  have h0 : 0 ≤ (n:ℝ) * Int.fract y := mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg _)
  have e : (n:ℝ) * y = (n:ℝ) * Int.fract y + ((n * ⌊y⌋ : ℤ) : ℝ) := by
    push_cast
    have := Int.self_sub_floor y
    rw [← this]; ring
  rw [e, Int.fract_add_intCast, Int.fract, ← Int.natCast_floor_eq_floor h0]
  simp

private lemma isNormalInBase_mul_iff {a c : ℝ} (ha : 0 ≤ a) (hc : c ≤ 1) {n : ℕ}
    (hn : 1 ≤ n) (y : ℝ) (j : ℕ) :
    (a ≤ Int.fract ((n:ℝ) * y) ∧ Int.fract ((n:ℝ) * y) < c ∧ ⌊(n:ℝ) * Int.fract y⌋₊ = j) ↔
      ((a + j) / n ≤ Int.fract y ∧ Int.fract y < (c + j) / n) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg _
  have h0 : 0 ≤ (n:ℝ) * Int.fract y := mul_nonneg hn'.le (Int.fract_nonneg _)
  rw [isNormalInBase_mul_fract, div_le_iff₀ hn', lt_div_iff₀ hn']
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [h3] at h1 h2
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    have hfl : ⌊(n:ℝ) * Int.fract y⌋₊ = j := by
      rw [Nat.floor_eq_iff h0]
      constructor <;> nlinarith
    rw [hfl]
    exact ⟨by nlinarith, by nlinarith, rfl⟩

private theorem isNormalInBase_mul_step2 {y : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) :
    FractEquidist y → FractEquidist (fun i => (n:ℝ) * y i) := by
  classical
  intro hy a c ha hac hc
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hcount : ∀ N : ℕ,
      (((Finset.range N).filter fun i => a ≤ Int.fract ((n:ℝ) * y i) ∧
          Int.fract ((n:ℝ) * y i) < c).card : ℝ) / N =
        ∑ j ∈ Finset.range n, (((Finset.range N).filter fun i =>
          (a + j) / n ≤ Int.fract (y i) ∧ Int.fract (y i) < (c + j) / n).card : ℝ) / N := by
    intro N
    rw [← Finset.sum_div]
    congr 1
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun i => ⌊(n:ℝ) * Int.fract (y i)⌋₊)
      (s := (Finset.range N).filter fun i => a ≤ Int.fract ((n:ℝ) * y i) ∧
          Int.fract ((n:ℝ) * y i) < c) (t := Finset.range n) (by
        intro i _
        simp only [Finset.mem_coe, Finset.mem_range]
        rw [Nat.floor_lt (mul_nonneg hn'.le (Int.fract_nonneg _))]
        have := Int.fract_lt_one (y i)
        nlinarith)
    rw [hfib]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    ext i
    simp only [Finset.mem_filter]
    have := isNormalInBase_mul_iff ha hc hn (y i) j
    tauto
  simp_rw [hcount]
  have hlim : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range n, (((Finset.range N).filter fun i =>
          (a + j) / n ≤ Int.fract (y i) ∧ Int.fract (y i) < (c + j) / n).card : ℝ) / N) atTop
        (𝓝 (∑ j ∈ Finset.range n, (((c + j) / n) - ((a + j) / n)))) := by
    refine tendsto_finsetSum _ fun j hj => ?_
    have hj' : (j:ℝ) + 1 ≤ n := by
      have := Finset.mem_range.1 hj
      exact_mod_cast this
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
    apply hy
    · positivity
    · exact div_le_div_of_nonneg_right (by linarith) hn'.le
    · rw [div_le_one hn']; linarith
  convert hlim using 2
  symm
  rw [Finset.sum_congr rfl (fun (j : ℕ) _ => (by ring : (c + (j:ℝ)) / n - (a + (j:ℝ)) / n = (c -
                                                   a) / n))]
  simp
  field_simp

/-- Step 1 of the proof of `isNormalInBase_mul_step3`: the value of a word of digits
`< b` is below `b ^ length`. -/
private lemma isNormalInBase_mul_foldl_lt {b : ℕ} (U : List ℕ)
    (hU : ∀ d ∈ U, d < b) :
    U.foldl (fun acc d => acc * b + d) 0 < b ^ U.length := by
  induction U using List.reverseRecOn with
  | nil => simp
  | append_singleton U d ih =>
    have hd : d < b := hU d (by simp)
    have hU' : ∀ e ∈ U, e < b := fun e he => hU e (by simp [he])
    have h1 := ih hU'
    have hfold : (U ++ [d]).foldl (fun acc e => acc * b + e) 0
        = U.foldl (fun acc e => acc * b + e) 0 * b + d := by
      simp [List.foldl_append]
    have hlen : (U ++ [d]).length = U.length + 1 := by simp
    rw [hfold, hlen, pow_succ]
    generalize U.foldl (fun acc e => acc * b + e) 0 = V at h1 ⊢
    generalize b ^ U.length = P at h1 ⊢
    nlinarith

private theorem isNormalInBase_mul_step3 {b : ℕ} (hb : 2 ≤ b) {α : ℝ} :
    FractEquidist (fun i => (b:ℝ)^i * α) → IsNormalInBase b α := by
  classical
  intro h U hU
  set m := U.length with hm
  set v := U.foldl (fun acc d => acc * b + d) 0 with hv
  have hvlt : v < b ^ m := isNormalInBase_mul_foldl_lt U hU
  have hbpos : (0 : ℝ) < (b : ℝ) ^ m := by
    have : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    positivity
  have hv1 : (v : ℝ) + 1 ≤ (b : ℝ) ^ m := by exact_mod_cast hvlt
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg _
  have ha : 0 ≤ (v : ℝ) / (b : ℝ) ^ m := by positivity
  have hac : (v : ℝ) / (b : ℝ) ^ m ≤ ((v : ℝ) + 1) / (b : ℝ) ^ m :=
    div_le_div_of_nonneg_right (by linarith) hbpos.le
  have hc1 : ((v : ℝ) + 1) / (b : ℝ) ^ m ≤ 1 := by
    rw [div_le_one hbpos]; exact hv1
  have hlim := h _ _ ha hac hc1
  have hdiff : ((v : ℝ) + 1) / (b : ℝ) ^ m - (v : ℝ) / (b : ℝ) ^ m = (b : ℝ)⁻¹ ^ m := by
    rw [← sub_div, inv_pow, add_sub_cancel_left, one_div]
  rw [hdiff] at hlim
  refine hlim.congr fun N => ?_
  unfold digitOccurrenceFreq
  congr 3
  apply Finset.filter_congr
  intro i _
  rw [exists_isNormalInBase_not_isNormalInBase_s1b_window b hb α U hU i]
  have hf0 : 0 ≤ (b : ℝ) ^ m * Int.fract ((b : ℝ) ^ i * α) :=
    mul_nonneg hbpos.le (Int.fract_nonneg _)
  beta_reduce
  rw [Nat.floor_eq_iff hf0, div_le_iff₀ hbpos, lt_div_iff₀ hbpos]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

open Classical in
private lemma isNormalInBase_mul_aux1 {y : ℕ → ℝ} (h : FractEquidist y) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Tendsto (fun N : ℕ => (((Finset.range N).filter fun i => Int.fract (y i) ≤ s).card : ℝ) / N)
      atTop (𝓝 s) := by
  rw [tendsto_order]
  constructor
  · intro a' ha'
    have h1 := h 0 s le_rfl hs0 hs1
    have h2 := (tendsto_order.1 h1).1 a' (by linarith)
    filter_upwards [h2] with N hN
    refine lt_of_lt_of_le hN ?_
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Finset.card_le_card (fun i hi => by
      simp only [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, hi.2.2.le⟩)
  · intro b' hb'
    by_cases hb1 : 1 < b'
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hc : (((Finset.range N).filter fun i => Int.fract (y i) ≤ s).card : ℝ) ≤ N := by
        exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
      have hN' : (0:ℝ) < N := by exact_mod_cast hN
      rw [div_lt_iff₀ hN']
      nlinarith
    · push Not at hb1
      set s' := (s + b') / 2 with hs'
      have hss' : s < s' := by rw [hs']; linarith
      have hs'b : s' < b' := by rw [hs']; linarith
      have h1 := h 0 s' le_rfl (by linarith) (by linarith)
      have h2 := (tendsto_order.1 h1).2 b' (by linarith)
      filter_upwards [h2] with N hN
      refine lt_of_le_of_lt ?_ hN
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast Finset.card_le_card (fun i hi => by
        simp only [Finset.mem_filter] at hi ⊢
        exact ⟨hi.1, Int.fract_nonneg _, lt_of_le_of_lt hi.2 hss'⟩)

open Classical in
private lemma isNormalInBase_mul_aux2 {y : ℕ → ℝ} {a c : ℝ} (hac : a ≤ c) (hc : c ≤ 1) (N : ℕ)
    :
    (((Finset.range N).filter fun i => Int.fract (y i) ≤ 1 - a).card : ℝ)
      - (((Finset.range N).filter fun i => Int.fract (y i) ≤ 1 - c).card : ℝ)
    ≤ (((Finset.range N).filter fun i => a ≤ Int.fract (-y i) ∧ Int.fract (-y i) < c).card : ℝ) ∧
    (((Finset.range N).filter fun i => a ≤ Int.fract (-y i) ∧ Int.fract (-y i) < c).card : ℝ)
    ≤ (((Finset.range N).filter fun i => Int.fract (y i) ≤ 1 - a).card : ℝ)
      - (((Finset.range N).filter fun i => Int.fract (y i) ≤ 1 - c).card : ℝ)
      + (((Finset.range N).filter fun i => Int.fract (y i) ≤ 0).card : ℝ) := by
  set A := (Finset.range N).filter fun i => Int.fract (y i) ≤ 1 - a
  set B := (Finset.range N).filter fun i => Int.fract (y i) ≤ 1 - c
  set Z := (Finset.range N).filter fun i => Int.fract (y i) ≤ 0
  set M := (Finset.range N).filter fun i => a ≤ Int.fract (-y i) ∧ Int.fract (-y i) < c
  have hBA : B ⊆ A := fun i hi => by
    simp only [A, B, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, by linarith [hi.2]⟩
  have hsub1 : A \ B ⊆ M := by
    intro i hi
    simp only [A, B, M, Finset.mem_sdiff, Finset.mem_filter, not_and, not_le] at hi ⊢
    obtain ⟨⟨hr, h1⟩, h2⟩ := hi
    have h2 := h2 hr
    have hne : Int.fract (y i) ≠ 0 := by intro h0; linarith [h0]
    rw [Int.fract_neg hne]
    exact ⟨hr, by linarith, by linarith⟩
  have hsub2 : M ⊆ (A \ B) ∪ Z := by
    intro i hi
    simp only [A, B, M, Z, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, not_and, not_le]
        at hi ⊢
    obtain ⟨hr, h1, h2⟩ := hi
    by_cases h0 : Int.fract (y i) = 0
    · right; exact ⟨hr, h0.le⟩
    · left
      rw [Int.fract_neg h0] at h1 h2
      exact ⟨⟨hr, by linarith⟩, fun _ => by linarith⟩
  have e : ((A \ B).card : ℝ) = (A.card : ℝ) - B.card := by
    rw [Finset.card_sdiff_of_subset hBA, Nat.cast_sub (Finset.card_le_card hBA)]
  constructor
  · rw [← e]; exact_mod_cast Finset.card_le_card hsub1
  · have h1 : M.card ≤ (A \ B).card + Z.card :=
      (Finset.card_le_card hsub2).trans (Finset.card_union_le _ _)
    have h2 : (M.card : ℝ) ≤ (A \ B).card + Z.card := by exact_mod_cast h1
    rw [e] at h2; exact h2

private theorem isNormalInBase_mul_step4 {y : ℕ → ℝ} :
    FractEquidist y → FractEquidist (fun i => - y i) := by
  intro h a c ha hac hc
  have hA := isNormalInBase_mul_aux1 h (s := 1 - a) (by linarith) (by linarith)
  have hB := isNormalInBase_mul_aux1 h (s := 1 - c) (by linarith) (by linarith)
  have hZ := isNormalInBase_mul_aux1 h (s := 0) le_rfl (by norm_num)
  have hlow := hA.sub hB
  have hup := (hA.sub hB).add hZ
  have e1 : (1 - a) - (1 - c) = c - a := by ring
  have e2 : (1 - a) - (1 - c) + 0 = c - a := by ring
  rw [e1] at hlow
  rw [e2] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup ?_ ?_
  · intro N
    simp only [← sub_div]
    exact div_le_div_of_nonneg_right (isNormalInBase_mul_aux2 hac hc N).1 (Nat.cast_nonneg _)
  · intro N
    simp only [← sub_div, ← add_div]
    exact div_le_div_of_nonneg_right (isNormalInBase_mul_aux2 hac hc N).2 (Nat.cast_nonneg _)

private def digitsVal (b : ℕ) (U : List ℕ) : ℕ := U.foldl (fun acc d => acc * b + d) 0

private theorem isNormalInBase_mul_window_lemma2 {b : ℕ} (hb : 2 ≤ b) (m : ℕ) (v : ℕ)
    (hv : v < b ^ m) :
    ∃ U : List ℕ, U.length = m ∧ (∀ d ∈ U, d < b) ∧ digitsVal b U = v := by
  induction m generalizing v with
  | zero =>
    refine ⟨[], rfl, by simp, ?_⟩
    have : v = 0 := by simpa using hv
    subst this
    rfl
  | succ m ih =>
    have hb0 : 0 < b := by omega
    have hdiv : v / b < b ^ m := by
      rw [Nat.div_lt_iff_lt_mul hb0]
      rw [pow_succ] at hv
      exact hv
    obtain ⟨U', hlen, hlt, hval⟩ := ih (v / b) hdiv
    refine ⟨U' ++ [v % b], by simp [hlen], ?_, ?_⟩
    · intro d hd
      rcases List.mem_append.1 hd with h | h
      · exact hlt d h
      · have : d = v % b := by simpa using h
        rw [this]
        exact Nat.mod_lt _ hb0
    · unfold digitsVal at hval ⊢
      rw [List.foldl_append, hval]
      simp only [List.foldl_cons, List.foldl_nil]
      exact Nat.div_add_mod' v b

private theorem isNormalInBase_mul_window_lemma3 {b : ℕ} (_hb : 2 ≤ b) (_α : ℝ) (U : List ℕ)
    (hU : ∀ d ∈ U, d < b) :
    digitsVal b U < b ^ U.length := by
  induction U using List.reverseRecOn with
  | nil => simp [digitsVal]
  | append_singleton U' d ih =>
    have hd : d < b := hU d (by simp)
    have ih' := ih (fun e he => hU e (by simp [he]))
    have e : digitsVal b (U' ++ [d]) = digitsVal b U' * b + d := by
      unfold digitsVal
      rw [List.foldl_append]
      simp
    rw [e, List.length_append, List.length_singleton, pow_succ]
    nlinarith
private theorem isNormalInBase_mul_window {b : ℕ} (hb : 2 ≤ b) (α : ℝ) (U : List ℕ) (hU : ∀ d ∈ U,
    d < b) (p : ℕ) :
    DigitOccursAt b α U p ↔
      (digitsVal b U : ℝ) / (b:ℝ)^U.length ≤ Int.fract ((b:ℝ)^p * α) ∧
      Int.fract ((b:ℝ)^p * α) < ((digitsVal b U : ℝ) + 1) / (b:ℝ)^U.length := by
  rw [exists_isNormalInBase_not_isNormalInBase_s1b_window b hb α U hU p]
  have hpos : (0 : ℝ) < (b:ℝ)^U.length := by
    have : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    positivity
  have hf0 : 0 ≤ Int.fract ((b:ℝ)^p * α) := Int.fract_nonneg _
  rw [show (U.foldl (fun acc d => acc * b + d) 0) = digitsVal b U from rfl,
    Nat.floor_eq_iff (mul_nonneg hpos.le hf0), div_le_iff₀ hpos, lt_div_iff₀ hpos]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- Multiplication by a non-zero integer preserves normality in any base `b ≥ 2`; this is the
general-base form of SUV Problem 258 (see `isNormalInBase_two_mul`). -/
theorem isNormalInBase_mul {b : ℕ} (hb : 2 ≤ b) {α : ℝ} (hα : IsNormalInBase b α)
    {k : ℤ} (hk : k ≠ 0) : IsNormalInBase b ((k : ℝ) * α) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hk)
    have h : FractEquidist (fun i : ℕ => (n:ℝ) * ((b:ℝ)^i * α)) :=
      isNormalInBase_mul_step2 hn (isNormalInBase_mul_step1 hb hα)
    have e : (fun i : ℕ => (n:ℝ) * ((b:ℝ)^i * α)) = fun i => (b:ℝ)^i * (((n:ℤ):ℝ) * α) :=
      funext fun i => by push_cast; ring
    rw [e] at h
    exact isNormalInBase_mul_step3 hb h
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hk)
    have h : FractEquidist (fun i : ℕ => -((n:ℝ) * ((b:ℝ)^i * α))) :=
      isNormalInBase_mul_step4 (isNormalInBase_mul_step2 hn (isNormalInBase_mul_step1 hb hα))
    have e : (fun i : ℕ => -((n:ℝ) * ((b:ℝ)^i * α))) = fun i => (b:ℝ)^i * (((-(n:ℤ):ℤ):ℝ) * α) :=
      funext fun i => by push_cast; ring
    rw [e] at h
    exact isNormalInBase_mul_step3 hb h

/-- **SUV Problem 258, p. 265.**  Multiplication by a non-zero integer preserves normality in base
`2`.  The book says "an integer factor", and the factor `0` has to be excluded: `0` is not
normal. -/
theorem isNormalInBase_two_mul {α : ℝ} (hα : IsNormalInBase 2 α) {k : ℤ} (hk : k ≠ 0) :
    IsNormalInBase 2 ((k : ℝ) * α) :=
  isNormalInBase_mul (by decide) hα hk

open scoped BigOperators

private noncomputable def isNormalInBase_div_int_weylSum (b : ℕ) (α : ℝ) (h : ℤ) (N : ℕ) : ℂ :=
  (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, Complex.exp (2 * ↑Real.pi * Complex.I * (h * (b : ℝ)^n * α :
      ℂ))

/-- Generalised Weyl sum of a real sequence `y`: `(1/N) ∑_{n<N} e(h y_n)`. -/
private noncomputable def isNormalInBase_div_int_weyl_wsum (y : ℕ → ℝ) (h : ℤ) (N : ℕ) : ℂ :=
  (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
    Complex.exp (2 * ↑Real.pi * Complex.I * (((h : ℝ) * y n : ℝ) : ℂ))

private lemma isNormalInBase_div_int_badic_aux_W {b : ℕ} (hb : 2 ≤ b) (α : ℝ)
    (m p : ℕ) :
    isNormalInBase_iff_pow_mp_W b α m p =
      ⌊(b : ℝ) ^ m * Int.fract ((b : ℝ) ^ p * α)⌋₊ := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hbp : (0 : ℝ) < (b : ℝ) ^ p := by positivity
  have hbm : (0 : ℝ) < (b : ℝ) ^ m := by positivity
  have hx0 : 0 ≤ Int.fract α := Int.fract_nonneg α
  have hy0 : 0 ≤ (b : ℝ) ^ p * Int.fract α := by positivity
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊(b : ℝ) ^ p * Int.fract α⌋₊ := ⟨_, rfl⟩
  have hn1 : (n : ℝ) ≤ (b : ℝ) ^ p * Int.fract α := by rw [hn]; exact Nat.floor_le hy0
  have hn2 : (b : ℝ) ^ p * Int.fract α < n + 1 := by rw [hn]; exact Nat.lt_floor_add_one _
  have hf : Int.fract ((b : ℝ) ^ p * α) = (b : ℝ) ^ p * Int.fract α - n := by
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, (b : ℤ) ^ p * ⌊α⌋ + n, ?_⟩
    push_cast
    rw [← Int.self_sub_floor]
    ring
  rw [hf]
  have hf0 : 0 ≤ (b : ℝ) ^ p * Int.fract α - n := by linarith
  have hf1 : (b : ℝ) ^ p * Int.fract α - n < 1 := by linarith
  have hsum : (b : ℝ) ^ (p + m) * Int.fract α =
      (b : ℝ) ^ m * ((b : ℝ) ^ p * Int.fract α - n) + ((b ^ m * n : ℕ) : ℝ) := by
    push_cast; rw [pow_add]; ring
  unfold isNormalInBase_iff_pow_mp_W
  rw [hsum, Nat.floor_add_natCast (mul_nonneg hbm.le hf0), Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  rw [Nat.floor_lt (mul_nonneg hbm.le hf0)]
  push_cast
  nlinarith

private lemma isNormalInBase_div_int_badic_aux_iff {b : ℕ} (hb : 2 ≤ b)
    (α : ℝ) (m p v : ℕ) :
    isNormalInBase_iff_pow_mp_W b α m p = v ↔
      ((v : ℝ) / (b : ℝ) ^ m ≤ Int.fract ((b : ℝ) ^ p * α) ∧
        Int.fract ((b : ℝ) ^ p * α) < ((v : ℝ) + 1) / (b : ℝ) ^ m) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hbm : (0 : ℝ) < (b : ℝ) ^ m := by positivity
  rw [isNormalInBase_div_int_badic_aux_W hb,
    Nat.floor_eq_iff (mul_nonneg hbm.le (Int.fract_nonneg _)), div_le_iff₀ hbm, lt_div_iff₀ hbm]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

private lemma isNormalInBase_div_int_badic_aux_foldl_lt {b : ℕ} (U : List ℕ)
    (hU : ∀ d ∈ U, d < b) :
    U.foldl (fun acc d => acc * b + d) 0 < b ^ U.length := by
  induction U using List.reverseRecOn with
  | nil => simp
  | append_singleton U d ih =>
    have hd : d < b := hU d (by simp)
    have ih' := ih (fun e he => hU e (by simp [he]))
    rw [List.foldl_append, List.length_append]
    simp only [List.foldl_cons, List.foldl_nil, List.length_singleton]
    rw [pow_succ]
    nlinarith

private lemma isNormalInBase_div_int_badic_aux_exists_list {b : ℕ} (hb : 2 ≤ b)
    (m : ℕ) : ∀ v : ℕ, v < b ^ m →
    ∃ U : List ℕ, U.length = m ∧ (∀ d ∈ U, d < b) ∧
      U.foldl (fun acc d => acc * b + d) 0 = v := by
  induction m with
  | zero =>
    intro v hv
    refine ⟨[], rfl, by simp, ?_⟩
    simp at hv
    simp [hv]
  | succ m ih =>
    intro v hv
    have hb0 : 0 < b := by omega
    have hv' : v / b < b ^ m := by
      apply Nat.div_lt_of_lt_mul
      rw [pow_succ'] at hv
      exact hv
    obtain ⟨U, hlen, hlt, hfold⟩ := ih (v / b) hv'
    refine ⟨U ++ [v % b], by simp [hlen], ?_, ?_⟩
    · intro d hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl
      · exact hlt d hd
      · exact Nat.mod_lt _ hb0
    · rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [hfold]
      exact Nat.div_add_mod' v b

/-- Step 1 of the proof of `isNormalInBase_div_int_weyl`: window lemma.  `α` is
normal in base `b` iff the sequence `{b^i α}` visits every `b`-adic interval `[v/b^m, (v+1)/b^m)`
with limit frequency `b^{-m}`. -/
private lemma isNormalInBase_div_int_badic {b : ℕ} (hb : 2 ≤ b) (α : ℝ) :
    IsNormalInBase b α ↔ ∀ m v : ℕ, v < b ^ m →
      Tendsto (fun N : ℕ => (((Finset.range N).filter fun i =>
        (v : ℝ) / (b : ℝ) ^ m ≤ Int.fract ((b : ℝ) ^ i * α) ∧
          Int.fract ((b : ℝ) ^ i * α) < ((v : ℝ) + 1) / (b : ℝ) ^ m).card : ℝ) / N)
        atTop (𝓝 ((b : ℝ)⁻¹ ^ m)) := by
  have hfun : ∀ U : List ℕ, (∀ d ∈ U, d < b) →
      (fun N : ℕ => (((Finset.range N).filter fun i =>
        ((U.foldl (fun acc d => acc * b + d) 0 : ℕ) : ℝ) / (b : ℝ) ^ U.length ≤
            Int.fract ((b : ℝ) ^ i * α) ∧
          Int.fract ((b : ℝ) ^ i * α) <
            (((U.foldl (fun acc d => acc * b + d) 0 : ℕ) : ℝ) + 1) / (b : ℝ) ^ U.length).card : ℝ)
          / N) = digitOccurrenceFreq b α U := by
    intro U hU
    funext N
    unfold digitOccurrenceFreq
    congr 3
    ext i
    simp only [Finset.mem_filter]
    rw [isNormalInBase_iff_pow_window b hb α U U.length i rfl hU,
      isNormalInBase_div_int_badic_aux_iff hb]
  constructor
  · intro hN m v hv
    obtain ⟨U, hlen, hlt, hfold⟩ :=
      isNormalInBase_div_int_badic_aux_exists_list hb m v hv
    subst hlen
    subst hfold
    rw [hfun U hlt]
    exact hN U hlt
  · intro h U hU
    have := h U.length _
      (isNormalInBase_div_int_badic_aux_foldl_lt U hU)
    rw [hfun U hU] at this
    exact this

private lemma isNormalInBase_div_int_wsum_of_badic_aux_dist (θ φ : ℝ) :
    ‖Complex.exp (2 * ↑Real.pi * Complex.I * ((θ : ℝ) : ℂ)) -
      Complex.exp (2 * ↑Real.pi * Complex.I * ((φ : ℝ) : ℂ))‖ ≤ 2 * Real.pi * |θ - φ| := by
  have e : Complex.exp (2 * ↑Real.pi * Complex.I * ((θ : ℝ) : ℂ)) -
      Complex.exp (2 * ↑Real.pi * Complex.I * ((φ : ℝ) : ℂ)) =
      Complex.exp (2 * ↑Real.pi * Complex.I * ((φ : ℝ) : ℂ)) *
        (Complex.exp (Complex.I * ((2 * Real.pi * (θ - φ) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast; ring
  rw [e, norm_mul]
  have h1 : ‖Complex.exp (2 * ↑Real.pi * Complex.I * ((φ : ℝ) : ℂ))‖ = 1 := by
    have : (2 * ↑Real.pi * Complex.I * ((φ : ℝ) : ℂ)) = ((2 * Real.pi * φ : ℝ) : ℂ) * Complex.I :=
        by
      push_cast; ring
    rw [this]; exact Complex.norm_exp_ofReal_mul_I _
  rw [h1, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]

private lemma isNormalInBase_div_int_wsum_of_badic_aux_geom (M : ℕ) (h : ℤ)
    (hh : h ≠ 0) (hM : |h| < M) :
    ∑ v ∈ Finset.range M,
      Complex.exp (2 * ↑Real.pi * Complex.I * (((h : ℝ) * ((v : ℝ) / M) : ℝ) : ℂ)) = 0 := by
  have hM0 : (M : ℂ) ≠ 0 := by
    have : 0 < M := by
      have := abs_nonneg h; omega
    exact_mod_cast this.ne'
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I * ((h : ℂ) / M)) with hζ
  have hterm : ∀ v : ℕ, Complex.exp (2 * ↑Real.pi * Complex.I * (((h : ℝ) * ((v : ℝ) / M) : ℝ) : ℂ))
      = ζ ^ v := by
    intro v
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  simp_rw [hterm]
  have hζM : ζ ^ M = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    have : (M : ℂ) * (2 * ↑Real.pi * Complex.I * ((h : ℂ) / M)) = (h : ℤ) *
        (2 * ↑Real.pi * Complex.I) := by
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [hζ, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have : (h : ℂ) = (n : ℂ) * M := by
      have hpi : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      field_simp at hn
      rw [hn]; ring
    have hz : h = n * M := by exact_mod_cast this
    have : n ≠ 0 := by rintro rfl; rw [Int.zero_mul] at hz; exact hh hz
    have h2 : (1 : ℤ) ≤ |n| := Int.one_le_abs this
    have : |h| = |n| * M := by rw [hz, abs_mul]; simp
    have hMi : (0:ℤ) ≤ M := by positivity
    nlinarith
  rw [geom_sum_eq hζ1, hζM]; simp

/-- Step 2 of the proof of `isNormalInBase_div_int_weyl`: if a real sequence `y`
visits every `b`-adic interval of every level `m` with limit frequency `b^{-m}`, then all its
Weyl sums with `h ≠ 0` tend to `0` (the equidistribution-to-Weyl-sums direction). -/
private lemma isNormalInBase_div_int_wsum_of_badic {b : ℕ} (hb : 2 ≤ b)
    (y : ℕ → ℝ)
    (hy : ∀ m v : ℕ, v < b ^ m →
      Tendsto (fun N : ℕ => (((Finset.range N).filter fun i =>
        (v : ℝ) / (b : ℝ) ^ m ≤ Int.fract (y i) ∧
          Int.fract (y i) < ((v : ℝ) + 1) / (b : ℝ) ^ m).card : ℝ) / N)
        atTop (𝓝 ((b : ℝ)⁻¹ ^ m))) :
    ∀ h : ℤ, h ≠ 0 →
      Tendsto (isNormalInBase_div_int_weyl_wsum y h) atTop (𝓝 0) := by
  intro h hh
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℂ, ∀ t, E t =
      Complex.exp (2 * ↑Real.pi * Complex.I * ((t : ℝ) : ℂ)) := ⟨_, fun _ => rfl⟩
  have hw : ∀ N, isNormalInBase_div_int_weyl_wsum y h N =
      (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, E ((h : ℝ) * y n) := by
    intro N; simp only [isNormalInBase_div_int_weyl_wsum, hE]
  have hdist : ∀ θ φ : ℝ, ‖E θ - E φ‖ ≤ 2 * Real.pi * |θ - φ| := by
    intro θ φ; rw [hE, hE]
    exact isNormalInBase_div_int_wsum_of_badic_aux_dist θ φ
  have hper : ∀ (t : ℝ) (k : ℤ), E (t + k) = E t := by
    intro t k
    rw [hE, hE]
    have : (2 * ↑Real.pi * Complex.I * (((t + k : ℝ)) : ℂ)) =
        2 * ↑Real.pi * Complex.I * (t : ℂ) + (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hgeom : ∀ (M : ℕ), |h| < M →
      ∑ v ∈ Finset.range M, E ((h : ℝ) * ((v : ℝ) / M)) = 0 := by
    intro M hM
    simp only [hE]
    exact isNormalInBase_div_int_wsum_of_badic_aux_geom M h hh hM
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((|h| : ℝ) + 4 * Real.pi * |h| / ε)
    (by exact_mod_cast hb : (1 : ℝ) < b)
  set M : ℕ := b ^ m with hMdef
  have hMR : (M : ℝ) = (b : ℝ) ^ m := by simp [hMdef]
  have hhabs : (0 : ℝ) < |(h : ℝ)| := by simpa using hh
  rw [Int.cast_abs] at hm
  have hpos : (0 : ℝ) < 4 * Real.pi * |(h : ℝ)| / ε := by positivity
  have hM1 : |(h : ℝ)| < M := by rw [hMR]; linarith
  have hM2 : 4 * Real.pi * |(h : ℝ)| / ε < M := by rw [hMR]; linarith [abs_nonneg (h : ℝ)]
  have hMpos : (0 : ℝ) < M := by linarith
  have hM1' : |h| < (M : ℤ) := by
    have : ((|h| : ℤ) : ℝ) < ((M : ℤ) : ℝ) := by push_cast; exact hM1
    exact_mod_cast this
  have hδ : 2 * Real.pi * |(h : ℝ)| / M < ε / 2 := by
    rw [div_lt_iff₀ hMpos]
    rw [div_lt_iff₀ hε] at hM2
    nlinarith
  -- cells
  set cell : ℕ → ℕ := fun n => ⌊(M : ℝ) * Int.fract (y n)⌋₊ with hcell
  have hcellM : ∀ n, cell n < M := by
    intro n
    rw [hcell]; dsimp only
    rw [Nat.floor_lt (by have := Int.fract_nonneg (y n); positivity)]
    have := Int.fract_lt_one (y n)
    nlinarith
  have hcell_le : ∀ n, (cell n : ℝ) ≤ M * Int.fract (y n) := fun n =>
    Nat.floor_le (by have := Int.fract_nonneg (y n); positivity)
  have hcell_lt : ∀ n, M * Int.fract (y n) < (cell n : ℝ) + 1 := fun n =>
    Nat.lt_floor_add_one _
  have hcell_iff : ∀ n v : ℕ, cell n = v ↔
      (v : ℝ) / (b : ℝ) ^ m ≤ Int.fract (y n) ∧
        Int.fract (y n) < ((v : ℝ) + 1) / (b : ℝ) ^ m := by
    intro n v
    rw [← hMR, div_le_iff₀ hMpos, lt_div_iff₀ hMpos, hcell]
    dsimp only
    rw [Nat.floor_eq_iff (by have := Int.fract_nonneg (y n); positivity)]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  -- the cell sums
  set cnt : ℕ → ℕ → ℕ := fun N v => ((Finset.range N).filter fun i => cell i = v).card with hcnt
  have hcnt_tend : ∀ v, v < M → Tendsto (fun N : ℕ => (cnt N v : ℝ) / N) atTop
      (𝓝 ((M : ℝ)⁻¹)) := by
    intro v hv
    have h2 := hy m v hv
    have e : ((b : ℝ)⁻¹) ^ m = (M : ℝ)⁻¹ := by rw [inv_pow, hMR]
    rw [e] at h2
    refine h2.congr (fun N => ?_)
    simp only [hcnt]
    congr 3
    ext i
    simp only [Finset.mem_filter]
    rw [hcell_iff i v]
  set S : ℕ → ℂ := fun N => ∑ v ∈ Finset.range M,
    (((cnt N v : ℝ) / N : ℝ) : ℂ) * E ((h : ℝ) * ((v : ℝ) / M)) with hS
  have hS_tend : Tendsto S atTop (𝓝 0) := by
    have : Tendsto S atTop (𝓝 (∑ v ∈ Finset.range M,
        (((M : ℝ)⁻¹ : ℝ) : ℂ) * E ((h : ℝ) * ((v : ℝ) / M)))) := by
      apply tendsto_finsetSum
      intro v hv
      exact ((Complex.continuous_ofReal.tendsto _).comp
        (hcnt_tend v (Finset.mem_range.mp hv))).mul_const _
    rwa [← Finset.mul_sum, hgeom M hM1', mul_zero] at this
  have hSeq : ∀ N, S N = (1 / (N : ℂ)) *
      ∑ n ∈ Finset.range N, E ((h : ℝ) * ((cell n : ℝ) / M)) := by
    intro N
    have hfib := Finset.sum_fiberwise_of_maps_to (s := Finset.range N) (t := Finset.range M)
      (g := cell) (f := fun n => E ((h : ℝ) * ((cell n : ℝ) / M)))
      (fun n _ => Finset.mem_range.mpr (hcellM n))
    rw [← hfib, hS]
    dsimp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have : ∑ n ∈ (Finset.range N).filter (fun n => cell n = v),
        E ((h : ℝ) * ((cell n : ℝ) / M)) = (cnt N v : ℂ) * E ((h : ℝ) * ((v : ℝ) / M)) := by
      rw [Finset.sum_congr rfl (g := fun _ => E ((h : ℝ) * ((v : ℝ) / M)))
        (fun n hn => by rw [(Finset.mem_filter.mp hn).2])]
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [this]
    push_cast
    ring
  have hbound : ∀ N, ‖isNormalInBase_div_int_weyl_wsum y h N - S N‖ ≤
      2 * Real.pi * |(h : ℝ)| / M := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [isNormalInBase_div_int_weyl_wsum, CharP.cast_eq_zero, div_zero, Finset.range_zero,
        Complex.ofReal_mul, Complex.ofReal_intCast, Finset.sum_empty, mul_zero, hSeq, sub_self,
        norm_zero]
      positivity
    have hterm : ∀ n, ‖E ((h : ℝ) * y n) - E ((h : ℝ) * ((cell n : ℝ) / M))‖ ≤
        2 * Real.pi * |(h : ℝ)| / M := by
      intro n
      have e1 : E ((h : ℝ) * y n) = E ((h : ℝ) * Int.fract (y n)) := by
        have : (h : ℝ) * y n = (h : ℝ) * Int.fract (y n) + ((h * ⌊y n⌋ : ℤ) : ℝ) := by
          rw [← Int.self_sub_floor]; push_cast; ring
        rw [this, hper]
      rw [e1]
      refine (hdist _ _).trans ?_
      have h3 : (cell n : ℝ) / M ≤ Int.fract (y n) := by
        rw [div_le_iff₀ hMpos]; linarith [hcell_le n]
      have h4 : Int.fract (y n) < ((cell n : ℝ) + 1) / M := by
        rw [lt_div_iff₀ hMpos]; linarith [hcell_lt n]
      have h5 : |Int.fract (y n) - (cell n : ℝ) / M| ≤ 1 / M := by
        rw [abs_of_nonneg (by linarith)]
        have : ((cell n : ℝ) + 1) / M = (cell n : ℝ) / M + 1 / M := by ring
        linarith
      calc 2 * Real.pi * |(h : ℝ) * Int.fract (y n) - (h : ℝ) * ((cell n : ℝ) / M)|
          = 2 * Real.pi * (|(h : ℝ)| * |Int.fract (y n) - (cell n : ℝ) / M|) := by
            rw [← abs_mul]; congr 2; ring
        _ ≤ 2 * Real.pi * (|(h : ℝ)| * (1 / M)) := by gcongr
        _ = 2 * Real.pi * |(h : ℝ)| / M := by ring
    rw [hw, hSeq, ← mul_sub, ← Finset.sum_sub_distrib, norm_mul]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have : ‖(1 / (N : ℂ))‖ = 1 / (N : ℝ) := by simp
    rw [this]
    calc 1 / (N : ℝ) * ‖∑ n ∈ Finset.range N, (E ((h : ℝ) * y n) -
          E ((h : ℝ) * ((cell n : ℝ) / M)))‖
        ≤ 1 / (N : ℝ) * (N * (2 * Real.pi * |(h : ℝ)| / M)) := by
          gcongr
          refine (norm_sum_le _ _).trans ?_
          refine (Finset.sum_le_card_nsmul _ _ _ (fun n _ => hterm n)).trans ?_
          simp
      _ = 2 * Real.pi * |(h : ℝ)| / M := by field_simp
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hS_tend (ε / 2) (by positivity)
  refine ⟨N0, fun N hN => ?_⟩
  have h1 := hN0 N hN
  rw [dist_zero_right] at h1 ⊢
  calc ‖isNormalInBase_div_int_weyl_wsum y h N‖
      = ‖(isNormalInBase_div_int_weyl_wsum y h N - S N) + S N‖ := by rw [sub_add_cancel]
    _ ≤ ‖isNormalInBase_div_int_weyl_wsum y h N - S N‖ + ‖S N‖ := norm_add_le _ _
    _ < ε := by linarith [hbound N]

/-- Averages of a trigonometric polynomial along `y` tend to its constant coefficient. -/
private lemma isNormalInBase_div_int_avg_of_wsum_aux_trig_avg (y : ℕ → ℝ)
    (hw : ∀ h : ℤ, h ≠ 0 →
      Tendsto (isNormalInBase_div_int_weyl_wsum y h) atTop (𝓝 0)) (c : ℤ →₀ ℂ) :
    Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
      ∑ h ∈ c.support, c h * Complex.exp (2 * ↑Real.pi * Complex.I * (((h : ℝ) * y n : ℝ) : ℂ)))
      atTop (𝓝 (c 0)) := by
  have hsum : ∀ N : ℕ, (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
      ∑ h ∈ c.support, c h * Complex.exp (2 * ↑Real.pi * Complex.I * (((h : ℝ) * y n : ℝ) : ℂ))
      = ∑ h ∈ c.support, c h * isNormalInBase_div_int_weyl_wsum y h N := by
    intro N
    unfold isNormalInBase_div_int_weyl_wsum
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.mul_sum]; ring
  simp_rw [hsum]
  have h0 : Tendsto (isNormalInBase_div_int_weyl_wsum y 0) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    unfold isNormalInBase_div_int_weyl_wsum
    simp
    have : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
  have key : Tendsto (fun N => ∑ h ∈ c.support, c h * isNormalInBase_div_int_weyl_wsum y h N)
      atTop (𝓝 (∑ h ∈ c.support, c h * (if h = 0 then 1 else 0))) := by
    refine tendsto_finsetSum _ fun h _ => ?_
    by_cases hh : h = 0
    · subst hh; simpa using h0.const_mul (c 0)
    · simpa [hh] using (hw h hh).const_mul (c h)
  convert key using 2
  by_cases h : (0 : ℤ) ∈ c.support
  · simp [Finset.sum_ite_eq' , h]
  · simp [Finset.sum_ite_eq', h, Finsupp.notMem_support_iff.mp h]

/-- The integral over `[0,1]` of a trigonometric polynomial is its constant coefficient. -/
private lemma isNormalInBase_div_int_avg_of_wsum_aux_trig_integral
    (c : ℤ →₀ ℂ) :
    ∫ x in (0 : ℝ)..1, ∑ h ∈ c.support,
      c h * Complex.exp (2 * ↑Real.pi * Complex.I * (((h : ℝ) * x : ℝ) : ℂ)) = c 0 := by
  rw [intervalIntegral.integral_finsetSum]
  · have : ∀ h ∈ c.support, ∫ x in (0 : ℝ)..1,
        c h * Complex.exp (2 * ↑Real.pi * Complex.I * (((h : ℝ) * x : ℝ) : ℂ))
        = c h * (if h = 0 then 1 else 0) := by
      intro h _
      rw [intervalIntegral.integral_const_mul]
      congr 1
      by_cases hh : h = 0
      · subst hh; simp
      · simp only [hh, ite_false]
        have hc : (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) ≠ 0 := by
          simp [Real.pi_ne_zero, hh, Complex.I_ne_zero]
        have := integral_exp_mul_complex (a := 0) (b := 1) hc
        convert this using 3
        · push_cast; ring_nf
        · have e := Complex.exp_int_mul_two_pi_mul_I h
          have e1 : 2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (((1 : ℝ)) : ℂ)
              = (h : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
          rw [e1, e]; simp
    rw [Finset.sum_congr rfl this]
    by_cases h : (0 : ℤ) ∈ c.support
    · simp [Finset.sum_ite_eq', h]
    · simp [Finset.sum_ite_eq', h, Finsupp.notMem_support_iff.mp h]
  · intro h _
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- Uniform approximation of a continuous `1`-periodic complex function by trigonometric
polynomials (`span_fourier_closure_eq_top`). -/
private lemma isNormalInBase_div_int_avg_of_wsum_aux_trig_approx
    (f : ℝ → ℂ) (hf : Continuous f) (hper : ∀ x, f (x + 1) = f x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℤ →₀ ℂ, ∀ x : ℝ, ‖f x - ∑ h ∈ c.support,
      c h * Complex.exp (2 * ↑Real.pi * Complex.I * (((h : ℝ) * x : ℝ) : ℂ))‖ < ε := by
  have : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have hp : Function.Periodic f (1 : ℝ) := hper
  have hcont : Continuous (hp.lift : AddCircle (1 : ℝ) → ℂ) := by
    have := (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff
      (g := (hp.lift : AddCircle (1 : ℝ) → ℂ))
    refine this.mpr ?_
    have e : ((hp.lift : AddCircle (1 : ℝ) → ℂ) ∘ ((↑) : ℝ → AddCircle (1:ℝ))) = f := by
      funext x; simp [Function.Periodic.lift_coe]
    rw [e]; exact hf
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨hp.lift, hcont⟩
  have hmem : F ∈ (Submodule.span ℂ (Set.range (@fourier (1 : ℝ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]; trivial
  obtain ⟨p, hpmem, hdist⟩ := Metric.mem_closure_iff.mp
    (show F ∈ closure (Submodule.span ℂ (Set.range (@fourier (1 : ℝ))) :
      Set C(AddCircle (1 : ℝ), ℂ)) from hmem) ε hε
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hpmem
  refine ⟨c, fun x => ?_⟩
  have hx := (ContinuousMap.dist_lt_iff hε).mp hdist (x : AddCircle (1 : ℝ))
  rw [← hc] at hx
  simp only [Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, fourier_coe_apply, F] at hx
  rw [dist_eq_norm] at hx
  convert hx using 3
  · simp [Function.Periodic.lift_coe]
  · refine Finset.sum_congr rfl fun h _ => ?_
    congr 2
    push_cast; ring

/-- Complex-valued version of Weyl's averaging theorem. -/
private lemma isNormalInBase_div_int_avg_of_wsum_aux_complex (y : ℕ → ℝ)
    (hw : ∀ h : ℤ, h ≠ 0 →
      Tendsto (isNormalInBase_div_int_weyl_wsum y h) atTop (𝓝 0))
    (f : ℝ → ℂ) (hf : Continuous f) (hper : ∀ x, f (x + 1) = f x) :
    Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, f (y n)) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨c, hc⟩ :=
    isNormalInBase_div_int_avg_of_wsum_aux_trig_approx f hf hper (ε / 3)
      (by positivity)
  set p : ℝ → ℂ := fun x => ∑ h ∈ c.support,
    c h * Complex.exp (2 * ↑Real.pi * Complex.I * (((h : ℝ) * x : ℝ) : ℂ)) with hp
  have hpc : Continuous p := by
    rw [hp]; fun_prop
  have hI : ‖(∫ x in (0 : ℝ)..1, f x) - c 0‖ ≤ ε / 3 := by
    rw [← isNormalInBase_div_int_avg_of_wsum_aux_trig_integral c,
      ← intervalIntegral.integral_sub
      (hf.intervalIntegrable _ _) (hpc.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun x => f x - p x) (C := ε / 3) (fun x _ => (hc x).le)
    simpa using this
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp
    (isNormalInBase_div_int_avg_of_wsum_aux_trig_avg y hw c) (ε / 3)
    (by positivity)
  refine ⟨max N1 1, fun N hN => ?_⟩
  have hN1' := hN1 N (le_trans (le_max_left _ _) hN)
  have hNpos : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hA : ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, f (y n) -
      (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, p (y n)‖ ≤ ε / 3 := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul]
    have h1 : ‖∑ n ∈ Finset.range N, (f (y n) - p (y n))‖ ≤ N * (ε / 3) := by
      calc _ ≤ ∑ n ∈ Finset.range N, ‖f (y n) - p (y n)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.range N, (ε / 3) :=
          Finset.sum_le_sum fun n _ => (hc (y n)).le
        _ = N * (ε / 3) := by simp
    have h2 : ‖(1 / (N : ℂ))‖ = 1 / (N : ℝ) := by
      simp [norm_inv]
    rw [h2]
    calc 1 / (N : ℝ) * _ ≤ 1 / (N : ℝ) * (N * (ε / 3)) := by gcongr
      _ = ε / 3 := by field_simp
  rw [dist_eq_norm] at hN1' ⊢
  calc ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, f (y n) - ∫ x in (0 : ℝ)..1, f x‖
      = ‖((1 / (N : ℂ)) * ∑ n ∈ Finset.range N, f (y n) -
          (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, p (y n)) +
        (((1 / (N : ℂ)) * ∑ n ∈ Finset.range N, p (y n) - c 0) -
          ((∫ x in (0 : ℝ)..1, f x) - c 0))‖ := by congr 1; ring
    _ ≤ ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, f (y n) -
          (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, p (y n)‖ +
        (‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, p (y n) - c 0‖ +
          ‖(∫ x in (0 : ℝ)..1, f x) - c 0‖) := by
      refine (norm_add_le _ _).trans ?_
      gcongr
      exact norm_sub_le _ _
    _ < ε := by linarith

/-- Step 3 of the proof of `isNormalInBase_div_int_weyl`: Weyl's averaging theorem.
If all Weyl sums of `y` with `h ≠ 0` tend to `0`, then for every continuous `1`-periodic
`f : ℝ → ℝ` the averages `(1/N) ∑_{n<N} f(y_n)` tend to `∫_0^1 f` (trigonometric polynomials are
uniformly dense: `span_fourier_closure_eq_top`). -/
private lemma isNormalInBase_div_int_avg_of_wsum (y : ℕ → ℝ)
    (hw : ∀ h : ℤ, h ≠ 0 →
      Tendsto (isNormalInBase_div_int_weyl_wsum y h) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : Continuous f) (hper : ∀ x, f (x + 1) = f x) :
    Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, f (y n)) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  have H := isNormalInBase_div_int_avg_of_wsum_aux_complex y hw
    (fun x => (f x : ℂ)) (Complex.continuous_ofReal.comp hf) (fun x => by simp [hper x])
  have H2 := (Complex.continuous_re.tendsto _).comp H
  rw [intervalIntegral.integral_ofReal, Complex.ofReal_re] at H2
  refine H2.congr fun N => ?_
  simp only [Function.comp]
  rw [← Complex.ofReal_re (1 / (N : ℝ) * ∑ n ∈ Finset.range N, f (y n))]
  congr 1
  push_cast; rfl

/-- The ramp `u ↦ max 0 (u - s)`. -/
private def isNormalInBase_div_int_sandwich_ramp (s u : ℝ) : ℝ := max 0 (u - s)

private lemma isNormalInBase_div_int_sandwich_ramp_continuous (s : ℝ) :
    Continuous (isNormalInBase_div_int_sandwich_ramp s) := by
  unfold isNormalInBase_div_int_sandwich_ramp
  exact continuous_const.max (continuous_id.sub continuous_const)

private lemma isNormalInBase_div_int_sandwich_ramp_integral (p q s : ℝ)
    (hps : p ≤ s) (hsq : s ≤ q) :
    ∫ u in p..q, isNormalInBase_div_int_sandwich_ramp s u = (q - s) ^ 2 / 2 := by
  have hc := isNormalInBase_div_int_sandwich_ramp_continuous s
  have h1 : ∫ u in p..s, isNormalInBase_div_int_sandwich_ramp s u = 0 := by
    have : ∫ u in p..s, isNormalInBase_div_int_sandwich_ramp s u
        = ∫ u in p..s, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hps] at hu
      simp only [isNormalInBase_div_int_sandwich_ramp]
      exact max_eq_left (by linarith [hu.2])
    simpa using this
  have h2 : ∫ u in s..q, isNormalInBase_div_int_sandwich_ramp s u
      = (q - s) ^ 2 / 2 := by
    have : ∫ u in s..q, isNormalInBase_div_int_sandwich_ramp s u
        = ∫ u in s..q, (u - s) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hsq] at hu
      simp only [isNormalInBase_div_int_sandwich_ramp]
      exact max_eq_right (by linarith [hu.1])
    rw [this]
    have h3 := intervalIntegral.integral_comp_sub_right (fun u : ℝ => u) (a := s) (b := q) s
    simp only [integral_id] at h3
    rw [h3]; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := s)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), h1, h2, zero_add]

/-- The trapezoid with ramps `[p, p + δ]` and `[r, r + δ]`. -/
private noncomputable def isNormalInBase_div_int_sandwich_trap
    (δ p r u : ℝ) : ℝ :=
  (isNormalInBase_div_int_sandwich_ramp p u
    - isNormalInBase_div_int_sandwich_ramp (p + δ) u
    - isNormalInBase_div_int_sandwich_ramp r u
    + isNormalInBase_div_int_sandwich_ramp (r + δ) u) / δ

private lemma isNormalInBase_div_int_sandwich_trap_continuous (δ p r : ℝ) :
    Continuous (isNormalInBase_div_int_sandwich_trap δ p r) := by
  unfold isNormalInBase_div_int_sandwich_trap
  have := isNormalInBase_div_int_sandwich_ramp_continuous
  exact ((((this p).sub (this (p + δ))).sub (this r)).add (this (r + δ))).div_const _

private lemma isNormalInBase_div_int_sandwich_trap_bounds {δ p r : ℝ}
    (hδ : 0 < δ) (hpr : p + δ ≤ r) (u : ℝ) :
    0 ≤ isNormalInBase_div_int_sandwich_trap δ p r u ∧
    isNormalInBase_div_int_sandwich_trap δ p r u ≤ 1 := by
  unfold isNormalInBase_div_int_sandwich_trap
    isNormalInBase_div_int_sandwich_ramp
  constructor
  · apply div_nonneg _ hδ.le
    simp only [max_def]; split_ifs <;> linarith
  · rw [div_le_one hδ]
    simp only [max_def]; split_ifs <;> linarith

private lemma isNormalInBase_div_int_sandwich_trap_zero {δ p r : ℝ}
    (hδ : 0 < δ) (hpr : p + δ ≤ r) (u : ℝ) (hu : u ≤ p ∨ r + δ ≤ u) :
    isNormalInBase_div_int_sandwich_trap δ p r u = 0 := by
  unfold isNormalInBase_div_int_sandwich_trap
    isNormalInBase_div_int_sandwich_ramp
  rw [div_eq_zero_iff]; left
  simp only [max_def]
  rcases hu with hu | hu <;> split_ifs <;> linarith

private lemma isNormalInBase_div_int_sandwich_trap_one {δ p r : ℝ}
    (hδ : 0 < δ) (u : ℝ) (hu1 : p + δ ≤ u) (hu2 : u ≤ r) :
    isNormalInBase_div_int_sandwich_trap δ p r u = 1 := by
  unfold isNormalInBase_div_int_sandwich_trap
    isNormalInBase_div_int_sandwich_ramp
  rw [div_eq_one_iff_eq hδ.ne']
  simp only [max_def]
  split_ifs <;> linarith

private lemma isNormalInBase_div_int_sandwich_trap_integral {δ p r : ℝ}
    (hδ : 0 < δ) (P Q : ℝ) (hP : P ≤ p) (hpr : p + δ ≤ r) (hQ : r + δ ≤ Q) :
    ∫ u in P..Q, isNormalInBase_div_int_sandwich_trap δ p r u = r - p := by
  have hc := isNormalInBase_div_int_sandwich_ramp_continuous
  have hi : ∀ s, IntervalIntegrable
      (isNormalInBase_div_int_sandwich_ramp s) volume P Q :=
    fun s => (hc s).intervalIntegrable _ _
  unfold isNormalInBase_div_int_sandwich_trap
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add ((((hi p).sub (hi (p + δ))).sub (hi r))) (hi (r + δ)),
    intervalIntegral.integral_sub ((hi p).sub (hi (p + δ))) (hi r),
    intervalIntegral.integral_sub (hi p) (hi (p + δ)),
    isNormalInBase_div_int_sandwich_ramp_integral P Q p hP (by linarith),
    isNormalInBase_div_int_sandwich_ramp_integral P Q (p + δ) (by linarith)
      (by linarith),
    isNormalInBase_div_int_sandwich_ramp_integral P Q r (by linarith)
      (by linarith),
    isNormalInBase_div_int_sandwich_ramp_integral P Q (r + δ) (by linarith)
      (by linarith)]
  field_simp
  ring

private lemma isNormalInBase_div_int_sandwich_periodize (Φ : ℝ → ℝ)
    (hΦ : Continuous Φ) (h01 : Φ 0 = Φ 1) :
    Continuous (fun x => Φ (Int.fract x)) ∧ (∀ x, Φ (Int.fract (x + 1)) = Φ (Int.fract x)) ∧
      ∫ x in (0 : ℝ)..1, Φ (Int.fract x) = ∫ x in (0 : ℝ)..1, Φ x := by
  refine ⟨?_, fun x => by rw [Int.fract_add_one], ?_⟩
  · exact (ContinuousOn.comp_fract'' hΦ.continuousOn h01 :)
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    simp only
    rcases hx.2.eq_or_lt with h | h
    · subst h; simp [h01]
    · rw [Int.fract_eq_self.mpr ⟨hx.1, h⟩]

private lemma isNormalInBase_div_int_sandwich_upper (a c : ℝ) (ha : 0 ≤ a)
    (hac : a ≤ c) (hc : c ≤ 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ G : ℝ → ℝ, Continuous G ∧ (∀ x, G (x + 1) = G x) ∧
      (∀ x, (if a ≤ Int.fract x ∧ Int.fract x < c then (1 : ℝ) else 0) ≤ G x) ∧
      ∫ x in (0 : ℝ)..1, G x = c - a + δ := by
  set ρ := isNormalInBase_div_int_sandwich_trap δ (a - δ) c with hρ
  have hρc : Continuous ρ := isNormalInBase_div_int_sandwich_trap_continuous _ _ _
  have hpr : a - δ + δ ≤ c := by linarith
  have hb := isNormalInBase_div_int_sandwich_trap_bounds hδ hpr
  have hz := isNormalInBase_div_int_sandwich_trap_zero hδ hpr
  have h1 := isNormalInBase_div_int_sandwich_trap_one (δ := δ) (p := a - δ)
    (r := c) hδ
  set Φ : ℝ → ℝ := fun t => ρ t + ρ (t - 1) + ρ (t + 1) with hΦ
  have hΦc : Continuous Φ := by
    have h2 : Continuous fun t : ℝ => ρ (t - 1) := hρc.comp (continuous_id.sub continuous_const)
    have h3 : Continuous fun t : ℝ => ρ (t + 1) := hρc.comp (continuous_id.add continuous_const)
    exact (hρc.add h2).add h3
  have h0 : ρ (0 - 1) = 0 := hz _ (Or.inl (by linarith))
  have h2' : ρ (1 + 1) = 0 := hz _ (Or.inr (by linarith))
  have hΦ01 : Φ 0 = Φ 1 := by
    simp only [hΦ]
    rw [h0, h2']
    have : (0:ℝ) + 1 = 1 := by norm_num
    have : (1:ℝ) - 1 = 0 := by norm_num
    simp [*]
    ring
  obtain ⟨hcont, hper, hint⟩ :=
    isNormalInBase_div_int_sandwich_periodize Φ hΦc hΦ01
  refine ⟨fun x => Φ (Int.fract x), hcont, hper, ?_, ?_⟩
  · intro x
    have hn : ∀ y, 0 ≤ ρ y := fun y => (hb y).1
    have hΦn : ρ (Int.fract x) ≤ Φ (Int.fract x) := by
      simp only [hΦ]
      linarith [hn (Int.fract x - 1), hn (Int.fract x + 1)]
    have hΦ0 : 0 ≤ Φ (Int.fract x) := by
      simp only [hΦ]
      linarith [hn (Int.fract x - 1), hn (Int.fract x + 1), hn (Int.fract x)]
    split_ifs with h
    · rw [← h1 (Int.fract x) (by linarith [h.1]) h.2.le]
      exact hΦn
    · exact hΦ0
  · change ∫ x in (0 : ℝ)..1, Φ (Int.fract x) = _
    rw [hint]
    have hm : Continuous fun t : ℝ => ρ (t - 1) := hρc.comp (continuous_id.sub continuous_const)
    have hp : Continuous fun t : ℝ => ρ (t + 1) := hρc.comp (continuous_id.add continuous_const)
    have e1 : ∫ t in (0 : ℝ)..1, ρ (t - 1) = ∫ t in (-1 : ℝ)..0, ρ t := by
      rw [intervalIntegral.integral_comp_sub_right ρ (a := 0) (b := 1) 1]
      norm_num
    have e2 : ∫ t in (0 : ℝ)..1, ρ (t + 1) = ∫ t in (1 : ℝ)..2, ρ t := by
      rw [intervalIntegral.integral_comp_add_right ρ (a := 0) (b := 1) 1]
      norm_num
    have e3 : ∫ t in (0 : ℝ)..1, Φ t = (∫ t in (0 : ℝ)..1, ρ t) +
        (∫ t in (0 : ℝ)..1, ρ (t - 1)) + ∫ t in (0 : ℝ)..1, ρ (t + 1) := by
      simp only [hΦ]
      rw [intervalIntegral.integral_add
          ((hρc.intervalIntegrable _ _).add (hm.intervalIntegrable _ _))
          (hp.intervalIntegrable _ _),
        intervalIntegral.integral_add (hρc.intervalIntegrable _ _) (hm.intervalIntegrable _ _)]
    have e4 : (∫ t in (-1 : ℝ)..0, ρ t) + (∫ t in (0 : ℝ)..1, ρ t) + (∫ t in (1 : ℝ)..2, ρ t)
        = ∫ t in (-1 : ℝ)..2, ρ t := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hρc.intervalIntegrable _ _)
          (hρc.intervalIntegrable _ _),
        intervalIntegral.integral_add_adjacent_intervals (hρc.intervalIntegrable _ _)
          (hρc.intervalIntegrable _ _)]
    have e5 := isNormalInBase_div_int_sandwich_trap_integral (δ := δ)
      (p := a - δ) (r := c) hδ (-1) 2 (by linarith) hpr (by linarith)
    rw [e3, e1, e2]
    have e6 : ∫ t in (-1 : ℝ)..2, ρ t = c - (a - δ) := e5
    linarith

private lemma isNormalInBase_div_int_sandwich_lower (a c : ℝ) (ha : 0 ≤ a)
    (hc : c ≤ 1) (δ : ℝ) (hδ : 0 < δ) (hac : a + δ + δ ≤ c) :
    ∃ g : ℝ → ℝ, Continuous g ∧ (∀ x, g (x + 1) = g x) ∧
      (∀ x, g x ≤ if a ≤ Int.fract x ∧ Int.fract x < c then (1 : ℝ) else 0) ∧
      ∫ x in (0 : ℝ)..1, g x = c - δ - a := by
  set ρ := isNormalInBase_div_int_sandwich_trap δ a (c - δ) with hρ
  have hρc : Continuous ρ := isNormalInBase_div_int_sandwich_trap_continuous _ _ _
  have hpr : a + δ ≤ c - δ := by linarith
  have hb := isNormalInBase_div_int_sandwich_trap_bounds hδ hpr
  have hz := isNormalInBase_div_int_sandwich_trap_zero hδ hpr
  have h01 : ρ 0 = ρ 1 := by
    have z0 : ρ 0 = 0 := hz 0 (Or.inl ha)
    have z1 : ρ 1 = 0 := hz 1 (Or.inr (by linarith))
    rw [z0, z1]
  obtain ⟨hcont, hper, hint⟩ :=
    isNormalInBase_div_int_sandwich_periodize ρ hρc h01
  refine ⟨fun x => ρ (Int.fract x), hcont, hper, ?_, ?_⟩
  · intro x
    split_ifs with h
    · exact (hb _).2
    · apply le_of_eq
      apply hz
      by_cases h' : a ≤ Int.fract x
      · right
        have : c ≤ Int.fract x := by
          by_contra hlt
          exact h ⟨h', not_le.mp hlt⟩
        linarith
      · left; exact (not_le.mp h').le
  · change ∫ x in (0 : ℝ)..1, ρ (Int.fract x) = _
    rw [hint]
    have := isNormalInBase_div_int_sandwich_trap_integral (δ := δ)
      (p := a) (r := c - δ) hδ 0 1 ha hpr (by linarith)
    rw [this]

/-- Step 4 of the proof of `isNormalInBase_div_int_weyl`: continuous periodic
sandwich of the indicator of `[a, c)` (taken on the fractional part). -/
private lemma isNormalInBase_div_int_sandwich (a c : ℝ) (ha : 0 ≤ a)
    (hac : a ≤ c) (hc : c ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ g G : ℝ → ℝ, Continuous g ∧ Continuous G ∧ (∀ x, g (x + 1) = g x) ∧
      (∀ x, G (x + 1) = G x) ∧
      (∀ x, g x ≤ if a ≤ Int.fract x ∧ Int.fract x < c then (1 : ℝ) else 0) ∧
      (∀ x, (if a ≤ Int.fract x ∧ Int.fract x < c then (1 : ℝ) else 0) ≤ G x) ∧
      c - a - ε ≤ ∫ x in (0 : ℝ)..1, g x ∧ ∫ x in (0 : ℝ)..1, G x ≤ c - a + ε := by
  obtain ⟨G, hGc, hGp, hGge, hGint⟩ :=
    isNormalInBase_div_int_sandwich_upper a c ha hac hc (min (ε / 2) 1)
      (lt_min (by linarith) one_pos) (min_le_right _ _)
  have hδε : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
  by_cases hcase : c - a ≤ ε
  · refine ⟨fun _ => 0, G, continuous_const, hGc, fun _ => rfl, hGp, ?_, hGge, ?_, ?_⟩
    · intro x; split_ifs <;> norm_num
    · simp; linarith
    · rw [hGint]; linarith
  · obtain ⟨g, hgc, hgp, hgle, hgint⟩ :=
      isNormalInBase_div_int_sandwich_lower a c ha hc (ε / 2) (by linarith)
        (by linarith [not_le.mp hcase])
    refine ⟨g, G, hgc, hGc, hgp, hGp, hgle, hGge, ?_, ?_⟩
    · rw [hgint]; linarith
    · rw [hGint]; linarith

/-- Step 5 of the proof of `isNormalInBase_div_int_weyl`: if the averages of every
continuous `1`-periodic function along `y` converge to its integral over `[0,1]`, then `y` is
equidistributed mod `1` (sandwich the indicator functions of the intervals `[a, c)` using step 4).
-/
private lemma isNormalInBase_div_int_equidist_of_avg (y : ℕ → ℝ)
    (hconv : ∀ f : ℝ → ℝ, Continuous f → (∀ x, f (x + 1) = f x) →
      Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, f (y n)) atTop
        (𝓝 (∫ x in (0 : ℝ)..1, f x))) :
    FractEquidist y := by
  intro a c ha hac hc
  have hfreq : ∀ N : ℕ, (((Finset.range N).filter fun i =>
      a ≤ Int.fract (y i) ∧ Int.fract (y i) < c).card : ℝ) / N =
      (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
        (if a ≤ Int.fract (y n) ∧ Int.fract (y n) < c then (1 : ℝ) else 0) := by
    intro N
    rw [Finset.card_filter]
    push_cast
    rw [one_div, inv_mul_eq_div]
  simp only [hfreq]
  rw [tendsto_order]
  constructor
  · intro r hr
    have hε : 0 < (c - a - r) / 2 := by linarith
    obtain ⟨g, G, hg, hG, hgp, hGp, hgi, hGi, hg1, hG1⟩ :=
      isNormalInBase_div_int_sandwich a c ha hac hc ((c - a - r) / 2) hε
    have hlim := hconv g hg hgp
    have hev := (tendsto_order.1 hlim).1 r (by linarith)
    filter_upwards [hev] with N hN
    refine lt_of_lt_of_le hN ?_
    have hN0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) hN0
    exact hgi (y n) |>.trans (by simp)
  · intro r hr
    have hε : 0 < (r - (c - a)) / 2 := by linarith
    obtain ⟨g, G, hg, hG, hgp, hGp, hgi, hGi, hg1, hG1⟩ :=
      isNormalInBase_div_int_sandwich a c ha hac hc ((r - (c - a)) / 2) hε
    have hlim := hconv G hG hGp
    have hev := (tendsto_order.1 hlim).2 r (by linarith)
    filter_upwards [hev] with N hN
    refine lt_of_le_of_lt ?_ hN
    have hN0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) hN0
    exact hGi (y n)

/-- Step 6 of the proof of `isNormalInBase_div_int_weyl`: the Weyl sum of the
statement is the generalised Weyl sum of `n ↦ b^n α`. -/
private lemma isNormalInBase_div_int_wsum_eq (b : ℕ) (α : ℝ) (h : ℤ) :
    isNormalInBase_div_int_weylSum b α h =
      isNormalInBase_div_int_weyl_wsum (fun n => (b : ℝ) ^ n * α) h := by
  unfold isNormalInBase_div_int_weylSum isNormalInBase_div_int_weyl_wsum
  funext N
  push_cast
  simp only [mul_assoc]

/-- Step 1 of the proof of `isNormalInBase_div_int`: Weyl form of normality for b>=2. -/
private lemma isNormalInBase_div_int_weyl {b : ℕ} (hb : 2 ≤ b) (α : ℝ) :
    IsNormalInBase b α ↔ ∀ h : ℤ, h ≠ 0 → Tendsto (isNormalInBase_div_int_weylSum b α h) atTop
        (𝓝 0) := by
  have hw : ∀ h : ℤ, Tendsto (isNormalInBase_div_int_weylSum b α h) atTop (𝓝 0) ↔
      Tendsto (isNormalInBase_div_int_weyl_wsum (fun n => (b : ℝ) ^ n * α) h) atTop
        (𝓝 0) := by
    intro h
    rw [isNormalInBase_div_int_wsum_eq b α h]
  constructor
  · intro hα h hh
    rw [hw]
    exact isNormalInBase_div_int_wsum_of_badic hb _
      ((isNormalInBase_div_int_badic hb α).mp hα) h hh
  · intro hα
    have hFE : FractEquidist (fun n : ℕ => (b : ℝ) ^ n * α) :=
      isNormalInBase_div_int_equidist_of_avg _ fun f hf hper =>
        isNormalInBase_div_int_avg_of_wsum _
          (fun h hh => (hw h).mp (hα h hh)) f hf hper
    rw [isNormalInBase_div_int_badic hb α]
    intro m v hv
    have hbm : (0 : ℝ) < (b : ℝ) ^ m := by
      have : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
      positivity
    have hv' : (v : ℝ) + 1 ≤ (b : ℝ) ^ m := by exact_mod_cast hv
    have := hFE ((v : ℝ) / (b : ℝ) ^ m) (((v : ℝ) + 1) / (b : ℝ) ^ m)
      (by positivity) (by gcongr; linarith) ((div_le_one hbm).mpr hv')
    have e : ((v : ℝ) + 1) / (b : ℝ) ^ m - (v : ℝ) / (b : ℝ) ^ m = (b : ℝ)⁻¹ ^ m := by
      rw [inv_pow]; field_simp; ring
    rwa [e] at this

private lemma isNormalInBase_div_int_vDC_shift (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (N h : ℕ) :
    ‖∑ n ∈ Finset.range N, f (n + h) - ∑ n ∈ Finset.range N, f n‖ ≤ 2 * h := by
  have h1 : ∑ x ∈ Finset.range (h + N), f x
      = ∑ x ∈ Finset.range h, f x + ∑ x ∈ Finset.range N, f (h + x) := Finset.sum_range_add f h N
  have h2 : ∑ x ∈ Finset.range (N + h), f x
      = ∑ x ∈ Finset.range N, f x + ∑ x ∈ Finset.range h, f (N + x) := Finset.sum_range_add f N h
  have h3 : ∑ n ∈ Finset.range N, f (n + h) = ∑ x ∈ Finset.range N, f (h + x) :=
    Finset.sum_congr rfl (fun n _ => by rw [add_comm])
  rw [add_comm h N] at h1
  have e : ∑ n ∈ Finset.range N, f (n + h) - ∑ n ∈ Finset.range N, f n
      = ∑ x ∈ Finset.range h, f (N + x) - ∑ x ∈ Finset.range h, f x := by
    rw [h3]; linear_combination h2 - h1
  rw [e]
  have hb : ∀ g : ℕ → ℂ, (∀ n, ‖g n‖ ≤ 1) → ‖∑ x ∈ Finset.range h, g x‖ ≤ h := by
    intro g hg
    calc ‖∑ x ∈ Finset.range h, g x‖ ≤ ∑ x ∈ Finset.range h, ‖g x‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ Finset.range h, (1:ℝ) := Finset.sum_le_sum (fun x _ => hg x)
      _ = h := by simp
  have := norm_sub_le (∑ x ∈ Finset.range h, f (N + x)) (∑ x ∈ Finset.range h, f x)
  have a1 := hb (fun x => f (N + x)) (fun n => hf _)
  have a2 := hb f hf
  linarith

private lemma isNormalInBase_div_int_vDC_bound (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ ≤ 1) (H N : ℕ) :
    (H * ‖∑ m ∈ Finset.range N, u m‖)^2 ≤
      2 * N * (H * N + H^2 * (∑ s ∈ Finset.range H,
        ‖∑ m ∈ Finset.range N, u (m + (s+1)) * starRingEnd ℂ (u m)‖ + 2 * H)) + 8 * H^4 := by
  set C : ℝ := ∑ s ∈ Finset.range H,
        ‖∑ m ∈ Finset.range N, u (m + (s+1)) * starRingEnd ℂ (u m)‖ with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hc : ∀ s, 1 ≤ s → s ≤ H →
      ‖∑ m ∈ Finset.range N, u (m + s) * starRingEnd ℂ (u m)‖ ≤ C := by
    intro s hs1 hsH
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s-1, by omega⟩
    exact Finset.single_le_sum (f := fun s => ‖∑ m ∈ Finset.range N, u (m + (s+1)) * starRingEnd ℂ
        (u m)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  have hD1 : ∀ h h', h' < h → h < H →
      ‖∑ n ∈ Finset.range N, u (n + h) * starRingEnd ℂ (u (n + h'))‖ ≤ C + 2 * H := by
    intro h h' hlt hH'
    obtain ⟨s, rfl⟩ : ∃ s, h = h' + s := ⟨h - h', by omega⟩
    have hs : 1 ≤ s := by omega
    set f : ℕ → ℂ := fun m => u (m + s) * starRingEnd ℂ (u m) with hf
    have hfb : ∀ n, ‖f n‖ ≤ 1 := by
      intro n
      simp only [hf, norm_mul, Complex.norm_conj]
      calc ‖u (n+s)‖ * ‖u n‖ ≤ 1 * 1 :=
            mul_le_mul (hu _) (hu _) (norm_nonneg _) zero_le_one
        _ = 1 := by norm_num
    have e : ∑ n ∈ Finset.range N, u (n + (h' + s)) * starRingEnd ℂ (u (n + h'))
        = ∑ n ∈ Finset.range N, f (n + h') := by
      apply Finset.sum_congr rfl; intro n _; simp only [hf]; rw [add_assoc]
    rw [e]
    have h1 := isNormalInBase_div_int_vDC_shift f hfb N h'
    have h2 := norm_sub_norm_le (∑ n ∈ Finset.range N, f (n + h')) (∑ n ∈ Finset.range N, f n)
    have h3 := hc s hs (by omega)
    have h4 : (h' : ℝ) ≤ H := by exact_mod_cast (by omega : h' ≤ H)
    simp only [hf] at h2 h3 ⊢
    linarith
  have hD : ∀ h h', h < H → h' < H → h ≠ h' →
      ‖∑ n ∈ Finset.range N, u (n + h) * starRingEnd ℂ (u (n + h'))‖ ≤ C + 2 * H := by
    intro h h' hh hh' hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hD1 h' h hlt hh'
      have e : ∑ n ∈ Finset.range N, u (n + h) * starRingEnd ℂ (u (n + h'))
          = starRingEnd ℂ (∑ n ∈ Finset.range N, u (n + h') * starRingEnd ℂ (u (n + h))) := by
        simp [map_sum, mul_comm]
      rw [e, Complex.norm_conj]; exact this
    · exact hD1 h h' hlt hh
  have hDd : ∀ h, ‖∑ n ∈ Finset.range N, u (n + h) * starRingEnd ℂ (u (n + h))‖ ≤ N := by
    intro h
    calc _ ≤ ∑ n ∈ Finset.range N, ‖u (n + h) * starRingEnd ℂ (u (n + h))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N, (1:ℝ) := by
        apply Finset.sum_le_sum; intro n _
        rw [norm_mul, Complex.norm_conj]
        calc ‖u (n+h)‖ * ‖u (n+h)‖ ≤ 1 * 1 :=
              mul_le_mul (hu _) (hu _) (norm_nonneg _) zero_le_one
          _ = 1 := by norm_num
      _ = N := by simp
  set T : ℕ → ℂ := fun n => ∑ h ∈ Finset.range H, u (n + h) with hT
  have hsq : ((∑ n ∈ Finset.range N, ‖T n‖^2 : ℝ) : ℂ)
      = ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ∑ n ∈ Finset.range N, u (n+h) * starRingEnd ℂ (u (n+h')) := by
    have key : ∀ n, ((‖T n‖^2 : ℝ) : ℂ) = T n * starRingEnd ℂ (T n) := fun n => by
      push_cast; exact (Complex.mul_conj' _).symm
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun n _ => key n)]
    simp only [hT, map_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro h _
    rw [Finset.sum_comm]
  have hTsum : ∑ n ∈ Finset.range N, ‖T n‖^2 ≤ H * N + H^2 * (C + 2 * H) := by
    have h0 : 0 ≤ ∑ n ∈ Finset.range N, ‖T n‖^2 :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have h1 : ∑ n ∈ Finset.range N, ‖T n‖^2 = ‖((∑ n ∈ Finset.range N, ‖T n‖^2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg h0]
    rw [h1, hsq]
    calc _ ≤ ∑ h ∈ Finset.range H, ‖∑ h' ∈ Finset.range H,
          ∑ n ∈ Finset.range N, u (n+h) * starRingEnd ℂ (u (n+h'))‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ‖∑ n ∈ Finset.range N, u (n+h) * starRingEnd ℂ (u (n+h'))‖ :=
          Finset.sum_le_sum (fun h _ => norm_sum_le _ _)
      _ ≤ ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ((if h = h' then (N:ℝ) else 0) + (C + 2 * H)) := by
          apply Finset.sum_le_sum; intro h hh
          apply Finset.sum_le_sum; intro h' hh'
          rw [Finset.mem_range] at hh hh'
          by_cases hne : h = h'
          · subst hne
            have := hDd h
            simp only [ite_true]
            linarith [hC0, (Nat.cast_nonneg H : (0:ℝ) ≤ H)]
          · simp only [hne, ite_false, zero_add]
            exact hD h h' hh hh' hne
      _ = H * N + H^2 * (C + 2 * H) := by
          have : ∀ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
              ((if h = h' then (N:ℝ) else 0) + (C + 2 * H)) = N + H * (C + 2 * H) := by
            intro h hh
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left hh]
            simp
            ring
          rw [Finset.sum_congr rfl this]
          simp
          ring
  -- shift comparison
  have hshift : (H:ℝ) * ‖∑ m ∈ Finset.range N, u m‖ ≤ ‖∑ n ∈ Finset.range N, T n‖ + 2 * H^2 := by
    have e : (H:ℂ) * ∑ m ∈ Finset.range N, u m - ∑ n ∈ Finset.range N, T n
        = ∑ h ∈ Finset.range H, (∑ m ∈ Finset.range N, u m - ∑ n ∈ Finset.range N, u (n + h)) := by
      simp only [hT]
      rw [Finset.sum_comm, Finset.sum_sub_distrib]
      simp
    have hb : ‖(H:ℂ) * ∑ m ∈ Finset.range N, u m - ∑ n ∈ Finset.range N, T n‖ ≤ 2 * H^2 := by
      rw [e]
      calc _ ≤ ∑ h ∈ Finset.range H, ‖∑ m ∈ Finset.range N, u m - ∑ n ∈ Finset.range N,
          u (n + h)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ h ∈ Finset.range H, (2 * (H:ℝ)) := by
            apply Finset.sum_le_sum; intro h hh
            rw [Finset.mem_range] at hh
            rw [norm_sub_rev]
            have := isNormalInBase_div_int_vDC_shift u hu N h
            have h4 : (h : ℝ) ≤ H := by exact_mod_cast hh.le
            linarith
        _ = 2 * H^2 := by simp; ring
    have := norm_sub_norm_le ((H:ℂ) * ∑ m ∈ Finset.range N, u m) (∑ n ∈ Finset.range N, T n)
    rw [norm_mul, Complex.norm_natCast] at this
    linarith
  -- Cauchy-Schwarz
  have hCS : ‖∑ n ∈ Finset.range N, T n‖^2 ≤ N * ∑ n ∈ Finset.range N, ‖T n‖^2 := by
    have h1 : ‖∑ n ∈ Finset.range N, T n‖ ≤ ∑ n ∈ Finset.range N, ‖T n‖ := norm_sum_le _ _
    have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := fun n => ‖T n‖)
    simp only [Finset.card_range] at h2
    calc _ ≤ (∑ n ∈ Finset.range N, ‖T n‖)^2 := by gcongr
      _ ≤ _ := h2
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  set a := ‖∑ n ∈ Finset.range N, T n‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hA0 : 0 ≤ (H:ℝ) * ‖∑ m ∈ Finset.range N, u m‖ := by positivity
  have h5 : ((H:ℝ) * ‖∑ m ∈ Finset.range N, u m‖)^2 ≤ (a + 2 * H^2)^2 :=
    pow_le_pow_left₀ hA0 hshift 2
  have h6 : a^2 ≤ N * (H * N + H^2 * (C + 2 * H)) :=
    hCS.trans (mul_le_mul_of_nonneg_left hTsum hN)
  nlinarith [sq_nonneg (a - 2 * (H:ℝ)^2)]

/-- Step 2 of the proof of `isNormalInBase_div_int`: van der Corput lemma. -/
private lemma isNormalInBase_div_int_vDC (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ ≤ 1) :
    (∀ s ≥ 1, Tendsto (fun M : ℕ => (1 / (M : ℂ)) * ∑ m ∈ Finset.range M, u (m + s) * starRingEnd ℂ
        (u m)) atTop (𝓝 0)) →
    Tendsto (fun M : ℕ => (1 / (M : ℂ)) * ∑ m ∈ Finset.range M, u m) atTop (𝓝 0) := by
  intro hs
  have hn : ∀ (M : ℕ) (z : ℂ), ‖(1 / (M:ℂ)) * z‖ = ‖z‖ / M := by
    intro M z
    rw [norm_mul, one_div, norm_inv, Complex.norm_natCast]
    ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [hn]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨H, hH⟩ := exists_nat_gt (4 / ε^2)
  have hε2 : 0 < ε^2 := by positivity
  have hH0 : 0 < (H:ℝ) := lt_trans (by positivity) hH
  have hH4 : 4 < ε^2 * H := by
    rw [div_lt_iff₀ hε2] at hH; linarith
  set C : ℕ → ℝ := fun N => ∑ s ∈ Finset.range H,
        ‖∑ m ∈ Finset.range N, u (m + (s+1)) * starRingEnd ℂ (u m)‖ with hC
  have hC0 : ∀ N, 0 ≤ C N := fun N => Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hCt : Tendsto (fun N : ℕ => C N / N) atTop (𝓝 0) := by
    have : ∀ N : ℕ, C N / N = ∑ s ∈ Finset.range H,
        ‖∑ m ∈ Finset.range N, u (m + (s+1)) * starRingEnd ℂ (u m)‖ / N := fun N => by
      simp only [hC, Finset.sum_div]
    simp only [this]
    have h2 : Tendsto (fun N : ℕ => ∑ s ∈ Finset.range H,
        ‖∑ m ∈ Finset.range N, u (m + (s+1)) * starRingEnd ℂ (u m)‖ / N) atTop
        (𝓝 (∑ s ∈ Finset.range H, (0:ℝ))) := by
      apply tendsto_finsetSum
      intro s _
      have := (tendsto_zero_iff_norm_tendsto_zero.1 (hs (s+1) (by omega)))
      simpa only [hn] using this
    simpa using h2
  set G : ℕ → ℝ := fun N => 2 * (C N / N) + (4 * H + 8 * H^2) / N with hG
  have hGt : Tendsto G atTop (𝓝 0) := by
    have := (hCt.const_mul 2).add (tendsto_const_div_atTop_nhds_zero_nat (4 * (H:ℝ) + 8 * H^2))
    simpa using this
  have hev := (hGt.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε^2/2))).and
    (eventually_ge_atTop 1)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hGN, hN1⟩ := hN0 N hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  set A := ‖∑ m ∈ Finset.range N, u m‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  have hb := isNormalInBase_div_int_vDC_bound u hu H N
  have key : (A / N)^2 ≤ 2 / H + G N := by
    have e1 : (A / N)^2 = ((H:ℝ) * A)^2 / (H^2 * N^2) := by field_simp
    have e2 : (2 * (N:ℝ) * (H * N + H^2 * (C N + 2 * H)) + 8 * H^4) / (H^2 * N^2)
        = 2 / H + 2 * (C N / N) + 4 * H / N + 8 * H^2 / N^2 := by
      field_simp; ring
    have e3 : 8 * (H:ℝ)^2 / N^2 ≤ 8 * H^2 / N := by
      have hN1' : (1:ℝ) ≤ N := by exact_mod_cast hN1
      apply div_le_div_of_nonneg_left (by positivity) hNpos
      nlinarith
    calc (A / N)^2 = ((H:ℝ) * A)^2 / (H^2 * N^2) := e1
      _ ≤ (2 * (N:ℝ) * (H * N + H^2 * (C N + 2 * H)) + 8 * H^4) / (H^2 * N^2) :=
          div_le_div_of_nonneg_right hb (by positivity)
      _ = 2 / H + 2 * (C N / N) + 4 * H / N + 8 * H^2 / N^2 := e2
      _ ≤ 2 / H + G N := by
          simp only [hG]
          have : (4 * (H:ℝ) + 8 * H^2) / N = 4 * H / N + 8 * H^2 / N := by ring
          rw [this]; linarith
  have h2H : 2 / (H:ℝ) < ε^2 / 2 := by
    rw [div_lt_div_iff₀ hH0 (by norm_num)]; nlinarith
  have hlt : (A / N)^2 < ε^2 := by linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt

/-- Step 3 of the proof of `isNormalInBase_div_int`: diff lemma. -/
private lemma isNormalInBase_div_int_diff {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk_pos : 0 < k)
    (hk_div : k ∣ B * (B - 1))
    {y : ℝ} (hy : ∀ h : ℤ, h ≠ 0 → Tendsto (isNormalInBase_div_int_weylSum B y h) atTop (𝓝 0)) :
    ∀ h : ℤ, h ≠ 0 → Tendsto (isNormalInBase_div_int_weylSum B (y / (k : ℝ)) h) atTop (𝓝 0) := by
  intro h hh
  have hconj : ∀ a : ℝ, starRingEnd ℂ (Complex.exp (2 * ↑Real.pi * Complex.I * (a : ℂ))) =
      Complex.exp (-(2 * ↑Real.pi * Complex.I * (a : ℂ))) := by
    intro a
    rw [← Complex.exp_conj]
    congr 1
    simp [map_mul, Complex.conj_ofReal, map_ofNat]
  set u : ℕ → ℂ := fun n => Complex.exp (2 * ↑Real.pi * Complex.I *
                              ((h * (B : ℝ) ^ n * (y / (k : ℝ)) : ℝ) : ℂ))
    with hu_def
  have hu : ∀ n, ‖u n‖ ≤ 1 := by
    intro n
    have hnorm : ∀ a : ℝ, ‖Complex.exp (2 * ↑Real.pi * Complex.I * (a : ℂ))‖ ≤ 1 := by
      intro a
      rw [Complex.norm_exp]
      simp
    exact hnorm _
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk_pos
  have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hvdc := isNormalInBase_div_int_vDC u hu ?_
  · have heq : isNormalInBase_div_int_weylSum B (y / (k : ℝ)) h =
        fun M : ℕ => (1 / (M : ℂ)) * ∑ m ∈ Finset.range M, u m := by
      funext M
      simp only [isNormalInBase_div_int_weylSum, hu_def]
      push_cast
      rfl
    rw [heq]
    exact hvdc
  · intro s hs
    have hdvd : k ∣ B * (B ^ s - 1) := by
      refine hk_div.trans (Nat.mul_dvd_mul_left B ?_)
      exact Nat.sub_one_dvd_pow_sub_one B s
    obtain ⟨t, ht⟩ := hdvd
    have hBs : 2 ≤ B ^ s := by
      calc 2 ≤ B := hB
        _ = B ^ 1 := (pow_one B).symm
        _ ≤ B ^ s := Nat.pow_le_pow_right (by omega) hs
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        have : 0 < B * (B ^ s - 1) := Nat.mul_pos (by omega) (by omega)
        omega
      · exact h0
    have htR : (k : ℝ) * t = B * ((B : ℝ) ^ s - 1) := by
      have h1 : ((B * (B ^ s - 1) : ℕ) : ℝ) = ((k * t : ℕ) : ℝ) := by rw [ht]
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one] at h1
      linarith
    have hw := hy (h * (t : ℤ)) (mul_ne_zero hh (by exact_mod_cast htpos.ne'))
    set W : ℕ → ℂ := isNormalInBase_div_int_weylSum B y (h * (t : ℤ)) with hW
    have hterm : ∀ m : ℕ, u (m + 1 + s) * starRingEnd ℂ (u (m + 1)) =
        Complex.exp (2 * ↑Real.pi * Complex.I * (((h * (t : ℤ) : ℤ) : ℂ) * (B : ℂ) ^ m * (y : ℂ)))
            := by
      intro m
      simp only [hu_def]
      rw [hconj, ← Complex.exp_add]
      congr 1
      have hx : ((h : ℝ) * (B : ℝ) ^ (m + 1 + s) * (y / k) - (h : ℝ) * (B : ℝ) ^ (m + 1) * (y / k)
          = (h : ℝ) * (t : ℝ) * (B : ℝ) ^ m * y) := by
        have hk0 : (k : ℝ) ≠ 0 := hkR.ne'
        calc (h : ℝ) * (B : ℝ) ^ (m + 1 + s) * (y / k) - (h : ℝ) * (B : ℝ) ^ (m + 1) * (y / k)
            = (h : ℝ) * (B : ℝ) ^ m * y * ((B : ℝ) * ((B : ℝ) ^ s - 1)) / k := by
              rw [pow_add, pow_succ]; ring
          _ = (h : ℝ) * (B : ℝ) ^ m * y * ((k : ℝ) * t) / k := by rw [htR]
          _ = (h : ℝ) * (t : ℝ) * (B : ℝ) ^ m * y := by field_simp
      have hx' := congrArg (fun r : ℝ => (r : ℂ)) hx
      push_cast at hx' ⊢
      linear_combination (2 * ↑Real.pi * Complex.I) * hx'
    have hWM : ∀ M : ℕ, W M = (1 / (M : ℂ)) * ∑ n ∈ Finset.range M,
        Complex.exp (2 * ↑Real.pi * Complex.I * (((h * (t : ℤ) : ℤ) : ℂ) * (B : ℂ) ^ n * (y : ℂ)))
            := by
      intro M
      simp [hW, isNormalInBase_div_int_weylSum]
    -- shift
    have hshift : ∀ M : ℕ, (1 / ((M : ℂ) + 1)) * ∑ m ∈ Finset.range (M + 1), u (m + s) * starRingEnd
        ℂ (u m)
        = (1 / ((M : ℂ) + 1)) * (u s * starRingEnd ℂ (u 0)) + ((M : ℂ) / ((M : ℂ) + 1)) * W M := by
      intro M
      rw [Finset.sum_range_succ']
      simp only [hterm, zero_add, hWM]
      have hM1 : ((M : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero M
      rcases Nat.eq_zero_or_pos M with hM | hM
      · subst hM
        simp
      · have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
        field_simp
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl (fun x _ => ?_)
        congr 1
        ring
    have h1 : Tendsto (fun M : ℕ => (1 / ((M : ℂ) + 1))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h0
      rw [Complex.ofReal_zero] at h2
      refine h2.congr (fun n => ?_)
      simp
    have h3 : Tendsto (fun M : ℕ => ((M : ℂ) / ((M : ℂ) + 1))) atTop (𝓝 1) := by
      have h4 : Tendsto (fun M : ℕ => 1 - 1 / ((M : ℂ) + 1)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub h1
      rw [sub_zero] at h4
      refine h4.congr (fun M => ?_)
      have hM1 : ((M : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero M
      field_simp
      ring
    have h5 : Tendsto (fun M : ℕ => (1 / ((M : ℂ) + 1)) * (u s * starRingEnd ℂ (u 0)) +
        ((M : ℂ) / ((M : ℂ) + 1)) * W M) atTop (𝓝 (0 * (u s * starRingEnd ℂ (u 0)) + 1 * 0)) :=
      (h1.mul_const _).add (h3.mul hw)
    rw [zero_mul, one_mul, add_zero] at h5
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    refine h5.congr (fun M => ?_)
    rw [← hshift M]
    push_cast
    rfl

/-- Step 4 of the proof of `isNormalInBase_div_int`: find L for pigeonhole. -/
private lemma isNormalInBase_div_int_L (b k : ℕ) (hk : 0 < k) :
    ∃ L ≥ 1, k ∣ b^L * (b^L - 1) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact ⟨1, le_refl _, by simp⟩
  have : NeZero k := ⟨hk.ne'⟩
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (⟨b ^ n % k, Nat.mod_lt _ hk⟩ : Fin k))
  have hmod : b ^ i % k = b ^ j % k := by simpa using heq
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm heq.symm hmod.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  have hd : 1 ≤ d := by omega
  have hdvd : k ∣ b ^ (i + d) - b ^ i :=
    (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right hb (by omega))).mp hmod
  have hfac : b ^ (i + d) - b ^ i = b ^ i * (b ^ d - 1) := by
    rw [Nat.mul_sub, pow_add, mul_one, mul_comm]
  have hiL : i ≤ d * (i + 1) := by nlinarith
  refine ⟨d * (i + 1), by nlinarith, ?_⟩
  refine hdvd.trans ?_
  rw [hfac]
  apply mul_dvd_mul
  · exact pow_dvd_pow b hiL
  · have := Nat.sub_dvd_pow_sub_pow (b ^ d) 1 (i + 1)
    simpa [← pow_mul] using this

private lemma isNormalInBase_div_int_sum_aux_split (g : ℕ → ℂ) (L M : ℕ) :
    ∑ n ∈ Finset.range (L * M), g n = ∑ c ∈ Finset.range L, ∑ q ∈ Finset.range M, g (L * q + c) :=
        by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [Finset.sum_range_succ, Finset.sum_add_distrib]

private lemma isNormalInBase_div_int_sum_aux_class (b L c : ℕ) (x : ℝ) (h : ℤ) (M : ℕ) :
    isNormalInBase_div_int_weylSum (b^L) ((b^c : ℝ) * x) h M =
      (1 / (M : ℂ)) * ∑ q ∈ Finset.range M,
        Complex.exp (2 * ↑Real.pi * Complex.I * (h * (b : ℝ)^(L * q + c) * x : ℂ)) := by
  unfold isNormalInBase_div_int_weylSum
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 2
  push_cast
  ring

/-- Step 5 of the proof of `isNormalInBase_div_int`: sum the L residue classes. -/
private lemma isNormalInBase_div_int_sum {b : ℕ} (_hb : 2 ≤ b) {L : ℕ} (hL : 1 ≤ L)
    {x : ℝ} (hx : ∀ c < L, ∀ h : ℤ, h ≠ 0 → Tendsto (isNormalInBase_div_int_weylSum (b^L)
        ((b^c : ℝ) * x) h) atTop (𝓝 0)) :
    ∀ h : ℤ, h ≠ 0 → Tendsto (isNormalInBase_div_int_weylSum b x h) atTop (𝓝 0) := by
  intro h hh
  set g : ℕ → ℂ := fun n => Complex.exp (2 * ↑Real.pi * Complex.I * (h * (b : ℝ)^n * x : ℂ)) with hg
  have hgn : ∀ n, ‖g n‖ ≤ 1 := by
    intro n
    simp only [hg]
    have : (2 * ↑Real.pi * Complex.I * (h * (b : ℝ)^n * x : ℂ)) =
        ((2 * Real.pi * (h * (b : ℝ)^n * x) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hW : ∀ N, isNormalInBase_div_int_weylSum b x h N = (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
      g n := by
    intro N; rfl
  have hcls : ∀ c < L, Tendsto (fun M : ℕ => (1 / (M : ℂ)) * ∑ q ∈ Finset.range M, g (L * q + c))
      atTop (𝓝 0) := by
    intro c hc
    have := hx c hc h hh
    refine this.congr (fun M => ?_)
    exact isNormalInBase_div_int_sum_aux_class b L c x h M
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hblock : Tendsto (fun M : ℕ => ‖(1 / ((L * M : ℕ) : ℂ)) * ∑ n ∈ Finset.range (L * M), g n‖)
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun M : ℕ => (1 / (L : ℂ)) * ∑ c ∈ Finset.range L,
        (1 / (M : ℂ)) * ∑ q ∈ Finset.range M, g (L * q + c)) atTop (𝓝 0) := by
      have : Tendsto (fun M : ℕ => ∑ c ∈ Finset.range L,
          (1 / (M : ℂ)) * ∑ q ∈ Finset.range M, g (L * q + c)) atTop (𝓝 0) := by
        have := tendsto_finsetSum (Finset.range L) (f := fun c (M : ℕ) =>
          (1 / (M : ℂ)) * ∑ q ∈ Finset.range M, g (L * q + c)) (a := fun _ => (0 : ℂ))
          (fun c hc => hcls c (Finset.mem_range.mp hc))
        simpa using this
      simpa using this.const_mul (1 / (L : ℂ))
    have h2 := hsum.norm
    simp only [norm_zero] at h2
    refine h2.congr (fun M => ?_)
    rw [isNormalInBase_div_int_sum_aux_split, ← Finset.mul_sum]
    congr 1
    rw [← mul_assoc]
    congr 1
    push_cast
    rw [one_div, one_div, one_div, mul_inv]
  have hMt : Tendsto (fun N : ℕ => N / L) atTop atTop := Nat.tendsto_div_const_atTop (by omega)
  have hcomp := hblock.comp hMt
  have hLN : Tendsto (fun N : ℕ => (L : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hup := hcomp.add hLN
  rw [zero_add] at hup
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) ?_ hup
  filter_upwards [eventually_ge_atTop L] with N hN
  set M := N / L with hM
  have hM1 : 1 ≤ M := (Nat.one_le_div_iff (by omega)).mpr hN
  have hLM : L * M ≤ N := Nat.mul_div_le N L
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hLMpos : (0 : ℝ) < ((L * M : ℕ) : ℝ) := by exact_mod_cast (by positivity : 0 < L * M)
  have htail : ‖∑ n ∈ Finset.range N, g n - ∑ n ∈ Finset.range (L * M), g n‖ ≤ L := by
    have hN' : N = L * M + (N - L * M) := by omega
    have hlt : N - L * M < L := by
      have := Nat.mod_lt N (by omega : 0 < L)
      have h3 : L * M + N % L = N := Nat.div_add_mod N L
      omega
    have : ∑ n ∈ Finset.range N, g n - ∑ n ∈ Finset.range (L * M), g n
        = ∑ n ∈ Finset.range (N - L * M), g (L * M + n) := by
      conv_lhs => rw [hN', Finset.sum_range_add]
      ring
    rw [this]
    calc _ ≤ ∑ n ∈ Finset.range (N - L * M), ‖g (L * M + n)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range (N - L * M), (1 : ℝ) := Finset.sum_le_sum fun n _ => hgn _
      _ = ((N - L * M : ℕ) : ℝ) := by simp
      _ ≤ L := by exact_mod_cast hlt.le
  simp only [Function.comp]
  rw [hW, norm_mul]
  have hnormN : ‖(1 / (N : ℂ))‖ = 1 / (N : ℝ) := by simp
  have hnormLM : ‖(1 / ((L * M : ℕ) : ℂ))‖ = 1 / ((L * M : ℕ) : ℝ) := by simp
  rw [hnormN, norm_mul, hnormLM]
  set T := ∑ n ∈ Finset.range (L * M), g n
  have hle : ‖∑ n ∈ Finset.range N, g n‖ ≤ ‖T‖ + L := by
    calc ‖∑ n ∈ Finset.range N, g n‖ = ‖(∑ n ∈ Finset.range N, g n - T) + T‖ := by congr 1; ring
      _ ≤ ‖∑ n ∈ Finset.range N, g n - T‖ + ‖T‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hcastle : ((L * M : ℕ) : ℝ) ≤ N := by exact_mod_cast hLM
  calc 1 / (N : ℝ) * ‖∑ n ∈ Finset.range N, g n‖ ≤ 1 / (N : ℝ) * (‖T‖ + L) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = ‖T‖ / N + L / N := by ring
    _ ≤ 1 / ((L * M : ℕ) : ℝ) * ‖T‖ + L / N := by
        gcongr
        rw [div_eq_mul_one_div, mul_comm]
        gcongr

/-- Step 6 of the proof of `isNormalInBase_div_int`: negation preserves normality. -/
private lemma isNormalInBase_div_int_neg {b : ℕ} (hb : 2 ≤ b) {α : ℝ} (hα : IsNormalInBase b
    α) :
    IsNormalInBase b (-α) := by
  rw [isNormalInBase_div_int_weyl hb] at hα ⊢
  intro h hh
  have h1 := hα (-h) (neg_ne_zero.mpr hh)
  have h2 : isNormalInBase_div_int_weylSum b (-α) h = isNormalInBase_div_int_weylSum b α (-h) := by
    funext N
    unfold isNormalInBase_div_int_weylSum
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    push_cast
    ring
  rw [h2]
  exact h1

/-- Helper assembling `isNormalInBase_div_int` for positive integer divisors. -/
private lemma isNormalInBase_div_int_pos {b : ℕ} (hb : 2 ≤ b) {α : ℝ} (hα : IsNormalInBase b α)
    {k : ℕ} (hk : 0 < k) : IsNormalInBase b (α / (k : ℝ)) := by
  have ⟨L, hL1, hL2⟩ := isNormalInBase_div_int_L b k hk
  have hB : 2 ≤ b^L := by
    have H : b^1 ≤ b^L := Nat.pow_le_pow_right (by omega) hL1
    rw [Nat.pow_one] at H
    exact le_trans hb H
  have h_weyl := (isNormalInBase_div_int_weyl hb (α / (k : ℝ))).mpr (by
    apply isNormalInBase_div_int_sum hb hL1
    intro c _ h h_neq
    have hy_eq : (b^c : ℝ) * (α / (k : ℝ)) = ((b^c : ℝ) * α) / (k : ℝ) := by ring
    rw [hy_eq]
    apply isNormalInBase_div_int_diff hB hk hL2 _ h h_neq
    intro h' h_neq'
    have hy_normal : IsNormalInBase b ((((b^c : ℕ) : ℤ) : ℝ) * α) := by
      apply isNormalInBase_mul hb hα
      intro hc0
      have hc0_nat : (b^c : ℕ) = 0 := by exact_mod_cast hc0
      have hb_pos : 0 < b := by omega
      have hbc_pos : 0 < b^c := by positivity
      omega
    have hy_cast : ((((b^c : ℕ) : ℤ) : ℝ) * α) = ((b^c : ℝ) * α) := by
      have hcast : ((((b^c : ℕ) : ℤ) : ℝ)) = (b^c : ℝ) := by simp
      rw [hcast]
    rw [hy_cast] at hy_normal
    have hB_normal : IsNormalInBase (b^L) ((b^c : ℝ) * α) :=
        (isNormalInBase_iff_pow hb hL1 ((b^c : ℝ) * α)).mp hy_normal
    exact (isNormalInBase_div_int_weyl hB ((b^c : ℝ) * α)).mp hB_normal h' h_neq'
  )
  exact h_weyl

/-- **SUV Section 9.3, p. 265 (Wall)**: "normality is preserved also when we divide a number
by some integer".  This external result [216, 87] is reported without proof in the book.
As for Problem 258, the integer must be nonzero and the base at least two. -/
theorem isNormalInBase_div_int {b : ℕ} (hb : 2 ≤ b) {α : ℝ} (hα : IsNormalInBase b α)
    {k : ℤ} (hk : k ≠ 0) : IsNormalInBase b (α / (k : ℝ)) := by
  rcases lt_trichotomy 0 k with h | h | h
  · have h_eq : (k : ℝ) = (k.toNat : ℝ) := by
      have ht : k = (k.toNat : ℤ) := (Int.toNat_of_nonneg (le_of_lt h)).symm
      exact congrArg (fun (x : ℤ) => (x : ℝ)) ht
    have hk_pos : 0 < k.toNat := by
      have ht : k = (k.toNat : ℤ) := (Int.toNat_of_nonneg (le_of_lt h)).symm
      have hz : (0 : ℤ) < (k.toNat : ℤ) := by
        calc (0 : ℤ) < k := h
          _ = (k.toNat : ℤ) := ht
      exact Int.ofNat_lt.mp hz
    have ht : α / (k : ℝ) = α / (k.toNat : ℝ) := by rw [h_eq]
    rw [ht]
    exact isNormalInBase_div_int_pos hb hα hk_pos
  · exact (hk h.symm).elim
  · have h_neg : 0 < -k := neg_pos.mpr h
    have h_eq : (k : ℝ) = -((-k).toNat : ℝ) := by
      have ht : -k = ((-k).toNat : ℤ) := (Int.toNat_of_nonneg (le_of_lt h_neg)).symm
      have ht_cast : ((-k : ℤ) : ℝ) = (((-k).toNat : ℤ) : ℝ) := congrArg (fun (x : ℤ) => (x : ℝ)) ht
      have ht2 : ((-k : ℤ) : ℝ) = -(k : ℝ) := Int.cast_neg k
      calc (k : ℝ) = -(-(k : ℝ)) := by ring
        _ = -((-k : ℤ) : ℝ) := by rw [ht2]
        _ = -(((-k).toNat : ℤ) : ℝ) := by rw [ht_cast]
        _ = -(((-k).toNat : ℝ)) := by rfl
    have hk_pos : 0 < (-k).toNat := by
      have ht : -k = ((-k).toNat : ℤ) := (Int.toNat_of_nonneg (le_of_lt h_neg)).symm
      have hz : (0 : ℤ) < ((-k).toNat : ℤ) := by
        calc (0 : ℤ) < -k := h_neg
          _ = ((-k).toNat : ℤ) := ht
      exact Int.ofNat_lt.mp hz
    have ht : α / (k : ℝ) = - (α / ((-k).toNat : ℝ)) := by
      rw [h_eq]
      rw [div_neg]
    rw [ht]
    apply isNormalInBase_div_int_neg hb
    exact isNormalInBase_div_int_pos hb hα hk_pos

end Kolmogorov.FrequencyGames
