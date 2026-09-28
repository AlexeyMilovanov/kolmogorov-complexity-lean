import KolmogorovMathlib.StoppingComplexity.Schedule

/-!
# A fully discrete divergence proof for the discount `F`

Blueprint 04 §5 ("A fully discrete divergence proof for F").  With `a_j = 2^{-F (E_j)}` the
partial sums `S_R = Σ_{j=1}^{R} a_j` (`discountSums discountF R`) are shown to be unbounded by
three nested block estimates over dyadic ranges of the index:

* `A_k = Σ_{2^k ≤ j < 2^{k+1}} a_j ≥ 1 / (16 (k + 3) (L k + 2))` for `k ≥ 4` (`04-DB1`);
* `D_ℓ = Σ_{2^ℓ ≤ k < 2^{ℓ+1}} A_k ≥ 1 / (64 (ℓ + 3))` for `ℓ ≥ 2` (`04-DB2`);
* `J_r = Σ_{2^r ≤ ℓ < 2^{r+1}} D_ℓ ≥ 1 / 256` for `r ≥ 2` (`04-DB3`);

and finally `S_{2^{2^{2^{N+2}}} - 1} ≥ N / 256` for `N ≥ 1`, hence DIV for `F`, with the explicit
termination certificate EXPLICIT-R (`04-DB4`).  All quantities are finite rational sums; no
condensation theorem, real asymptotics or computable-real ceiling is used.
-/

namespace Kolmogorov

/-- The first block `A_k = Σ_{j=2^k}^{2^{k+1}-1} 2^{-F (E_j)}`.
Blueprint 04 Lemma first-block (`04-DB1`). -/
def firstBlock (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), (1 / 2 : ℚ) ^ discountF (expSchedule j)

private lemma expSchedule_le_mul_stepSize {j : ℕ} (hj : 16 ≤ j) :
    expSchedule j ≤ 16 + j * stepSize j := by
  have hd : expSchedule j = 16 + ∑ i ∈ Finset.Ico 1 (j + 1), stepSize i := by
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [expSchedule, ih]
      have h_Ico : Finset.Ico 1 (n + 1 + 1) = Finset.Ico 1 (n + 1) ∪ {n + 1} := by
        ext x
        rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico, Finset.mem_Ico]
        omega
      have h_disj : Disjoint (Finset.Ico 1 (n + 1)) {n + 1} := by
        simp only [Finset.disjoint_singleton_right, Finset.mem_Ico]
        omega
      rw [h_Ico, Finset.sum_union h_disj, Finset.sum_singleton]
      ring
  rw [hd]
  apply Nat.add_le_add_left
  have h_bound : ∑ i ∈ Finset.Ico 1 (j + 1), stepSize i ≤ ∑ i ∈ Finset.Ico 1 (j + 1), stepSize j :=
    by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hle : i ≤ j := by omega
    unfold stepSize
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.clog_mono_right
    omega
  have h_eq : ∑ i ∈ Finset.Ico 1 (j + 1), stepSize j = j * stepSize j := by
    rw [Finset.sum_const, Nat.card_Ico]
    have h_sub : j + 1 - 1 = j := by omega
    rw [h_sub, smul_eq_mul]
  omega

private lemma firstBlock_bound_aux_1 {k j : ℕ} (hk : 4 ≤
  k) (hj1 : 2 ^ k ≤ j) (hj2 : j < 2 ^ (k + 1)) :
    expSchedule j ≤ 2 ^ (k + 2) * (k + 3) := by
  have hj16 : 16 ≤ j := by
    calc 16 = 2 ^ 4 := by rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
      _ ≤ j := hj1
  have h1 : expSchedule j ≤ 16 + j * stepSize j := expSchedule_le_mul_stepSize hj16
  have h2 : stepSize j ≤ 2 * k + 5 := by
    unfold stepSize
    apply Nat.add_le_add_right
    have hm : 2 * Nat.clog 2 (j + 1) ≤ 2 * (k + 1) := by
      apply Nat.mul_le_mul_left
      apply Nat.clog_le_of_le_pow
      omega
    have hm2 : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [hm2] at hm
    omega
  have h3 : 16 + j * stepSize j ≤ 16 + j * (2 * k + 5) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left j h2) 16
  have h4 : 16 + j * (2 * k + 5) ≤ j + j * (2 * k + 5) :=
    Nat.add_le_add_right hj16 (j * (2 * k + 5))
  have h5 : j + j * (2 * k + 5) = j * (2 * k + 6) := by ring
  have h6 : j * (2 * k + 6) ≤ 2 ^ (k + 1) * (2 * k + 6) :=
    Nat.mul_le_mul_right (2 * k + 6) (by omega)
  have h7 : 2 ^ (k + 1) * (2 * k + 6) = 2 ^ (k + 2) * (k + 3) := by
    have hk1 : 2 ^ (k + 2) = 2 ^ (k + 1) * 2 := by ring
    have hk2 : 2 * k + 6 = 2 * (k + 3) := by ring
    rw [hk1, hk2]
    ring
  omega

private lemma hk3_pow_helper {k : ℕ} (hk : 4 ≤ k) : k + 3 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h1 : n + 1 + 3 = (n + 3) + 1 := by ring
    rw [h1]
    have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := by ring
    rw [h2]
    have h3 : 2 ^ n ≥ 1 := Nat.one_le_two_pow
    omega

private lemma firstBlock_bound_aux_2 {k j : ℕ} (hk : 4 ≤
  k) (hb1 : expSchedule j ≤ 2 ^ (k + 2) * (k + 3)) :
    discountF (expSchedule j) ≤ k + 2 + Nat.clog 2 (k + 3) + Nat.clog 2 (Nat.clog 2 k + 2) := by
  have hj16 : 16 ≤ expSchedule j := by
    have h_ge : 16 + 5 * j ≤ expSchedule j := expSchedule_ge j
    omega
  have hd : discountF (expSchedule j) =
    Nat.clog 2 (expSchedule j) + Nat.clog 2 (Nat.clog 2 (Nat.clog 2 (expSchedule j))) := by
    unfold discountF
    have h_max : max 16 (expSchedule j) = expSchedule j := Nat.max_eq_right hj16
    rw [h_max]
  rw [hd]
  have hc1 : Nat.clog 2 (expSchedule j) ≤ Nat.clog 2 (2 ^ (k + 2) * (k + 3)) := by
    apply Nat.clog_mono_right
    exact hb1
  have hc1_le : Nat.clog 2 (2 ^ (k + 2) * (k + 3)) ≤ k + 2 + Nat.clog 2 (k + 3) := by
    have hm := clogTwo_two_pow_mul (n := k + 3) (by omega) (k + 2)
    omega
  have hl1 : Nat.clog 2 (expSchedule j) ≤ k + 2 + Nat.clog 2 (k + 3) := by omega
  have hb2 : k + 2 + Nat.clog 2 (k + 3) ≤ 2 * k + 2 := by
    have hclog : Nat.clog 2 (k + 3) ≤ k := by
      apply Nat.clog_le_of_le_pow
      exact hk3_pow_helper hk
    omega
  have hc2 : Nat.clog 2 (Nat.clog 2 (expSchedule j)) ≤ Nat.clog 2 (2 * k + 2) := by
    apply Nat.clog_mono_right
    omega
  have hc2_le : Nat.clog 2 (2 * k + 2) ≤ 1 + Nat.clog 2 (k + 1) := by
    have hr : 2 * k + 2 = 2 ^ 1 * (k + 1) := by ring
    rw [hr]
    have hm := clogTwo_two_pow_mul (n := k + 1) (by omega) 1
    omega
  have hk1_le : k + 1 ≤ 2 * k := by omega
  have hc2_le2 : Nat.clog 2 (k + 1) ≤ Nat.clog 2 (2 * k) := by
    apply Nat.clog_mono_right
    omega
  have hc2_le3 : Nat.clog 2 (2 * k) ≤ 1 + Nat.clog 2 k := by
    have hr : 2 * k = 2 ^ 1 * k := by ring
    rw [hr]
    have hm := clogTwo_two_pow_mul (n := k) (by omega) 1
    omega
  have hl2 : Nat.clog 2 (Nat.clog 2 (expSchedule j)) ≤ Nat.clog 2 k + 2 := by omega
  have hc3 : Nat.clog 2 (Nat.clog 2 (Nat.clog 2 (expSchedule j))) ≤ Nat.clog 2 (Nat.clog 2 k + 2) :=
    by
    apply Nat.clog_mono_right
    omega
  omega

private lemma firstBlock_bound_aux_3 {k : ℕ} (hk : 4 ≤ k) {x : ℕ}
    (hx : x ≤ k + 2 + Nat.clog 2 (k + 3) + Nat.clog 2 (Nat.clog 2 k + 2)) :
    1 / (2 ^ (k + 4) * (k + 3) * (Nat.clog 2 k + 2) : ℚ) ≤ (1 / 2 : ℚ) ^ x := by
  have hp : (1 / 2 : ℚ) ^ (k + 2 + Nat.clog 2 (k + 3) + Nat.clog 2 (Nat.clog 2 k + 2)) =
      (1 / 2 : ℚ) ^ (k + 2) * (1 / 2 : ℚ) ^ Nat.clog 2 (k + 3) * (1 / 2 : ℚ)
        ^ Nat.clog 2 (Nat.clog 2 k + 2)
        := by
    rw [pow_add, pow_add]
  have h_bound1 : (1 / 2 : ℚ) ^ Nat.clog 2 (k + 3) ≥ 1 / (2 * (k + 3) : ℚ) := by
    have ht : (1 / 2 : ℚ) ^ Nat.clog 2 (k + 3) = 1 / (2 : ℚ) ^ Nat.clog 2 (k + 3) :=
      by rw [one_div_pow]
    rw [ht]
    apply one_div_le_one_div_of_le (by positivity)
    have hc : ((2 ^ Nat.clog 2 (k + 3) : ℕ) : ℚ) ≤ ((2 * (k + 3) : ℕ) : ℚ) := by
      exact Nat.cast_le.mpr (clogTwo_pow_le_two_mul (n := k + 3) (by omega))
    push_cast at hc
    exact hc
  have h_bound2 : (1 / 2 : ℚ) ^ Nat.clog 2 (Nat.clog 2 k + 2) ≥ 1 / (2 * (Nat.clog 2 k + 2) : ℚ) :=
    by
    have ht : (1 / 2 : ℚ) ^ Nat.clog 2 (Nat.clog 2 k + 2) = 1 / (2 : ℚ)
      ^ Nat.clog 2 (Nat.clog 2 k + 2)
      := by rw [one_div_pow]
    rw [ht]
    apply one_div_le_one_div_of_le (by positivity)
    have hc : ((2 ^ Nat.clog 2 (Nat.clog 2 k + 2) : ℕ) : ℚ) ≤ ((2 * (Nat.clog 2 k + 2) : ℕ) : ℚ) :=
      by
      exact Nat.cast_le.mpr (clogTwo_pow_le_two_mul (n := Nat.clog 2 k + 2) (by omega))
    push_cast at hc
    exact hc
  have hp2 : (1 / 2 : ℚ) ^ (k + 2) = 1 / (2 : ℚ) ^ (k + 2) := by rw [one_div_pow]
  have ht1 : 1 / (2 : ℚ) ^ (k + 2) * (1 / (2 * (k + 3) : ℚ)) * (1 / (2 * (Nat.clog 2 k + 2) : ℚ)) ≤
      (1 / 2 : ℚ) ^ (k + 2) * (1 / 2 : ℚ) ^ Nat.clog 2 (k + 3) * (1 / 2 : ℚ)
        ^ Nat.clog 2 (Nat.clog 2 k + 2)
        := by
    rw [hp2]
    apply mul_le_mul
    · apply mul_le_mul (by rfl) h_bound1 (by positivity) (by positivity)
    · exact h_bound2
    · positivity
    · positivity
  have hm1 : 1 / (2 : ℚ) ^ (k + 2) * (1 / (2 * (k + 3) : ℚ)) * (1 / (2 * (Nat.clog 2 k + 2) : ℚ)) =
      1 / ((2 : ℚ) ^ (k + 2) * (2 * (k + 3) : ℚ) * (2 * (Nat.clog 2 k + 2) : ℚ)) := by
    rw [one_div_mul_one_div_rev, one_div_mul_one_div_rev]
    have hc : (2 * (Nat.clog 2 k + 2) : ℚ) * ((2 * (k + 3) : ℚ) * (2 : ℚ) ^ (k + 2)) =
        (2 : ℚ) ^ (k + 2) * (2 * (k + 3) : ℚ) * (2 * (Nat.clog 2 k + 2) : ℚ) := by ring
    rw [hc]
  rw [hm1] at ht1
  have hr : (2 : ℚ) ^ (k + 2) * (2 * (k + 3) : ℚ) * (2 * (Nat.clog 2 k + 2) : ℚ) =
      (2 : ℚ) ^ (k + 4) * (k + 3) * (Nat.clog 2 k + 2) := by
    have hk1 : (2 : ℚ) ^ (k + 4) = (2 : ℚ) ^ (k + 2) * (2 : ℚ) ^ 2 := by
      have h : k + 4 = k + 2 + 2 := by omega
      rw [h, pow_add]
    have hk2 : (2 : ℚ) ^ 2 = 2 * 2 := by ring
    rw [hk1, hk2]
    ring
  rw [hr] at ht1
  rw [← hp] at ht1
  have ht2 : (1 / 2 : ℚ) ^ (k + 2 + Nat.clog 2 (k + 3) + Nat.clog 2 (Nat.clog 2 k + 2)) =
      1 / (2 : ℚ) ^ (k + 2 + Nat.clog 2 (k + 3) + Nat.clog 2 (Nat.clog 2 k + 2)) :=
        by rw [one_div_pow]
  rw [ht2] at ht1
  have ht3 : (1 / 2 : ℚ) ^ x = 1 / (2 : ℚ) ^ x := by rw [one_div_pow]
  rw [ht3]
  apply le_trans ht1
  apply one_div_le_one_div_of_le (by positivity)
  have hp_bound : (2 : ℚ) ^ x ≤
    (2 : ℚ) ^ (k + 2 + Nat.clog 2 (k + 3) + Nat.clog 2 (Nat.clog 2 k + 2)) := by
    have hc : ((2 ^ x : ℕ) : ℚ) = (2 : ℚ) ^ x := by push_cast; rfl
    have hc2 : ((2 ^ (k + 2 + Nat.clog 2 (k + 3) + Nat.clog 2 (Nat.clog 2 k + 2)) : ℕ) : ℚ) =
        (2 : ℚ) ^ (k + 2 + Nat.clog 2 (k + 3) + Nat.clog 2 (Nat.clog 2 k + 2)) := by push_cast; rfl
    rw [← hc, ← hc2]
    apply Nat.cast_le.mpr
    apply Nat.pow_le_pow_right (by decide) hx
  exact hp_bound

/-- first-block: for every `k ≥ 4`, `A_k ≥ 1 / (16 (k + 3) (L k + 2))` (on the block
`E_j ≤ 2^{k+2} (k + 3)`, so `F (E_j) ≤ k + 2 + L (k + 3) + L (L k + 2)`, and the block has
`2^k` indices).  Blueprint 04 Lemma first-block (DB1) (`04-DB1`). -/
theorem firstBlock_ge {k : ℕ} (hk : 4 ≤ k) :
    1 / (16 * (k + 3) * (Nat.clog 2 k + 2) : ℚ) ≤ firstBlock k := by
  have h_bound : ∀ j ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
      1 / (2 ^ (k + 4) * (k + 3) * (Nat.clog 2 k + 2) : ℚ) ≤
        (1 / 2 : ℚ) ^ discountF (expSchedule j) :=
        by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hb1 : expSchedule j ≤ 2 ^ (k + 2) * (k + 3) := firstBlock_bound_aux_1 hk hj.1 hj.2
    have hd : discountF (expSchedule j) ≤
      k + 2 + Nat.clog 2 (k + 3) + Nat.clog 2 (Nat.clog 2 k + 2) :=
      firstBlock_bound_aux_2 hk hb1
    exact firstBlock_bound_aux_3 hk hd
  have h_sum := Finset.card_nsmul_le_sum _ _ _ h_bound
  rw [Nat.card_Ico] at h_sum
  have h_len : 2 ^ (k + 1) - 2 ^ k = 2 ^ k := by
    have h1 : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
    omega
  rw [h_len] at h_sum
  unfold firstBlock
  calc 1 / (16 * (k + 3) * (Nat.clog 2 k + 2) : ℚ)
    _ = (2 ^ k : ℕ) • (1 / (2 ^ (k + 4) * (k + 3) * (Nat.clog 2 k + 2) : ℚ)) := by
      rw [nsmul_eq_mul]
      push_cast
      have h2k4_eq : (2 ^ (k + 4) : ℚ) = 16 * 2 ^ k := by
        have : (2 ^ (k + 4) : ℚ) = 2 ^ k * (2 : ℚ) ^ 4 := by rw [pow_add]
        rw [this]
        ring
      rw [h2k4_eq]
      have hd : (2 ^ k : ℚ) * (1 / (16 * 2 ^ k * (k + 3) * (Nat.clog 2 k + 2))) =
                (2 ^ k : ℚ) / (2 ^ k * (16 * (k + 3) * (Nat.clog 2 k + 2))) := by
        rw [mul_one_div]
        congr 1
        ring
      rw [hd]
      have h2k : (2 ^ k : ℚ) ≠ 0 := by positivity
      have h2k2 : (2 ^ k : ℚ) * 1 = 2 ^ k := by ring
      have h2k3 : (2 ^ k : ℚ) / (2 ^ k * (16 * (k + 3) * (Nat.clog 2 k + 2))) =
                  ((2 ^ k : ℚ) * 1) / (2 ^ k * (16 * (k + 3) * (Nat.clog 2 k + 2))) := by rw [h2k2]
      rw [h2k3]
      rw [mul_div_mul_left _ _ h2k]
    _ ≤ ∑ j ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), (1 / 2 : ℚ) ^ discountF (expSchedule j) := h_sum

/-- The second block `D_ℓ = Σ_{k=2^ℓ}^{2^{ℓ+1}-1} A_k`.
Blueprint 04 Lemma second-block (`04-DB2`). -/
def secondBlock (l : ℕ) : ℚ :=
  ∑ k ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), firstBlock k

/-- second-block: for every `ℓ ≥ 2`, `D_ℓ ≥ 1 / (64 (ℓ + 3))` (every `k` in the range has
`k ≥ 4`, `k + 3 ≤ 2^{ℓ+2}` and `L k + 2 ≤ ℓ + 3`, and there are `2^ℓ` terms).
Blueprint 04 Lemma second-block (DB2) (`04-DB2`). -/
theorem secondBlock_ge {l : ℕ} (hl : 2 ≤ l) : 1 / (64 * (l + 3) : ℚ) ≤ secondBlock l := by
  have h_bound : ∀ k ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)),
      1 / (16 * (2 ^ (l + 2)) * (l + 3) : ℚ) ≤ firstBlock k := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk4 : 4 ≤ k := by
      calc 4 = 2 ^ 2 := by rfl
        _ ≤ 2 ^ l := Nat.pow_le_pow_right (by decide) hl
        _ ≤ k := hk.1
    have h1 : firstBlock k ≥ 1 / (16 * (k + 3) * (Nat.clog 2 k + 2) : ℚ) := firstBlock_ge hk4
    have h2 : (16 * (k + 3) * (Nat.clog 2 k + 2) : ℚ) ≤ (16 * (2 ^ (l + 2)) * (l + 3) : ℚ) := by
      have hc1 : ((16 * (k + 3) * (Nat.clog 2 k + 2) : ℕ) : ℚ) = (16 * (k + 3) * (Nat.clog 2 k + 2)
        : ℚ)
        := by push_cast; rfl
      have hc2 : ((16 * (2 ^ (l + 2)) * (l + 3) : ℕ) : ℚ) = (16 * (2 ^ (l + 2)) * (l + 3) : ℚ) :=
        by push_cast; rfl
      rw [← hc1, ← hc2]
      apply Nat.cast_le.mpr
      apply Nat.mul_le_mul
      · apply Nat.mul_le_mul (by rfl)
        · have : k ≤ 2 ^ (l + 1) - 1 := by omega
          have hk1 : 2 ^ (l + 1) * 2 = 2 ^ (l + 2) := by ring
          omega
      · have hc : Nat.clog 2 k ≤ l + 1 := by
          apply Nat.clog_le_of_le_pow
          omega
        omega
    have h3 : 1 / (16 * (2 ^ (l + 2)) * (l + 3) : ℚ) ≤
      1 / (16 * (k + 3) * (Nat.clog 2 k + 2) : ℚ) :=
      by
      apply one_div_le_one_div_of_le (by positivity) h2
    exact le_trans h3 h1
  have h_sum := Finset.card_nsmul_le_sum _ _ _ h_bound
  rw [Nat.card_Ico] at h_sum
  have h_len : 2 ^ (l + 1) - 2 ^ l = 2 ^ l := by
    have h1 : 2 ^ (l + 1) = 2 ^ l * 2 := by ring
    omega
  rw [h_len] at h_sum
  unfold secondBlock
  calc 1 / (64 * (l + 3) : ℚ)
    _ = (2 ^ l : ℕ) • (1 / (16 * (2 ^ (l + 2)) * (l + 3) : ℚ)) := by
      rw [nsmul_eq_mul]
      push_cast
      have h2l : (2 ^ (l + 2) : ℚ) = 4 * 2 ^ l := by
        have : (2 ^ (l + 2) : ℚ) = 2 ^ l * (2 : ℚ) ^ 2 := by rw [pow_add]
        rw [this]
        ring
      rw [h2l]
      have hd : (2 ^ l : ℚ) * (1 / (16 * (4 * 2 ^ l) * (l + 3))) =
                (2 ^ l : ℚ) / (2 ^ l * (64 * (l + 3))) := by
        rw [mul_one_div]
        congr 1
        ring
      rw [hd]
      have h2k : (2 ^ l : ℚ) ≠ 0 := by positivity
      have h2k2 : (2 ^ l : ℚ) * 1 = 2 ^ l := by ring
      have h2k3 : (2 ^ l : ℚ) / (2 ^ l * (64 * (l + 3))) =
                  ((2 ^ l : ℚ) * 1) / (2 ^ l * (64 * (l + 3))) := by rw [h2k2]
      rw [h2k3]
      rw [mul_div_mul_left _ _ h2k]
    _ ≤ ∑ k ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), firstBlock k := h_sum

/-- The third block `J_r = Σ_{ℓ=2^r}^{2^{r+1}-1} D_ℓ`.
Blueprint 04 Lemma third-block (`04-DB3`). -/
def thirdBlock (r : ℕ) : ℚ :=
  ∑ l ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), secondBlock l

/-- third-block: for every `r ≥ 2`, `J_r ≥ 1 / 256` (each of the `2^r` summands is at least
`1 / (64 · 2^{r+2})`).  Blueprint 04 Lemma third-block (DB3) (`04-DB3`). -/
theorem thirdBlock_ge {r : ℕ} (hr : 2 ≤ r) : (1 / 256 : ℚ) ≤ thirdBlock r := by
  have h_bound : ∀ l ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)),
      1 / (64 * 2 ^ (r + 2) : ℚ) ≤ secondBlock l := by
    intro l hl
    rw [Finset.mem_Ico] at hl
    have hl2 : 2 ≤ l := by
      calc 2 ≤ 4 := by decide
        _ = 2 ^ 2 := by rfl
        _ ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) hr
        _ ≤ l := hl.1
    have h1 : secondBlock l ≥ 1 / (64 * (l + 3) : ℚ) := secondBlock_ge hl2
    have h2 : (64 * (l + 3) : ℚ) ≤ (64 * 2 ^ (r + 2) : ℚ) := by
      have hc1 : ((64 * (l + 3) : ℕ) : ℚ) = (64 * (l + 3) : ℚ) := by push_cast; rfl
      have hc2 : ((64 * 2 ^ (r + 2) : ℕ) : ℚ) = (64 * 2 ^ (r + 2) : ℚ) := by push_cast; rfl
      rw [← hc1, ← hc2]
      apply Nat.cast_le.mpr
      apply Nat.mul_le_mul (by rfl)
      have : l ≤ 2 ^ (r + 1) - 1 := by omega
      have hr1 : 2 ^ (r + 1) * 2 = 2 ^ (r + 2) := by ring
      omega
    have h3 : 1 / (64 * 2 ^ (r + 2) : ℚ) ≤ 1 / (64 * (l + 3) : ℚ) := by
      apply one_div_le_one_div_of_le (by positivity) h2
    exact le_trans h3 h1
  have h_sum := Finset.card_nsmul_le_sum _ _ _ h_bound
  rw [Nat.card_Ico] at h_sum
  have h_len : 2 ^ (r + 1) - 2 ^ r = 2 ^ r := by
    have h1 : 2 ^ (r + 1) = 2 ^ r * 2 := by ring
    omega
  rw [h_len] at h_sum
  unfold thirdBlock
  calc (1 / 256 : ℚ)
    _ = (2 ^ r : ℕ) • (1 / (64 * 2 ^ (r + 2) : ℚ)) := by
      rw [nsmul_eq_mul]
      push_cast
      have h2r : (2 ^ (r + 2) : ℚ) = 4 * 2 ^ r := by
        have : (2 ^ (r + 2) : ℚ) = 2 ^ r * (2 : ℚ) ^ 2 := by rw [pow_add]
        rw [this]
        ring
      rw [h2r]
      have hd : (2 ^ r : ℚ) * (1 / (64 * (4 * 2 ^ r))) =
                (2 ^ r : ℚ) / (2 ^ r * 256) := by
        rw [mul_one_div]
        congr 1
        ring
      rw [hd]
      have h2k : (2 ^ r : ℚ) ≠ 0 := by positivity
      have h2k2 : (2 ^ r : ℚ) * 1 = 2 ^ r := by ring
      have h2k3 : (2 ^ r : ℚ) / (2 ^ r * 256) =
                  ((2 ^ r : ℚ) * 1) / (2 ^ r * 256) := by rw [h2k2]
      rw [h2k3]
      rw [mul_div_mul_left _ _ h2k]
    _ ≤ ∑ l ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), secondBlock l := h_sum

private lemma sum_Ico_blocks {a : ℕ → ℚ} {b : ℕ → ℕ} (hb : Monotone b) {m n : ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Finset.Ico m n, ∑ j ∈ Finset.Ico (b k) (b (k + 1)), a j = ∑ j ∈ Finset.Ico (b m) (b n),
      a j := by
  induction n, hmn using Nat.le_induction with
  | base =>
    have h1 : Finset.Ico m m = ∅ := Finset.Ico_self m
    have h2 : Finset.Ico (b m) (b m) = ∅ := Finset.Ico_self (b m)
    rw [h1, h2, Finset.sum_empty, Finset.sum_empty]
  | succ d hd ih =>
    rw [Finset.sum_Ico_succ_top hd, ih]
    have h_adj : b m ≤ b d := hb hd
    have h_adj2 : b d ≤ b (d + 1) := hb (by omega)
    rw [Finset.sum_Ico_consecutive _ h_adj h_adj2]

private lemma mono_pow_2 : Monotone (fun x => 2 ^ x) :=
  fun _ _ h => Nat.pow_le_pow_right (by decide) h

private lemma mono_pow_2_2 : Monotone (fun x => 2 ^ 2 ^ x) :=
  fun _ _ h => mono_pow_2 (mono_pow_2 h)

private lemma mono_pow_2_2_2 : Monotone (fun x => 2 ^ 2 ^ 2 ^ x) :=
  fun _ _ h => mono_pow_2 (mono_pow_2_2 h)

/-- F-diverges with an explicit integer certificate: for `N ≥ 1`, the partial sum of
`2^{-F (E_j)}` up to `R = 2^{2^{2^{N+2}}} - 1` is at least `N / 256` (the blocks `J_2, …, J_{N+1}`
are disjoint and adjacent, and `J_r` is the sum over `2^{2^{2^r}} ≤ j < 2^{2^{2^{r+1}}}`).
Blueprint 04 Corollary F-diverges (DB4) (`04-DB4`). -/
theorem discountSums_discountF_ge {N : ℕ} (hN : 1 ≤ N) :
    (N : ℚ) / 256 ≤ discountSums discountF (2 ^ 2 ^ 2 ^ (N + 2) - 1) := by
  have h_sum_third : ∀ r, thirdBlock r = ∑ j ∈ Finset.Ico (2 ^ 2 ^ 2 ^ r) (2 ^ 2 ^ 2 ^ (r + 1)),
    (1 / 2 : ℚ) ^ discountF (expSchedule j) := by
    intro r
    unfold thirdBlock secondBlock firstBlock
    have h1 : ∑ l ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)),
      ∑ k ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)),
      ∑ j ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), (1 / 2 : ℚ) ^ discountF (expSchedule j) =
      ∑ l ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)),
      ∑ j ∈ Finset.Ico (2 ^ 2 ^ l) (2 ^ 2 ^ (l + 1)), (1 / 2 : ℚ) ^ discountF (expSchedule j) := by
        apply Finset.sum_congr rfl
        intro l hl
        have hl_le : 2 ^ l ≤ 2 ^ (l + 1) := mono_pow_2 (by omega)
        exact sum_Ico_blocks mono_pow_2 hl_le
    rw [h1]
    have hr_le : 2 ^ r ≤ 2 ^ (r + 1) := mono_pow_2 (by omega)
    exact sum_Ico_blocks mono_pow_2_2 hr_le
  have h_sum_N : ∑ r ∈ Finset.Ico 2 (N + 2), thirdBlock r =
      ∑ j ∈ Finset.Ico (2 ^ 2 ^ 2 ^ 2) (2 ^ 2 ^ 2 ^ (N + 2)),
        (1 / 2 : ℚ) ^ discountF (expSchedule j) := by
    have hs1 : ∑ r ∈ Finset.Ico 2 (N + 2), thirdBlock r =
        ∑ r ∈ Finset.Ico 2 (N + 2), ∑ j ∈ Finset.Ico (2 ^ 2 ^ 2 ^ r) (2 ^ 2 ^ 2 ^ (r + 1)),
          (1 / 2 : ℚ) ^ discountF (expSchedule j) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact h_sum_third r
    rw [hs1]
    have hn_le : 2 ≤ N + 2 := by omega
    exact sum_Ico_blocks mono_pow_2_2_2 hn_le
  have h_N_bound : (N : ℚ) / 256 ≤ ∑ r ∈ Finset.Ico 2 (N + 2), thirdBlock r := by
    have h_each : ∀ r ∈ Finset.Ico 2 (N + 2), (1 / 256 : ℚ) ≤ thirdBlock r := by
      intro r hr
      rw [Finset.mem_Ico] at hr
      exact thirdBlock_ge hr.1
    have h_card := Finset.card_nsmul_le_sum _ _ _ h_each
    rw [Nat.card_Ico] at h_card
    have h_sub : N + 2 - 2 = N := by omega
    rw [h_sub, nsmul_eq_mul] at h_card
    have hm : (N : ℚ) * (1 / 256) = (N : ℚ) / 256 := by ring
    rw [hm] at h_card
    exact h_card
  have h_Ico_sub : Finset.Ico (2 ^ 2 ^ 2 ^ 2) (2 ^ 2 ^ 2 ^ (N + 2)) ⊆
      Finset.Icc 1 (2 ^ 2 ^ 2 ^ (N + 2)
    - 1)
    := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_Icc]
    have h16 : 1 ≤ 2 ^ 2 ^ 2 ^ 2 := by decide
    have hj1 : 1 ≤ j := by omega
    have hj2 : j ≤ 2 ^ 2 ^ 2 ^ (N + 2) - 1 := by omega
    exact ⟨hj1, hj2⟩
  have h_sum_le : ∑ j ∈ Finset.Ico (2 ^ 2 ^ 2 ^ 2) (2 ^ 2 ^ 2 ^ (N + 2)),
    (1 / 2 : ℚ) ^ discountF (expSchedule j) ≤
      ∑ j ∈ Finset.Icc 1 (2 ^ 2 ^ 2 ^ (N + 2) - 1), (1 / 2 : ℚ) ^ discountF (expSchedule j) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h_Ico_sub
    intro i hi1 hi2
    positivity
  have hd : discountSums discountF (2 ^ 2 ^ 2 ^ (N + 2) - 1) =
      ∑ j ∈ Finset.Icc 1 (2 ^ 2 ^ 2 ^ (N + 2) - 1), (1 / 2 : ℚ)
    ^ discountF (expSchedule j)
    := rfl
  rw [hd]
  rw [← h_sum_N] at h_sum_le
  exact le_trans h_N_bound h_sum_le

/-- DIV for the discount `F`: the partial sums `Σ_{i=1}^{R} 2^{-F (E_i)}` are unbounded
(take `N = 256 Q` in DB4; `Q = 0` is trivial).  Blueprint 04 Corollary F-diverges (`04-DB4`). -/
theorem discountF_hasDivergentSums : HasDivergentSums discountF := by
  intro Q
  obtain h | h := eq_or_lt_of_le (zero_le Q)
  · use 0
    rw [←h, discountSums]
    simp
  · use 2 ^ 2 ^ 2 ^ (256 * Q + 2) - 1
    have hN : 1 ≤ 256 * Q := Nat.succ_le_of_lt (Nat.mul_pos (by decide) h)
    have := discountSums_discountF_ge (N := 256 * Q) hN
    have h1 : ((256 * Q : ℕ) : ℚ) / 256 = Q := by
      push_cast
      ring
    rw [h1] at this
    exact this

/-- The explicit horizon `R_c = 2^{2^{2^{N_c + 2}}} - 1` with `N_c = 1024 · 2^c` of EXPLICIT-R.
Blueprint 04 Corollary F-diverges, (EXPLICIT-R) (`04-DB4`). -/
def explicitRounds (c : ℕ) : ℕ := 2 ^ 2 ^ 2 ^ (1024 * 2 ^ c + 2) - 1

/-- EXPLICIT-R: the explicit horizon `R_c` satisfies the round-search test
`Σ_{i=1}^{R_c} 2^{-F (E_i)} ≥ 4 · 2^c` (a termination certificate for the first-success search,
with no claim of a good size estimate).  Blueprint 04 Corollary F-diverges, (EXPLICIT-R)
(`04-DB4`). -/
theorem explicitRounds_spec (c : ℕ) :
    (4 * 2 ^ c : ℚ) ≤ discountSums discountF (explicitRounds c) := by
  unfold explicitRounds
  have hN : 1 ≤ 1024 * 2 ^ c := by
    have hc : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    calc
      1 ≤ 1024 * 1 := by norm_num
      _ ≤ 1024 * 2 ^ c := Nat.mul_le_mul_left 1024 hc
  have := discountSums_discountF_ge (N := 1024 * 2 ^ c) hN
  have h1 : ((1024 * 2 ^ c : ℕ) : ℚ) / 256 = 4 * 2 ^ c := by
    push_cast
    ring
  rwa [h1] at this

end Kolmogorov
