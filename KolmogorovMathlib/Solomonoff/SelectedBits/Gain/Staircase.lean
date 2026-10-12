import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun
import KolmogorovMathlib.Solomonoff.SelectedBits.Gain

/-!
# The staircase gains

For an integer `m ≥ 1` the staircase gain at stage `s` and ratio `r` is
`1 + ∑_{1 ≤ j ≤ s} c_j [r > t_j]` with thresholds `t_j = 2^{-m j}` and weights
`c_j = 2^{-(m+1) j}`.  All its ingredients are rational and the comparisons are decidable, so it
enters the enumerator of the demands without real powers.  Its limit multiplier is
`1 + c_{j(e)}`, where `j(e)` is the least `j ≥ 1` with `e > t_j` (and `1` if there is none), its
logarithmic constant is `2^{-(m+1)} log 2` and its exponent is `1 + 1 / m`; with `m` large the
exponent approaches `1`, which gives every exponent `γ > 1`.

* `stairThreshold`, `stairWeight`, `staircaseGain`, `computable₂_staircaseGain`.
* `threshold_packing_le`: in the packing setting, the blocks whose ratio exceeds a threshold
  `θ > 0` have total mass at most `b s / θ`.
* `sum_stairWeight_div_stairThreshold_le_one`, `staircaseGain_packing`: summing the threshold
  bound with the weights `c_j` costs `b s ∑ c_j / t_j ≤ b s`.
* `staircaseTarget`, `staircaseTarget_spec`, `staircaseGain_target_liminf`,
  `staircaseGain_log_target`, and the family `staircaseGainFamily m hm`.
-/

namespace Kolmogorov.SelectedBits

open Filter Topology

/-! ### Thresholds, weights and the gain -/

/-- The `j`-th threshold `t_j = 2^{-m j}`. -/
def stairThreshold (m j : ℕ) : ℚ := (1 / 2) ^ (m * j)

/-- The `j`-th weight `c_j = 2^{-(m+1) j}`. -/
def stairWeight (m j : ℕ) : ℚ := (1 / 2) ^ ((m + 1) * j)

/-- The staircase gain `1 + ∑_{1 ≤ j ≤ s} c_j [t_j < r]` at stage `s` and ratio `r`. -/
def staircaseGain (m : ℕ) (s : ℕ) (r : ℚ) : ℚ :=
  1 + ∑ j ∈ Finset.Icc 1 s, if stairThreshold m j < r then stairWeight m j else 0

/-- The thresholds are positive. -/
theorem stairThreshold_pos (m j : ℕ) : 0 < stairThreshold m j := by
  unfold stairThreshold
  positivity

/-- The weights are positive. -/
theorem stairWeight_pos (m j : ℕ) : 0 < stairWeight m j := by
  unfold stairWeight
  positivity

/-- The weights are at most `1`. -/
theorem stairWeight_le_one (m j : ℕ) : stairWeight m j ≤ 1 := by
  unfold stairWeight
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- The weight over the threshold is `2^{-j}`. -/
theorem stairWeight_div_stairThreshold (m j : ℕ) :
    stairWeight m j / stairThreshold m j = (1 / 2) ^ j := by
  unfold stairWeight stairThreshold
  rw [div_eq_iff (by positivity), ← pow_add]
  congr 1
  ring

/-- The geometric sum `∑_{1 ≤ j ≤ s} 2^{-j} = 1 - 2^{-s}`. -/
theorem sum_Icc_one_half_pow (s : ℕ) :
    ∑ j ∈ Finset.Icc 1 s, ((1 : ℚ) / 2) ^ j = 1 - (1 / 2) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

/-- The weights over the thresholds sum to at most `1`. -/
theorem sum_stairWeight_div_stairThreshold_le_one (m s : ℕ) :
    ∑ j ∈ Finset.Icc 1 s, stairWeight m j / stairThreshold m j ≤ 1 := by
  simp_rw [stairWeight_div_stairThreshold]
  rw [sum_Icc_one_half_pow]
  have : (0 : ℚ) ≤ (1 / 2) ^ s := by positivity
  linarith

/-- The staircase gain is at least `1`. -/
theorem one_le_staircaseGain (m s : ℕ) (r : ℚ) : 1 ≤ staircaseGain m s r := by
  refine le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => ?_)
  split_ifs
  · exact (stairWeight_pos m j).le
  · exact le_rfl

/-- A passed threshold `t_j < r` with `1 ≤ j ≤ s` contributes its weight to the gain. -/
theorem one_add_stairWeight_le_staircaseGain {m s j : ℕ} {r : ℚ} (hj1 : 1 ≤ j) (hjs : j ≤ s)
    (hr : stairThreshold m j < r) : 1 + stairWeight m j ≤ staircaseGain m s r := by
  unfold staircaseGain
  have hmem : j ∈ Finset.Icc 1 s := Finset.mem_Icc.mpr ⟨hj1, hjs⟩
  have h := Finset.single_le_sum
    (f := fun j => if stairThreshold m j < r then stairWeight m j else 0)
    (fun i _ => by
      split_ifs
      · exact (stairWeight_pos m i).le
      · exact le_rfl) hmem
  rw [ite_eq_left hr] at h
  linarith

/-- The real cast of the staircase gain. -/
theorem staircaseGain_cast (m s : ℕ) (r : ℚ) :
    (staircaseGain m s r : ℝ) =
      1 + ∑ j ∈ Finset.Icc 1 s, if stairThreshold m j < r then (stairWeight m j : ℝ) else 0 := by
  rw [staircaseGain, Rat.cast_add, Rat.cast_one, Rat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-! ### Computability -/

/-- The thresholds are computable. -/
theorem computable_stairThreshold (m : ℕ) : Computable (stairThreshold m) := by
  refine computable_of_num_den (N := fun _ : ℕ => (1 : ℤ)) (D := fun j => 2 ^ (m * j))
    (Computable.const 1) ?_ (fun j => by positivity) (fun j => ?_)
  · exact comp_pow.comp (Primrec.nat_mul.comp (Primrec.const m) Primrec.id).to_comp
  · simp [stairThreshold]

/-- The weights are computable. -/
theorem computable_stairWeight (m : ℕ) : Computable (stairWeight m) := by
  refine computable_of_num_den (N := fun _ : ℕ => (1 : ℤ)) (D := fun j => 2 ^ ((m + 1) * j))
    (Computable.const 1) ?_ (fun j => by positivity) (fun j => ?_)
  · exact comp_pow.comp (Primrec.nat_mul.comp (Primrec.const (m + 1)) Primrec.id).to_comp
  · simp [stairWeight]

/-- The `j`-th staircase summand: `c_j` if `t_j < r`, and `0` otherwise. -/
def stairTerm (m : ℕ) (r : ℚ) (j : ℕ) : ℚ :=
  if stairThreshold m j < r then stairWeight m j else 0

/-- The staircase summand is computable in the ratio and the index. -/
theorem computable₂_stairTerm (m : ℕ) : Computable₂ (stairTerm m) := by
  have hc : Computable (fun p : ℚ × ℕ => decide (stairThreshold m p.2 < p.1)) :=
    computable₂_ratLt.comp ((computable_stairThreshold m).comp Computable.snd) Computable.fst
  refine (Computable.cond hc ((computable_stairWeight m).comp Computable.snd)
    (Computable.const 0)).of_eq fun p => ?_
  simp [stairTerm]

/-- The partial staircase sum `∑_{1 ≤ j ≤ n} stairTerm m r j`, by recursion on `n`. -/
def stairPartial (m : ℕ) (r : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => stairPartial m r n + stairTerm m r (n + 1)

/-- The recursive partial sum is the sum over `Finset.Icc 1 n`. -/
theorem stairPartial_eq (m : ℕ) (r : ℚ) (n : ℕ) :
    stairPartial m r n = ∑ j ∈ Finset.Icc 1 n, stairTerm m r j := by
  induction n with
  | zero => simp [stairPartial]
  | succ n ih => rw [stairPartial, ih, Finset.sum_Icc_succ_top (by omega)]

/-- The staircase gain is one plus the recursive partial sum. -/
theorem staircaseGain_eq_stairPartial (m s : ℕ) (r : ℚ) :
    staircaseGain m s r = 1 + stairPartial m r s := by
  rw [stairPartial_eq]
  rfl

/-- The staircase gain is computable in the stage and the ratio. -/
theorem computable₂_staircaseGain (m : ℕ) : Computable₂ (staircaseGain m) := by
  have hh : Computable₂ (fun (p : ℕ × ℚ) (q : ℕ × ℚ) => q.2 + stairTerm m p.2 (q.1 + 1)) := by
    have h1 : Computable (fun x : (ℕ × ℚ) × (ℕ × ℚ) => x.2.2) :=
      Computable.snd.comp Computable.snd
    have h2 : Computable (fun x : (ℕ × ℚ) × (ℕ × ℚ) => stairTerm m x.1.2 (x.2.1 + 1)) :=
      (computable₂_stairTerm m).comp (Computable.snd.comp Computable.fst)
        (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))
    exact computable₂_ratAdd.comp h1 h2
  have hrec := Computable.nat_rec (σ := ℚ) Computable.fst (Computable.const (0 : ℚ)) hh
  have hpart : Computable (fun p : ℕ × ℚ => stairPartial m p.2 p.1) := by
    refine hrec.of_eq fun p => ?_
    obtain ⟨s, r⟩ := p
    induction s with
    | zero => rfl
    | succ s ih => simpa [stairPartial] using congrArg (· + stairTerm m r (s + 1)) ih
  exact (computable₂_ratAdd.comp (Computable.const 1) hpart).of_eq fun p =>
    (staircaseGain_eq_stairPartial m p.1 p.2).symm

/-! ### Packing -/

/-- **Threshold packing.**  In the packing setting, the blocks `[w t, w (t + 1)]`, `t ≤ s`,
whose ratio exceeds a threshold `θ > 0` have total mass at most `b s / θ`: they all lie below
`w (t* + 1) ≤ a t*` for the last selected time `t*`, and `r t* > θ` gives `θ a t* < b t*`. -/
theorem threshold_packing_le {s : ℕ} {a b w : ℕ → ℝ} {r : ℕ → ℚ} (hb : Monotone b)
    (ha0 : ∀ t, 0 ≤ a t) (hb0 : ∀ t, 0 ≤ b t) (hw : Monotone w) (hw0 : w 0 = 0)
    (hwa : ∀ t ≤ s, w (t + 1) ≤ a t) (hr : ∀ t ≤ s, (r t : ℝ) = ratioOf (a t) (b t))
    {θ : ℚ} (hθ : 0 < θ) :
    ∑ t ∈ (Finset.range (s + 1)).filter (fun t => θ < r t), (w (t + 1) - w t) ≤
      b s / (θ : ℝ) := by
  set F := (Finset.range (s + 1)).filter (fun t => θ < r t) with hF
  have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · rw [hFe, Finset.sum_empty]
    exact div_nonneg (hb0 s) hθR.le
  set T := F.max' hFne with hT
  obtain ⟨hTs, hθT⟩ := Finset.mem_filter.mp (F.max'_mem hFne)
  have hTs' : T ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hTs)
  have hsub : F ⊆ Finset.range (T + 1) := fun t ht =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (F.le_max' t ht))
  have hsum : ∑ t ∈ F, (w (t + 1) - w t) ≤ w (T + 1) := by
    calc ∑ t ∈ F, (w (t + 1) - w t) ≤ ∑ t ∈ Finset.range (T + 1), (w (t + 1) - w t) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun t _ _ => sub_nonneg.mpr (hw (Nat.le_succ t)))
      _ = w (T + 1) := by rw [Finset.sum_range_sub, hw0, sub_zero]
  have hrT : (θ : ℝ) < ratioOf (a T) (b T) := by
    rw [← hr T hTs']
    exact_mod_cast hθT
  have hpos : 0 < a T + b T := by
    rcases (add_nonneg (ha0 T) (hb0 T)).eq_or_lt with h | h
    · rw [ratioOf, ← h, div_zero] at hrT
      linarith
    · exact h
  have haT : a T ≤ b T / θ := by
    rw [ratioOf, lt_div_iff₀ hpos] at hrT
    rw [le_div_iff₀ hθR]
    nlinarith [mul_nonneg hθR.le (hb0 T)]
  calc ∑ t ∈ F, (w (t + 1) - w t) ≤ w (T + 1) := hsum
    _ ≤ a T := hwa T hTs'
    _ ≤ b T / θ := haT
    _ ≤ b s / θ := div_le_div_of_nonneg_right (hb hTs') hθR.le

/-- **Packing for the staircase gain.**  In the setting of `GainFamily.packing`, the blocks
weighted by the staircase gains fit into `a s + b s`: the unit parts telescope to
`w (s + 1) ≤ a s`; after extending each inner range `Icc 1 t` to `Icc 1 s` and swapping the
sums, the `j`-th time sum is bounded by `threshold_packing_le` at `θ = t_j`, and
`b s ∑ c_j / t_j ≤ b s`. -/
theorem staircaseGain_packing (m : ℕ) (s : ℕ) (a b w : ℕ → ℝ) (r : ℕ → ℚ)
    (_ha : Monotone a) (hb : Monotone b) (ha0 : ∀ t, 0 ≤ a t) (hb0 : ∀ t, 0 ≤ b t)
    (hw : Monotone w) (hw0 : w 0 = 0) (hwa : ∀ t ≤ s, w (t + 1) ≤ a t)
    (hr : ∀ t ≤ s, (r t : ℝ) = ratioOf (a t) (b t)) :
    ∑ t ∈ Finset.range (s + 1), (w (t + 1) - w t) * (staircaseGain m t (r t) : ℝ) ≤
      a s + b s := by
  have hterm : ∀ t j, 0 ≤ (w (t + 1) - w t) *
      (if stairThreshold m j < r t then (stairWeight m j : ℝ) else 0) := by
    intro t j
    refine mul_nonneg (sub_nonneg.mpr (hw (Nat.le_succ t))) ?_
    split_ifs
    · exact_mod_cast (stairWeight_pos m j).le
    · exact le_rfl
  have hsum : ∑ j ∈ Finset.Icc 1 s, ((stairWeight m j / stairThreshold m j : ℚ) : ℝ) ≤ 1 := by
    exact_mod_cast sum_stairWeight_div_stairThreshold_le_one m s
  calc ∑ t ∈ Finset.range (s + 1), (w (t + 1) - w t) * (staircaseGain m t (r t) : ℝ)
      = ∑ t ∈ Finset.range (s + 1), (w (t + 1) - w t) +
          ∑ t ∈ Finset.range (s + 1), ∑ j ∈ Finset.Icc 1 t, (w (t + 1) - w t) *
            (if stairThreshold m j < r t then (stairWeight m j : ℝ) else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [staircaseGain_cast, mul_add, mul_one, Finset.mul_sum]
    _ ≤ w (s + 1) + ∑ t ∈ Finset.range (s + 1), ∑ j ∈ Finset.Icc 1 s, (w (t + 1) - w t) *
            (if stairThreshold m j < r t then (stairWeight m j : ℝ) else 0) := by
        rw [Finset.sum_range_sub, hw0, sub_zero]
        refine add_le_add le_rfl (Finset.sum_le_sum fun t ht => ?_)
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)))
          (fun j _ _ => hterm t j)
    _ = w (s + 1) + ∑ j ∈ Finset.Icc 1 s, (stairWeight m j : ℝ) *
          ∑ t ∈ (Finset.range (s + 1)).filter (fun t => stairThreshold m j < r t),
            (w (t + 1) - w t) := by
        rw [Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        split_ifs <;> ring
    _ ≤ w (s + 1) + ∑ j ∈ Finset.Icc 1 s,
          (stairWeight m j : ℝ) * (b s / (stairThreshold m j : ℝ)) := by
        refine add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_)
        exact mul_le_mul_of_nonneg_left
          (threshold_packing_le hb ha0 hb0 hw hw0 hwa hr (stairThreshold_pos m j))
          (by exact_mod_cast (stairWeight_pos m j).le)
    _ = w (s + 1) + b s * ∑ j ∈ Finset.Icc 1 s,
          ((stairWeight m j / stairThreshold m j : ℚ) : ℝ) := by
        rw [Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        push_cast
        ring
    _ ≤ a s + b s := by
        have h1 := hwa s le_rfl
        nlinarith [hb0 s]

/-! ### The limit multiplier -/

/-- The limit multiplier of the staircase: `1 + c_j` for the least `j ≥ 1` with `t_j < e`, and
`1` when no threshold lies below `e`. -/
noncomputable def staircaseTarget (m : ℕ) (e : ℝ) : ℝ := by
  classical
  exact if h : ∃ j, 1 ≤ j ∧ ((stairThreshold m j : ℚ) : ℝ) < e then
    1 + (stairWeight m (Nat.find h) : ℝ) else 1

/-- An instance-free description of the staircase target: either `j` is the least index
`j ≥ 1` with `t_j < e` and the target is `1 + c_j`, or no threshold of index `≥ 1` lies below
`e` and the target is `1`. -/
theorem staircaseTarget_spec (m : ℕ) (e : ℝ) :
    (∃ j, 1 ≤ j ∧ ((stairThreshold m j : ℚ) : ℝ) < e ∧
      (∀ i, 1 ≤ i → ((stairThreshold m i : ℚ) : ℝ) < e → j ≤ i) ∧
      staircaseTarget m e = 1 + (stairWeight m j : ℝ)) ∨
    ((∀ j, 1 ≤ j → e ≤ ((stairThreshold m j : ℚ) : ℝ)) ∧ staircaseTarget m e = 1) := by
  classical
  unfold staircaseTarget
  split_ifs with h
  · exact Or.inl ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2,
      fun i hi hie => Nat.find_min' h ⟨hi, hie⟩, rfl⟩
  · refine Or.inr ⟨fun j hj => ?_, rfl⟩
    by_contra hlt
    exact h ⟨j, hj, lt_of_not_ge hlt⟩

/-- The staircase target is at least `1`. -/
theorem one_le_staircaseTarget (m : ℕ) (e : ℝ) : 1 ≤ staircaseTarget m e := by
  rcases staircaseTarget_spec m e with ⟨j, -, -, -, h⟩ | ⟨-, h⟩
  · rw [h]
    exact le_add_of_nonneg_right (by exact_mod_cast (stairWeight_pos m j).le)
  · rw [h]

/-- The staircase gains along rational errors converging to `e` eventually exceed every value
below the target: if `t_j < e` then eventually `t_j < es s` and `j ≤ s`, so the gain is at least
`1 + c_j`; strict thresholds make continuity unnecessary. -/
theorem staircaseGain_target_liminf (m : ℕ) (e : ℝ) (es : ℕ → ℚ)
    (hes : Tendsto (fun s => (es s : ℝ)) atTop (𝓝 e)) (c : ℝ) (hc : c < staircaseTarget m e) :
    ∀ᶠ s in atTop, c < (staircaseGain m s (es s) : ℝ) := by
  rcases staircaseTarget_spec m e with ⟨j, hj1, hje, -, heq⟩ | ⟨-, heq⟩
  · rw [heq] at hc
    filter_upwards [hes.eventually (lt_mem_nhds hje), eventually_ge_atTop j] with s hs hjs
    have hq : stairThreshold m j < es s := by exact_mod_cast hs
    have hle : ((1 + stairWeight m j : ℚ) : ℝ) ≤ (staircaseGain m s (es s) : ℝ) := by
      exact_mod_cast one_add_stairWeight_le_staircaseGain hj1 hjs hq
    push_cast at hle
    linarith
  · rw [heq] at hc
    refine Eventually.of_forall fun s => ?_
    have h : (1 : ℝ) ≤ (staircaseGain m s (es s) : ℝ) := by
      exact_mod_cast one_le_staircaseGain m s (es s)
    linarith

/-- On `(0, 1]`, the least threshold below `e` has index `k + 1` with `e ≤ 2^{-m k}`, and the
staircase target is `1 + c_{k+1}`. -/
theorem exists_staircaseTarget_eq_of_pos (m : ℕ) (hm : 0 < m) {e : ℝ} (he : 0 < e)
    (he1 : e ≤ 1) :
    ∃ k : ℕ, e ≤ ((1 : ℝ) / 2) ^ (m * k) ∧
      staircaseTarget m e = 1 + (stairWeight m (k + 1) : ℝ) := by
  rcases staircaseTarget_spec m e with ⟨j, hj1, -, hmin, heq⟩ | ⟨hall, -⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    refine ⟨k, ?_, heq⟩
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simpa using he1
    · by_contra hlt
      have hk' := hmin k hk (by push_cast [stairThreshold]; exact lt_of_not_ge hlt)
      omega
  · exfalso
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one he (by norm_num : (1 / 2 : ℝ) < 1)
    have h := hall (n + 1) (by omega)
    have ht : ((stairThreshold m (n + 1) : ℚ) : ℝ) ≤ (1 / 2 : ℝ) ^ n := by
      push_cast [stairThreshold]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
        ((Nat.le_succ n).trans (Nat.le_mul_of_pos_left (n + 1) hm))
    linarith

/-- The logarithmic estimate of the staircase target for `m ≥ 1`:
`2^{-(m+1)} log 2 · e ^ (1 + 1/m) ≤ log (staircaseTarget m e)` on `[0, 1]`.  For `e = 0` both
sides vanish; for `0 < e ≤ 1` the least threshold below `e` has index `k + 1` with
`e ≤ 2^{-m k}`, so `2^{-(m+1)} e ^ (1 + 1/m) ≤ c_{k+1}`, and `c log 2 ≤ log (1 + c)` on
`[0, 1]`. -/
theorem staircaseGain_log_target (m : ℕ) (hm : 0 < m) (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (1 / 2) ^ (m + 1) * Real.log 2 * e ^ (1 + 1 / (m : ℝ)) ≤
      Real.log (staircaseTarget m e) := by
  have hβ : (0 : ℝ) < 1 + 1 / (m : ℝ) := by positivity
  rcases he0.eq_or_lt with he | he
  · subst he
    rw [Real.zero_rpow hβ.ne', mul_zero]
    exact Real.log_nonneg (one_le_staircaseTarget m 0)
  obtain ⟨k, hek, heq⟩ := exists_staircaseTarget_eq_of_pos m hm he he1
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hpow : e ^ (1 + 1 / (m : ℝ)) ≤ ((1 : ℝ) / 2) ^ ((m + 1) * k) := by
    calc e ^ (1 + 1 / (m : ℝ)) ≤ (((1 : ℝ) / 2) ^ (m * k)) ^ (1 + 1 / (m : ℝ)) :=
          Real.rpow_le_rpow he.le hek hβ.le
      _ = ((1 : ℝ) / 2) ^ ((m + 1) * k) := by
          have h1 : ((1 : ℝ) / 2) ^ (m * k) = ((1 : ℝ) / 2) ^ ((m * k : ℕ) : ℝ) :=
            (Real.rpow_natCast _ _).symm
          have h2 : ((1 : ℝ) / 2) ^ ((m + 1) * k) = ((1 : ℝ) / 2) ^ (((m + 1) * k : ℕ) : ℝ) :=
            (Real.rpow_natCast _ _).symm
          rw [h1, h2, ← Real.rpow_mul (by norm_num)]
          congr 1
          push_cast
          field_simp
  have hw : (stairWeight m (k + 1) : ℝ) =
      ((1 : ℝ) / 2) ^ (m + 1) * ((1 : ℝ) / 2) ^ ((m + 1) * k) := by
    push_cast [stairWeight]
    rw [← pow_add]
    congr 1
    ring
  have hc : ((1 : ℝ) / 2) ^ (m + 1) * e ^ (1 + 1 / (m : ℝ)) ≤ (stairWeight m (k + 1) : ℝ) := by
    rw [hw]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hc0 : (0 : ℝ) ≤ (stairWeight m (k + 1) : ℝ) := by
    exact_mod_cast (stairWeight_pos m (k + 1)).le
  have hc1 : (stairWeight m (k + 1) : ℝ) ≤ 1 := by exact_mod_cast stairWeight_le_one m (k + 1)
  rw [heq]
  calc (1 / 2) ^ (m + 1) * Real.log 2 * e ^ (1 + 1 / (m : ℝ))
      = ((1 / 2) ^ (m + 1) * e ^ (1 + 1 / (m : ℝ))) * Real.log 2 := by ring
    _ ≤ (stairWeight m (k + 1) : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hc (Real.log_nonneg one_le_two)
    _ ≤ Real.log (1 + (stairWeight m (k + 1) : ℝ)) := mul_log_two_le_log_one_add hc0 hc1

/-! ### The staircase gain family -/

/-- The **staircase gain family** of an integer `m ≥ 1`: thresholds `2^{-m j}`, weights
`2^{-(m+1) j}`, logarithmic constant `2^{-(m+1)} log 2` and exponent `1 + 1/m`. -/
noncomputable def staircaseGainFamily (m : ℕ) (hm : 0 < m) : GainFamily where
  gain := staircaseGain m
  one_le := one_le_staircaseGain m
  computable := computable₂_staircaseGain m
  packing := staircaseGain_packing m
  target := staircaseTarget m
  one_le_target := fun e _ _ => one_le_staircaseTarget m e
  target_liminf := fun e _ _ => staircaseGain_target_liminf m e
  kappa := (1 / 2) ^ (m + 1) * Real.log 2
  beta := 1 + 1 / (m : ℝ)
  kappa_pos := mul_pos (by positivity) (Real.log_pos one_lt_two)
  log_target := staircaseGain_log_target m hm

/-- The gain of the staircase family. -/
@[simp] theorem staircaseGainFamily_gain (m : ℕ) (hm : 0 < m) :
    (staircaseGainFamily m hm).gain = staircaseGain m := rfl

/-- The limit multiplier of the staircase family. -/
@[simp] theorem staircaseGainFamily_target (m : ℕ) (hm : 0 < m) :
    (staircaseGainFamily m hm).target = staircaseTarget m := rfl

/-- The logarithmic constant of the staircase family is `2^{-(m+1)} log 2`. -/
@[simp] theorem staircaseGainFamily_kappa (m : ℕ) (hm : 0 < m) :
    (staircaseGainFamily m hm).kappa = (1 / 2) ^ (m + 1) * Real.log 2 := rfl

/-- The exponent of the staircase family is `1 + 1/m`. -/
@[simp] theorem staircaseGainFamily_beta (m : ℕ) (hm : 0 < m) :
    (staircaseGainFamily m hm).beta = 1 + 1 / (m : ℝ) := rfl

end Kolmogorov.SelectedBits
