import KolmogorovMathlib.Solomonoff.SelectedBits.Flow
import KolmogorovMathlib.Solomonoff.SelectedBits.Gain

/-!
# Antichain packing and the envelope process

The key estimate of the selected-bit argument.  Let `A t` (`t ∈ ℕ`) be raw flows from a node `v`
that increase pointwise with `t`, with root masses `a t = A t v`, let `b` be a nondecreasing
nonnegative sequence (the stage mass of the forbidden sibling of `v`), and let `r t` be the
rational sibling ratio `ratioOf (a t) (b t)`.  The *packed demand*

  `packedDemand G A r s y = max_{t ≤ s} gain t (r t) * A t y`

may be large at different words for different times, yet on every finite prefix-free set of
extensions of `v` its sum is at most `a s + b s` (`sum_packedDemand_le`).  The proof chooses a
witness time per word, groups the words by time (`fiberMass`, `cumulativeMass`), bounds the
cumulative masses by the antichain bound of the raw flows (`cumulativeMass_succ_le`) and applies
the scalar `packing` property of the gain family (`sum_gain_mul_le_of_witness`).

The *envelope process* `envelopeProcess G A r v D s` is the truncated antichain envelope of the
packed demand at stage `s`.  It is a raw flow from `v`, nondecreasing in `s`, dominates
`gain s (r s) * A s` and has root at most `a s + b s` (`envelopeProcess_root_le`).
-/

namespace Kolmogorov.SelectedBits

/-! ### The packed demand -/

/-- The **packed demand** at stage `s`: the largest amplified mass `gain t (r t) * A t y` over
the times `t ≤ s`. -/
noncomputable def packedDemand (G : GainFamily) (A : ℕ → BitString → ℝ) (r : ℕ → ℚ) (s : ℕ)
    (y : BitString) : ℝ :=
  (Finset.range (s + 1)).sup' Finset.nonempty_range_add_one
    (fun t => (G.gain t (r t) : ℝ) * A t y)

/-- Every amplified mass at a time `t ≤ s` is at most the packed demand at stage `s`. -/
theorem gain_mul_le_packedDemand (G : GainFamily) (A : ℕ → BitString → ℝ) (r : ℕ → ℚ)
    {s t : ℕ} (ht : t ≤ s) (y : BitString) :
    (G.gain t (r t) : ℝ) * A t y ≤ packedDemand G A r s y :=
  Finset.le_sup' (fun t => (G.gain t (r t) : ℝ) * A t y)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))

/-- The packed demand is attained at some witness time `t ≤ s`. -/
theorem exists_packedDemand_eq (G : GainFamily) (A : ℕ → BitString → ℝ) (r : ℕ → ℚ) (s : ℕ)
    (y : BitString) :
    ∃ t ≤ s, packedDemand G A r s y = (G.gain t (r t) : ℝ) * A t y := by
  obtain ⟨t, ht, h⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    (fun t => (G.gain t (r t) : ℝ) * A t y)
  exact ⟨t, Nat.lt_succ_iff.mp (Finset.mem_range.mp ht), h⟩

/-- The packed demand does not decrease from one stage to the next. -/
theorem packedDemand_le_succ (G : GainFamily) (A : ℕ → BitString → ℝ) (r : ℕ → ℚ) (s : ℕ)
    (y : BitString) : packedDemand G A r s y ≤ packedDemand G A r (s + 1) y :=
  Finset.sup'_mono (fun t => (G.gain t (r t) : ℝ) * A t y)
    (Finset.range_subset_range.mpr (Nat.le_succ (s + 1))) Finset.nonempty_range_add_one

/-- The packed demand of nonnegative masses is nonnegative. -/
theorem packedDemand_nonneg (G : GainFamily) {A : ℕ → BitString → ℝ} (hA : ∀ t y, 0 ≤ A t y)
    (r : ℕ → ℚ) (s : ℕ) (y : BitString) : 0 ≤ packedDemand G A r s y :=
  (mul_nonneg (G.gain_cast_pos 0 (r 0)).le (hA 0 y)).trans
    (gain_mul_le_packedDemand G A r (Nat.zero_le s) y)

/-! ### Grouping an antichain by witness times -/

/-- The mass of the time fiber `t`: the sum of `A t y` over the words `y ∈ S` with witness time
`τ y = t`. -/
noncomputable def fiberMass (A : ℕ → BitString → ℝ) (S : Finset BitString) (τ : BitString → ℕ)
    (t : ℕ) : ℝ :=
  ∑ y ∈ S.filter (fun y => τ y = t), A t y

/-- The cumulative mass of the time fibers before `t`. -/
noncomputable def cumulativeMass (A : ℕ → BitString → ℝ) (S : Finset BitString)
    (τ : BitString → ℕ) (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range t, fiberMass A S τ j

/-- The cumulative mass is `0` before the first time. -/
@[simp] theorem cumulativeMass_zero (A : ℕ → BitString → ℝ) (S : Finset BitString)
    (τ : BitString → ℕ) : cumulativeMass A S τ 0 = 0 := by
  simp [cumulativeMass]

/-- One step of the cumulative mass adds the next fiber. -/
theorem cumulativeMass_succ (A : ℕ → BitString → ℝ) (S : Finset BitString)
    (τ : BitString → ℕ) (t : ℕ) :
    cumulativeMass A S τ (t + 1) = cumulativeMass A S τ t + fiberMass A S τ t :=
  Finset.sum_range_succ _ _

/-- For nonnegative masses the cumulative mass is monotone. -/
theorem monotone_cumulativeMass {A : ℕ → BitString → ℝ} (hA : ∀ t y, 0 ≤ A t y)
    (S : Finset BitString) (τ : BitString → ℕ) : Monotone (cumulativeMass A S τ) :=
  monotone_nat_of_le_succ fun t => by
    rw [cumulativeMass_succ]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun y _ => hA t y)

/-- **The cumulative masses fit below the valid mass.**  If the `A t` are raw flows from `v`
increasing in `t` and `S` is a finite prefix-free set of extensions of `v`, then the fibers of
the times `≤ t` carry at most `A t v`: each term `A (τ y) y` of these fibers is `≤ A t y` by
monotonicity in time, the fibers regroup into the sum of `A t` over the sub-antichain
`S.filter (τ · ≤ t)`, and the antichain bound `IsRawFlowFrom.sum_antichain_le` for `A t`
concludes. -/
theorem cumulativeMass_succ_le {A : ℕ → BitString → ℝ} {v : BitString}
    (hflow : ∀ t, IsRawFlowFrom v (A t)) (hmono : ∀ t y, A t y ≤ A (t + 1) y)
    (S : Finset BitString) (hext : ∀ y ∈ S, v <+: y) (hS : IsPrefixFree (S : Set BitString))
    (τ : BitString → ℕ) (t : ℕ) : cumulativeMass A S τ (t + 1) ≤ A t v := by
  have hmaps : ∀ y ∈ S.filter (fun y => τ y ≤ t), τ y ∈ Finset.range (t + 1) := fun y hy =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hy).2)
  calc cumulativeMass A S τ (t + 1)
      ≤ ∑ j ∈ Finset.range (t + 1), ∑ y ∈ S.filter (fun y => τ y = j), A t y := by
        unfold cumulativeMass fiberMass
        refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun y _ => ?_
        exact monotone_nat_of_le_succ (fun k => hmono k y)
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = ∑ y ∈ S.filter (fun y => τ y ≤ t), A t y := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.filter_filter]
        refine Finset.sum_congr (Finset.filter_congr fun y _ => ?_) fun _ _ => rfl
        have hjt := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact ⟨fun h => ⟨h ▸ hjt, h⟩, fun h => h.2⟩
    _ ≤ A t v :=
        (hflow t).sum_antichain_le _ (fun y hy => hext y (Finset.mem_filter.mp hy).1)
          (hS.mono (Finset.coe_subset.mpr (Finset.filter_subset _ S)))

/-- **Regrouping by time fibers.**  When every witness time is at most `s`, the sum of the
amplified masses over `S` is the sum over the times `t ≤ s` of the fiber increments of the
cumulative mass, weighted by the gain at time `t`. -/
theorem sum_gain_mul_eq_sum_cumulativeMass (G : GainFamily) (A : ℕ → BitString → ℝ)
    (r : ℕ → ℚ) (s : ℕ) (S : Finset BitString) (τ : BitString → ℕ) (hτ : ∀ y ∈ S, τ y ≤ s) :
    ∑ y ∈ S, (G.gain (τ y) (r (τ y)) : ℝ) * A (τ y) y =
      ∑ t ∈ Finset.range (s + 1),
        (cumulativeMass A S τ (t + 1) - cumulativeMass A S τ t) * (G.gain t (r t) : ℝ) := by
  have hmaps : ∀ y ∈ S, τ y ∈ Finset.range (s + 1) := fun y hy =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hτ y hy))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [cumulativeMass_succ, add_sub_cancel_left, fiberMass, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [(Finset.mem_filter.mp hy).2]
  ring

/-! ### The packing bound -/

/-- **Antichain packing with witness times.**  Let the `A t` be raw flows from `v`, increasing
in `t`, let `b` be nondecreasing and nonnegative, and let `r t` be the sibling ratio of
`A t v` and `b t`.  For a finite prefix-free set `S` of extensions of `v` and any witness times
`τ y ≤ s`, the amplified masses `gain (τ y) (r (τ y)) * A (τ y) y` sum to at most
`A s v + b s`: regroup by time fibers and apply `G.packing` to `a t = A t v`, `b` and
`w = cumulativeMass A S τ`. -/
theorem sum_gain_mul_le_of_witness (G : GainFamily) {A : ℕ → BitString → ℝ} {v : BitString}
    {b : ℕ → ℝ} {r : ℕ → ℚ} (hflow : ∀ t, IsRawFlowFrom v (A t))
    (hmono : ∀ t y, A t y ≤ A (t + 1) y) (hb : Monotone b) (hb0 : ∀ t, 0 ≤ b t)
    (hr : ∀ t, (r t : ℝ) = ratioOf (A t v) (b t)) (s : ℕ) (S : Finset BitString)
    (hext : ∀ y ∈ S, v <+: y) (hS : IsPrefixFree (S : Set BitString)) (τ : BitString → ℕ)
    (hτ : ∀ y ∈ S, τ y ≤ s) :
    ∑ y ∈ S, (G.gain (τ y) (r (τ y)) : ℝ) * A (τ y) y ≤ A s v + b s := by
  rw [sum_gain_mul_eq_sum_cumulativeMass G A r s S τ hτ]
  have hA0 : ∀ t y, 0 ≤ A t y := fun t y => (hflow t).nonneg y
  exact G.packing s (fun t => A t v) b (cumulativeMass A S τ) r
    (monotone_nat_of_le_succ fun t => hmono t v) hb (fun t => hA0 t v) hb0
    (monotone_cumulativeMass hA0 S τ) (cumulativeMass_zero A S τ)
    (fun t _ => cumulativeMass_succ_le hflow hmono S hext hS τ t) (fun t _ => hr t)

/-- **Antichain packing of the packed demand.**  Under the hypotheses of
`sum_gain_mul_le_of_witness`, the packed demand at stage `s` sums to at most `A s v + b s` over
every finite prefix-free set of extensions of `v`. -/
theorem sum_packedDemand_le (G : GainFamily) {A : ℕ → BitString → ℝ} {v : BitString}
    {b : ℕ → ℝ} {r : ℕ → ℚ} (hflow : ∀ t, IsRawFlowFrom v (A t))
    (hmono : ∀ t y, A t y ≤ A (t + 1) y) (hb : Monotone b) (hb0 : ∀ t, 0 ≤ b t)
    (hr : ∀ t, (r t : ℝ) = ratioOf (A t v) (b t)) (s : ℕ) (S : Finset BitString)
    (hext : ∀ y ∈ S, v <+: y) (hS : IsPrefixFree (S : Set BitString)) :
    ∑ y ∈ S, packedDemand G A r s y ≤ A s v + b s := by
  choose τ hτs hτ using fun y => exists_packedDemand_eq G A r s y
  calc ∑ y ∈ S, packedDemand G A r s y
      = ∑ y ∈ S, (G.gain (τ y) (r (τ y)) : ℝ) * A (τ y) y :=
        Finset.sum_congr rfl fun y _ => hτ y
    _ ≤ A s v + b s :=
        sum_gain_mul_le_of_witness G hflow hmono hb hb0 hr s S hext hS τ fun y _ => hτs y

/-! ### The envelope process -/

/-- The **envelope process** at stage `s`: the antichain envelope of the packed demand below
`v`, truncated at the absolute length `D`. -/
noncomputable def envelopeProcess (G : GainFamily) (A : ℕ → BitString → ℝ) (r : ℕ → ℚ)
    (v : BitString) (D s : ℕ) : BitString → ℝ :=
  truncatedEnvelope (packedDemand G A r s) v D

/-- The envelope process of nonnegative masses is a raw flow from `v`. -/
theorem isRawFlowFrom_envelopeProcess (G : GainFamily) {A : ℕ → BitString → ℝ}
    (hA : ∀ t y, 0 ≤ A t y) (r : ℕ → ℚ) (v : BitString) (D s : ℕ) :
    IsRawFlowFrom v (envelopeProcess G A r v D s) :=
  isRawFlowFrom_truncatedEnvelope (fun y => packedDemand_nonneg G hA r s y) v D

/-- The envelope process does not decrease from one stage to the next. -/
theorem envelopeProcess_le_succ (G : GainFamily) (A : ℕ → BitString → ℝ) (r : ℕ → ℚ)
    (v : BitString) (D s : ℕ) (y : BitString) :
    envelopeProcess G A r v D s y ≤ envelopeProcess G A r v D (s + 1) y :=
  truncatedEnvelope_mono (fun x => packedDemand_le_succ G A r s x) v D y

/-- The envelope process dominates the current amplified mass inside its domain. -/
theorem gain_mul_le_envelopeProcess (G : GainFamily) (A : ℕ → BitString → ℝ) (r : ℕ → ℚ)
    {v y : BitString} {D : ℕ} (s : ℕ) (hvy : v <+: y) (hyD : y.length ≤ D) :
    (G.gain s (r s) : ℝ) * A s y ≤ envelopeProcess G A r v D s y :=
  (gain_mul_le_packedDemand G A r le_rfl y).trans
    (le_truncatedEnvelope (packedDemand G A r s) hvy hyD)

/-- **The root of the envelope process is at most `a s + b s`.** -/
theorem envelopeProcess_root_le (G : GainFamily) {A : ℕ → BitString → ℝ} {v : BitString}
    {b : ℕ → ℝ} {r : ℕ → ℚ} (hflow : ∀ t, IsRawFlowFrom v (A t))
    (hmono : ∀ t y, A t y ≤ A (t + 1) y) (hb : Monotone b) (hb0 : ∀ t, 0 ≤ b t)
    (hr : ∀ t, (r t : ℝ) = ratioOf (A t v) (b t)) (D s : ℕ) :
    envelopeProcess G A r v D s v ≤ A s v + b s := by
  by_cases hvD : v.length ≤ D
  · rw [envelopeProcess, truncatedEnvelope_of_prefix List.prefix_rfl hvD]
    obtain ⟨S, hS, hext, -, hsum⟩ :=
      exists_prefixFree_sum_eq_finiteEnvelope (packedDemand G A r s) (D - v.length) v
    rw [← hsum]
    exact sum_packedDemand_le G hflow hmono hb hb0 hr s S hext hS
  · rw [envelopeProcess, truncatedEnvelope_of_not fun h => hvD h.2]
    exact add_nonneg ((hflow s).nonneg v) (hb0 s)

end Kolmogorov.SelectedBits
