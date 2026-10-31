/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Lower.NullCovers

/-!
# Zero-potential pressure and entropy: nonnegativity and effective variants

For the zero potential, the classical and effective lower and upper entropies are the
nonnegative-parameter versions of the corresponding pressures.  This module proves the
comparison lemmas of the blueprint node `pressure:entropy-nonnegative`:

* the signed classical pressures `lowerPressure` and `upperPressure` of a nonempty set
  are nonnegative at the zero potential, and so are the effective pressures
  `effectiveLowerPressure` and `effectiveUpperPressure`, for every oracle;
* the effective entropies `effectiveLowerEntropy` and `effectiveUpperEntropy` are the
  nonnegative embeddings of the effective zero-potential pressures, since negative exponents
  admit neither null covers nor uniform nets;
* the classical entropies are bounded by the effective ones for every oracle.

These facts are used by the zero-potential entropy point-to-set principle in
`KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyPointToSet` and by the modules importing
`KolmogorovMathlib.PointToSet.Pressure.Lower`.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-- Birkhoff sums of the zero potential vanish. -/
private lemma birkhoffSum_fun_zero {α M : Type*} [AddCommMonoid M] (f : α → α) (n : ℕ) (x : α) :
    birkhoffSum f (fun _ ↦ (0 : M)) n x = 0 := by
  simp [birkhoffSum]

/-- The extended pressure rate at a positive order is nonnegative once the sum is at
least `1`. -/
private lemma pressureRate_nonneg_of_one_le {q : ℕ → ℝ≥0∞} {n : ℕ} (hn : 1 ≤ n)
    (hq : 1 ≤ q n) : 0 ≤ pressureRate q n := by
  have hn0 : n ≠ 0 := by omega
  have hrate : pressureRate q n = pressureLog (q n) * ((n : ℝ)⁻¹ : ℝ) := by
    simp [pressureRate, hn0]
  rw [hrate, pressureLog]
  exact EReal.mul_nonneg
    (EReal.mul_nonneg (ENNReal.zero_le_log_iff.2 hq)
      (EReal.coe_nonneg.2 (inv_nonneg.2 (Real.log_nonneg one_le_two))))
    (EReal.coe_nonneg.2 (inv_nonneg.2 n.cast_nonneg))

/-- If the sums are at least `1` from order `1` on, the upper limit of the pressure rates is
nonnegative. -/
private lemma zero_le_limsup_pressureRate {q : ℕ → ℝ≥0∞} (hq : ∀ n ≥ 1, 1 ≤ q n) :
    0 ≤ limsup (pressureRate q) atTop :=
  le_limsup_of_frequently_le (hu_le := isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩)
    (eventually_atTop.2 ⟨1, fun n hn ↦ pressureRate_nonneg_of_one_le hn (hq n hn)⟩).frequently

/-- The `EReal` coercion of an infimum of `ENNReal.ofReal s` over the nonnegative exponents
admitted by a predicate `Q` is the infimum of the exponents themselves. -/
private lemma coe_iInf_ofReal_nonneg {α : Type*} (Q : ℝ → α → Prop) :
    (↑(⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ E : α, ⨅ (_ : Q s E), ENNReal.ofReal s) : EReal) =
      ⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ E : α, ⨅ (_ : Q s E), (s : EReal) := by
  rw [EReal.coe_ennreal_iInf]
  refine iInf_congr fun s ↦ ?_
  rw [EReal.coe_ennreal_iInf]
  refine iInf_congr fun hs ↦ ?_
  rw [EReal.coe_ennreal_iInf]
  refine iInf_congr fun E ↦ ?_
  rw [EReal.coe_ennreal_iInf]
  exact iInf_congr fun _ ↦ by rw [EReal.coe_ennreal_ofReal, max_eq_left hs]

/-- If every admissible exponent is nonnegative, the infimum over all exponents equals the
infimum over nonnegative ones. -/
private lemma iInf_exponent_eq_iInf_nonneg {α : Type*} (Q : ℝ → α → Prop)
    (h : ∀ s E, Q s E → 0 ≤ s) :
    (⨅ s : ℝ, ⨅ E : α, ⨅ (_ : Q s E), (s : EReal)) =
      ⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ E : α, ⨅ (_ : Q s E), (s : EReal) := by
  refine iInf_congr fun s ↦ ?_
  by_cases hs : 0 ≤ s
  · rw [iInf_pos hs]
  · have hQ : ∀ E, ¬ Q s E := fun E hE ↦ hs (h s E hE)
    simp [hQ]

/-- The pressure data of the zero potential on a presentation, with the dyadic radii as
oscillation bounds. -/
noncomputable def zeroPotentialData (P : Presentation X) (T : X → X)
    (hT : Continuous T) : PressureData X where
  presentation := P
  T := T
  continuous_T := hT
  φ := fun _ ↦ 0
  uniformContinuous_φ := uniformContinuous_const
  p₀ := 0
  ω := dyadicRadius
  ω_pos := fun p _ ↦ dyadicRadius_pos p
  ω_tendsto := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  oscillation := fun p _ _ _ _ ↦ by
    rw [sub_self, abs_zero]
    exact (dyadicRadius_pos p).le

/-- A nonempty set has no zero-potential null cover with a negative exponent: the cover has
triples of unbounded order, hence is infinite, and each triple has weight at least `1`. -/
private lemma not_isNullPressureCover_zero_of_neg (P : Presentation X) (T : X → X)
    {Z : Set X} (hZ : Z.Nonempty) {s : ℝ} (hs : s < 0) (E : Set (ℕ × ℕ × ℕ)) :
    ¬ IsNullPressureCover P T (fun _ ↦ 0) 0 Z s E := by
  rintro ⟨-, hmass, hcover⟩
  obtain ⟨x, hx⟩ := hZ
  have hinf : E.Infinite := by
    refine Set.Infinite.of_image (fun t : ℕ × ℕ × ℕ ↦ t.2.1)
      (Set.infinite_of_not_bddAbove (not_bddAbove_iff.2 fun N ↦ ?_))
    obtain ⟨i, n, hn, hmem, -⟩ := hcover 0 le_rfl (N + 1) (by omega) x hx
    exact ⟨n, ⟨_, hmem, rfl⟩, by omega⟩
  have := hinf.to_subtype
  have hweight : ∀ t : E, (1 : ℝ≥0∞) ≤
      (2 : ℝ≥0∞) ^ (-s * t.val.2.1 + birkhoffSum T (fun _ ↦ (0 : ℝ)) t.val.2.1 (P.ι t.val.1)) :=
    fun t ↦ by
      rw [birkhoffSum_fun_zero, add_zero]
      calc (1 : ℝ≥0∞) = 2 ^ (0 : ℝ) := ENNReal.rpow_zero.symm
        _ ≤ _ := ENNReal.rpow_le_rpow_of_exponent_le one_le_two
          (mul_nonneg (neg_nonneg.2 hs.le) (Nat.cast_nonneg _))
  have htop : ⊤ ≤ nullPressureMass P T (fun _ ↦ 0) s E :=
    (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm.le.trans
      (ENNReal.tsum_le_tsum hweight)
  exact hmass.ne (top_le_iff.1 htop)

/-- A zero-potential uniform net of a nonempty set has a nonnegative exponent: the slice
covering a point has at least one index at every order, so its rate is nonnegative. -/
private lemma nonneg_of_isUniformPressureNet (P : Presentation X) (T : X → X) {Z : Set X}
    (hZ : Z.Nonempty) {s : ℝ} {E : Set (ℕ × ℕ × ℕ × ℕ)}
    (hE : IsUniformPressureNet P T (fun _ ↦ 0) 0 Z s E) : 0 ≤ s := by
  obtain ⟨-, hrate, hcover⟩ := hE
  obtain ⟨x, hx⟩ := hZ
  obtain ⟨k, hk⟩ := hcover 0 le_rfl x hx
  have hsum : ∀ n ≥ 1, 1 ≤ uniformPressureSum P T (fun _ ↦ 0) E n 0 k := fun n hn ↦ by
    obtain ⟨i, hi, -⟩ := hk n hn
    calc (1 : ℝ≥0∞) = 2 ^ birkhoffSum T (fun _ ↦ (0 : ℝ)) n (P.ι i) := by
          rw [birkhoffSum_fun_zero, ENNReal.rpow_zero]
      _ ≤ _ := ENNReal.le_tsum (f := fun j : {j : ℕ | (j, n, 0, k) ∈ E} ↦
          (2 : ℝ≥0∞) ^ birkhoffSum T (fun _ ↦ (0 : ℝ)) n (P.ι j.1)) ⟨i, hi⟩
  exact EReal.coe_nonneg.1 ((zero_le_limsup_pressureRate hsum).trans (hrate 0 le_rfl k))

/-- Effective lower entropy embeds as zero-potential effective pressure for every oracle.
Blueprint node `pressure:entropy-nonnegative`. -/
theorem entropy_eq_zeroPotentialPressure_of_nonempty_effective (P : Presentation X)
    (T : X → X) (hT : Continuous T) (A : Set ℕ) (Z : Set X) (hZ : Z.Nonempty) :
    (effectiveLowerEntropy P T A Z : EReal) =
      effectiveLowerPressure P T (fun _ => 0) 0 A Z := by
  have _ := hT
  refine (coe_iInf_ofReal_nonneg fun s E ↦
    IsNullPressureCover P T (fun _ ↦ 0) 0 Z s E ∧ IsREIn A E).trans
    (iInf_exponent_eq_iInf_nonneg _ fun _ E h ↦ ?_).symm
  exact le_of_not_gt fun hs ↦ not_isNullPressureCover_zero_of_neg P T hZ hs E h.1

/-- The effective upper comparison also holds for every oracle.
Blueprint node `pressure:entropy-nonnegative`. -/
theorem entropy_eq_zeroPotentialPressure_of_nonempty_effective_upper (P : Presentation X)
    (T : X → X) (hT : Continuous T) (A : Set ℕ) (Z : Set X) (hZ : Z.Nonempty) :
    (effectiveUpperEntropy P T A Z : EReal) =
      effectiveUpperPressure P T (fun _ => 0) 0 A Z := by
  have _ := hT
  refine (coe_iInf_ofReal_nonneg fun s E ↦
    IsUniformPressureNet P T (fun _ ↦ 0) 0 Z s E ∧ IsREIn A E).trans
    (iInf_exponent_eq_iInf_nonneg _ fun _ _ h ↦ ?_).symm
  exact nonneg_of_isUniformPressureNet P T hZ h.1

/-- The signed lower zero-potential pressure of a nonempty set is nonnegative.
Blueprint node `pressure:entropy-nonnegative`. -/
theorem entropy_eq_zeroPotentialPressure_of_nonempty_nonneg (P : Presentation X)
    (T : X → X) (hT : Continuous T) (Z : Set X) (hZ : Z.Nonempty) :
    0 ≤ lowerPressure T (fun _ => 0) 0 Z := by
  refine le_of_le_of_eq ?_ (lowerPressure_eq_iInf_nullCover (zeroPotentialData P T hT) Z).symm
  refine le_iInf₂ fun s hs ↦ ?_
  obtain ⟨E, hE⟩ := hs
  exact EReal.coe_nonneg.2 (le_of_not_gt fun h ↦ not_isNullPressureCover_zero_of_neg P T hZ h E hE)

/-- Every cover of a nonempty set by a countable family of Bowen balls has total
zero-potential weight at least `1`. -/
private lemma one_le_partitionSum_zero (T : X → X) {Y : Set X} (hY : Y.Nonempty) (n : ℕ)
    (r : ℝ) : 1 ≤ partitionSum T (fun _ ↦ 0) .centered Y n r := by
  refine le_iInf₂ fun F hF ↦ ?_
  obtain ⟨y, hy⟩ := hY
  obtain ⟨z, hz, -⟩ := Set.mem_iUnion₂.1 (hF.2 hy)
  calc (1 : ℝ≥0∞) = pressureBallWeight T (fun _ ↦ 0) .centered n z r := by
        rw [pressureBallWeight, birkhoffSum_fun_zero, ENNReal.rpow_zero]
    _ ≤ partitionCoverCost T (fun _ ↦ 0) .centered F n r :=
        ENNReal.le_tsum (f := fun y : F ↦ pressureBallWeight T (fun _ ↦ 0) .centered n y r)
          ⟨z, hz⟩

/-- The zero-potential upper capacity of a nonempty set is nonnegative. -/
private lemma zero_le_upperCapacity_zero (T : X → X) {Y : Set X} (hY : Y.Nonempty) (r : ℝ) :
    0 ≤ upperCapacity T (fun _ ↦ 0) .centered Y r :=
  zero_le_limsup_pressureRate fun n _ ↦ one_le_partitionSum_zero T hY n r

/-- The zero-potential countably modified upper pressure of a nonempty set is nonnegative. -/
private lemma zero_le_modifiedUpperPressure_zero (T : X → X) {Z : Set X} (hZ : Z.Nonempty)
    (r : ℝ) : 0 ≤ modifiedUpperPressure T (fun _ ↦ 0) .centered Z r := by
  refine le_iInf₂ fun Y hY ↦ ?_
  obtain ⟨x, hx⟩ := hZ
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hY hx)
  exact le_iSup_of_le k (zero_le_upperCapacity_zero T ⟨x, hk⟩ r)

/-- The signed upper zero-potential pressure of a nonempty set is nonnegative.
The presentation `P` and the continuity of `T` are not needed.
Blueprint node `pressure:entropy-nonnegative`. -/
theorem entropy_eq_zeroPotentialPressure_of_nonempty_nonneg_upper (P : Presentation X)
    (T : X → X) (hT : Continuous T) (Z : Set X) (hZ : Z.Nonempty) :
    0 ≤ upperPressure T (fun _ => 0) 0 Z := by
  have _ := P
  have _ := hT
  exact (zero_le_modifiedUpperPressure_zero T hZ (dyadicRadius 0)).trans
    (le_iSup₂_of_le 0 le_rfl le_rfl)

/-- Effective lower zero-potential pressure is nonnegative on nonempty sets for every oracle.
Blueprint node `pressure:entropy-nonnegative`. -/
theorem entropy_eq_zeroPotentialPressure_of_nonempty_nonneg_effective (P : Presentation X)
    (T : X → X) (hT : Continuous T) (A : Set ℕ) (Z : Set X) (hZ : Z.Nonempty) :
    0 ≤ effectiveLowerPressure P T (fun _ => 0) 0 A Z :=
  (entropy_eq_zeroPotentialPressure_of_nonempty_nonneg P T hT Z hZ).trans
    (effectiveLowerPressure_ge (zeroPotentialData P T hT) A Z)

/-- Effective upper zero-potential pressure is likewise nonnegative for every oracle.
The continuity of `T` is not needed.
Blueprint node `pressure:entropy-nonnegative`. -/
theorem entropy_eq_zeroPotentialPressure_of_nonempty_nonneg_effective_upper (P : Presentation X)
    (T : X → X) (hT : Continuous T) (A : Set ℕ) (Z : Set X) (hZ : Z.Nonempty) :
    0 ≤ effectiveUpperPressure P T (fun _ => 0) 0 A Z := by
  have _ := hT
  exact le_iInf₂ fun _ _ ↦ le_iInf fun hE ↦
    EReal.coe_nonneg.2 (nonneg_of_isUniformPressureNet P T hZ hE.1)

/-- A zero-potential null cover with exponent `s ≥ 0` bounds the classical lower entropy of
the covered set by `ENNReal.ofReal s`. -/
private lemma lowerEntropy_le_ofReal_of_isNullPressureCover (P : Presentation X) (T : X → X)
    (hT : Continuous T) {Z : Set X} {s : ℝ} (hs : 0 ≤ s) {E : Set (ℕ × ℕ × ℕ)}
    (hE : IsNullPressureCover P T (fun _ ↦ 0) 0 Z s E) : lowerEntropy T Z ≤ ENNReal.ofReal s := by
  refine iSup_le fun p ↦ ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hε' : (0 : ℝ) < ε := NNReal.coe_pos.2 hε
  calc _ ≤ ENNReal.ofReal (s + ε) :=
        iInf_le_of_le (s + ε) <| iInf_le_of_le (add_nonneg hs hε'.le) <|
          iInf_le_of_le (lowerContentLimit_centered_eq_zero_of_nullCover
            (zeroPotentialData P T hT) _ s E hE p p.zero_le (s + ε) (by linarith)) le_rfl
    _ ≤ ENNReal.ofReal s + ε := by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_add_le

/-- Classical lower entropy is at most effective lower entropy for every oracle.
Blueprint node `pressure:entropy-nonnegative`. -/
theorem entropy_eq_zeroPotentialPressure_of_nonempty_le_effective (P : Presentation X)
    (T : X → X) (hT : Continuous T) (A : Set ℕ) (Z : Set X) :
    lowerEntropy T Z ≤ effectiveLowerEntropy P T A Z :=
  le_iInf₂ fun _ hs ↦ le_iInf₂ fun _ hE ↦
    lowerEntropy_le_ofReal_of_isNullPressureCover P T hT hs hE.1

/-- The same universal inequality holds for upper entropy, including the empty set.
The continuity of `T` is not needed.
Blueprint node `pressure:entropy-nonnegative`. -/
theorem entropy_eq_zeroPotentialPressure_of_nonempty_upper_le_effective (P : Presentation X)
    (T : X → X) (hT : Continuous T) (A : Set ℕ) (Z : Set X) :
    upperEntropy P T Z ≤ effectiveUpperEntropy P T A Z := by
  have _ := hT
  exact iInf_mono fun _ ↦ iInf_mono fun _ ↦ iInf_mono fun _ ↦
    le_iInf fun hE ↦ iInf_le_of_le hE.1 le_rfl

end Kolmogorov.PointToSet
