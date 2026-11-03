/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.Index
import KolmogorovMathlib.Solomonoff.Domination.IndexedMeasures

/-!
# Dyadic brackets for indexed cylinder masses

Finite execution of a numeric index supplies corrected lower and upper dyadic requests.
The running maximum and minimum are meaningful for every code; their convergence is
asserted only when the code indexes a proper measure.
Blueprint nodes: `exp:dyadic-bracket`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-! ## Running dyadic brackets -/

/-- A stage-bounded request to a numeric measure code. Blueprint node `exp:dyadic-bracket`. -/
def measureIndexRequest (e budget precision : ℕ) (x : BitString) : Option ℕ :=
  Nat.Partrec.Code.evaln budget (Denumerable.ofNat Nat.Partrec.Code e)
    (Encodable.encode (x, precision))

/-- The running certified lower mass bracket. Blueprint node `exp:dyadic-bracket`. -/
noncomputable def massLower (e s : ℕ) (x : BitString) : ℝ≥0∞ :=
  (Finset.range (s + 1)).sup fun k =>
    match measureIndexRequest e s k x with
    | some a => min 1 (dyadicValue (a - 1) k)
    | none => 0

/-- The running certified upper mass bracket. Blueprint node `exp:dyadic-bracket`. -/
noncomputable def massUpper (e s : ℕ) (x : BitString) : ℝ≥0∞ :=
  (Finset.range (s + 1)).inf fun k =>
    match measureIndexRequest e s k x with
    | some a => min 1 (dyadicValue (a + 1) k)
    | none => 1

/-- The certified lower mass increases with the stage. -/
private lemma massLower_mono (e : ℕ) (x : BitString) (s : ℕ) :
    massLower e s x ≤ massLower e (s + 1) x := by
  unfold massLower
  apply Finset.sup_le
  intro k hk
  have hsubset : k ∈ Finset.range (s + 1 + 1) := by
    rw [Finset.mem_range] at hk ⊢
    omega
  refine le_trans ?_ (Finset.le_sup hsubset)
  generalize h1 : measureIndexRequest e s k x = m1
  generalize h2 : measureIndexRequest e (s + 1) k x = m2
  cases m1 with
  | none =>
    dsimp
    cases m2 with
    | none => exact le_rfl
    | some a => exact zero_le
  | some a =>
    have heq : m2 = some a := by
      rw [← h2]
      unfold measureIndexRequest
      unfold measureIndexRequest at h1
      exact Nat.Partrec.Code.evaln_mono (Nat.le_succ _) h1
    rw [heq]

/-- The certified upper mass decreases with the stage. -/
private lemma massUpper_antitone (e : ℕ) (x : BitString) (s : ℕ) :
    massUpper e (s + 1) x ≤ massUpper e s x := by
  unfold massUpper
  apply Finset.le_inf
  intro k hk
  have hsubset : k ∈ Finset.range (s + 1 + 1) := by
    rw [Finset.mem_range] at hk ⊢
    omega
  refine le_trans (Finset.inf_le hsubset) ?_
  generalize h1 : measureIndexRequest e s k x = m1
  generalize h2 : measureIndexRequest e (s + 1) k x = m2
  cases m1 with
  | none =>
    dsimp
    cases m2 with
    | none => exact le_rfl
    | some a => exact min_le_left _ _
  | some a =>
    have heq : m2 = some a := by
      rw [← h2]
      unfold measureIndexRequest
      unfold measureIndexRequest at h1
      exact Nat.Partrec.Code.evaln_mono (Nat.le_succ _) h1
    rw [heq]

/-- A valid measure code gives lower brackets below its cylinder mass. -/
private lemma massLower_le_cantorMass (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (e : ℕ) (he : IsComputableMeasureIndex P e) (x : BitString) (s : ℕ) :
    massLower e s x ≤ cantorMass P x := by
  unfold massLower
  apply Finset.sup_le
  intro k hk
  unfold measureIndexRequest
  generalize hreq : Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
    (Encodable.encode (x, k)) = opt
  cases opt with
  | none => exact zero_le
  | some a =>
    have ha : a ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval
      (Encodable.encode (x, k)) :=
      Nat.Partrec.Code.evaln_sound hreq
    rcases he x k with ⟨a', ha', hle, hge⟩
    have heq : a = a' := Part.mem_unique ha ha'
    rw [heq]
    refine le_trans (min_le_right _ _) ?_
    by_cases ha0 : a' = 0
    · rw [ha0, Nat.zero_sub]
      have hz : dyadicValue 0 k = 0 := by
        unfold dyadicValue
        simp
      rw [hz]
      exact zero_le
    · have h_add : dyadicValue (a' - 1) k + dyadicValue 1 k = dyadicValue a' k := by
        rw [← dyadicValue_add]
        have heq_add : a' - 1 + 1 = a' := by omega
        rw [heq_add]
      have h1 : dyadicValue (a' - 1) k + dyadicValue 1 k ≤ cantorMass P x + dyadicValue 1 k :=
        h_add.le.trans hle
      have hne : dyadicValue 1 k ≠ ⊤ := by
        unfold dyadicValue
        exact ENNReal.div_ne_top ENNReal.coe_ne_top (by norm_num)
      exact ENNReal.le_of_add_le_add_right hne h1

/-- A valid measure code gives upper brackets above its cylinder mass. -/
private lemma cantorMass_le_massUpper (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (e : ℕ) (he : IsComputableMeasureIndex P e) (x : BitString) (s : ℕ) :
    cantorMass P x ≤ massUpper e s x := by
  unfold massUpper
  apply Finset.le_inf
  intro k hk
  unfold measureIndexRequest
  generalize hreq : Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
    (Encodable.encode (x, k)) = opt
  cases opt with
  | none => exact prob_le_one
  | some a =>
    have ha : a ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval
      (Encodable.encode (x, k)) :=
      Nat.Partrec.Code.evaln_sound hreq
    rcases he x k with ⟨a', ha', hle, hge⟩
    have heq : a = a' := Part.mem_unique ha ha'
    rw [heq]
    apply le_min prob_le_one
    have h_add : dyadicValue a' k + dyadicValue 1 k = dyadicValue (a' + 1) k := by
      rw [← dyadicValue_add]
    rw [← h_add]
    exact hge

/-- Every upper bracket is at most one. -/
private lemma massUpper_le_one (e : ℕ) (x : BitString) (s : ℕ) :
    massUpper e s x ≤ 1 := by
  unfold massUpper
  have h_zero : 0 ∈ Finset.range (s + 1) := by
    rw [Finset.mem_range]
    omega
  refine le_trans (Finset.inf_le h_zero) ?_
  generalize hreq : measureIndexRequest e s 0 x = opt
  cases opt with
  | none => exact le_rfl
  | some a => exact min_le_left _ _

/-! ## Limits for valid measure indices -/

/-- The lower brackets converge to the indexed cylinder mass. -/
private lemma iSup_massLower_eq (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (e : ℕ) (he : IsComputableMeasureIndex P e) (x : BitString) :
    (⨆ s, massLower e s x) = cantorMass P x := by
  refine le_antisymm (iSup_le fun s => massLower_le_cantorMass P e he x s) ?_
  have hhalf : ∀ k, dyadicValue 1 (k + 1) + dyadicValue 1 (k + 1) = dyadicValue 1 k := fun k => by
    rw [dyadicValue_one_eq_inv_two_pow', dyadicValue_one_eq_inv_two_pow', pow_succ,
      ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
  have key : ∀ k, cantorMass P x ≤ (⨆ s, massLower e s x) + dyadicValue 1 k := fun k => by
    obtain ⟨a, ha, hle, hge⟩ := he x (k + 1)
    obtain ⟨s0, hs0⟩ := Nat.Partrec.Code.evaln_complete.mp ha
    have hreq : measureIndexRequest e (max s0 (k + 1)) (k + 1) x = some a :=
      Nat.Partrec.Code.evaln_mono (le_max_left _ _) hs0
    have hk : k + 1 ∈ Finset.range (max s0 (k + 1) + 1) := by
      rw [Finset.mem_range]; omega
    have h1 : min 1 (dyadicValue (a - 1) (k + 1)) ≤ massLower e (max s0 (k + 1)) x := by
      unfold massLower
      refine le_trans (le_of_eq ?_) (Finset.le_sup hk)
      simp only [hreq]
    have h2 : massLower e (max s0 (k + 1)) x ≤ ⨆ s, massLower e s x :=
      le_iSup (fun s => massLower e s x) (max s0 (k + 1))
    have hmass : min 1 (dyadicValue (a - 1) (k + 1)) ≤ ⨆ s, massLower e s x :=
      le_trans h1 h2
    rcases le_total 1 (dyadicValue (a - 1) (k + 1)) with h_one | h_one
    · rw [min_eq_left h_one] at hmass
      exact le_trans prob_le_one (le_trans hmass le_self_add)
    · rw [min_eq_right h_one] at hmass
      by_cases ha0 : a = 0
      · rw [ha0, Nat.zero_sub] at hmass
        have hz : dyadicValue 0 (k + 1) = 0 := by unfold dyadicValue; simp
        rw [hz] at hmass
        have h_bound : cantorMass P x ≤ dyadicValue 1 (k + 1) + dyadicValue 1 (k + 1) := by
          rw [ha0] at hge
          have hz2 : dyadicValue 0 (k + 1) = 0 := by unfold dyadicValue; simp
          rw [hz2, zero_add] at hge
          exact le_trans hge (le_add_left le_rfl)
        rw [hhalf k] at h_bound
        have h_add2 : dyadicValue 1 k ≤ (⨆ s, massLower e s x) + dyadicValue 1 k :=
          le_add_left le_rfl
        exact le_trans h_bound h_add2
      · have h_bound : cantorMass P x ≤ dyadicValue (a - 1) (k + 1) + dyadicValue 1 (k + 1)
            + dyadicValue 1 (k + 1) := by
          have h_add_a : dyadicValue (a - 1) (k + 1) + dyadicValue 1 (k + 1) =
              dyadicValue a (k + 1) := by
            rw [← dyadicValue_add]
            have h_eq : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
            rw [h_eq]
          rw [h_add_a]
          exact hge
        rw [add_assoc, hhalf k] at h_bound
        exact le_trans h_bound (add_le_add hmass le_rfl)
  exact ENNReal.le_of_forall_pos_le_add fun ε hε _ => by
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (ENNReal.coe_ne_zero.mpr hε.ne')
    have H := key n
    rw [dyadicValue_one_eq_inv_two_pow'] at H
    exact le_trans H (add_le_add le_rfl hn.le)

/-- The upper brackets converge to the indexed cylinder mass. -/
private lemma iInf_massUpper_eq (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (e : ℕ) (he : IsComputableMeasureIndex P e) (x : BitString) :
    (⨅ s, massUpper e s x) = cantorMass P x := by
  refine le_antisymm ?_ (le_iInf fun s => cantorMass_le_massUpper P e he x s)
  have hhalf : ∀ k, dyadicValue 1 (k + 1) + dyadicValue 1 (k + 1) = dyadicValue 1 k := fun k => by
    rw [dyadicValue_one_eq_inv_two_pow', dyadicValue_one_eq_inv_two_pow', pow_succ,
      ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
  have key : ∀ k, (⨅ s, massUpper e s x) ≤ cantorMass P x + dyadicValue 1 k := fun k => by
    obtain ⟨a, ha, hle, hge⟩ := he x (k + 1)
    obtain ⟨s0, hs0⟩ := Nat.Partrec.Code.evaln_complete.mp ha
    have hreq : measureIndexRequest e (max s0 (k + 1)) (k + 1) x = some a :=
      Nat.Partrec.Code.evaln_mono (le_max_left _ _) hs0
    have hk : k + 1 ∈ Finset.range (max s0 (k + 1) + 1) := by
      rw [Finset.mem_range]; omega
    have h1 : massUpper e (max s0 (k + 1)) x ≤ min 1 (dyadicValue (a + 1) (k + 1)) := by
      unfold massUpper
      refine le_trans (Finset.inf_le hk) (le_of_eq ?_)
      simp only [hreq]
    have h2 : (⨅ s, massUpper e s x) ≤ massUpper e (max s0 (k + 1)) x :=
      iInf_le (fun s => massUpper e s x) (max s0 (k + 1))
    have hmass : (⨅ s, massUpper e s x) ≤ dyadicValue (a + 1) (k + 1) :=
      le_trans h2 (le_trans h1 (min_le_right _ _))
    have hmass2 : (⨅ s, massUpper e s x) ≤ dyadicValue a (k + 1) + dyadicValue 1 (k + 1) := by
      rw [← dyadicValue_add]
      exact hmass
    rw [← hhalf k, ← add_assoc]
    exact le_trans hmass2 (add_le_add hle le_rfl)
  exact ENNReal.le_of_forall_pos_le_add fun ε hε _ => by
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (ENNReal.coe_ne_zero.mpr hε.ne')
    have H := key n
    rw [dyadicValue_one_eq_inv_two_pow'] at H
    exact le_trans H (add_le_add le_rfl hn.le)

/-- For a valid index, the brackets are monotone, certified, and converge to each
cylinder mass. Blueprint node `exp:dyadic-bracket`. -/
theorem exp_dyadic_bracket (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (e : ℕ) (he : IsComputableMeasureIndex P e) (x : BitString) :
    (∀ s, massLower e s x ≤ massLower e (s + 1) x) ∧
    (∀ s, massUpper e (s + 1) x ≤ massUpper e s x) ∧
    (∀ s, massLower e s x ≤ cantorMass P x ∧
      cantorMass P x ≤ massUpper e s x ∧ massUpper e s x ≤ 1) ∧
    (⨆ s, massLower e s x) = cantorMass P x ∧
    (⨅ s, massUpper e s x) = cantorMass P x := by
  refine ⟨massLower_mono e x,
    massUpper_antitone e x,
    fun s => ⟨massLower_le_cantorMass P e he x s,
      cantorMass_le_massUpper P e he x s,
      massUpper_le_one e x s⟩,
    iSup_massLower_eq P e he x,
    iInf_massUpper_eq P e he x⟩

open Filter Topology

/-- The gap between the two certified mass brackets tends to zero.
Blueprint node `exp:dyadic-bracket`. -/
theorem exp_dyadic_bracket_gap (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (e : ℕ) (he : IsComputableMeasureIndex P e) (x : BitString) :
    Filter.Tendsto (fun s => (massUpper e s x).toReal -
      (massLower e s x).toReal) Filter.atTop (nhds 0) := by
  have H := exp_dyadic_bracket P e he x
  rcases H with ⟨H1, H2, H3, H4, H5⟩
  have H1m : Monotone (fun s => massLower e s x) := monotone_nat_of_le_succ H1
  have H2a : Antitone (fun s => massUpper e s x) := antitone_nat_of_succ_le H2
  have H4' : Tendsto (fun s => massLower e s x) atTop (nhds (cantorMass P x)) := by
    rw [← H4]
    exact tendsto_atTop_ciSup H1m ⟨cantorMass P x, fun _ ⟨s, hs⟩ => hs ▸ (H3 s).1⟩
  have H5' : Tendsto (fun s => massUpper e s x) atTop (nhds (cantorMass P x)) := by
    rw [← H5]
    exact tendsto_atTop_ciInf H2a ⟨cantorMass P x, fun _ ⟨s, hs⟩ => hs ▸ (H3 s).2.1⟩
  have H_ne_top_x : cantorMass P x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  have H4'' : Tendsto (fun s => (massLower e s x).toReal) atTop (nhds (cantorMass P x).toReal) :=
    (ENNReal.tendsto_toReal H_ne_top_x).comp H4'
  have H5'' : Tendsto (fun s => (massUpper e s x).toReal) atTop (nhds (cantorMass P x).toReal) :=
    (ENNReal.tendsto_toReal H_ne_top_x).comp H5'
  have H_diff : Tendsto (fun s => (massUpper e s x).toReal - (massLower e s x).toReal)
      atTop (nhds ((cantorMass P x).toReal - (cantorMass P x).toReal)) :=
    Tendsto.sub H5'' H4''
  have h_sub_zero : (cantorMass P x).toReal - (cantorMass P x).toReal = 0 := sub_self _
  rw [h_sub_zero] at H_diff
  exact H_diff

end Kolmogorov.MDLPrediction
