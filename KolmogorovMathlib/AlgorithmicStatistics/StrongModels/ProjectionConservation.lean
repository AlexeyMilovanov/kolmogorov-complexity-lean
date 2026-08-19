import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.DistributionProjection
import KolmogorovMathlib.AlgorithmicStatistics.DeficiencyTest
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure

/-!
# Exact probability algebra for first-coordinate projection

This module proves the finite fibre reindexing used by projection conservation
and constructs the single source-code-indexed semimeasure required for a uniform
deficiency constant.  Its dyadic approximation is computable and monotone, and
its exact supremum is established by rational floor convergence.
-/

namespace Kolmogorov

open scoped ENNReal

lemma foldr_zero_of_not_mem {l : List CodedDistributionEntry} {x : BitString}
    (hx : x ∉ l.foldr (fun e acc => insert e.point acc) Finset.empty) :
    l.foldr (fun e acc => (if e.point = x then e.mass.value else 0) + acc) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.foldr_cons, Finset.mem_insert, not_or] at hx
    simp only [List.foldr_cons]
    have hneq : e.point ≠ x := by
      intro h
      exact hx.1 h.symm
    rw [show (if e.point = x then e.mass.value else 0) = 0 from if_neg hneq]
    rw [ih hx.2, add_zero]

lemma expected_value_foldr_data (data : List CodedDistributionEntry) (f : BitString → ENNReal) :
  ∑ z ∈ data.foldr (fun e acc => insert e.point acc) Finset.empty,
    (data.foldr (fun e acc => (if e.point = z then e.mass.value else 0) + acc) 0) * f z =
  data.foldr (fun e acc => e.mass.value * f e.point + acc) 0 := by
  induction data with
  | nil => simp
  | cons e l ih =>
    simp only [List.foldr_cons, add_mul, Finset.sum_add_distrib]
    by_cases h : e.point ∈ List.foldr (fun e acc => insert e.point acc) Finset.empty l
    · rw [Finset.insert_eq_of_mem h]
      rw [ih]
      rw [Finset.sum_eq_single e.point]
      · simp
      · intro b hb hne
        simp [hne.symm]
      · intro hnot
        exact False.elim (hnot h)
    · rw [Finset.sum_insert h]
      have h1 : (∑ x ∈ l.foldr (fun e acc => insert e.point acc) Finset.empty,
        (if e.point = x then e.mass.value else 0) * f x) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        have : e.point ≠ x := by
          intro heq
          rw [heq] at h
          exact h hx
        simp [this]
      rw [h1, add_zero]
      have h2 : (∑ x ∈ insert e.point (l.foldr (fun e acc => insert e.point acc) Finset.empty),
        List.foldr (fun e acc => (if e.point = x then e.mass.value else 0) + acc) 0 l * f x) =
        ∑ x ∈ l.foldr (fun e acc => insert e.point acc) Finset.empty,
        List.foldr (fun e acc => (if e.point = x then e.mass.value else 0) + acc) 0 l * f x := by
        rw [Finset.sum_insert h]
        have h3 :
            l.foldr
              (fun e_1 acc =>
                (if e_1.point = e.point then e_1.mass.value else 0) + acc)
              0 = 0 := by
          apply foldr_zero_of_not_mem h
        rw [h3, zero_mul, zero_add]
      rw [h2]
      rw [ih]
      have h_if : (if e.point = e.point then e.mass.value else 0) = e.mass.value := if_pos rfl
      rw [h_if]

/-- The exact fibre-mass formula over `P.support`. -/
theorem codedFstPushforward_mass_eq_fiber_sum
    (P : CodedFiniteDistribution) (a : BitString) :
    (codedFstPushforward P).mass a =
      ∑ z ∈ P.support.filter (fun x => decodeFirst x = a), P.mass z := by
  unfold codedFstPushforward CodedFiniteDistribution.mass CodedFiniteDistribution.support
  rw [List.foldr_map]
  have h := expected_value_foldr_data P.data (fun x => if decodeFirst x = a then 1 else 0)
  have h_eq : ∀ e : CodedDistributionEntry,
      e.mass.value * (if decodeFirst e.point = a then 1 else 0) =
        if decodeFirst e.point = a then e.mass.value else 0 := by
    intro e
    split_ifs
    · exact mul_one _
    · exact mul_zero _
  have h_foldr_eq :
      P.data.foldr
          (fun e acc =>
            e.mass.value * (if decodeFirst e.point = a then 1 else 0) + acc)
          0 =
        P.data.foldr
          (fun e acc =>
            (if decodeFirst e.point = a then e.mass.value else 0) + acc)
          0 := by
    induction P.data with
    | nil => rfl
    | cons e l ih =>
      simp only [List.foldr_cons]
      rw [h_eq e, ih]
  rw [h_foldr_eq] at h
  rw [← h]
  have h_sum_eq : ∀ z ∈ P.data.foldr (fun e acc => insert e.point acc) Finset.empty,
    P.data.foldr
        (fun e acc => (if e.point = z then e.mass.value else 0) + acc) 0 *
        (if decodeFirst z = a then 1 else 0) =
      if decodeFirst z = a then
        P.data.foldr
          (fun e acc => (if e.point = z then e.mass.value else 0) + acc) 0
      else 0 := by
    intro z _
    split_ifs
    · exact mul_one _
    · exact mul_zero _
  rw [Finset.sum_congr rfl h_sum_eq]
  rw [Finset.sum_filter]

/-- The finite-sum reindexing identity `codedFstPushforward_expectation`. -/
theorem codedFstPushforward_expectation
    (P : CodedFiniteDistribution) (g : BitString → ENNReal) :
    (∑ z ∈ P.support, P.mass z * g (decodeFirst z)) =
      ∑ a ∈ (codedFstPushforward P).support,
        (codedFstPushforward P).mass a * g a := by
  have h1 := expected_value_foldr_data P.data (fun z => g (decodeFirst z))
  have h2 := expected_value_foldr_data (codedFstPushforward P).data g
  unfold CodedFiniteDistribution.support CodedFiniteDistribution.mass
  unfold codedFstPushforward at h2 ⊢
  simp only [List.foldr_map] at h2 ⊢
  rw [h1, h2]

/-- The final expectation inequality from `canonicalTest_expectation_le_one`. -/
theorem fstProjectionPullback_expectation_le_one
    (U : Map) (hU : IsOptimalPrefixConditional U) (P : CodedFiniteDistribution) :
    (∑ z ∈ P.support, P.mass z * canonicalTest U (codedFstPushforward P) (decodeFirst z)) ≤ 1 := by
  rw [codedFstPushforward_expectation P (fun a => canonicalTest U (codedFstPushforward P) a)]
  exact canonicalTest_expectation_le_one U hU (codedFstPushforward P)

noncomputable def fstProjectionTestSemimeasure
    (U : Map) (z : BitString) (ctx : BitString) : ENNReal :=
  let P : CodedFiniteDistribution := ⟨CodedFiniteDistribution.decodeDistributionData ctx⟩
  let a := decodeFirst z
  let P_fst := codedFstPushforward P
  P.mass z * (aprioriMeasure U a P_fst.code / P_fst.mass a)

theorem fstProjectionTestSemimeasure_isConditionalSemimeasure
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    IsConditionalSemimeasure (fstProjectionTestSemimeasure U) := by
  intro ctx
  let P : CodedFiniteDistribution := ⟨CodedFiniteDistribution.decodeDistributionData ctx⟩
  let P_fst := codedFstPushforward P
  let g := fun (a : BitString) => aprioriMeasure U a P_fst.code / P_fst.mass a
  have h_sum : (∑' (z : BitString), fstProjectionTestSemimeasure U z ctx) =
      ∑ z ∈ P.support, P.mass z * g (decodeFirst z) := by
    apply tsum_eq_sum
    intro z hz
    have : P.mass z = 0 := CodedFiniteDistribution.mass_eq_zero_of_not_mem_support P z hz
    change P.mass z * _ = 0
    rw [this, zero_mul]
  rw [h_sum]
  have h_expect : (∑ z ∈ P.support, P.mass z * g (decodeFirst z)) =
      ∑ a ∈ P_fst.support, P_fst.mass a * g a :=
    codedFstPushforward_expectation P g
  rw [h_expect]
  have h_le : ∀ a ∈ P_fst.support, P_fst.mass a * g a ≤ aprioriMeasure U a P_fst.code := by
    intro a _
    unfold g
    rw [div_eq_mul_inv, mul_comm (aprioriMeasure U a P_fst.code), ← mul_assoc]
    have : P_fst.mass a * (P_fst.mass a)⁻¹ ≤ 1 := ENNReal.mul_inv_le_one (P_fst.mass a)
    calc P_fst.mass a * (P_fst.mass a)⁻¹ * aprioriMeasure U a P_fst.code
      _ ≤ 1 * aprioriMeasure U a P_fst.code := mul_le_mul this (le_refl _) (zero_le) (zero_le)
      _ = aprioriMeasure U a P_fst.code := one_mul _
  apply le_trans (Finset.sum_le_sum h_le)
  apply le_trans (ENNReal.sum_le_tsum P_fst.support)
  exact aprioriMeasure_isConditionalSemimeasure U hU.isPrefixMachine P_fst.code

private def fstProjectionDecodedData (ctx : BitString) :
    List CodedDistributionEntry :=
  CodedFiniteDistribution.decodeDistributionData ctx

private def fstProjectionProjectedData (ctx : BitString) :
    List CodedDistributionEntry :=
  (fstProjectionDecodedData ctx).map fun e =>
    { point := decodeFirst e.point, mass := e.mass }

private def fstProjectionSourceMass (z ctx : BitString) : RatMass :=
  CodedFiniteDistribution.combinePointMass z (fstProjectionDecodedData ctx)

private def fstProjectionFiberMass (z ctx : BitString) : RatMass :=
  CodedFiniteDistribution.combinePointMass (decodeFirst z)
    (fstProjectionProjectedData ctx)

private def fstProjectionProjectedCode (ctx : BitString) : BitString :=
  codedDistributionDataCode (fstProjectionProjectedData ctx)

private def fstProjectionScale (p : RatMass × RatMass × ℕ) : ℕ :=
  if p.2.1.num = 0 then 0
  else (p.1.num * p.2.1.den * p.2.2) / (p.1.den * p.2.1.num)

private def fstProjectionMassPair
    (p : ℕ × BitString × BitString) : RatMass × RatMass :=
  (fstProjectionSourceMass p.2.1 p.2.2, fstProjectionFiberMass p.2.1 p.2.2)

private def fstProjectionAprioriArgs (p : ℕ × BitString × BitString) :
    ℕ × BitString × BitString :=
  (p.1, decodeFirst p.2.1, fstProjectionProjectedCode p.2.2)

private def fstProjectionAprioriNumerator (c : Nat.Partrec.Code)
    (p : ℕ × BitString × BitString) : ℕ :=
  aprioriApprox c (fstProjectionAprioriArgs p).1
    (fstProjectionAprioriArgs p).2.1 (fstProjectionAprioriArgs p).2.2

private def fstProjectionInputs (c : Nat.Partrec.Code)
    (p : ℕ × BitString × BitString) : RatMass × RatMass × ℕ :=
  ((fstProjectionMassPair p).1, (fstProjectionMassPair p).2,
    fstProjectionAprioriNumerator c p)

def fstProjectionApprox (c : Nat.Partrec.Code) (s : ℕ) (z : BitString) (ctx : BitString) : ℕ :=
  fstProjectionScale (fstProjectionInputs c (s, z, ctx))

theorem fstProjectionApprox_mono (c : Nat.Partrec.Code) (s : ℕ) (z : BitString) (ctx : BitString) :
    dyadicValue (fstProjectionApprox c s z ctx) s ≤
      dyadicValue (fstProjectionApprox c (s + 1) z ctx) (s + 1) := by
  simp only [fstProjectionApprox, fstProjectionInputs, fstProjectionMassPair,
    fstProjectionAprioriNumerator, fstProjectionAprioriArgs, fstProjectionScale]
  split_ifs with hzero
  · simp [dyadicValue]
  · let a := decodeFirst z
    let A := (fstProjectionSourceMass z ctx).num *
      (fstProjectionFiberMass z ctx).den
    let B := (fstProjectionSourceMass z ctx).den *
      (fstProjectionFiberMass z ctx).num
    have hB : 0 < B := Nat.mul_pos
      (fstProjectionSourceMass z ctx).den_pos
      (Nat.pos_of_ne_zero hzero)
    have hN : 2 * aprioriApprox c s a (fstProjectionProjectedCode ctx) ≤
        aprioriApprox c (s + 1) a (fstProjectionProjectedCode ctx) := by
      have h := aprioriApprox_mono c s a (fstProjectionProjectedCode ctx)
      rw [← dyadicValue_two_mul_succ] at h
      unfold dyadicValue at h
      have hp : (2 : ENNReal) ^ (s + 1) ≠ 0 := by positivity
      have ht : (2 : ENNReal) ^ (s + 1) ≠ ⊤ := by simp
      rw [ENNReal.div_le_iff_le_mul (Or.inl hp) (Or.inl ht)] at h
      rw [ENNReal.div_mul_cancel hp ht] at h
      exact_mod_cast h
    have hfloor : 2 * (A * aprioriApprox c s a (fstProjectionProjectedCode ctx) / B) ≤
        A * aprioriApprox c (s + 1) a (fstProjectionProjectedCode ctx) / B := by
      calc
        2 * (A * aprioriApprox c s a (fstProjectionProjectedCode ctx) / B)
            ≤ A * (2 * aprioriApprox c s a (fstProjectionProjectedCode ctx)) / B := by
              rw [Nat.le_div_iff_mul_le hB]
              have hdiv := Nat.div_mul_le_self
                (A * aprioriApprox c s a (fstProjectionProjectedCode ctx)) B
              nlinarith
        _ ≤ A * aprioriApprox c (s + 1) a (fstProjectionProjectedCode ctx) / B :=
          Nat.div_le_div_right (Nat.mul_le_mul_left A hN)
    change dyadicValue (A * aprioriApprox c s a (fstProjectionProjectedCode ctx) / B) s ≤
      dyadicValue (A * aprioriApprox c (s + 1) a (fstProjectionProjectedCode ctx) / B) (s + 1)
    rw [← dyadicValue_two_mul_succ]
    unfold dyadicValue
    gcongr

private lemma dyadicFloorScale_iter (N : Nat → Nat)
    (hN : ∀ s, 2 * N s ≤ N (s + 1)) :
    ∀ s k, 2 ^ k * N s ≤ N (s + k) := by
  intro s k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        2 ^ (k + 1) * N s = 2 * (2 ^ k * N s) := by rw [pow_succ]; ring
        _ ≤ 2 * N (s + k) := Nat.mul_le_mul_left 2 ih
        _ ≤ N ((s + k) + 1) := hN (s + k)
        _ = N (s + (k + 1)) := by rw [Nat.add_assoc]

private lemma dyadicFloorScale_stage_lower
    (A B : Nat) (hB : 0 < B) (N : Nat → Nat)
    (hN : ∀ s, 2 * N s ≤ N (s + 1)) (s k : Nat) :
    ((A : ENNReal) / (B : ENNReal)) * dyadicValue (N s) s ≤
      dyadicValue (A * N (s + k) / B) (s + k) +
        (2 : ENNReal)⁻¹ ^ (s + k) := by
  have hNk : 2 ^ k * N s ≤ N (s + k) := dyadicFloorScale_iter N hN s k
  have hdivlt : A * N (s + k) <
      (A * N (s + k) / B + 1) * B := by
    exact (Nat.div_lt_iff_lt_mul hB).mp (Nat.lt_succ_self _)
  have hNat : A * N s * 2 ^ k ≤
      B * (A * N (s + k) / B + 1) := by
    exact (calc
      A * N s * 2 ^ k = A * (2 ^ k * N s) := by ring
      _ ≤ A * N (s + k) := Nat.mul_le_mul_left A hNk
      _ < (A * N (s + k) / B + 1) * B := hdivlt
      _ = B * (A * N (s + k) / B + 1) := Nat.mul_comm _ _).le
  have hleftTop :
      ((A : ENNReal) / (B : ENNReal)) * dyadicValue (N s) s ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.div_ne_top
      · simp
      · exact_mod_cast hB.ne'
    · unfold dyadicValue
      apply ENNReal.div_ne_top
      · simp
      · simp
  have hrightTop : dyadicValue (A * N (s + k) / B + 1) (s + k) ≠ ⊤ := by
    unfold dyadicValue
    apply ENNReal.div_ne_top
    · simp
    · simp
  have hmain :
      ((A : ENNReal) / (B : ENNReal)) * dyadicValue (N s) s ≤
        dyadicValue (A * N (s + k) / B + 1) (s + k) := by
    rw [← ENNReal.toReal_le_toReal hleftTop hrightTop]
    simp only [dyadicValue, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    norm_num at hNat ⊢
    field_simp
    have hNat' : A * N s * 2 ^ (s + k) ≤
        B * 2 ^ s * (A * N (s + k) / B + 1) := by
      rw [pow_add]
      calc
        A * N s * (2 ^ s * 2 ^ k) = 2 ^ s * (A * N s * 2 ^ k) := by ring
        _ ≤ 2 ^ s * (B * (A * N (s + k) / B + 1)) :=
          Nat.mul_le_mul_left _ hNat
        _ = B * 2 ^ s * (A * N (s + k) / B + 1) := by ring
    exact_mod_cast hNat'
  calc
    ((A : ENNReal) / (B : ENNReal)) * dyadicValue (N s) s
        ≤ dyadicValue (A * N (s + k) / B + 1) (s + k) := hmain
    _ = dyadicValue (A * N (s + k) / B) (s + k) +
        (2 : ENNReal)⁻¹ ^ (s + k) := by
      unfold dyadicValue
      rw [Nat.cast_add, Nat.cast_one]
      simp only [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow]
      ring

private lemma dyadicFloorScale_stage_upper
    (A B : Nat) (hB : 0 < B) (N : Nat → Nat) (s : Nat) :
    dyadicValue (A * N s / B) s ≤
      ((A : ENNReal) / (B : ENNReal)) * dyadicValue (N s) s := by
  have hleftTop : dyadicValue (A * N s / B) s ≠ ⊤ := by
    unfold dyadicValue
    apply ENNReal.div_ne_top <;> simp
  have hrightTop :
      ((A : ENNReal) / (B : ENNReal)) * dyadicValue (N s) s ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.div_ne_top
      · simp
      · exact_mod_cast hB.ne'
    · unfold dyadicValue
      apply ENNReal.div_ne_top <;> simp
  rw [← ENNReal.toReal_le_toReal hleftTop hrightTop]
  simp only [dyadicValue, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  field_simp
  exact_mod_cast Nat.div_mul_le_self (A * N s) B

theorem iSup_dyadic_floor_scale
    (A B : Nat) (hB : 0 < B) (N : Nat → Nat)
    (hN : ∀ s, 2 * N s ≤ N (s + 1)) :
    (⨆ s, dyadicValue (A * N s / B) s) =
      ((A : ENNReal) / (B : ENNReal)) *
        (⨆ s, dyadicValue (N s) s) := by
  apply le_antisymm
  · refine iSup_le fun s => ?_
    refine (dyadicFloorScale_stage_upper A B hB N s).trans ?_
    gcongr
    exact le_iSup (fun t => dyadicValue (N t) t) s
  · rw [ENNReal.mul_iSup]
    refine iSup_le fun s => ?_
    apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    obtain ⟨eps, heps, hreps⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hr
    have heps0 : (eps : ENNReal) ≠ 0 := by exact_mod_cast heps.ne'
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_two_pow_lt heps0
    have herr : (2 : ENNReal)⁻¹ ^ (s + k) < (eps : ENNReal) := by
      calc
        (2 : ENNReal)⁻¹ ^ (s + k) =
            (2 : ENNReal)⁻¹ ^ s * (2 : ENNReal)⁻¹ ^ k := pow_add _ _ _
        _ ≤ 1 * (2 : ENNReal)⁻¹ ^ k := by
          gcongr
          exact pow_le_one₀ (by norm_num) (by norm_num)
        _ < (eps : ENNReal) := by simpa using hk
    have hrerr : (r : ENNReal) + (2 : ENNReal)⁻¹ ^ (s + k) <
        ((A : ENNReal) / (B : ENNReal)) * dyadicValue (N s) s :=
      (ENNReal.add_lt_add_left (a := (r : ENNReal)) (by simp) herr).trans hreps
    have hstage := dyadicFloorScale_stage_lower A B hB N hN s k
    have hcancel : (r : ENNReal) + (2 : ENNReal)⁻¹ ^ (s + k) <
        dyadicValue (A * N (s + k) / B) (s + k) +
          (2 : ENNReal)⁻¹ ^ (s + k) := hrerr.trans_le hstage
    have hrstage : (r : ENNReal) <
        dyadicValue (A * N (s + k) / B) (s + k) := by
      exact (ENNReal.add_lt_add_iff_right (by simp)).mp hcancel
    exact (le_of_lt hrstage).trans
      (le_iSup (fun t => dyadicValue (A * N t / B) t) (s + k))

theorem fstProjectionApprox_iSup
    (U : Map) (c : Nat.Partrec.Code) (hc : IsCodeFor c U)
    (z : BitString) (ctx : BitString) :
    (⨆ s, dyadicValue (fstProjectionApprox c s z ctx) s) =
      fstProjectionTestSemimeasure U z ctx := by
  simp only [fstProjectionApprox, fstProjectionInputs, fstProjectionMassPair,
    fstProjectionAprioriNumerator, fstProjectionAprioriArgs, fstProjectionScale]
  split_ifs with hzero
  · rw [show (⨆ s, dyadicValue 0 s) = 0 by simp [dyadicValue]]
    let P : CodedFiniteDistribution :=
      ⟨CodedFiniteDistribution.decodeDistributionData ctx⟩
    let a := decodeFirst z
    let P_fst := codedFstPushforward P
    have hFiber : P_fst.mass a = 0 := by
      rw [CodedFiniteDistribution.mass_eq_combinePointMass]
      change (fstProjectionFiberMass z ctx).value = 0
      unfold RatMass.value
      rw [hzero]
      simp
    have hSource : P.mass z = 0 := by
      exact bot_unique ((codedFstPushforward_mass_ge P z).trans_eq hFiber)
    change 0 = P.mass z * (aprioriMeasure U a P_fst.code / P_fst.mass a)
    rw [hSource, zero_mul]
  · let a := decodeFirst z
    let A := (fstProjectionSourceMass z ctx).num *
      (fstProjectionFiberMass z ctx).den
    let B := (fstProjectionSourceMass z ctx).den *
      (fstProjectionFiberMass z ctx).num
    let N := fun s => aprioriApprox c s a (fstProjectionProjectedCode ctx)
    have hB : 0 < B := Nat.mul_pos
      (fstProjectionSourceMass z ctx).den_pos
      (Nat.pos_of_ne_zero hzero)
    have hN : ∀ s, 2 * N s ≤ N (s + 1) := by
      intro s
      have h := aprioriApprox_mono c s a (fstProjectionProjectedCode ctx)
      rw [← dyadicValue_two_mul_succ] at h
      unfold dyadicValue at h
      have hp : (2 : ENNReal) ^ (s + 1) ≠ 0 := by positivity
      have ht : (2 : ENNReal) ^ (s + 1) ≠ ⊤ := by simp
      rw [ENNReal.div_le_iff_le_mul (Or.inl hp) (Or.inl ht)] at h
      rw [ENNReal.div_mul_cancel hp ht] at h
      exact_mod_cast h
    rw [show (⨆ s,
        dyadicValue
          ((fstProjectionSourceMass z ctx).num * (fstProjectionFiberMass z ctx).den *
              aprioriApprox c s (decodeFirst z) (fstProjectionProjectedCode ctx) /
            ((fstProjectionSourceMass z ctx).den * (fstProjectionFiberMass z ctx).num)) s) =
        (⨆ s, dyadicValue (A * N s / B) s) from rfl]
    rw [iSup_dyadic_floor_scale A B hB N hN]
    rw [show (⨆ s, dyadicValue (N s) s) = aprioriMeasure U a
        (fstProjectionProjectedCode ctx) from aprioriApprox_iSup c hc a _]
    let P : CodedFiniteDistribution :=
      ⟨CodedFiniteDistribution.decodeDistributionData ctx⟩
    let P_fst := codedFstPushforward P
    have hSource : P.mass z = (fstProjectionSourceMass z ctx).value := by
      rw [CodedFiniteDistribution.mass_eq_combinePointMass]
      rfl
    have hFiber : P_fst.mass a = (fstProjectionFiberMass z ctx).value := by
      rw [CodedFiniteDistribution.mass_eq_combinePointMass]
      rfl
    change ((A : ENNReal) / (B : ENNReal)) *
        aprioriMeasure U a (fstProjectionProjectedCode ctx) =
      P.mass z * (aprioriMeasure U a P_fst.code / P_fst.mass a)
    rw [hSource, hFiber]
    change ((A : ENNReal) / (B : ENNReal)) *
        aprioriMeasure U a (fstProjectionProjectedCode ctx) =
      (fstProjectionSourceMass z ctx).value *
        (aprioriMeasure U a (fstProjectionProjectedCode ctx) /
          (fstProjectionFiberMass z ctx).value)
    dsimp [A, B]
    unfold RatMass.value
    push_cast
    have hSourceDen0 : ((fstProjectionSourceMass z ctx).den : ENNReal) ≠ 0 := by
      exact_mod_cast (fstProjectionSourceMass z ctx).den_pos.ne'
    have hFiberNum0 : ((fstProjectionFiberMass z ctx).num : ENNReal) ≠ 0 := by
      exact_mod_cast hzero
    have hFiberDen0 : ((fstProjectionFiberMass z ctx).den : ENNReal) ≠ 0 := by
      exact_mod_cast (fstProjectionFiberMass z ctx).den_pos.ne'
    have hleftTop :
        ((fstProjectionSourceMass z ctx).num : ENNReal) *
            (fstProjectionFiberMass z ctx).den /
            (((fstProjectionSourceMass z ctx).den : ENNReal) *
              (fstProjectionFiberMass z ctx).num) ≠ ⊤ := by
      apply ENNReal.div_ne_top
      · apply ENNReal.mul_ne_top <;> simp
      · exact mul_ne_zero hSourceDen0 hFiberNum0
    have hrightTop :
        ((fstProjectionSourceMass z ctx).num : ENNReal) /
            (fstProjectionSourceMass z ctx).den /
          (((fstProjectionFiberMass z ctx).num : ENNReal) /
            (fstProjectionFiberMass z ctx).den) ≠ ⊤ := by
      apply ENNReal.div_ne_top
      · apply ENNReal.div_ne_top
        · simp
        · exact hSourceDen0
      · exact ENNReal.div_ne_zero.mpr ⟨hFiberNum0, by simp⟩
    have hcoeff :
        ((fstProjectionSourceMass z ctx).num : ENNReal) *
              (fstProjectionFiberMass z ctx).den /
              (((fstProjectionSourceMass z ctx).den : ENNReal) *
                (fstProjectionFiberMass z ctx).num) =
          (((fstProjectionSourceMass z ctx).num : ENNReal) /
              (fstProjectionSourceMass z ctx).den) /
            (((fstProjectionFiberMass z ctx).num : ENNReal) /
              (fstProjectionFiberMass z ctx).den) := by
      apply (ENNReal.toReal_eq_toReal_iff' hleftTop hrightTop).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast]
      field_simp
    rw [hcoeff]
    simp only [ENNReal.div_eq_inv_mul]
    ring

private theorem fstProjectionScale_computable : Computable fstProjectionScale := by
  have hs : Computable (fun p : RatMass × RatMass × ℕ => p.1) := Computable.fst
  have hf : Computable (fun p : RatMass × RatMass × ℕ => p.2.1) :=
    Computable.fst.comp Computable.snd
  have hN : Computable (fun p : RatMass × RatMass × ℕ => p.2.2) :=
    Computable.snd.comp Computable.snd
  have hsn := CodedFiniteDistribution.ratMass_num_primrec.to_comp.comp hs
  have hsd := CodedFiniteDistribution.ratMass_den_primrec.to_comp.comp hs
  have hfn := CodedFiniteDistribution.ratMass_num_primrec.to_comp.comp hf
  have hfd := CodedFiniteDistribution.ratMass_den_primrec.to_comp.comp hf
  have hnum := Primrec.nat_mul.to_comp.comp
    (Primrec.nat_mul.to_comp.comp hsn hfd) hN
  have hden := Primrec.nat_mul.to_comp.comp hsd hfn
  have hval := Primrec.nat_div.to_comp.comp hnum hden
  have hcond : Computable (fun p : RatMass × RatMass × ℕ =>
      decide (p.2.1.num = 0)) :=
    (PrimrecPred.decide (PrimrecRel.comp Primrec.eq
      (CodedFiniteDistribution.ratMass_num_primrec.comp
        (Primrec.fst.comp Primrec.snd))
      (Primrec.const 0))).to_comp
  exact (Computable.cond hcond (Computable.const 0) hval).of_eq fun p => by
    simp only [fstProjectionScale, Bool.cond_decide]

private theorem fstProjectionDecodedData_computable :
    Computable fstProjectionDecodedData :=
  CodedFiniteDistribution.decodeDistributionData_primrec.to_comp

private theorem fstProjectionProjectedData_computable :
    Computable fstProjectionProjectedData := by
  have hentry : Primrec (fun e : CodedDistributionEntry =>
      ({ point := decodeFirst e.point, mass := e.mass } : CodedDistributionEntry)) := by
    have hpair : Primrec (fun e : CodedDistributionEntry =>
        (decodeFirst e.point, e.mass)) :=
      (CodedFiniteDistribution.decodeFirst_primrec.comp
        CodedFiniteDistribution.entry_point_primrec).pair
        CodedFiniteDistribution.entry_mass_primrec
    exact (Primrec.of_equiv_symm
      (e := CodedFiniteDistribution.CodedDistributionEntry.equivProd)).comp hpair
  exact (Primrec.list_map CodedFiniteDistribution.decodeDistributionData_primrec
    (hentry.comp Primrec.snd).to₂).to_comp

private theorem fstProjectionSourceMass_computable :
    Computable (fun p : BitString × BitString =>
      fstProjectionSourceMass p.1 p.2) := by
  exact CodedFiniteDistribution.combinePointMass_primrec.to_comp.comp
    Computable.fst (fstProjectionDecodedData_computable.comp Computable.snd)

private theorem fstProjectionFiberMass_computable :
    Computable (fun p : BitString × BitString =>
      fstProjectionFiberMass p.1 p.2) := by
  exact CodedFiniteDistribution.combinePointMass_primrec.to_comp.comp
    (decodeFirst_computable.comp Computable.fst)
    (fstProjectionProjectedData_computable.comp Computable.snd)

private theorem fstProjectionProjectedCode_computable :
    Computable fstProjectionProjectedCode :=
  CodedFiniteDistribution.codedDistributionDataCode_primrec.to_comp.comp
    fstProjectionProjectedData_computable

private theorem fstProjectionMassPair_computable :
    Computable fstProjectionMassPair := by
  have hsource : Computable (fun p : ℕ × BitString × BitString =>
      fstProjectionSourceMass p.2.1 p.2.2) :=
    fstProjectionSourceMass_computable.comp Computable.snd
  have hfiber : Computable (fun p : ℕ × BitString × BitString =>
      fstProjectionFiberMass p.2.1 p.2.2) :=
    fstProjectionFiberMass_computable.comp Computable.snd
  change Computable (fun p : ℕ × BitString × BitString =>
    (fstProjectionSourceMass p.2.1 p.2.2, fstProjectionFiberMass p.2.1 p.2.2))
  exact hsource.pair hfiber

private theorem fstProjectionAprioriArgs_computable :
    Computable fstProjectionAprioriArgs := by
  have ha : Computable (fun p : ℕ × BitString × BitString =>
      decodeFirst p.2.1) :=
    decodeFirst_computable.comp (Computable.fst.comp Computable.snd)
  have hcode : Computable (fun p : ℕ × BitString × BitString =>
      fstProjectionProjectedCode p.2.2) :=
    fstProjectionProjectedCode_computable.comp (Computable.snd.comp Computable.snd)
  change Computable (fun p : ℕ × BitString × BitString =>
    (p.1, decodeFirst p.2.1, fstProjectionProjectedCode p.2.2))
  exact Computable.fst.pair (ha.pair hcode)

private theorem fstProjectionAprioriNumerator_computable (c : Nat.Partrec.Code) :
    Computable (fstProjectionAprioriNumerator c) := by
  change Computable (fun p => aprioriApprox c (fstProjectionAprioriArgs p).1
    (fstProjectionAprioriArgs p).2.1 (fstProjectionAprioriArgs p).2.2)
  exact (aprioriApprox_computable c).comp fstProjectionAprioriArgs_computable

private theorem fstProjectionInputs_computable (c : Nat.Partrec.Code) :
    Computable (fstProjectionInputs c) := by
  have hm := fstProjectionMassPair_computable
  have hsource : Computable (fun p => (fstProjectionMassPair p).1) :=
    Computable.fst.comp hm
  have hfiber : Computable (fun p => (fstProjectionMassPair p).2) :=
    Computable.snd.comp hm
  change Computable (fun p => ((fstProjectionMassPair p).1,
    (fstProjectionMassPair p).2, fstProjectionAprioriNumerator c p))
  exact hsource.pair (hfiber.pair (fstProjectionAprioriNumerator_computable c))

theorem fstProjectionApprox_computable (c : Nat.Partrec.Code) :
    Computable (fun p : ℕ × BitString × BitString => fstProjectionApprox c p.1 p.2.1 p.2.2) := by
  change Computable (fun p : ℕ × BitString × BitString =>
    fstProjectionScale (fstProjectionInputs c p))
  exact fstProjectionScale_computable.comp (fstProjectionInputs_computable c)

theorem fstProjectionTestSemimeasure_isLSC
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    IsLSC (fstProjectionTestSemimeasure U) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hU.isPrefixDecompressor.isDecompressor
  refine ⟨fstProjectionApprox c, ?_, ?_, ?_⟩
  · intro s out ctx; exact fstProjectionApprox_mono c s out ctx
  · intro out ctx; exact fstProjectionApprox_iSup U c hc out ctx
  · exact fstProjectionApprox_computable c

theorem deficiency_fstPushforward_conserved
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ P z beta,
      P.IsProbability →
      DeficiencyLe U P z beta →
      DeficiencyLe U (codedFstPushforward P)
        (decodeFirst z) (beta + c) := by
  obtain ⟨M', hM', c₀, hreal⟩ :=
    kraftChaitin_realization_bound_unit
      (fstProjectionTestSemimeasure_isLSC U hU)
      (fstProjectionTestSemimeasure_isConditionalSemimeasure U hU)
  obtain ⟨c, hc⟩ :=
    complexityWeight_dominates_of_prefix_realization hU hM' hreal
  refine ⟨c, ?_⟩
  intro P z beta _hP hdef
  obtain ⟨cPlain, hPlain⟩ := KP_le_KPPlain U hU
  obtain ⟨cLen, hLen⟩ := KPPlain_le_two_mul_length U hU
  have hKP : KP U z P.code ≠ ⊤ := by
    have hbound : KP U z P.code ≤
        ((2 * z.length + cLen + cPlain : Nat) : ENat) := by
      calc
        KP U z P.code ≤ KPPlain U z + (cPlain : ENat) := hPlain z P.code
        _ ≤ ((2 * z.length + cLen : Nat) : ENat) + (cPlain : ENat) := by
          gcongr
          exact hLen z
        _ = ((2 * z.length + cLen + cPlain : Nat) : ENat) := by
          push_cast
          rfl
    exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hbound
  have hPpos : 0 < P.mass z :=
    mass_pos_of_deficiencyLe_of_KP_ne_top hdef hKP
  have hP0 : P.mass z ≠ 0 := ne_of_gt hPpos
  have hPtop : P.mass z ≠ ⊤ := by
    rw [CodedFiniteDistribution.mass_eq_combinePointMass]
    unfold RatMass.value
    apply ENNReal.div_ne_top
    · simp
    · exact_mod_cast
        (CodedFiniteDistribution.combinePointMass z P.data).den_pos.ne'
  let a := decodeFirst z
  let P_fst := codedFstPushforward P
  have hFpos : 0 < P_fst.mass a :=
    lt_of_lt_of_le hPpos (codedFstPushforward_mass_ge P z)
  have hF0 : P_fst.mass a ≠ 0 := ne_of_gt hFpos
  have hFtop : P_fst.mass a ≠ ⊤ := by
    rw [CodedFiniteDistribution.mass_eq_combinePointMass]
    unfold RatMass.value
    apply ENNReal.div_ne_top
    · simp
    · exact_mod_cast
        (CodedFiniteDistribution.combinePointMass a P_fst.data).den_pos.ne'
  have hsem :
      (2 : ENNReal)⁻¹ ^ c *
          (P.mass z * (aprioriMeasure U a P_fst.code / P_fst.mass a)) ≤
        complexityWeight (KP U z P.code) := by
    have hraw := hc z P.code
    change (2 : ENNReal)⁻¹ ^ c *
      (let Q : CodedFiniteDistribution :=
        ⟨CodedFiniteDistribution.decodeDistributionData P.code⟩
       let b := decodeFirst z
       let Q_fst := codedFstPushforward Q
       Q.mass z * (aprioriMeasure U b Q_fst.code / Q_fst.mass b)) ≤
      complexityWeight (KP U z P.code) at hraw
    rw [show P.code = codedDistributionDataCode P.data from rfl,
      CodedFiniteDistribution.decodeDistributionData_code] at hraw
    exact hraw
  have hdom :
      (2 : ENNReal)⁻¹ ^ c *
          (P.mass z * (aprioriMeasure U a P_fst.code / P_fst.mass a)) ≤
        (2 : ENNReal) ^ beta * P.mass z :=
    hsem.trans hdef
  have hcancelP :
      (2 : ENNReal)⁻¹ ^ c *
          (aprioriMeasure U a P_fst.code / P_fst.mass a) ≤
        (2 : ENNReal) ^ beta := by
    apply (ENNReal.mul_le_mul_iff_left hP0 hPtop).mp
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdom
  have hpowCancel :
      (2 : ENNReal) ^ c * (2 : ENNReal)⁻¹ ^ c = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel] <;> norm_num
  have hapDiv :
      aprioriMeasure U a P_fst.code / P_fst.mass a ≤
        (2 : ENNReal) ^ (beta + c) := by
    calc
      aprioriMeasure U a P_fst.code / P_fst.mass a
          = 1 * (aprioriMeasure U a P_fst.code / P_fst.mass a) := by
            rw [one_mul]
      _ = ((2 : ENNReal) ^ c * (2 : ENNReal)⁻¹ ^ c) *
          (aprioriMeasure U a P_fst.code / P_fst.mass a) := by
            rw [hpowCancel]
      _ = (2 : ENNReal) ^ c * ((2 : ENNReal)⁻¹ ^ c *
          (aprioriMeasure U a P_fst.code / P_fst.mass a)) := by
            rw [mul_assoc]
      _ ≤ (2 : ENNReal) ^ c * (2 : ENNReal) ^ beta := by
            gcongr
      _ = (2 : ENNReal) ^ (beta + c) := by
            rw [← pow_add, add_comm]
  have hap : aprioriMeasure U a P_fst.code ≤
      (2 : ENNReal) ^ (beta + c) * P_fst.mass a :=
    (ENNReal.div_le_iff hF0 hFtop).mp hapDiv
  unfold DeficiencyLe CodedFiniteDistribution.DeficiencyLe
  exact (complexityWeight_KP_le_aprioriMeasure U a P_fst.code).trans hap

theorem isStochastic_fst_of_pair
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ x y alpha beta,
      IsStochastic U (pairCode x y) alpha beta →
      IsStochastic U x (alpha + c) (beta + c) := by
  obtain ⟨cDef, hDef⟩ := deficiency_fstPushforward_conserved U hU
  obtain ⟨cComp, hComp⟩ := codedFstPushforward_complexity_le U hU
  refine ⟨cComp + cDef, ?_⟩
  intro x y alpha beta hstoch
  obtain ⟨P, hP, hPcomp, hPdef⟩ := hstoch
  refine ⟨codedFstPushforward P, codedFstPushforward_isProbability P hP, ?_, ?_⟩
  · calc
      (codedFstPushforward P).complexity U
          ≤ P.complexity U + (cComp : ENat) := hComp P
      _ ≤ (alpha : ENat) + (cComp : ENat) := by
            gcongr
      _ ≤ ((alpha + (cComp + cDef) : Nat) : ENat) := by
            exact_mod_cast
              (show alpha + cComp ≤ alpha + (cComp + cDef) by omega)
  · have hh := hDef P (pairCode x y) beta hP hPdef
    rw [decodeFirst_pairCode] at hh
    exact hh.mono_beta (by omega)

end Kolmogorov
