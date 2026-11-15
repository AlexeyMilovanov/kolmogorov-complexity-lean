/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic

/-!
# The Lovász local lemma (SUV Section 8.5.2, pp. 244-247)

The statement of p. 246: events `A_i`, `i ∈ ι` finite, with a set of neighbours `N(i) ∌ i`, not
assumed symmetric, such that `A_i` is independent *of the tuple of its non-neighbours*, not just of
each of them.  The independence is `ProbabilityTheory.Indep` of the generated σ-algebras.

The two problems on tapes of p. 247 are the applications to pairs, with exact fractions.
-/

namespace Kolmogorov.Applications

open MeasureTheory ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

/-- The event `A_i` is independent of the tuple of events outside `{i} ∪ N(i)`.  SUV p. 246. -/
def IsLocallyIndependent (P : Measure Ω) (A : ι → Set Ω) (N : ι → Finset ι) : Prop :=
  ∀ i, Indep (MeasurableSpace.generateFrom {A i})
    (MeasurableSpace.generateFrom {s | ∃ j, j ≠ i ∧ j ∉ N i ∧ s = A j}) P

/-- The event that none of the events of `S` happens. -/
def avoidAll (A : ι → Set Ω) (S : Finset ι) : Set Ω := ⋂ j ∈ S, (A j)ᶜ

omit [Fintype ι] in
/-- Removing an event from the condition: `Pr[¬A_j ∧ B] = Pr[B] - Pr[A_j ∧ B]`. -/
private lemma real_avoidAll_insert (P : Measure Ω) [IsProbabilityMeasure P] {A : ι → Set Ω}
    (hA : ∀ i, MeasurableSet (A i)) (j : ι) (T : Finset ι) :
    P.real (avoidAll A (insert j T)) = P.real (avoidAll A T) - P.real (A j ∩ avoidAll A T) := by
  have hset : avoidAll A (insert j T) = avoidAll A T \ A j := by
    ext x
    simp only [avoidAll, Set.mem_iInter, Finset.mem_insert, Set.mem_sdiff, Set.mem_compl_iff]
    constructor
    · exact fun h => ⟨fun i hi => h i (Or.inr hi), h j (Or.inl rfl)⟩
    · rintro ⟨h1, h2⟩ i (rfl | hi)
      · exact h2
      · exact h1 i hi
  have hsplit := measure_inter_add_sdiff (μ := P) (avoidAll A T) (hA j)
  have hreal :
      P.real (avoidAll A T ∩ A j) + P.real (avoidAll A T \ A j) = P.real (avoidAll A T) := by
    simp only [Measure.real]
    rw [← ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _), hsplit]
  rw [hset, Set.inter_comm (A j)]
  linarith

omit [Fintype ι] in
/-- The induction of the proof of Theorem 160.  If the conditional bound (1) holds for all condition
sets with fewer than `n` elements, then for disjoint `S₁`, `S₂` with `|S₁ ∪ S₂| ≤ n` one has
`Pr[B_{S₁ ∪ S₂}] ≥ ∏_{j ∈ S₁} (1 - ε_j) · Pr[B_{S₂}]`.  This is statement (2) of the book, without
division. -/
private lemma prod_mul_le_avoidAll (P : Measure Ω) [IsProbabilityMeasure P] {A : ι → Set Ω}
    (hA : ∀ i, MeasurableSet (A i)) {ε : ι → ℝ} (hε1 : ∀ i, ε i < 1) {n : ℕ}
    (hcond : ∀ (i : ι) (S : Finset ι), S.card < n → i ∉ S →
      P.real (A i ∩ avoidAll A S) ≤ ε i * P.real (avoidAll A S))
    (S₂ : Finset ι) (S₁ : Finset ι) (hdisj : Disjoint S₁ S₂) (hcard : (S₁ ∪ S₂).card ≤ n) :
    (∏ j ∈ S₁, (1 - ε j)) * P.real (avoidAll A S₂) ≤ P.real (avoidAll A (S₁ ∪ S₂)) := by
  induction S₁ using Finset.induction_on with
  | empty => simp
  | insert j T hjT ih =>
    have hdisjT : Disjoint T S₂ := Finset.disjoint_of_subset_left (Finset.subset_insert j T) hdisj
    have hjS₂ : j ∉ S₂ := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self j T)
    have hjU : j ∉ T ∪ S₂ := by simp [hjT, hjS₂]
    have hU : insert j T ∪ S₂ = insert j (T ∪ S₂) := Finset.insert_union j T S₂
    have hcardT : (T ∪ S₂).card < n := by
      rw [hU, Finset.card_insert_of_notMem hjU] at hcard
      omega
    have hih := ih hdisjT hcardT.le
    have hstep := hcond j (T ∪ S₂) hcardT hjU
    rw [hU, real_avoidAll_insert P hA, Finset.prod_insert hjT]
    have hfac : 0 ≤ 1 - ε j := by linarith [hε1 j]
    calc (1 - ε j) * (∏ k ∈ T, (1 - ε k)) * P.real (avoidAll A S₂)
        = (1 - ε j) * ((∏ k ∈ T, (1 - ε k)) * P.real (avoidAll A S₂)) := by ring
      _ ≤ (1 - ε j) * P.real (avoidAll A (T ∪ S₂)) := mul_le_mul_of_nonneg_left hih hfac
      _ ≤ P.real (avoidAll A (T ∪ S₂)) - P.real (A j ∩ avoidAll A (T ∪ S₂)) := by linarith

omit [Fintype ι] [DecidableEq ι] in
/-- **SUV p. 246, proof of Theorem 160, statement (1).**  The induction hypothesis in its
conditional form: for every `i` and every set `S` of events not containing `i`, the probability of
`A_i` given that no event of `S` happens is at most `ε_i`.  Written without division, so that no
condition of probability `0` has to be excluded. -/
theorem lovasz_conditional_bound (P : Measure Ω) [IsProbabilityMeasure P] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (N : ι → Finset ι)
    (hind : IsLocallyIndependent P A N) (ε : ι → ℝ) (hε0 : ∀ i, 0 < ε i) (hε1 : ∀ i, ε i < 1)
    (hbound : ∀ i, P.real (A i) ≤ ε i * ∏ j ∈ N i, (1 - ε j)) (i : ι) (S : Finset ι) (hi : i ∉ S) :
    P.real (A i ∩ avoidAll A S) ≤ ε i * P.real (avoidAll A S) := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing i S with
  | _ n ih =>
    have hcond : ∀ (i' : ι) (S' : Finset ι), S'.card < n → i' ∉ S' →
        P.real (A i' ∩ avoidAll A S') ≤ ε i' * P.real (avoidAll A S') := fun i' S' hlt hi' =>
      ih S'.card (by omega) i' S' hi' rfl
    set S₁ := S.filter (· ∈ N i) with hS₁
    set S₂ := S.filter (· ∉ N i) with hS₂
    have hunion : S₁ ∪ S₂ = S := Finset.filter_union_filter_not_eq _ S
    have hdisj : Disjoint S₁ S₂ := Finset.disjoint_filter_filter_not _ _ _
    have hprod := prod_mul_le_avoidAll P hA hε1 hcond S₂ S₁ hdisj (by rw [hunion]; omega)
    rw [hunion] at hprod
    -- Independence of `A i` from the far events.
    have hindep : P.real (A i ∩ avoidAll A S₂) = P.real (A i) * P.real (avoidAll A S₂) := by
      have hfar : MeasurableSet[MeasurableSpace.generateFrom
          {s | ∃ j, j ≠ i ∧ j ∉ N i ∧ s = A j}] (avoidAll A S₂) := by
        refine Finset.measurableSet_biInter S₂ fun j hj => MeasurableSet.compl ?_
        refine MeasurableSpace.measurableSet_generateFrom ⟨j, ?_, ?_, rfl⟩
        · rintro rfl
          exact hi (Finset.mem_filter.mp hj).1
        · exact (Finset.mem_filter.mp hj).2
      have hnear : MeasurableSet[MeasurableSpace.generateFrom {A i}] (A i) :=
        MeasurableSpace.measurableSet_generateFrom rfl
      have h := (Indep_iff _ _ P).mp (hind i) _ _ hnear hfar
      simp only [Measure.real]
      rw [h, ENNReal.toReal_mul]
    have hnn : 0 ≤ P.real (avoidAll A S₂) := ENNReal.toReal_nonneg
    have hprodle : ∏ j ∈ N i, (1 - ε j) ≤ ∏ j ∈ S₁, (1 - ε j) := by
      have hsubN : S₁ ⊆ N i := fun j hj => (Finset.mem_filter.mp hj).2
      rw [← Finset.prod_sdiff hsubN]
      have hle1 : ∏ j ∈ N i \ S₁, (1 - ε j) ≤ 1 :=
        Finset.prod_le_one₀ (fun j _ => by linarith [hε1 j]) (fun j _ => by linarith [hε0 j])
      have hnn1 : 0 ≤ ∏ j ∈ S₁, (1 - ε j) :=
        Finset.prod_nonneg fun j _ => by linarith [hε1 j]
      nlinarith
    have hsub : A i ∩ avoidAll A S ⊆ A i ∩ avoidAll A S₂ := by
      refine Set.inter_subset_inter_right _ ?_
      intro x hx
      simp only [avoidAll, Set.mem_iInter] at hx ⊢
      exact fun j hj => hx j (Finset.mem_filter.mp hj).1
    calc P.real (A i ∩ avoidAll A S) ≤ P.real (A i ∩ avoidAll A S₂) :=
          ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
      _ = P.real (A i) * P.real (avoidAll A S₂) := hindep
      _ ≤ (ε i * ∏ j ∈ N i, (1 - ε j)) * P.real (avoidAll A S₂) :=
          mul_le_mul_of_nonneg_right (hbound i) hnn
      _ ≤ (ε i * ∏ j ∈ S₁, (1 - ε j)) * P.real (avoidAll A S₂) := by
          refine mul_le_mul_of_nonneg_right ?_ hnn
          exact mul_le_mul_of_nonneg_left hprodle (hε0 i).le
      _ = ε i * ((∏ j ∈ S₁, (1 - ε j)) * P.real (avoidAll A S₂)) := by ring
      _ ≤ ε i * P.real (avoidAll A S) := mul_le_mul_of_nonneg_left hprod (hε0 i).le

omit [DecidableEq ι] in
/-- **SUV Theorem 160, p. 246 (Lovász local lemma).**  If reals `ε_i ∈ (0, 1)` satisfy
`Pr[A_i] ≤ ε_i ∏_{j ∈ N(i)} (1 - ε_j)` for all `i`, then the probability of avoiding all the `A_i`
is at least `∏_i (1 - ε_i)`.  The hypothesis `i ∉ N(i)` of the book is kept, although the proof does
not use it. -/
theorem lovasz_local_lemma (P : Measure Ω) [IsProbabilityMeasure P] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (N : ι → Finset ι) (_hN : ∀ i, i ∉ N i)
    (hind : IsLocallyIndependent P A N) (ε : ι → ℝ) (hε0 : ∀ i, 0 < ε i) (hε1 : ∀ i, ε i < 1)
    (hbound : ∀ i, P.real (A i) ≤ ε i * ∏ j ∈ N i, (1 - ε j)) :
    ∏ i, (1 - ε i) ≤ P.real (⋂ i, (A i)ᶜ) := by
  classical
  have hcond : ∀ (i : ι) (S : Finset ι), S.card < Fintype.card ι + 1 → i ∉ S →
      P.real (A i ∩ avoidAll A S) ≤ ε i * P.real (avoidAll A S) := fun i S _ hi =>
    lovasz_conditional_bound P A hA N hind ε hε0 hε1 hbound i S hi
  have h := prod_mul_le_avoidAll P hA hε1 hcond ∅ Finset.univ (Finset.disjoint_empty_right _)
    (by simp)
  have hempty : avoidAll A (∅ : Finset ι) = Set.univ := by simp [avoidAll]
  have huniv : avoidAll A (Finset.univ ∪ ∅ : Finset ι) = ⋂ i, (A i)ᶜ := by simp [avoidAll]
  rw [hempty, huniv, probReal_univ, mul_one] at h
  exact h

/-- A sequence of `L + 1` cells filled with numbers below `N` that avoids the prohibited pairs. -/
def IsValidFilling {L N : ℕ} (forbidden : Fin L → Finset (Fin N × Fin N))
    (a : Fin (L + 1) → Fin N) : Prop :=
  ∀ i : Fin L, (a i.castSucc, a i.succ) ∉ forbidden i


private noncomputable def exists_isValidFilling_of_four_div_twentySeven_uniformMeasure
    {L N : ℕ} : MeasureTheory.Measure (Fin (L + 1) → Fin N) :=
  MeasureTheory.Measure.pi (fun _ => (N : ENNReal)⁻¹ • MeasureTheory.Measure.count)

/-- Step 2 of the proof of `exists_isValidFilling_of_four_div_twentySeven`: uniformMeasure
is a probability measure. -/
private lemma exists_isValidFilling_of_four_div_twentySeven_isProbabilityMeasure_uniformMeasure
    {L N : ℕ} (hN : 0 < N) :
  MeasureTheory.IsProbabilityMeasure
    (exists_isValidFilling_of_four_div_twentySeven_uniformMeasure (L := L) (N := N)) := by
  have : MeasureTheory.IsProbabilityMeasure
      ((N : ENNReal)⁻¹ • (MeasureTheory.Measure.count : MeasureTheory.Measure (Fin N))) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.count_apply_finite _
        Set.finite_univ]
    simp only [Set.Finite.toFinset_univ, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)
  unfold exists_isValidFilling_of_four_div_twentySeven_uniformMeasure
  infer_instance

private def exists_isValidFilling_of_four_div_twentySeven_badEvent {L N : ℕ} (forbidden :
    Fin L → Finset (Fin N × Fin N)) (i : Fin L) : Set (Fin (L + 1) → Fin N) :=
  { a | (a i.castSucc, a i.succ) ∈ forbidden i }

/-- Step 4 of the proof of `exists_isValidFilling_of_four_div_twentySeven`: badEvent is
measurable. -/
private lemma exists_isValidFilling_of_four_div_twentySeven_measurableSet_badEvent {L N : ℕ}
    (forbidden : Fin L → Finset (Fin N × Fin N)) (i : Fin L) :
  MeasurableSet (exists_isValidFilling_of_four_div_twentySeven_badEvent forbidden i) := by
  dsimp [exists_isValidFilling_of_four_div_twentySeven_badEvent]
  have h_meas : Measurable (fun (a : Fin (L + 1) → Fin N) => (a i.castSucc, a i.succ)) :=
    (measurable_pi_apply i.castSucc).prodMk (measurable_pi_apply i.succ)
  have h_set : MeasurableSet (↑(forbidden i) : Set (Fin N × Fin N)) :=
      Finset.measurableSet (forbidden i)
  exact h_meas h_set

private def exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors {L : ℕ}
    (i : Fin L) : Finset (Fin L) :=
  Finset.univ.filter (fun j => j.val = i.val + 1 ∨ i.val = j.val + 1)

/-- Step 6 of the proof of `exists_isValidFilling_of_four_div_twentySeven`:
badEventNeighbors does not contain i. -/
private lemma exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors_not_mem {L : ℕ}
    (i : Fin L) :
  i ∉ exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors i := by
  unfold exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors
  simp

/-- The uniform measure on one cell is a probability measure. -/
private lemma exists_isValidFilling_of_four_div_twentySeven_badEvent_isLocallyIndependent_aux1
    {N : ℕ} (hN : 0 < N) :
    MeasureTheory.IsProbabilityMeasure ((N : ENNReal)⁻¹ • (MeasureTheory.Measure.count :
        MeasureTheory.Measure (Fin N))) := by
  refine ⟨?_⟩
  rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.count_apply_finite _ Set.finite_univ]
  simp only [Set.Finite.toFinset_univ, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)

/-- A bad event is measurable for the σ-algebra generated by any set of coordinates containing its
two cells. -/
private lemma exists_isValidFilling_of_four_div_twentySeven_badEvent_isLocallyIndependent_aux2
    {L N : ℕ}
    (forbidden : Fin L → Finset (Fin N × Fin N)) (j : Fin L) (U : Set (Fin (L + 1)))
    (h1 : j.castSucc ∈ U) (h2 : j.succ ∈ U) :
    MeasurableSet[⨆ k ∈ U, MeasurableSpace.comap (fun a : Fin (L + 1) → Fin N => a k) inferInstance]
      (exists_isValidFilling_of_four_div_twentySeven_badEvent forbidden j) := by
  have hU : ∀ k ∈ U, Measurable[⨆ k ∈ U, MeasurableSpace.comap (fun a : Fin (L + 1) → Fin N => a k)
      inferInstance]
      (fun a : Fin (L + 1) → Fin N => a k) := fun k hk =>
    (measurable_iff_comap_le).2 (le_iSup₂ (f := fun k (_ : k ∈ U) =>
      MeasurableSpace.comap (fun a : Fin (L + 1) → Fin N => a k) inferInstance) k hk)
  have hm : Measurable[⨆ k ∈ U, MeasurableSpace.comap (fun a : Fin (L + 1) → Fin N => a k)
      inferInstance]
      (fun a : Fin (L + 1) → Fin N => (a j.castSucc, a j.succ)) :=
    (hU _ h1).prodMk (hU _ h2)
  exact hm (Finset.measurableSet (forbidden j))

/-- Step 7 of the proof of `exists_isValidFilling_of_four_div_twentySeven`: badEvents are
locally independent. -/
private lemma exists_isValidFilling_of_four_div_twentySeven_badEvent_isLocallyIndependent
    {L N : ℕ} (hN : 0 < N)
  (forbidden : Fin L → Finset (Fin N × Fin N)) :
  IsLocallyIndependent (exists_isValidFilling_of_four_div_twentySeven_uniformMeasure (L := L)
      (N := N)) (exists_isValidFilling_of_four_div_twentySeven_badEvent forbidden)
      exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors := by
  intro i
  have := exists_isValidFilling_of_four_div_twentySeven_badEvent_isLocallyIndependent_aux1 hN
  have : MeasureTheory.IsProbabilityMeasure
      (exists_isValidFilling_of_four_div_twentySeven_uniformMeasure (L := L) (N := N)) := by
    unfold exists_isValidFilling_of_four_div_twentySeven_uniformMeasure
    infer_instance
  have hind : iIndepFun (fun (k : Fin (L + 1)) (a : Fin (L + 1) → Fin N) => a k)
      (exists_isValidFilling_of_four_div_twentySeven_uniformMeasure (L := L) (N := N)) :=
    iIndepFun_pi (μ := fun _ : Fin (L + 1) => (N : ENNReal)⁻¹ • (MeasureTheory.Measure.count :
                                                MeasureTheory.Measure (Fin N)))
      (X := fun _ => id) (fun _ => aemeasurable_id)
  have hi := (iIndepFun_iff_iIndep (fun _ => (inferInstance : MeasurableSpace (Fin N))) _ _).mp hind
  have hle : ∀ k : Fin (L + 1), MeasurableSpace.comap (fun a : Fin (L + 1) → Fin N => a k)
      inferInstance ≤
      (inferInstance : MeasurableSpace (Fin (L + 1) → Fin N)) :=
          fun k => (measurable_pi_apply k).comap_le
  have hdisj : Disjoint ({i.castSucc, i.succ} : Set (Fin (L + 1))) {k | k ≠ i.castSucc ∧ k ≠ i.succ}
      := by
    rw [Set.disjoint_left]
    rintro k (rfl | rfl) ⟨h1, h2⟩
    · exact h1 rfl
    · exact h2 rfl
  have h := indep_iSup_of_disjoint hle hi hdisj
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s (rfl)
    exact exists_isValidFilling_of_four_div_twentySeven_badEvent_isLocallyIndependent_aux2 forbidden
        i _
      (by simp) (by simp)
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨j, hji, hjn, rfl⟩
    simp only [exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors,
        Finset.mem_filter,
      Finset.mem_univ, true_and, not_or] at hjn
    have := Fin.val_ne_of_ne hji
    refine exists_isValidFilling_of_four_div_twentySeven_badEvent_isLocallyIndependent_aux2
      forbidden j _ ?_ ?_
    · simp only [Set.mem_ofPred_eq, ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
      omega
    · simp only [Set.mem_ofPred_eq, ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
      omega

/-- Step 1 of the proof of
`exists_isValidFilling_of_four_div_twentySeven_badEvent_prob_bound`: prob is F / N^2. -/
private lemma exists_isValidFilling_of_four_div_twentySeven_prob
    {L N : ℕ} (hN : 0 < N)
  (forbidden : Fin L → Finset (Fin N × Fin N)) (i : Fin L) :
  (exists_isValidFilling_of_four_div_twentySeven_uniformMeasure (L := L) (N := N)).real
      (exists_isValidFilling_of_four_div_twentySeven_badEvent forbidden i) =
  ((forbidden i).card : ℝ) / (N : ℝ) ^ 2 := by
  classical
  have := exists_isValidFilling_of_four_div_twentySeven_badEvent_isLocallyIndependent_aux1 hN
  have : MeasureTheory.IsProbabilityMeasure
      (exists_isValidFilling_of_four_div_twentySeven_uniformMeasure (L := L) (N := N)) := by
    unfold exists_isValidFilling_of_four_div_twentySeven_uniformMeasure
    infer_instance
  set ν : MeasureTheory.Measure (Fin N) := (N : ENNReal)⁻¹ • (MeasureTheory.Measure.count :
      MeasureTheory.Measure (Fin N)) with hν
  set P := exists_isValidFilling_of_four_div_twentySeven_uniformMeasure (L := L) (N := N) with
      hP
  have hind : iIndepFun (fun (k : Fin (L + 1)) (a : Fin (L + 1) → Fin N) => a k) P :=
    iIndepFun_pi (μ := fun _ : Fin (L + 1) => ν) (X := fun _ => id) (fun _ => aemeasurable_id)
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ).ne
  have hI := hind.indepFun hne
  have hmap : ∀ k : Fin (L + 1), P.map (fun a : Fin (L + 1) → Fin N => a k) = ν := by
    intro k
    have := MeasureTheory.Measure.pi_map_eval (μ := fun _ : Fin (L + 1) => ν) k
    have h1 : (∏ j ∈ Finset.univ.erase k, ν Set.univ) = 1 := by
      apply Finset.prod_eq_one
      intro j _
      exact measure_univ
    rw [h1, one_smul] at this
    exact this
  have hpair := (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply i.castSucc).aemeasurable (measurable_pi_apply i.succ).aemeasurable).mp hI
  rw [hmap, hmap] at hpair
  have hmeas : Measurable (fun a : Fin (L + 1) → Fin N => (a i.castSucc, a i.succ)) :=
    (measurable_pi_apply i.castSucc).prodMk (measurable_pi_apply i.succ)
  have hset : exists_isValidFilling_of_four_div_twentySeven_badEvent forbidden i =
      (fun a : Fin (L + 1) → Fin N => (a i.castSucc, a i.succ)) ⁻¹' (↑(forbidden i) :
          Set (Fin N × Fin N)) := rfl
  have hsing : ∀ p : Fin N × Fin N, (ν.prod ν) {p} = ((N : ENNReal)⁻¹ * (N : ENNReal)⁻¹) := by
    intro p
    have : ({p} : Set (Fin N × Fin N)) = ({p.1} : Set (Fin N)) ×ˢ ({p.2} : Set (Fin N)) := by
      ext q; simp [Prod.ext_iff]
    rw [this, MeasureTheory.Measure.prod_prod]
    simp [hν]
  have hENN : P (exists_isValidFilling_of_four_div_twentySeven_badEvent forbidden i) =
      ((forbidden i).card : ENNReal) * ((N : ENNReal)⁻¹ * (N : ENNReal)⁻¹) := by
    rw [hset, ← MeasureTheory.Measure.map_apply hmeas (Finset.measurableSet (forbidden i)), hpair,
      ← MeasureTheory.sum_measure_singleton]
    simp only [hsing, Finset.sum_const, nsmul_eq_mul]
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [MeasureTheory.measureReal_def, hENN, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  field_simp

/-- Step 2 of the proof of
`exists_isValidFilling_of_four_div_twentySeven_badEvent_prob_bound`: number of neighbours is
<= 2. -/
private lemma exists_isValidFilling_of_four_div_twentySeven_card
    {L : ℕ} (i : Fin L) :
  (exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors i).card ≤ 2 := by
  have hinj : Function.Injective (fun j : Fin L => j.val) := Fin.val_injective
  rw [← Finset.card_image_of_injective _ hinj]
  have hsub : (exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors i).image
      (fun j : Fin L => j.val) ⊆ ({i.val + 1, i.val - 1} : Finset ℕ) := by
    intro n hn
    simp only [exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors,
        Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    obtain ⟨j, hj, rfl⟩ := hn
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact (Finset.card_le_card hsub).trans (Finset.card_le_two)

/-- Step 3 of the proof of
`exists_isValidFilling_of_four_div_twentySeven_badEvent_prob_bound`: algebra. -/
private lemma exists_isValidFilling_of_four_div_twentySeven_algebra
    {c : ℕ} (hc : c ≤ 2)
  {F N : ℝ} (hN : 0 < N) (hfrac : F ≤ (4 / 27) * N ^ 2) :
  F / N ^ 2 ≤ (1 / 3) * (2 / 3) ^ c := by
  have h_pow : (4 / 9 : ℝ) ≤ (2 / 3) ^ c := by
    cases c with
    | zero => norm_num
    | succ c =>
      cases c with
      | zero => norm_num
      | succ c =>
        cases c with
        | zero => norm_num
        | succ c => omega
  have hF : F / N ^ 2 ≤ 4 / 27 := by
    rw [div_le_iff₀]
    · exact hfrac
    · positivity
  linarith

/-- Step 8 of the proof of `exists_isValidFilling_of_four_div_twentySeven`: prob of bad
event is bounded. -/
private lemma exists_isValidFilling_of_four_div_twentySeven_badEvent_prob_bound {L N : ℕ}
    (hN : 0 < N)
  (forbidden : Fin L → Finset (Fin N × Fin N))
  (hfrac : ∀ i, ((forbidden i).card : ℝ) ≤ (4 / 27) * (N : ℝ) ^ 2) (i : Fin L) :
  (exists_isValidFilling_of_four_div_twentySeven_uniformMeasure (L := L) (N := N)).real
      (exists_isValidFilling_of_four_div_twentySeven_badEvent forbidden i) ≤
    (1 / 3) * ∏ _j ∈ exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors i,
        (1 - (1 / 3 : ℝ)) := by
  have h1 := exists_isValidFilling_of_four_div_twentySeven_prob hN
      forbidden i
  rw [h1]
  have h2 := exists_isValidFilling_of_four_div_twentySeven_card i
  have h3 := exists_isValidFilling_of_four_div_twentySeven_algebra
      h2 (Nat.cast_pos.mpr hN) (hfrac i)
  have hprod : ∏ _j ∈ exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors i,
      (1 - (1 / 3 : ℝ)) = (2 / 3 : ℝ) ^
      (exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors i).card := by
    calc ∏ _j ∈ exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors i,
        (1 - (1 / 3 : ℝ))
      _ = ∏ _j ∈ exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors i,
          (2 / 3 : ℝ) := by
        apply Finset.prod_congr rfl
        intro _ _
        norm_num
      _ = (2 / 3 : ℝ) ^ (exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors
          i).card := by
        exact Finset.prod_const _
  rw [hprod]
  exact h3

/-- Step 9 of the proof of `exists_isValidFilling_of_four_div_twentySeven`: if avoidAll
has pos prob, a valid filling exists. -/
private lemma exists_isValidFilling_of_four_div_twentySeven_exists_of_prob_avoidAll_pos
    {L N : ℕ}
  (forbidden : Fin L → Finset (Fin N × Fin N))
  (hpos : 0 < (exists_isValidFilling_of_four_div_twentySeven_uniformMeasure (L := L)
      (N := N)).real (⋂ i, (exists_isValidFilling_of_four_div_twentySeven_badEvent forbidden
      i)ᶜ)) :
  ∃ a, IsValidFilling forbidden a := by
  have hne : (⋂ i, (exists_isValidFilling_of_four_div_twentySeven_badEvent forbidden
      i)ᶜ).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [h] at hpos
    simp [MeasureTheory.Measure.real] at hpos
  obtain ⟨a, ha⟩ := hne
  refine ⟨a, fun i => ?_⟩
  have := Set.mem_iInter.mp ha i
  simpa [exists_isValidFilling_of_four_div_twentySeven_badEvent] using this

/-- **SUV Problem 249, p. 247.**  A finite tape with cells holding numbers among `N` values, with a
set of prohibited pairs for each border.  If for each border the prohibited pairs are at most the
fraction `4/27` of all `N²` pairs, all cells can be filled.  The tape is a non-empty one with
`L + 1` cells, and the hypothesis `0 < N` excludes the empty alphabet, for which there is nothing to
fill with. -/
theorem exists_isValidFilling_of_four_div_twentySeven {L N : ℕ} (hN : 0 < N)
    (forbidden : Fin L → Finset (Fin N × Fin N))
    (hfrac : ∀ i, ((forbidden i).card : ℝ) ≤ (4 / 27) * (N : ℝ) ^ 2) :
    ∃ a, IsValidFilling forbidden a := by
  have : MeasureTheory.IsProbabilityMeasure
      (exists_isValidFilling_of_four_div_twentySeven_uniformMeasure (L := L) (N := N)) :=
      exists_isValidFilling_of_four_div_twentySeven_isProbabilityMeasure_uniformMeasure hN
  have hpos : 0 < (exists_isValidFilling_of_four_div_twentySeven_uniformMeasure (L := L)
      (N := N)).real (⋂ i, (exists_isValidFilling_of_four_div_twentySeven_badEvent forbidden
      i)ᶜ) := by
    have h_lll := lovasz_local_lemma
      (exists_isValidFilling_of_four_div_twentySeven_uniformMeasure (L := L) (N := N))
      (exists_isValidFilling_of_four_div_twentySeven_badEvent forbidden)
      (exists_isValidFilling_of_four_div_twentySeven_measurableSet_badEvent forbidden)
      exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors
      exists_isValidFilling_of_four_div_twentySeven_badEventNeighbors_not_mem
      (exists_isValidFilling_of_four_div_twentySeven_badEvent_isLocallyIndependent hN forbidden)
      (fun _ => (1 / 3 : ℝ))
      (fun _ => by norm_num)
      (fun _ => by norm_num)
      (exists_isValidFilling_of_four_div_twentySeven_badEvent_prob_bound hN forbidden hfrac)
    have hprod : 0 < ∏ i : Fin L, (1 - (1 / 3 : ℝ)) := by
      apply Finset.prod_pos
      intro _ _
      norm_num
    exact lt_of_lt_of_le hprod h_lll
  exact exists_isValidFilling_of_four_div_twentySeven_exists_of_prob_avoidAll_pos forbidden
      hpos

/-- Step 1 of the proof of `exists_isValidFilling_of_lt_quarter`: More than half of
elements are good on the left. -/
private lemma exists_isValidFilling_of_lt_quarter_left_good {N : ℕ}
    (F : Finset (Fin N × Fin N)) (hF : 4 * F.card < N ^ 2) :
    ∃ S : Finset (Fin N), N < 2 * S.card ∧
      ∀ l ∈ S, N < 2 * (Finset.univ.filter fun r => (l, r) ∉ F).card := by
  classical
  refine ⟨Finset.univ.filter fun l : Fin N =>
    N < 2 * (Finset.univ.filter fun r => (l, r) ∉ F).card, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    set S := Finset.univ.filter fun l : Fin N =>
      N < 2 * (Finset.univ.filter fun r => (l, r) ∉ F).card with hS
    set T := Finset.univ.filter fun l : Fin N =>
      ¬ N < 2 * (Finset.univ.filter fun r => (l, r) ∉ F).card with hT
    have hST : S.card + T.card = N := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
        (fun l : Fin N => N < 2 * (Finset.univ.filter fun r => (l, r) ∉ F).card)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      exact this
    have hT2 : N ≤ 2 * T.card := by omega
    set f : Fin N → ℕ := fun l => (Finset.univ.filter fun r => (l, r) ∈ F).card with hf
    have hFsum : F.card = ∑ l, f l := by
      have h1 : F.card = ∑ p : Fin N × Fin N, if p ∈ F then 1 else 0 := by
        rw [← Finset.card_filter]
        congr 1
        ext p; simp
      rw [h1, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hf]; simp only
      rw [Finset.card_filter]
    have hfl : ∀ l ∈ T, N ≤ 2 * f l := by
      intro l hl
      have hl' : ¬ N < 2 * (Finset.univ.filter fun r => (l, r) ∉ F).card := by
        simpa [hT] using hl
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
        (fun r : Fin N => (l, r) ∈ F)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      simp only [hf]
      omega
    have hTF : ∑ l ∈ T, f l ≤ F.card := by
      rw [hFsum]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ T)
    have hTN : T.card * N ≤ 2 * ∑ l ∈ T, f l := by
      have : ∑ l ∈ T, N ≤ ∑ l ∈ T, 2 * f l := Finset.sum_le_sum hfl
      rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at this
      exact this
    nlinarith
  · intro l hl
    exact (Finset.mem_filter.mp hl).2

/-- Step 2 of the proof of `exists_isValidFilling_of_lt_quarter`: Any two sets strictly
larger than N/2 intersect. -/
private lemma exists_isValidFilling_of_lt_quarter_inter {N : ℕ} (S1 S2 : Finset (Fin N))
    (h1 : N < 2 * S1.card) (h2 : N < 2 * S2.card) : (S1 ∩ S2).Nonempty := by
  by_contra h
  rw [Finset.nonempty_iff_ne_empty, not_not] at h
  have h_disj : Disjoint S1 S2 := Finset.disjoint_iff_inter_eq_empty.mpr h
  have h_union : (S1 ∪ S2).card = S1.card + S2.card := Finset.card_union_of_disjoint h_disj
  have h_univ : (S1 ∪ S2).card ≤ N := by
    have h_sub : S1 ∪ S2 ⊆ Finset.univ := Finset.subset_univ (S1 ∪ S2)
    have h_card : (S1 ∪ S2).card ≤ Finset.univ.card := Finset.card_le_card h_sub
    have h_univ_card : Finset.univ.card = N := Fintype.card_fin N
    rw [h_univ_card] at h_card
    exact h_card
  have h_sum : 2 * N < 2 * (S1.card + S2.card) := by omega
  have h_sum2 : 2 * N < 2 * (S1 ∪ S2).card := by
    rw [h_union]
    exact h_sum
  have h_sum3 : 2 * N ≤ 2 * N := by rfl
  omega

/-- Step 3 of the proof of `exists_isValidFilling_of_lt_quarter`: Equivalence for
`IsValidFilling` of `Fin.cons x a'`. -/
private lemma exists_isValidFilling_of_lt_quarter_cons {L N : ℕ}
    (forbidden : Fin (L + 1) → Finset (Fin N × Fin N)) (x : Fin N) (a' : Fin (L + 1) → Fin N) :
    IsValidFilling forbidden (Fin.cons x a') ↔
    (x, a' 0) ∉ forbidden 0 ∧ IsValidFilling (fun i => forbidden i.succ) a' := by
  unfold IsValidFilling
  constructor
  · intro h
    refine ⟨?_, fun j => ?_⟩
    · simpa using h 0
    · simpa using h j.succ
  · rintro ⟨h0, h1⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using h0
    · simpa using h1 j

/-- Step 4 of the proof of `exists_isValidFilling_of_lt_quarter`: Inductive step
constructing the valid filling. -/
private lemma exists_isValidFilling_of_lt_quarter_induction {L N : ℕ} (hN : 0 < N)
    (forbidden : Fin L → Finset (Fin N × Fin N))
    (hF : ∀ i, 4 * (forbidden i).card < N ^ 2) :
    ∃ S : Finset (Fin N), N < 2 * S.card ∧
      ∀ l ∈ S, ∃ a : Fin (L + 1) → Fin N, a 0 = l ∧ IsValidFilling forbidden a := by
  induction L with
  | zero =>
    let S : Finset (Fin N) := Finset.univ
    have hS_card : S.card = N := Fintype.card_fin N
    have hS_bound : N < 2 * S.card := by omega
    use S
    refine ⟨hS_bound, ?_⟩
    intro l _
    use (fun _ => l)
    refine ⟨rfl, ?_⟩
    intro i
    exact Fin.elim0 i
  | succ L ih =>
    have h_forb_succ : ∀ i : Fin L, 4 * ((fun i => forbidden i.succ) i).card < N ^ 2 :=
        fun i => hF i.succ
    obtain ⟨S2, hS2_card, hS2_prop⟩ := ih (fun i => forbidden i.succ) h_forb_succ
    have h_F0 := hF 0
    obtain ⟨S1, hS1_card, hS1_prop⟩ := exists_isValidFilling_of_lt_quarter_left_good
        (forbidden 0) h_F0
    use S1
    refine ⟨hS1_card, ?_⟩
    intro l hl
    have hl_good := hS1_prop l hl
    have h_inter := exists_isValidFilling_of_lt_quarter_inter (Finset.univ.filter fun r =>
      (l, r) ∉ forbidden 0) S2 hl_good hS2_card
    have h_card_pos : 0 < ((Finset.univ.filter fun r => (l, r) ∉ forbidden 0) ∩ S2).card :=
        Finset.card_pos.mpr h_inter
    obtain ⟨x, hx⟩ : ∃ x, x ∈ (Finset.univ.filter fun r => (l, r) ∉ forbidden 0) ∩ S2 := by
      have hx1 := Finset.card_pos.mp h_card_pos
      exact hx1
    have hx_good : (l, x) ∉ forbidden 0 := by
      have hx1 : x ∈ Finset.univ.filter (fun r => (l, r) ∉ forbidden 0) :=
          Finset.mem_inter.mp hx |>.1
      exact (Finset.mem_filter.mp hx1).2
    have hx_S2 : x ∈ S2 := Finset.mem_inter.mp hx |>.2
    obtain ⟨a', ha'0, ha'⟩ := hS2_prop x hx_S2
    use Fin.cons l a'
    refine ⟨rfl, ?_⟩
    rw [exists_isValidFilling_of_lt_quarter_cons]
    have ha'0_eq : a' 0 = x := ha'0
    rw [ha'0_eq]
    exact ⟨hx_good, ha'⟩


/-- **SUV Problem 250, p. 247.**  The same, without the local lemma, if each set of prohibited pairs
contains less than `1/4` of all pairs. -/
theorem exists_isValidFilling_of_lt_quarter {L N : ℕ} (hN : 0 < N)
    (forbidden : Fin L → Finset (Fin N × Fin N))
    (hfrac : ∀ i, ((forbidden i).card : ℝ) < (1 / 4) * (N : ℝ) ^ 2) :
    ∃ a, IsValidFilling forbidden a := by
  have hF : ∀ i, 4 * (forbidden i).card < N ^ 2 := by
    intro i
    have hf := hfrac i
    have h1 : 4 * ((forbidden i).card : ℝ) < (N : ℝ) ^ 2 := by linarith
    have h2 : ((4 * (forbidden i).card : ℕ) : ℝ) = 4 * ((forbidden i).card : ℝ) := by
      push_cast; ring
    have h3 : ((N ^ 2 : ℕ) : ℝ) = (N : ℝ) ^ 2 := by push_cast; rfl
    rw [← h2, ← h3] at h1
    exact Nat.cast_lt.mp h1
  obtain ⟨S, hS_card, hS_prop⟩ := exists_isValidFilling_of_lt_quarter_induction hN forbidden
      hF
  have hS_nonempty : S.card > 0 := by omega
  obtain ⟨l, hl⟩ := Finset.card_pos.mp hS_nonempty
  obtain ⟨a, _, ha⟩ := hS_prop l hl
  exact ⟨a, ha⟩

private lemma exists_threshold_lll_forbidden_tail_aux_partial (q : ℝ) (N M : ℕ)
    (hs : Summable (fun k : ℕ => (k : ℝ) * q ^ k)) (hq0 : 0 < q) :
    ∑ k ∈ Finset.Icc (N + 1) M, (k : ℝ) * q ^ k
      ≤ ∑' j : ℕ, ((j + (N + 1) : ℕ) : ℝ) * q ^ (j + (N + 1)) := by
  have hs1 : Summable (fun j : ℕ => ((j + (N + 1) : ℕ) : ℝ) * q ^ (j + (N + 1))) :=
    (summable_nat_add_iff (f := fun k : ℕ => (k : ℝ) * q ^ k) (N + 1)).mpr hs
  have hnn : ∀ j : ℕ, 0 ≤ ((j + (N + 1) : ℕ) : ℝ) * q ^ (j + (N + 1)) := fun j => by positivity
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have := hs1.sum_le_tsum (Finset.range (M + 1 - (N + 1))) (fun j _ => hnn j)
  refine le_trans (le_of_eq ?_) this
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_comm (N + 1) j]

/-- Step 1 of the proof of `exists_threshold_lll_forbidden`: tail bound -/
private lemma exists_threshold_lll_forbidden_tail {α β : ℝ} (hαβ : α < β) (hβ : β < 1) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ M : ℕ, (2 : ℝ) ^ (α - β) ≤ 1 - ∑ k ∈ Finset.Icc T M, (k : ℝ) * (2 : ℝ) ^
        ((β - 1) * (k : ℝ)) := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (2 : ℝ) ^ (β - 1) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := by rw [hq]; exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
                           (by linarith)
  have hpow : ∀ k : ℕ, (2 : ℝ) ^ ((β - 1) * (k : ℝ)) = q ^ k := by
    intro k
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  simp_rw [hpow]
  have hs : Summable (fun k : ℕ => (k : ℝ) * q ^ k) := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
        (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
    simpa using this
  have hlt : (2 : ℝ) ^ (α - β) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hε : 0 < 1 - (2 : ℝ) ^ (α - β) := by linarith
  have ht := tendsto_sum_nat_add (fun k : ℕ => (k : ℝ) * q ^ k)
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hε)))
  have hN1 : ∑' j : ℕ, ((j + (N + 1) : ℕ) : ℝ) * q ^ (j + (N + 1)) < 1 - (2 : ℝ) ^ (α - β) :=
    hN (N + 1) (by omega)
  refine ⟨N + 1, by omega, fun M => ?_⟩
  have h2 := exists_threshold_lll_forbidden_tail_aux_partial q N M hs hq0
  linarith

/-- Weierstrass product inequality: `1 - ∑ x_k ≤ ∏ (1 - x_k)` for `x_k ∈ [0, 1]`. -/
private lemma exists_threshold_lll_forbidden_prod_weierstrass (s : Finset ℕ) (x : ℕ → ℝ)
    (h : ∀ k ∈ s, 0 ≤ x k ∧ x k ≤ 1) : 1 - ∑ k ∈ s, x k ≤ ∏ k ∈ s, (1 - x k) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ha' := h a (Finset.mem_insert_self a s)
    have ih' := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    have hS : 0 ≤ ∑ k ∈ s, x k := Finset.sum_nonneg fun k hk =>
      (h k (Finset.mem_insert_of_mem hk)).1
    nlinarith [mul_nonneg ha'.1 hS, mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr ha'.2)]

/-- Step 2 of the proof of `exists_threshold_lll_forbidden`: product inequality -/
private lemma exists_threshold_lll_forbidden_prod {T M n : ℕ} (hT : 1 ≤ T) (hn : 1 ≤ n)
    {α β : ℝ} (_hβ : β < 1)
    (htail : (2 : ℝ) ^ (α - β) ≤ 1 - ∑ k ∈ Finset.Icc T M, (k : ℝ) * (2 : ℝ) ^ ((β - 1) * (k : ℝ)))
        :
    ((2 : ℝ) ^ (α - β)) ^ (n : ℝ) ≤ ∏ k ∈ Finset.Icc T M, (1 - (2 : ℝ) ^ ((β - 1) * (k : ℝ))) ^
        (n + k - 1 : ℕ) := by
  have hq0 : (0 : ℝ) < (2 : ℝ) ^ (β - 1) := Real.rpow_pos_of_pos zero_lt_two _
  have hq1 : (2 : ℝ) ^ (β - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpow : ∀ k : ℕ, (2 : ℝ) ^ ((β - 1) * (k : ℝ)) = ((2 : ℝ) ^ (β - 1)) ^ k := by
    intro k
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  simp_rw [hpow] at htail ⊢
  generalize hqdef : (2 : ℝ) ^ (β - 1) = q at hq0 hq1 htail ⊢
  have hc : (0 : ℝ) < (2 : ℝ) ^ (α - β) := Real.rpow_pos_of_pos zero_lt_two _
  generalize hcdef : (2 : ℝ) ^ (α - β) = c at hc htail ⊢
  have hS0 : 0 ≤ ∑ k ∈ Finset.Icc T M, (k : ℝ) * q ^ k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0.le _)
  have hterm : ∀ k ∈ Finset.Icc T M, (k : ℝ) * q ^ k ≤ 1 := by
    intro k hk
    have := Finset.single_le_sum (f := fun k : ℕ => (k : ℝ) * q ^ k)
      (fun k _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0.le _)) hk
    linarith
  have hweier := exists_threshold_lll_forbidden_prod_weierstrass (Finset.Icc T M)
    (fun k : ℕ => (k : ℝ) * q ^ k) (fun k hk =>
      ⟨mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0.le _), hterm k hk⟩)
  have h1 : c ≤ ∏ k ∈ Finset.Icc T M, (1 - (k : ℝ) * q ^ k) := by linarith
  have h2 : ∏ k ∈ Finset.Icc T M, (1 - (k : ℝ) * q ^ k) ≤
      ∏ k ∈ Finset.Icc T M, (1 - q ^ k) ^ k := by
    apply Finset.prod_le_prod₀
    · intro k hk
      linarith [hterm k hk]
    · intro k hk
      have hqk1 : q ^ k ≤ 1 := pow_le_one₀ hq0.le hq1.le
      have := one_add_mul_le_pow (a := -(q ^ k)) (by linarith [pow_pos hq0 k]) k
      have e : 1 + (k : ℝ) * -(q ^ k) = 1 - (k : ℝ) * q ^ k := by ring
      rw [e] at this
      simpa [sub_eq_add_neg] using this
  have h3 : ∏ k ∈ Finset.Icc T M, ((1 - q ^ k) ^ k) ^ n ≤
      ∏ k ∈ Finset.Icc T M, (1 - q ^ k) ^ (n + k - 1) := by
    apply Finset.prod_le_prod₀
    · intro k hk
      exact pow_nonneg (pow_nonneg (by linarith [pow_le_one₀ hq0.le hq1.le (n := k)]) _) _
    · intro k hk
      have hk1 : 1 ≤ k := le_trans hT (Finset.mem_Icc.mp hk).1
      have hqk1 : q ^ k ≤ 1 := pow_le_one₀ hq0.le hq1.le
      have hqk0 : 0 < q ^ k := pow_pos hq0 k
      rw [← pow_mul]
      apply pow_le_pow_of_le_one (by linarith) (by linarith)
      have : n + k ≤ k * n + 1 := by nlinarith
      omega
  rw [Real.rpow_natCast]
  calc c ^ n ≤ (∏ k ∈ Finset.Icc T M, (1 - q ^ k) ^ k) ^ n :=
        pow_le_pow_left₀ hc.le (h1.trans h2) n
    _ = ∏ k ∈ Finset.Icc T M, ((1 - q ^ k) ^ k) ^ n := (Finset.prod_pow _ _ _).symm
    _ ≤ _ := h3

/-- Step 3 of the proof of `exists_threshold_lll_forbidden`: exponent algebra -/
private lemma exists_threshold_lll_forbidden_pow {α β : ℝ} {n : ℕ} (_hβ : β < 1)
    {P : ℝ} (hP : ((2 : ℝ) ^ (α - β)) ^ (n : ℝ) ≤ P) :
    (2 : ℝ) ^ ((α - 1) * (n : ℝ)) ≤ (2 : ℝ) ^ ((β - 1) * (n : ℝ)) * P := by
  have h1 : (2 : ℝ) ^ ((α - 1) * (n : ℝ)) = (2 : ℝ) ^ ((β - 1) * (n : ℝ)) * ((2 : ℝ) ^ (α - β)) ^
      (n : ℝ) := by
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_add zero_lt_two]
    congr 1
    ring
  rw [h1]
  exact mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num) _)

/-- **SUV p. 248, Section 8.5.3.**  The inequality needed to apply the local lemma to Theorem 157:
for `α < β < 1` there is a threshold `T` such that for every length `n` and every finite range of
lengths `[T, M]` of neighbouring intervals,
`2^{(α-1)n} ≤ 2^{(β-1)n} ∏_k (1 - 2^{(β-1)k})^{n+k-1}`.  The finite range is the one that occurs on
a finite string; the book writes the infinite product. -/
theorem exists_threshold_lll_forbidden {α β : ℝ} (hαβ : α < β) (hβ : β < 1) :
    ∃ T : ℕ, ∀ n M : ℕ, 1 ≤ n →
      (2 : ℝ) ^ ((α - 1) * n) ≤ (2 : ℝ) ^ ((β - 1) * n) *
        ∏ k ∈ Finset.Icc T M, (1 - (2 : ℝ) ^ ((β - 1) * k)) ^ (n + k - 1) := by
  rcases exists_threshold_lll_forbidden_tail hαβ hβ with ⟨T, hT, htail⟩
  use T
  intro n M hn
  apply exists_threshold_lll_forbidden_pow hβ
  apply exists_threshold_lll_forbidden_prod hT hn hβ (htail M)

end Kolmogorov.Applications
