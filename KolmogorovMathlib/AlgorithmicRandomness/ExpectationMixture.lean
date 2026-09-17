import KolmogorovMathlib.AlgorithmicRandomness.UniversalStages
import KolmogorovMathlib.AlgorithmicRandomness.Trim
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.DyadicEnumeration
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.MonotoneLimits
import KolmogorovMathlib.AlgorithmicRandomness.StageComputable
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations

/-!
# A maximal lower semicomputable function of integral at most one

Trimming the universal family of patched stage tables at the level of integrals
and mixing the trimmed components with the weights `2 ^ -(e + 2)` produces a
lower semicomputable function `mixVal` with `∫ mixVal ∂μ ≤ 1` which dominates,
up to a multiplicative constant, every lower semicomputable function of
integral at most one.  This is the construction behind SUV Theorem 42.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-! ## Trimming a component -/

/-- All stages below `s` of the `e`-th patched table have been accepted. -/
def accBelow (a : BitString → ℕ → ℕ) (e s : ℕ) : Bool :=
  Nat.rec true (fun j IH => IH && stageAccept (patchTable e j) a j) s

/-- All stages up to and including `s` of the `e`-th patched table have been
accepted. -/
def allAcc (a : BitString → ℕ → ℕ) (e s : ℕ) : Bool := accBelow a e (s + 1)

/-- The trimmed table, shifted by one: `trimStep a e x (s + 1)` is the value of
the trimmed `e`-th table at stage `s`. -/
def trimStep (a : BitString → ℕ → ℕ) (e : ℕ) (x : BitString) (s : ℕ) : ℕ :=
  Nat.rec 0 (fun j IH => if allAcc a e j = true then patchTable e j x else 2 * IH) s

/-- The trimmed table: it follows the patched table as long as all stages are
accepted, and freezes (doubling the numerator) afterwards. -/
def trimTable (a : BitString → ℕ → ℕ) (e : ℕ) (x : BitString) (s : ℕ) : ℕ :=
  trimStep a e x (s + 1)

variable {a : BitString → ℕ → ℕ}

/-- The running acceptance flag at stage `s + 1` conjoins the flag at stage `s` with the test at
stage `s`. -/
lemma accBelow_succ (a : BitString → ℕ → ℕ) (e s : ℕ) :
    accBelow a e (s + 1) = (accBelow a e s && stageAccept (patchTable e s) a s) := rfl

/-- At stage zero the cumulative acceptance flag is the stage-zero test. -/
lemma allAcc_zero (a : BitString → ℕ → ℕ) (e : ℕ) :
    allAcc a e 0 = stageAccept (patchTable e 0) a 0 := rfl

/-- The cumulative acceptance flag conjoins all stage tests up to the current stage. -/
lemma allAcc_succ (a : BitString → ℕ → ℕ) (e s : ℕ) :
    allAcc a e (s + 1) = (allAcc a e s && stageAccept (patchTable e (s + 1)) a (s + 1)) := rfl

/-- At stage zero the trimmed table is the patched table when the stage is accepted and zero
otherwise. -/
lemma trimTable_zero (a : BitString → ℕ → ℕ) (e : ℕ) (x : BitString) :
    trimTable a e x 0 = if allAcc a e 0 = true then patchTable e 0 x else 0 := rfl

/-- At a later stage the trimmed table is the patched table if all stages are accepted, and
otherwise merely doubles the previous value. -/
lemma trimTable_succ (a : BitString → ℕ → ℕ) (e : ℕ) (x : BitString) (s : ℕ) :
    trimTable a e x (s + 1) =
      if allAcc a e (s + 1) = true then patchTable e (s + 1) x else 2 * trimTable a e x s := rfl

/-- Cumulative acceptance at a stage implies it at all earlier stages. -/
lemma allAcc_of_succ {e s : ℕ} (h : allAcc a e (s + 1) = true) : allAcc a e s = true := by
  rw [allAcc_succ, Bool.and_eq_true] at h
  exact h.1

/-- Cumulative acceptance at a stage implies the test at that stage passes. -/
lemma stageAccept_of_allAcc {e : ℕ} : ∀ {s : ℕ}, allAcc a e s = true →
    stageAccept (patchTable e s) a s = true := by
  intro s h
  cases s with
  | zero => rwa [allAcc_zero] at h
  | succ s =>
      rw [allAcc_succ, Bool.and_eq_true] at h
      exact h.2

/-- While all stages are accepted, the trimmed table agrees with the patched table. -/
lemma trimTable_of_allAcc {e : ℕ} : ∀ {s : ℕ}, allAcc a e s = true →
    ∀ x, trimTable a e x s = patchTable e s x := by
  intro s h x
  cases s with
  | zero => rw [trimTable_zero, if_pos h]
  | succ s => rw [trimTable_succ, if_pos h]

/-- The trimmed table at least doubles from one stage to the next. -/
lemma two_mul_trimTable_le (a : BitString → ℕ → ℕ) (e : ℕ) (x : BitString) (s : ℕ) :
    2 * trimTable a e x s ≤ trimTable a e x (s + 1) := by
  by_cases h : allAcc a e (s + 1) = true
  · rw [trimTable_succ, if_pos h, trimTable_of_allAcc (allAcc_of_succ h) x]
    exact two_mul_patchTable_le e s x
  · rw [trimTable_succ, if_neg h]

/-- The trimmed table at stage `s` reads at most the first `s` bits of its string argument. -/
lemma trimTable_take (a : BitString → ℕ → ℕ) (e : ℕ) (x : BitString) {m : ℕ} :
    ∀ s, s ≤ m → trimTable a e (x.take m) s = trimTable a e x s := by
  intro s
  induction s with
  | zero =>
      intro _
      rw [trimTable_zero, trimTable_zero]
      by_cases h : allAcc a e 0 = true
      · rw [if_pos h, if_pos h, patchTable_take e 0 x (Nat.zero_le m)]
      · rw [if_neg h, if_neg h]
  | succ s ih =>
      intro hs
      rw [trimTable_succ, trimTable_succ]
      by_cases h : allAcc a e (s + 1) = true
      · rw [if_pos h, if_pos h, patchTable_take e (s + 1) x hs]
      · rw [if_neg h, if_neg h, ih (Nat.le_of_succ_le hs)]

/-! ## The trimmed component -/

/-- The value of the trimmed `e`-th component at stage `s`. -/
noncomputable def trimVal (a : BitString → ℕ → ℕ) (e s : ℕ) (w : CantorSeq) : ℝ≥0∞ :=
  dyadicValue (trimTable a e (cantorPrefix w s) s) s

/-- The stage value of the trimmed table is the stage function it determines. -/
lemma trimVal_eq_stageFun (a : BitString → ℕ → ℕ) (e s : ℕ) :
    trimVal a e s = stageFun (fun x => trimTable a e x s) s := rfl

/-- The stage values of the trimmed table are non-decreasing. -/
lemma trimVal_le_succ (a : BitString → ℕ → ℕ) (e s : ℕ) (w : CantorSeq) :
    trimVal a e s w ≤ trimVal a e (s + 1) w := by
  have htake : trimTable a e (cantorPrefix w (s + 1)) s = trimTable a e (cantorPrefix w s) s := by
    rw [← cantorPrefix_take w s (s + 1) (Nat.le_succ s),
      trimTable_take a e (cantorPrefix w (s + 1)) s le_rfl]
  have hstep : 2 * trimTable a e (cantorPrefix w (s + 1)) s
      ≤ trimTable a e (cantorPrefix w (s + 1)) (s + 1) :=
    two_mul_trimTable_le a e _ s
  rw [htake] at hstep
  calc trimVal a e s w
      = dyadicValue (2 * trimTable a e (cantorPrefix w s) s) (s + 1) := by
        rw [dyadicValue_two_mul_succ]
        rfl
    _ ≤ dyadicValue (trimTable a e (cantorPrefix w (s + 1)) (s + 1)) (s + 1) :=
        lscDyadicValue_mono _ hstep
    _ = trimVal a e (s + 1) w := rfl

/-- The stage values of the trimmed table are monotone in the stage. -/
lemma trimVal_monotone (a : BitString → ℕ → ℕ) (e : ℕ) (w : CantorSeq) :
    Monotone (fun s => trimVal a e s w) :=
  monotone_nat_of_le_succ fun s => trimVal_le_succ a e s w

/-- Each stage value of the trimmed table is measurable. -/
lemma measurable_trimVal (a : BitString → ℕ → ℕ) (e s : ℕ) :
    Measurable (trimVal a e s) :=
  measurable_comp_cantorPrefix s (fun x => dyadicValue (trimTable a e x s) s)

variable {μ : Measure CantorSeq}

/-- Every trimmed stage has integral at most `2`. -/
lemma lintegral_trimVal_le
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s) (e : ℕ) :
    ∀ s, ∫⁻ w, trimVal a e s w ∂μ ≤ 2 := by
  intro s
  induction s with
  | zero =>
      by_cases h : allAcc a e 0 = true
      · have hacc : stageAccept (patchTable e 0) a 0 = true := stageAccept_of_allAcc h
        have heq : trimVal a e 0 = stageFun (patchTable e 0) 0 := by
          funext w
          simp only [trimVal, stageFun, trimTable_of_allAcc h]
        rw [heq]
        exact lintegral_stageFun_le_of_accept ha hacc
      · have heq : ∀ w, trimVal a e 0 w = 0 := by
          intro w
          simp only [trimVal]
          rw [trimTable_zero, if_neg h]
          simp [dyadicValue]
        simp only [heq]
        simp
  | succ s ih =>
      by_cases h : allAcc a e (s + 1) = true
      · have hacc : stageAccept (patchTable e (s + 1)) a (s + 1) = true :=
          stageAccept_of_allAcc h
        have heq : trimVal a e (s + 1) = stageFun (patchTable e (s + 1)) (s + 1) := by
          funext w
          simp only [trimVal, stageFun, trimTable_of_allAcc h]
        rw [heq]
        exact lintegral_stageFun_le_of_accept ha hacc
      · have heq : ∀ w, trimVal a e (s + 1) w = trimVal a e s w := by
          intro w
          simp only [trimVal]
          rw [trimTable_succ, if_neg h, dyadicValue_two_mul_succ]
          congr 1
          rw [← cantorPrefix_take w s (s + 1) (Nat.le_succ s),
            trimTable_take a e (cantorPrefix w (s + 1)) s le_rfl]
        simp only [heq]
        exact ih

/-- The trimmed `e`-th component. -/
noncomputable def compVal (a : BitString → ℕ → ℕ) (e : ℕ) (w : CantorSeq) : ℝ≥0∞ :=
  ⨆ s, trimVal a e s w

/-- The value of the `e`-th trimmed test is measurable. -/
lemma measurable_compVal (a : BitString → ℕ → ℕ) (e : ℕ) : Measurable (compVal a e) :=
  Measurable.iSup fun s => measurable_trimVal a e s

/-- Each trimmed test has integral at most two against the measure it is built from. -/
lemma lintegral_compVal_le
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s) (e : ℕ) :
    ∫⁻ w, compVal a e w ∂μ ≤ 2 := by
  have hmono : Monotone (fun s => trimVal a e s) := by
    intro s t hst w
    exact trimVal_monotone a e w hst
  have hiSup := lintegral_iSup (μ := μ) (f := fun s => trimVal a e s)
    (fun s => measurable_trimVal a e s) hmono
  calc ∫⁻ w, compVal a e w ∂μ = ⨆ s, ∫⁻ w, trimVal a e s w ∂μ := hiSup
    _ ≤ 2 := iSup_le fun s => lintegral_trimVal_le ha e s

/-! ## Domination of an arbitrary test -/

/-- Every lower semicomputable function of integral at most one is dominated by one of the
trimmed tests, so the enumeration is complete. -/
lemma exists_index_compVal_ge
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {v : CantorSeq → ℝ≥0∞} (hv : IsLowerSemicomputableFun v) (hint : ∫⁻ w, v w ∂μ ≤ 1) :
    ∃ e, ∀ w, v w ≤ compVal a e w := by
  obtain ⟨A, hAcomp, hAmono, hAsup⟩ :=
    isMonotoneLimit_of_isSupremum (isSupremum_of_isLowerSemicomputableFun hv)
  have hAmono' : ∀ s (w : CantorSeq),
      2 * A s (cantorPrefix w s) ≤ A (s + 1) (cantorPrefix w (s + 1)) := by
    intro s w
    have h := hAmono s w
    have h' := (dyadicValue_le_dyadicValue_iff _ _ _ _).1 h
    have hpow : (2 : ℕ) ^ (s + 1) = 2 ^ s * 2 := by ring
    rw [hpow] at h'
    have h2 : 0 < (2 : ℕ) ^ s := Nat.two_pow_pos s
    nlinarith [h']
  obtain ⟨e, hzero, hconv⟩ := exists_code_rawTable hAcomp
  -- every stage of the patched table is dominated by `v`
  have hstage_le : ∀ s w, stageFun (patchTable e s) s w ≤ v w := by
    intro s w
    have hdom := patchTable_le_of_code hzero hAmono' s w
    calc stageFun (patchTable e s) s w
        ≤ dyadicValue (A s (cantorPrefix w s)) s :=
          lscDyadicValue_mono s hdom
      _ ≤ v w := by
          rw [hAsup w]
          exact le_iSup (fun s => dyadicValue (A s (cantorPrefix w s)) s) s
  have hacc : ∀ s, stageAccept (patchTable e s) a s = true := by
    intro s
    refine stageAccept_of_lintegral_le_one ha ?_
    calc ∫⁻ w, stageFun (patchTable e s) s w ∂μ ≤ ∫⁻ w, v w ∂μ :=
          lintegral_mono fun w => hstage_le s w
      _ ≤ 1 := hint
  have hall : ∀ s, allAcc a e s = true := by
    intro s
    induction s with
    | zero => exact hacc 0
    | succ s ih =>
        rw [allAcc_succ, Bool.and_eq_true]
        exact ⟨ih, hacc (s + 1)⟩
  refine ⟨e, fun w => ?_⟩
  rw [hAsup w]
  refine iSup_le fun s => ?_
  obtain ⟨b, hsb, hgrow⟩ := exists_bound_patchTable hconv s w
  have hval : dyadicValue (A s (cantorPrefix w s)) s
      ≤ dyadicValue (patchTable e b (cantorPrefix w b)) b := by
    have hsplit : b = s + (b - s) := by omega
    calc dyadicValue (A s (cantorPrefix w s)) s
        = dyadicValue (2 ^ (b - s) * A s (cantorPrefix w s)) (s + (b - s)) :=
          (dyadicValue_two_pow_mul_add _ _ _).symm
      _ ≤ dyadicValue (patchTable e b (cantorPrefix w b)) (s + (b - s)) := by
          rw [← hsplit] at *
          exact lscDyadicValue_mono b hgrow
      _ = dyadicValue (patchTable e b (cantorPrefix w b)) b := by rw [← hsplit]
  refine hval.trans ?_
  have : dyadicValue (patchTable e b (cantorPrefix w b)) b = trimVal a e b w := by
    simp only [trimVal, trimTable_of_allAcc (hall b)]
  rw [this]
  exact le_iSup (fun s => trimVal a e s w) b

/-! ## The mixture -/

/-- The mixture of all trimmed components with the weights `2 ^ -(e + 2)`. -/
noncomputable def mixVal (a : BitString → ℕ → ℕ) (w : CantorSeq) : ℝ≥0∞ :=
  ∑' e, dyadicValue 1 (e + 2) * compVal a e w

/-- The stage tables of the mixture. -/
def mixTable (a : BitString → ℕ → ℕ) (s : ℕ) (x : BitString) : ℕ :=
  ((List.range (s - 1)).map (fun e => trimTable a e x (s - e - 2))).sum

/-- A sum over an initial range is the sum of the corresponding list. -/
lemma sum_range_eq_list_sum (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ]; simp

/-- The stage value of the mixture table is the weighted sum of the trimmed tests with weights
`2^{-(e+2)}`. -/
lemma dyadicValue_mixTable (a : BitString → ℕ → ℕ) (s : ℕ) (w : CantorSeq) :
    dyadicValue (mixTable a s (cantorPrefix w s)) s
      = ∑ e ∈ Finset.range (s - 1), dyadicValue 1 (e + 2) * trimVal a e (s - e - 2) w := by
  rw [mixTable, ← sum_range_eq_list_sum, dyadicValue_finset_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hes : e + 2 ≤ s := by
    simp only [Finset.mem_range] at he
    omega
  have hj : s - e - 2 + (e + 2) = s := by omega
  have htake : trimTable a e (cantorPrefix w s) (s - e - 2)
      = trimTable a e (cantorPrefix w (s - e - 2)) (s - e - 2) := by
    rw [← cantorPrefix_take w (s - e - 2) s (by omega),
      trimTable_take a e (cantorPrefix w s) (s - e - 2) le_rfl]
  rw [htake]
  simp only [trimVal]
  rw [dyadicValue_mul_dyadicValue, one_mul, show e + 2 + (s - e - 2) = s by omega]

/-- The mixture is the supremum of the stage values of its table, hence lower semicomputable. -/
lemma mixVal_eq_iSup (a : BitString → ℕ → ℕ) (w : CantorSeq) :
    mixVal a w = ⨆ s, dyadicValue (mixTable a s (cantorPrefix w s)) s := by
  set F : ℕ → ℕ → ℝ≥0∞ := fun e j => dyadicValue 1 (e + 2) * trimVal a e j w with hF
  have hFmono : ∀ e, Monotone (F e) := by
    intro e j k hjk
    exact mul_le_mul_right (trimVal_monotone a e w hjk) _
  have hmix : mixVal a w = ∑' e, ⨆ j, F e j := by
    simp only [mixVal, compVal, hF]
    exact tsum_congr fun e => by rw [ENNReal.mul_iSup]
  rw [hmix]
  refine le_antisymm ?_ ?_
  · rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun n => ?_
    rw [ENNReal.finsetSum_iSup_of_monotone hFmono]
    refine iSup_le fun j => ?_
    refine le_trans ?_ (le_iSup (fun s => dyadicValue (mixTable a s (cantorPrefix w s)) s)
      (n + j + 2))
    rw [dyadicValue_mixTable]
    have hsub : Finset.range n ⊆ Finset.range (n + j + 2 - 1) :=
      Finset.range_subset.2 fun x _ => Finset.mem_range.2 (by omega)
    calc ∑ e ∈ Finset.range n, F e j
        ≤ ∑ e ∈ Finset.range n, F e (n + j + 2 - e - 2) := by
          refine Finset.sum_le_sum fun e he => ?_
          simp only [Finset.mem_range] at he
          refine hFmono e ?_
          omega
      _ ≤ ∑ e ∈ Finset.range (n + j + 2 - 1), F e (n + j + 2 - e - 2) :=
          Finset.sum_le_sum_of_subset hsub
  · refine iSup_le fun s => ?_
    rw [dyadicValue_mixTable]
    refine le_trans (Finset.sum_le_sum (fun e _ =>
      le_iSup (fun j => F e j) (s - e - 2))) ?_
    exact ENNReal.sum_le_tsum _

/-- The mixture is measurable. -/
lemma measurable_mixVal (a : BitString → ℕ → ℕ) : Measurable (mixVal a) := by
  unfold mixVal
  exact Measurable.tsum fun e => (measurable_compVal a e).const_mul _

/-- The mixture has integral at most one, so it is an expectation-bounded randomness test. -/
lemma lintegral_mixVal_le_one
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s) :
    ∫⁻ w, mixVal a w ∂μ ≤ 1 := by
  have hsum : ∫⁻ w, mixVal a w ∂μ = ∑' e, ∫⁻ w, dyadicValue 1 (e + 2) * compVal a e w ∂μ := by
    simp only [mixVal]
    exact lintegral_tsum fun e => ((measurable_compVal a e).const_mul _).aemeasurable
  rw [hsum]
  have hterm : ∀ e, ∫⁻ w, dyadicValue 1 (e + 2) * compVal a e w ∂μ
      ≤ dyadicValue 1 (e + 2) * 2 := by
    intro e
    rw [lintegral_const_mul _ (measurable_compVal a e)]
    exact mul_le_mul_right (lintegral_compVal_le ha e) _
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  have hgeom : ∑' e : ℕ, dyadicValue 1 (e + 2) = (2 : ℝ≥0∞)⁻¹ := by
    have h := tsum_inv_two_pow_shift 1
    have hcongr : ∀ e : ℕ, dyadicValue 1 (e + 2) = (2 : ℝ≥0∞)⁻¹ ^ (1 + e + 1) := by
      intro e
      rw [dyadicValue_eq_mul_inv_pow]
      simp only [Nat.cast_one, one_mul]
      congr 1
      omega
    calc ∑' e : ℕ, dyadicValue 1 (e + 2) = ∑' e : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (1 + e + 1) :=
          tsum_congr hcongr
      _ = (2 : ℝ≥0∞)⁻¹ ^ 1 := h
      _ = (2 : ℝ≥0∞)⁻¹ := pow_one _
  rw [ENNReal.tsum_mul_right, hgeom]
  rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-! ## Computability of the mixture

The composition lemmas below pass the intermediate function `g` explicitly.
Without it the elaborator has to solve a higher-order unification problem and
ends up unfolding `patchTable` / `stageAccept`, which is prohibitively slow. -/

/-- The running acceptance flag is computable. -/
lemma computable_accBelow (ha : Computable₂ a) :
    Computable (fun p : ℕ × ℕ => accBelow a p.1 p.2) := by
  have hpatch : Computable₂ (fun r : (ℕ × ℕ) × (ℕ × Bool) => patchTable r.1.1 r.2.1) :=
    computable_patchTable.comp
      (g := fun q : ((ℕ × ℕ) × (ℕ × Bool)) × BitString => (q.1.1.1, (q.1.2.1, q.2)))
      ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd))
  have hacc : Computable (fun r : (ℕ × ℕ) × (ℕ × Bool) =>
      stageAccept (patchTable r.1.1 r.2.1) a r.2.1) :=
    computable_stageAccept ha hpatch (Computable.fst.comp Computable.snd)
  have hstep : Computable₂ (fun (p : ℕ × ℕ) (q : ℕ × Bool) =>
      q.2 && stageAccept (patchTable p.1 q.1) a q.1) :=
    Computable₂.comp (f := fun b c : Bool => b && c) Primrec.and.to_comp
      (g := fun r : (ℕ × ℕ) × (ℕ × Bool) => r.2.2)
      (h := fun r : (ℕ × ℕ) × (ℕ × Bool) => stageAccept (patchTable r.1.1 r.2.1) a r.2.1)
      (Computable.snd.comp Computable.snd) hacc
  exact Computable.nat_rec Computable.snd (Computable.const true) hstep

/-- The cumulative acceptance flag is computable. -/
lemma computable_allAcc (ha : Computable₂ a) :
    Computable (fun p : ℕ × ℕ => allAcc a p.1 p.2) :=
  (computable_accBelow ha).comp (g := fun p : ℕ × ℕ => (p.1, p.2 + 1))
    (Computable.fst.pair (Computable.succ.comp Computable.snd))

/-- The one-step update of the trimmed table is computable. -/
lemma computable_trimStep (ha : Computable₂ a) :
    Computable (fun p : (ℕ × BitString) × ℕ => trimStep a p.1.1 p.1.2 p.2) := by
  have hallAcc := computable_allAcc ha
  have hc : Computable (fun r : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) => allAcc a r.1.1.1 r.2.1) :=
    hallAcc.comp (g := fun r : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) => (r.1.1.1, r.2.1))
      ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.fst.comp Computable.snd))
  have hp : Computable (fun r : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) =>
      patchTable r.1.1.1 r.2.1 r.1.1.2) :=
    computable_patchTable.comp
      (g := fun r : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) => (r.1.1.1, (r.2.1, r.1.1.2)))
      ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.fst.comp Computable.snd).pair
          (Computable.snd.comp (Computable.fst.comp Computable.fst))))
  have hd : Computable (fun r : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) => 2 * r.2.2) :=
    Computable₂.comp (f := fun m n : ℕ => m * n) (Primrec.nat_mul.to_comp)
      (g := fun _ : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) => 2)
      (h := fun r : ((ℕ × BitString) × ℕ) × (ℕ × ℕ) => r.2.2)
      (Computable.const 2) (Computable.snd.comp Computable.snd)
  have hstep : Computable₂ (fun (p : (ℕ × BitString) × ℕ) (q : ℕ × ℕ) =>
      if allAcc a p.1.1 q.1 = true then patchTable p.1.1 q.1 p.1.2 else 2 * q.2) :=
    (Computable.cond hc hp hd).of_eq fun r => by
      by_cases h : allAcc a r.1.1.1 r.2.1 = true <;> simp [h]
  exact Computable.nat_rec Computable.snd (Computable.const 0) hstep

/-- The trimmed table is computable. -/
lemma computable_trimTable (ha : Computable₂ a) :
    Computable (fun p : (ℕ × BitString) × ℕ => trimTable a p.1.1 p.1.2 p.2) :=
  (computable_trimStep ha).comp (g := fun p : (ℕ × BitString) × ℕ => (p.1, p.2 + 1))
    (Computable.fst.pair (Computable.succ.comp Computable.snd))

-- From here on `trimTable` is treated as opaque: unfolding it during unification
-- restarts the whole `allAcc` / `stageAccept` computation and does not terminate
-- within any reasonable elaboration budget.
attribute [local irreducible] trimTable

/-- The mixture table is computable. -/
lemma computable_mixTable (ha : Computable₂ a) :
    Computable (fun p : ℕ × BitString => mixTable a p.1 p.2) := by
  have htrim := computable_trimTable ha
  have hL : Computable (fun p : ℕ × BitString => List.range (p.1 - 1)) :=
    (Primrec.list_range.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))).to_comp
  have hf : Computable₂ (fun (p : ℕ × BitString) (e : ℕ) =>
      trimTable a e p.2 (p.1 - e - 2)) := by
    have harg : Computable (fun r : (ℕ × BitString) × ℕ => ((r.2, r.1.2), r.1.1 - r.2 - 2)) :=
      (Computable.snd.pair (Computable.snd.comp Computable.fst)).pair
        (Computable₂.comp (f := fun m n : ℕ => m - n) (Primrec.nat_sub.to_comp)
          (g := fun r : (ℕ × BitString) × ℕ => r.1.1 - r.2)
          (h := fun _ : (ℕ × BitString) × ℕ => 2)
          (Computable₂.comp (f := fun m n : ℕ => m - n) (Primrec.nat_sub.to_comp)
            (g := fun r : (ℕ × BitString) × ℕ => r.1.1)
            (h := fun r : (ℕ × BitString) × ℕ => r.2)
            (Computable.fst.comp Computable.fst) Computable.snd)
          (Computable.const 2))
    exact htrim.comp harg
  exact computable_list_sum_map hL hf

/-! ## The maximal test -/

/-- SUV Theorem 42: for a computable measure there is a maximal lower
semicomputable function of integral at most `1`. -/
theorem exists_maximal_lsc_integral_le_one (hμ : IsComputableMeasure μ) :
    ∃ u : CantorSeq → ℝ≥0∞, IsLowerSemicomputableFun u ∧ (∫⁻ w, u w ∂μ) ≤ 1 ∧
      ∀ v : CantorSeq → ℝ≥0∞, IsLowerSemicomputableFun v → (∫⁻ w, v w ∂μ) ≤ 1 →
        ∃ c : NNReal, ∀ w, v w ≤ c * u w := by
  obtain ⟨a, hacomp, ha⟩ := hμ
  refine ⟨mixVal a, ?_, lintegral_mixVal_le_one ha, ?_⟩
  · refine isLowerSemicomputableFun_of_isSupremum ⟨mixTable a, computable_mixTable hacomp, ?_⟩
    intro w
    exact mixVal_eq_iSup a w
  · intro v hv hint
    obtain ⟨e, he⟩ := exists_index_compVal_ge ha hv hint
    refine ⟨(2 : NNReal) ^ (e + 2), fun w => ?_⟩
    have hle : dyadicValue 1 (e + 2) * compVal a e w ≤ mixVal a w :=
      ENNReal.le_tsum e
    have hcast : ((((2 : NNReal) ^ (e + 2) : NNReal)) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (e + 2) := by
      push_cast
      rfl
    rw [hcast]
    calc v w ≤ compVal a e w := he w
      _ = (2 : ℝ≥0∞) ^ (e + 2) * (dyadicValue 1 (e + 2) * compVal a e w) := by
          rw [← mul_assoc]
          rw [dyadicValue_eq_mul_inv_pow]
          simp only [Nat.cast_one, one_mul]
          rw [← ENNReal.inv_pow, ENNReal.mul_inv_cancel (by positivity) (by simp), one_mul]
      _ ≤ (2 : ℝ≥0∞) ^ (e + 2) * mixVal a w := by gcongr

end Kolmogorov
