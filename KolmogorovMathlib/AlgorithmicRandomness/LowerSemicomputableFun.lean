import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveReal

/-!
# Lower-semicomputable functions on Cantor space

`IsLowerSemicomputableFun f` says `f : CantorSeq → ℝ≥0∞` is the pointwise supremum of a
computable family of basic (finite-prefix-determined) functions.  The three equivalent
presentations of SUV Theorem 40 are also stated here, as
`IsSupremumOfComputableBasicFunctions`, `IsMonotoneLimitOfComputableBasicFunctions` and
`IsSumOfComputableNonnegativeBasicFunctions`; that they agree is proved in
`LSCCharacterizations`.

The lemmas are the closure and regularity properties used by the randomness tests:
`isLowerSemicomputableFun_ofRat` and `IsLowerSemicomputableFun.rat_smul` (constants and
positive rational scaling), `IsLowerSemicomputableFun.isUniformlyEffectiveOpen_superlevel`
(the strict superlevel sets along a computable sequence of thresholds form a uniformly
effectively open family) and `IsLowerSemicomputableFun.measurable`.
-/

namespace Kolmogorov

open MeasureTheory Topology
open scoped ENNReal NNReal

-- The source definition preceding Theorem 40.  Uniformity is in the rational
-- threshold: one program enumerates all strict superlevel sets.
/-- A function `f : CantorSeq → ℝ≥0∞` is lower semicomputable when it is the pointwise
supremum of a computable increasing family of dyadic step functions of the prefixes. -/
def IsLowerSemicomputableFun (f : CantorSeq → ℝ≥0∞) : Prop :=
  ∃ enum : ℚ → ℕ → Option BitString,
    Computable (fun p : ℚ × ℕ => enum p.1 p.2) ∧
    ∀ q : ℚ, {w | (q : ℝ) < 0 ∨ ENNReal.ofReal (q : ℝ) < f w} =
      ⋃ i, (enum q i).elim ∅ cantorCylinder

/-- Theorem 40(b), using dyadic basic functions at stage `s`. -/
def IsSupremumOfComputableBasicFunctions (f : CantorSeq → ℝ≥0∞) : Prop :=
  ∃ approx : ℕ → BitString → ℕ,
    (Computable fun p : ℕ × BitString => approx p.1 p.2) ∧
    ∀ w, f w = ⨆ s, dyadicValue (approx s (cantorPrefix w s)) s

/-- Theorem 40(c), in a dyadic prefix-table presentation. -/
def IsMonotoneLimitOfComputableBasicFunctions (f : CantorSeq → ℝ≥0∞) : Prop :=
  ∃ approx : ℕ → BitString → ℕ,
    (Computable fun p : ℕ × BitString => approx p.1 p.2) ∧
    (∀ s w, dyadicValue (approx s (cantorPrefix w s)) s
      ≤ dyadicValue (approx (s + 1) (cantorPrefix w (s + 1))) (s + 1)) ∧
    (∀ w, f w = ⨆ s, dyadicValue (approx s (cantorPrefix w s)) s)

/-- Theorem 40(d), in a dyadic prefix-table presentation. -/
def IsSumOfComputableNonnegativeBasicFunctions (f : CantorSeq → ℝ≥0∞) : Prop :=
  ∃ term : ℕ → BitString → ℕ,
    (Computable fun p : ℕ × BitString => term p.1 p.2) ∧
    ∀ w, f w = ∑' s, dyadicValue (term s (cantorPrefix w s)) s

/-- Strict comparison of rationals is computable. -/
lemma computable₂_ratLt : Computable₂ (fun a b : ℚ => decide (a < b)) := by
  have hsub : Computable (fun p : ℚ × ℚ => p.2 - p.1) :=
    Computable₂.comp computable₂_ratSub Computable.snd Computable.fst
  have hnum : Computable (fun p : ℚ × ℚ => ((p.2 - p.1).num).toNat) :=
    (ComputableReals.primrec_intToNat.to_comp).comp (computable_ratNum.comp hsub)
  have hltc : Computable (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
    obtain ⟨_, hlt⟩ := Primrec.nat_lt
    convert Primrec.to_comp hlt
  have hmain : Computable (fun p : ℚ × ℚ => decide (0 < ((p.2 - p.1).num).toNat)) :=
    hltc.comp ((Computable.const 0).pair hnum)
  refine hmain.of_eq (fun p => ?_)
  have h1 : (0 < ((p.2 - p.1).num).toNat) ↔ 0 < (p.2 - p.1).num := by omega
  exact decide_eq_decide.mpr (h1.trans (Rat.num_pos.trans sub_pos))

/-- Comparison of a rational against a fixed rational constant is computable. -/
lemma computable_ratLtConst (s : ℚ) : Computable (fun q : ℚ => decide (q < s)) :=
  Computable₂.comp computable₂_ratLt Computable.id (Computable.const s)

/-- A constant rational function on Cantor space is lower semicomputable. -/
lemma isLowerSemicomputableFun_ofRat (r : ℚ) :
    IsLowerSemicomputableFun (fun _ : CantorSeq => ENNReal.ofReal (r : ℝ)) := by
  classical
  have hcyl : cantorCylinder ([] : BitString) = Set.univ := by
    ext w; simp [cantorCylinder, IsCantorPrefix]
  refine ⟨fun q _ => if q < max 0 r then some [] else none, ?_, ?_⟩
  · have hb : Computable (fun p : ℚ × ℕ => decide (p.1 < max 0 r)) :=
      (computable_ratLtConst (max 0 r)).comp Computable.fst
    have hc := Computable.cond hb (Computable.const (some ([] : BitString)))
      (Computable.const (none : Option BitString))
    refine hc.of_eq (fun p => ?_)
    by_cases h : p.1 < max 0 r <;> simp [h]
  · intro q
    have hiff : ((q : ℝ) < 0 ∨ ENNReal.ofReal (q : ℝ) < ENNReal.ofReal (r : ℝ)) ↔
        q < max 0 r := by
      constructor
      · rintro (h | h)
        · have hq : q < 0 := by exact_mod_cast h
          exact lt_max_iff.2 (Or.inl hq)
        · have hqr : (q : ℝ) < (r : ℝ) := by
            by_contra hc
            exact absurd h (not_lt.2 (ENNReal.ofReal_le_ofReal (not_lt.1 hc)))
          exact lt_max_iff.2 (Or.inr (by exact_mod_cast hqr))
      · intro h
        rcases lt_max_iff.1 h with h | h
        · exact Or.inl (by exact_mod_cast h)
        · rcases lt_or_ge q 0 with hq | hq
          · exact Or.inl (by exact_mod_cast hq)
          · have hq0 : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
            have hr0 : (0 : ℝ) < (r : ℝ) := lt_of_le_of_lt hq0 (by exact_mod_cast h)
            exact Or.inr ((ENNReal.ofReal_lt_ofReal_iff hr0).2 (by exact_mod_cast h))
    by_cases h : q < max 0 r
    · have h1 : {w : CantorSeq | (q : ℝ) < 0 ∨
          ENNReal.ofReal (q : ℝ) < ENNReal.ofReal (r : ℝ)} = Set.univ := by
        ext w; simpa using hiff.2 h
      rw [h1]
      ext w
      simp [h, hcyl]
    · have h1 : {w : CantorSeq | (q : ℝ) < 0 ∨
          ENNReal.ofReal (q : ℝ) < ENNReal.ofReal (r : ℝ)} = (∅ : Set CantorSeq) := by
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hc => h (hiff.1 hc)
      rw [h1]
      ext w
      simp [h]

/-- Division by a fixed positive rational constant is computable. -/
lemma computable_ratDivConst {c : ℚ} (hc : 0 < c) : Computable (fun q : ℚ => q / c) := by
  have hnumpos : 0 < c.num := Rat.num_pos.2 hc
  refine computable_of_num_den (f := fun q : ℚ => q / c)
    (N := fun q : ℚ => q.num * (c.den : ℤ)) (D := fun q : ℚ => q.den * c.num.toNat)
    (Computable₂.comp primrec_intMul.to_comp computable_ratNum (Computable.const _))
    (Computable₂.comp Primrec.nat_mul.to_comp computable_ratDen (Computable.const _))
    (fun q => Nat.mul_pos q.pos (by omega)) (fun q => ?_)
  have hd1 : ((q.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hd2 : ((c.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr c.den_nz
  have hcn : ((c.num.toNat : ℕ) : ℚ) = (c.num : ℚ) := by
    have h : (c.num.toNat : ℤ) = c.num := Int.toNat_of_nonneg hnumpos.le
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h
  have hq : (q.num : ℚ) = q * (q.den : ℚ) := (Rat.mul_den_eq_num q).symm
  have hcnum : (c.num : ℚ) = c * (c.den : ℚ) := (Rat.mul_den_eq_num c).symm
  have hcne : (c : ℚ) ≠ 0 := hc.ne'
  push_cast
  rw [hcn, hq, hcnum]
  field_simp

/-- Lower semicomputability is preserved by multiplication with a positive rational constant. -/
lemma IsLowerSemicomputableFun.rat_smul {f : CantorSeq → ℝ≥0∞}
    (hf : IsLowerSemicomputableFun f) {c : ℚ} (hc : 0 < c) :
    IsLowerSemicomputableFun (fun w => ENNReal.ofReal (c : ℝ) * f w) := by
  obtain ⟨enum, hcomp, hspec⟩ := hf
  have hc' : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  refine ⟨fun q i => enum (q / c) i, ?_, ?_⟩
  · exact hcomp.comp (((computable_ratDivConst hc).comp Computable.fst).pair Computable.snd)
  · intro q
    rw [← hspec (q / c)]
    ext w
    simp only [Set.mem_ofPred_eq]
    have hcast : (((q / c : ℚ) : ℝ)) = (q : ℝ) / (c : ℝ) := by push_cast; ring
    by_cases hq : (q : ℝ) < 0
    · have hneg : ((q / c : ℚ) : ℝ) < 0 := by
        rw [hcast]; exact div_neg_of_neg_of_pos hq hc'
      exact ⟨fun _ => Or.inl hneg, fun _ => Or.inl hq⟩
    · have hq0 : (0 : ℝ) ≤ (q : ℝ) := not_lt.1 hq
      have hnn : ¬ (((q / c : ℚ) : ℝ) < 0) := by
        rw [hcast]; exact not_lt.2 (div_nonneg hq0 hc'.le)
      have key : ENNReal.ofReal (c : ℝ) * ENNReal.ofReal ((q / c : ℚ) : ℝ)
          = ENNReal.ofReal (q : ℝ) := by
        rw [← ENNReal.ofReal_mul hc'.le]
        congr 1
        rw [hcast]
        field_simp
      have hne0 : ENNReal.ofReal (c : ℝ) ≠ 0 := (ENNReal.ofReal_pos.2 hc').ne'
      have hnet : ENNReal.ofReal (c : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
      constructor
      · rintro (h | h)
        · exact absurd h hq
        · refine Or.inr ?_
          rw [← key] at h
          exact (ENNReal.mul_lt_mul_iff_right hne0 hnet).1 h
      · rintro (h | h)
        · exact absurd h hnn
        · refine Or.inr ?_
          rw [← key]
          exact (ENNReal.mul_lt_mul_iff_right hne0 hnet).2 h

/-- The strict superlevel sets of a lower semicomputable function, taken along a computable
sequence of nonnegative rational thresholds, form a uniformly effectively open family. -/
lemma IsLowerSemicomputableFun.isUniformlyEffectiveOpen_superlevel
    {f : CantorSeq → ℝ≥0∞} (hf : IsLowerSemicomputableFun f)
    (q : ℕ → ℚ) (hq : Computable q) (hq0 : ∀ n, 0 ≤ q n) :
    IsUniformlyEffectiveOpen (fun n => {w | ENNReal.ofReal ((q n : ℝ)) < f w}) := by
  obtain ⟨enum, hcomp, hspec⟩ := hf
  have h_eq : ∀ n, {w | ENNReal.ofReal ((q n : ℝ)) < f w} =
      ⋃ i, (enum (q n) i).elim ∅ cantorCylinder := by
    intro n
    have h_spec_n := hspec (q n)
    have h_nonneg : ¬ ((q n : ℝ) < 0) := not_lt.2 (by exact_mod_cast hq0 n)
    ext w
    simp only [Set.mem_ofPred_eq]
    rw [show (ENNReal.ofReal ((q n : ℝ)) < f w) ↔
      ((q n : ℝ) < 0 ∨ ENNReal.ofReal (q n : ℝ) < f w) from
      ⟨fun h => Or.inr h, fun h => h.resolve_left h_nonneg⟩]
    exact Set.ext_iff.1 h_spec_n w
  refine ⟨fun n i => enum (q n) i, ?_, fun n => h_eq n⟩
  exact hcomp.comp ((hq.comp Computable.fst).pair Computable.snd)

/-- A lower semicomputable function on Cantor space is Borel measurable. -/
lemma IsLowerSemicomputableFun.measurable {f : CantorSeq → ℝ≥0∞}
    (hf : IsLowerSemicomputableFun f) : Measurable f := by
  obtain ⟨enum, hcomp, hspec⟩ := hf
  have hmeas : ∀ q : ℚ, MeasurableSet
      {w : CantorSeq | (q : ℝ) < 0 ∨ ENNReal.ofReal (q : ℝ) < f w} := by
    intro q
    rw [hspec q]
    refine MeasurableSet.iUnion fun i => ?_
    cases enum q i with
    | none => exact MeasurableSet.empty
    | some x => exact measurableSet_cantorCylinder x
  refine measurable_of_Ioi fun y => ?_
  have hdecomp : f ⁻¹' Set.Ioi y =
      ⋃ q : ℚ, ⋃ _ : y < ENNReal.ofReal (q : ℝ),
        {w : CantorSeq | (q : ℝ) < 0 ∨ ENNReal.ofReal (q : ℝ) < f w} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro h
      obtain ⟨q, _, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
      exact ⟨q, h1, Or.inr h2⟩
    · rintro ⟨q, h1, h2 | h2⟩
      · rw [ENNReal.ofReal_of_nonpos h2.le] at h1
        exact absurd h1 (not_lt.2 bot_le)
      · exact lt_trans h1 h2
  rw [hdecomp]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => hmeas q

end Kolmogorov
