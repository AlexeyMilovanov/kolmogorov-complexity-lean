/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.SubSemimeasureDomination
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorrTest

/-!
# The converse half of the Levin-Schnorr criterion for a priori complexity

`LevinSchnorrTest.lean` proves that a Martin-Löf random sequence satisfies
`KA (w ↾ n) ≥ n - c` for a single constant `c`.  This file proves the converse: a sequence
whose prefixes obey such a bound is Martin-Löf random for the uniform measure.

The argument is the classical one.  If `w` is not random, it lies in every level `U m` of
some Martin-Löf test.  The relative masses `x ↦ μ (U m ∩ Ω x)` are uniformly lower
semicomputable and additive along the two children of `x`, so the weighted sum

`d x = ∑' m, 2 ^ m · μ (U (2 * m + 2) ∩ Ω x)`

is a lower semicomputable sub-semimeasure (its root value is at most `∑ 2 ^ (-m-2) ≤ 1`).
The universal continuous semimeasure therefore dominates `d`
(`exists_const_mul_universalContinuousSemimeasure_ge`), while `d (w ↾ n) ≥ 2 ^ m · 2 ^ (-n)`
for all large `n`, since `w ∈ U (2 * m + 2)`.  Hence `KA (w ↾ n) ≤ n - m + O(1)` with `m`
arbitrary, contradicting the assumed lower bound.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ### Coding a test level together with a string -/

/-- Encode a test level `m` and a string `x` as a single string index. -/
def coverIndex (m : ℕ) (x : BitString) : BitString :=
  Nat.bits (Nat.pair m (Encodable.encode x))

/-- The test level encoded by an index string. -/
def coverLevel (y : BitString) : ℕ := (Nat.unpair (decodeBits y)).1

/-- The string encoded by an index string. -/
def coverString (y : BitString) : BitString :=
  (Encodable.decode (α := BitString) (Nat.unpair (decodeBits y)).2).getD []

/-- The level read back from a cover index. -/
@[simp] lemma coverLevel_coverIndex (m : ℕ) (x : BitString) :
    coverLevel (coverIndex m x) = m := by
  simp [coverLevel, coverIndex, decodeBits_natBits]

/-- The string read back from a cover index. -/
@[simp] lemma coverString_coverIndex (m : ℕ) (x : BitString) :
    coverString (coverIndex m x) = x := by
  simp [coverString, coverIndex, decodeBits_natBits]

/-! ### The relative open sets of a uniformly effective sequence -/

/-- `coverRel g p y` holds when `p` extends both the string coded by `y` and some basic
cylinder enumerated by `g` at the level coded by `y`.  The union of the cylinders `Ω p`
over all such `p` is exactly the intersection of the `y`-level open set with the cylinder
of the `y`-string. -/
def coverRel (g : ℕ → ℕ → Option BitString) (p y : BitString) : Prop :=
  ∃ i z, g (coverLevel y) i = some z ∧ z <+: p ∧ coverString y <+: p

/-- The level of a cover index is computable. -/
lemma computable_coverLevel : Computable coverLevel :=
  (Primrec.fst.comp (Primrec.unpair.comp primrec_decodeBits)).to_comp

/-- The string of a cover index is computable. -/
lemma computable_coverString : Computable coverString :=
  Computable.option_getD
    (Computable.decode.comp
      (Primrec.snd.comp (Primrec.unpair.comp primrec_decodeBits)).to_comp)
    (Computable.const [])

/-- Boolean test witnessing `coverRel` once the enumeration index is supplied. -/
def coverCheck (g : ℕ → ℕ → Option BitString) (w : (BitString × BitString) × ℕ) : Bool :=
  (((g (coverLevel w.1.2) w.2).map fun z => decide (z = w.1.1.take z.length)).getD false)
    && decide (coverString w.1.2 = w.1.1.take (coverString w.1.2).length)

/-- The cover check fires exactly when the enumeration produces a prefix of the candidate that
also extends the cover index's string. -/
lemma coverCheck_eq_true_iff (g : ℕ → ℕ → Option BitString)
    (w : (BitString × BitString) × ℕ) :
    coverCheck g w = true ↔
      ∃ z, g (coverLevel w.1.2) w.2 = some z ∧ z <+: w.1.1 ∧ coverString w.1.2 <+: w.1.1 := by
  rcases hz : g (coverLevel w.1.2) w.2 with _ | z <;>
    simp [coverCheck, hz, ← List.prefix_iff_eq_take]

/-- The cover check of a computable enumeration is computable. -/
lemma computable_coverCheck {g : ℕ → ℕ → Option BitString} (hg : Computable₂ g) :
    Computable (coverCheck g) := by
  have heq : Computable₂ fun a b : BitString => decide (a = b) :=
    (PrimrecPred.decide (Primrec.eq (α := BitString))).to_comp.to₂
  have htake : Computable₂ fun (l : BitString) (n : ℕ) => l.take n :=
    (Primrec.list_take.comp Primrec.snd Primrec.fst).to_comp
  have hlen : Computable fun l : BitString => l.length :=
    (Primrec.list_length (α := Bool)).to_comp
  have hlevel : Computable fun w : (BitString × BitString) × ℕ => coverLevel w.1.2 :=
    computable_coverLevel.comp (Computable.snd.comp Computable.fst)
  have hstr : Computable fun w : (BitString × BitString) × ℕ => coverString w.1.2 :=
    computable_coverString.comp (Computable.snd.comp Computable.fst)
  have hgw : Computable fun w : (BitString × BitString) × ℕ => g (coverLevel w.1.2) w.2 :=
    hg.comp hlevel Computable.snd
  have hinner : Computable₂ fun (w : (BitString × BitString) × ℕ) (z : BitString) =>
      decide (z = w.1.1.take z.length) :=
    heq.comp Computable.snd
      (htake.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
        (hlen.comp Computable.snd))
  have hmap : Computable fun w : (BitString × BitString) × ℕ =>
      ((g (coverLevel w.1.2) w.2).map fun z => decide (z = w.1.1.take z.length)).getD false :=
    Computable.option_getD (Computable.option_map hgw hinner) (Computable.const false)
  have houter : Computable fun w : (BitString × BitString) × ℕ =>
      decide (coverString w.1.2 = w.1.1.take (coverString w.1.2).length) :=
    heq.comp hstr (htake.comp (Computable.fst.comp Computable.fst) (hlen.comp hstr))
  refine (Computable.cond hmap houter (Computable.const false)).of_eq fun w => ?_
  cases h : (((g (coverLevel w.1.2) w.2).map fun z =>
      decide (z = w.1.1.take z.length)).getD false) <;> simp [coverCheck, h]

/-- The cover relation of a computable enumeration is recursively enumerable. -/
lemma isRE_coverRel {g : ℕ → ℕ → Option BitString} (hg : Computable₂ g) :
    IsRE fun q : BitString × BitString => coverRel g q.1 q.2 := by
  have hcheck : IsRE fun w : (BitString × BitString) × ℕ => coverCheck g w = true :=
    isRE_of_computable_bool _ (coverCheck g) (fun _ => Iff.rfl) (computable_coverCheck hg)
  have hex : IsRE fun q : BitString × BitString => ∃ i : ℕ, coverCheck g (q, i) = true :=
    IsRE.exists_encodable
      (R := fun (q : BitString × BitString) (i : ℕ) => coverCheck g (q, i) = true) hcheck
  refine hex.of_iff fun q => ?_
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨z, hz1, hz2, hz3⟩ := (coverCheck_eq_true_iff g (q, i)).mp hi
    exact ⟨i, z, hz1, hz2, hz3⟩
  · rintro ⟨i, z, hz1, hz2, hz3⟩
    exact ⟨i, (coverCheck_eq_true_iff g (q, i)).mpr ⟨z, hz1, hz2, hz3⟩⟩

/-- The open set generated at a cover index is the level-`m` test set intersected with the
cylinder of `x`. -/
lemma cantorOpen_coverRel_coverIndex {g : ℕ → ℕ → Option BitString} {U : ℕ → Set CantorSeq}
    (hU : ∀ n, U n = ⋃ i, (g n i).elim ∅ cantorCylinder) (m : ℕ) (x : BitString) :
    cantorOpen (coverRel g) (coverIndex m x) = U m ∩ cantorCylinder x := by
  ext w
  simp only [cantorOpen, coverRel, Set.mem_iUnion, Set.mem_inter_iff, hU m,
    coverLevel_coverIndex, coverString_coverIndex, exists_prop]
  constructor
  · rintro ⟨p, ⟨i, z, hgi, hzp, hxp⟩, hwp⟩
    refine ⟨⟨i, ?_⟩, cantorCylinder_subset_of_prefix hxp hwp⟩
    rw [hgi]
    exact cantorCylinder_subset_of_prefix hzp hwp
  · rintro ⟨⟨i, hi⟩, hwx⟩
    rcases hgi : g m i with _ | z
    · rw [hgi] at hi
      simp at hi
    · rw [hgi] at hi
      have hz : cantorPrefix w z.length = z :=
        (isCantorPrefix_iff_cantorPrefix_eq z w).1 hi
      have hx : cantorPrefix w x.length = x :=
        (isCantorPrefix_iff_cantorPrefix_eq x w).1 hwx
      refine ⟨cantorPrefix w (max z.length x.length), ⟨i, z, hgi, ?_, ?_⟩, ?_⟩
      · have hmono := cantorPrefix_mono w (le_max_left z.length x.length)
        rwa [hz] at hmono
      · have hmono := cantorPrefix_mono w (le_max_right z.length x.length)
        rwa [hx] at hmono
      · exact (isCantorPrefix_iff_cantorPrefix_eq _ w).2 (by rw [cantorPrefix_length])

/-- A cylinder is the disjoint union of the two cylinders of its children. -/
lemma cantorCylinder_eq_union_children (x : BitString) :
    cantorCylinder x = cantorCylinder (x ++ [false]) ∪ cantorCylinder (x ++ [true]) := by
  ext w
  constructor
  · intro hw
    have hx : cantorPrefix w x.length = x := (isCantorPrefix_iff_cantorPrefix_eq x w).1 hw
    have hsucc : cantorPrefix w (x.length + 1) = x ++ [w x.length] := by
      rw [cantorPrefix_succ, hx]
    cases hb : w x.length with
    | false =>
      refine Or.inl ((isCantorPrefix_iff_cantorPrefix_eq _ w).2 ?_)
      simp only [List.length_append, List.length_singleton]
      rw [hsucc, hb]
    | true =>
      refine Or.inr ((isCantorPrefix_iff_cantorPrefix_eq _ w).2 ?_)
      simp only [List.length_append, List.length_singleton]
      rw [hsucc, hb]
  · rintro (hw | hw)
    · exact cantorCylinder_subset_of_prefix ⟨[false], rfl⟩ hw
    · exact cantorCylinder_subset_of_prefix ⟨[true], rfl⟩ hw

/-- The cylinders of the two children of a string are disjoint. -/
lemma cantorCylinder_children_disjoint (x : BitString) :
    Disjoint (cantorCylinder (x ++ [false])) (cantorCylinder (x ++ [true])) := by
  refine cantorCylinder_disjoint_of_incompatible ?_ ?_
  · intro h
    have := h.eq_of_length (by simp)
    simp at this
  · intro h
    have := h.eq_of_length (by simp)
    simp at this

/-- A set enumerated by cylinders is measurable. -/
lemma measurableSet_of_enumeration {g : ℕ → ℕ → Option BitString} {U : ℕ → Set CantorSeq}
    (hU : ∀ n, U n = ⋃ i, (g n i).elim ∅ cantorCylinder) (m : ℕ) :
    MeasurableSet (U m) := by
  rw [hU m]
  refine MeasurableSet.iUnion (fun i => ?_)
  rcases g m i with _ | z
  · exact MeasurableSet.empty
  · exact measurableSet_cantorCylinder z

/-- The uniform mass of the `m`-th level of the effective open sequence enumerated by `g`,
restricted to the cylinder of `x`. -/
noncomputable def coverMass (g : ℕ → ℕ → Option BitString) (m : ℕ) (x : BitString) : ℝ≥0∞ :=
  cantorOpenMass (coverRel g) (coverIndex m x)

/-- The cover mass at `x` is the measure of the test set inside the cylinder of `x`. -/
lemma coverMass_eq {g : ℕ → ℕ → Option BitString} {U : ℕ → Set CantorSeq}
    (hU : ∀ n, U n = ⋃ i, (g n i).elim ∅ cantorCylinder) (m : ℕ) (x : BitString) :
    coverMass g m x = uniformMeasure (U m ∩ cantorCylinder x) := by
  rw [coverMass, cantorOpenMass, cantorOpen_coverRel_coverIndex hU]

/-- The cover mass splits exactly over the two children. -/
lemma coverMass_children {g : ℕ → ℕ → Option BitString} {U : ℕ → Set CantorSeq}
    (hU : ∀ n, U n = ⋃ i, (g n i).elim ∅ cantorCylinder) (m : ℕ) (x : BitString) :
    coverMass g m (x ++ [false]) + coverMass g m (x ++ [true]) = coverMass g m x := by
  rw [coverMass_eq hU, coverMass_eq hU, coverMass_eq hU]
  have hsplit : U m ∩ cantorCylinder x
      = (U m ∩ cantorCylinder (x ++ [false])) ∪ (U m ∩ cantorCylinder (x ++ [true])) := by
    rw [cantorCylinder_eq_union_children x, Set.inter_union_distrib_left]
  rw [hsplit, measure_union ((cantorCylinder_children_disjoint x).mono
    Set.inter_subset_right Set.inter_subset_right)
    ((measurableSet_of_enumeration hU m).inter (measurableSet_cantorCylinder _))]

/-- At the root the cover mass is the measure of the whole test set. -/
lemma coverMass_nil {g : ℕ → ℕ → Option BitString} {U : ℕ → Set CantorSeq}
    (hU : ∀ n, U n = ⋃ i, (g n i).elim ∅ cantorCylinder) (m : ℕ) :
    coverMass g m [] = uniformMeasure (U m) := by
  rw [coverMass_eq hU]
  congr 1
  have huniv : cantorCylinder ([] : BitString) = Set.univ := by
    ext w
    simp [cantorCylinder, IsCantorPrefix]
  rw [huniv, Set.inter_univ]

/-- A cylinder inside the test set contributes its full measure to the cover mass. -/
lemma le_coverMass_of_subset {g : ℕ → ℕ → Option BitString} {U : ℕ → Set CantorSeq}
    (hU : ∀ n, U n = ⋃ i, (g n i).elim ∅ cantorCylinder) (m : ℕ) (x : BitString)
    (hx : cantorCylinder x ⊆ U m) :
    (2 : ℝ≥0∞)⁻¹ ^ x.length ≤ coverMass g m x := by
  rw [coverMass_eq hU, Set.inter_eq_right.2 hx, uniformMeasure_cantorCylinder]

/-! ### The deficiency sub-semimeasure of a Martin-Löf test -/

/-- The weighted deficiency mass of the test enumerated by `g`: the level `2 * m + 2` is
given weight `2 ^ m`, so that the total root mass stays below one while a sequence lying in
level `2 * m + 2` receives mass at least `2 ^ m` times the uniform mass of its prefixes. -/
noncomputable def testDeficiencyMass (g : ℕ → ℕ → Option BitString) (x : BitString) : ℝ≥0∞ :=
  ∑' m, ((2 ^ m : ℕ) : ℝ≥0∞) * coverMass g (2 * m + 2) x

/-- The deficiency mass of the test is supermultiplicative over the two children. -/
lemma testDeficiencyMass_children {g : ℕ → ℕ → Option BitString} {U : ℕ → Set CantorSeq}
    (hU : ∀ n, U n = ⋃ i, (g n i).elim ∅ cantorCylinder) (x : BitString) :
    testDeficiencyMass g (x ++ [false]) + testDeficiencyMass g (x ++ [true])
      ≤ testDeficiencyMass g x := by
  unfold testDeficiencyMass
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum (fun m => ?_)
  rw [← mul_add, coverMass_children hU]

/-- For a test whose levels have measure at most `2 ^ -n`, the deficiency mass at the root is at
most one. -/
lemma testDeficiencyMass_nil_le_one {g : ℕ → ℕ → Option BitString} {U : ℕ → Set CantorSeq}
    (hU : ∀ n, U n = ⋃ i, (g n i).elim ∅ cantorCylinder)
    (hsmall : ∀ n, uniformMeasure (U n) ≤ dyadicValue 1 n) :
    testDeficiencyMass g [] ≤ 1 := by
  have hcanm : ∀ m : ℕ, (2 : ℝ≥0∞) ^ m * ((2 : ℝ≥0∞)⁻¹) ^ m = 1 := by
    intro m
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  have hterm : ∀ m : ℕ, ((2 ^ m : ℕ) : ℝ≥0∞) * coverMass g (2 * m + 2) []
      ≤ ((2 : ℝ≥0∞)⁻¹) ^ 2 * ((2 : ℝ≥0∞)⁻¹) ^ m := by
    intro m
    have hb : coverMass g (2 * m + 2) [] ≤ ((2 : ℝ≥0∞)⁻¹) ^ (2 * m + 2) := by
      rw [coverMass_nil hU]
      have hs := hsmall (2 * m + 2)
      rwa [dyadicValue_one_eq_inv_two_pow'] at hs
    have h2 : ((2 ^ m : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ m := by push_cast; ring
    have key : (2 : ℝ≥0∞) ^ m * ((2 : ℝ≥0∞)⁻¹) ^ (2 * m + 2)
        = ((2 : ℝ≥0∞)⁻¹) ^ 2 * ((2 : ℝ≥0∞)⁻¹) ^ m := by
      calc (2 : ℝ≥0∞) ^ m * ((2 : ℝ≥0∞)⁻¹) ^ (2 * m + 2)
          = ((2 : ℝ≥0∞) ^ m * ((2 : ℝ≥0∞)⁻¹) ^ m)
              * (((2 : ℝ≥0∞)⁻¹) ^ m * ((2 : ℝ≥0∞)⁻¹) ^ 2) := by
            rw [two_mul, pow_add, pow_add]; ring
        _ = ((2 : ℝ≥0∞)⁻¹) ^ 2 * ((2 : ℝ≥0∞)⁻¹) ^ m := by
            rw [hcanm m, one_mul, mul_comm]
    calc ((2 ^ m : ℕ) : ℝ≥0∞) * coverMass g (2 * m + 2) []
        ≤ ((2 ^ m : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ (2 * m + 2) := mul_le_mul_right hb _
      _ = ((2 : ℝ≥0∞)⁻¹) ^ 2 * ((2 : ℝ≥0∞)⁻¹) ^ m := by rw [h2, key]
  have hgeom : ∑' m : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ m = 2 := by
    rw [ENNReal.tsum_geometric]
    rw [show (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ from
      ENNReal.sub_eq_of_eq_add (by norm_num) (ENNReal.inv_two_add_inv_two).symm, inv_inv]
  have hhalf : ((2 : ℝ≥0∞)⁻¹) ^ 2 * 2 = (2 : ℝ≥0∞)⁻¹ := by
    rw [pow_two, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  calc testDeficiencyMass g []
      ≤ ∑' m : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ 2 * ((2 : ℝ≥0∞)⁻¹) ^ m := ENNReal.tsum_le_tsum hterm
    _ = ((2 : ℝ≥0∞)⁻¹) ^ 2 * ∑' m : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ m := ENNReal.tsum_mul_left
    _ = (2 : ℝ≥0∞)⁻¹ := by rw [hgeom, hhalf]
    _ ≤ 1 := ENNReal.inv_le_one.mpr (by norm_num)

/-- The cover index is computable in the level and the string. -/
lemma computable_coverIndex : Computable₂ coverIndex :=
  natBits_computable.comp
    ((Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd)).to_comp)

/-- The deficiency mass of a computable test is lower semicomputable. -/
lemma isLSC_testDeficiencyMass {g : ℕ → ℕ → Option BitString} (hg : Computable₂ g) :
    IsLSC fun x _ => testDeficiencyMass g x := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := cantorOpenMass_isLSC (isRE_coverRel hg)
  have hidx : Computable fun p : ℕ × ℕ × BitString => coverIndex (2 * p.1 + 2) p.2.2 :=
    computable_coverIndex.comp
      (g := fun p : ℕ × ℕ × BitString => 2 * p.1 + 2)
      (h := fun p : ℕ × ℕ × BitString => p.2.2)
      ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
        (Primrec.const 2)).to_comp)
      (Computable.snd.comp Computable.snd)
  refine isLSC_tsum_nsmul_of_uniform
    (wt := fun m => 2 ^ m) (b := fun m x => coverMass g (2 * m + 2) x)
    (A := fun m s x => approx s (coverIndex (2 * m + 2) x) [])
    ((Primrec₂.unpaired'.mp Nat.Primrec.pow).to_comp.comp (Computable.const 2) Computable.id)
    (fun m s x => hmono s (coverIndex (2 * m + 2) x) [])
    (fun m x => hsup (coverIndex (2 * m + 2) x) []) ?_
  exact hcomp.comp
    (g := fun p : ℕ × ℕ × BitString => (p.2.1, coverIndex (2 * p.1 + 2) p.2.2, ([] : BitString)))
    (Computable.pair (Computable.fst.comp Computable.snd)
      (Computable.pair hidx (Computable.const [])))

/-- If `w` belongs to the level `2 * m + 2` of the test then, from some length on, the
deficiency mass of its prefixes is at least `2 ^ m` times their uniform mass. -/
lemma exists_le_testDeficiencyMass_cantorPrefix {g : ℕ → ℕ → Option BitString}
    {U : ℕ → Set CantorSeq} (hU : ∀ n, U n = ⋃ i, (g n i).elim ∅ cantorCylinder)
    {w : CantorSeq} {m : ℕ} (hw : w ∈ U (2 * m + 2)) :
    ∃ n, m ≤ n ∧
      ((2 : ℝ≥0∞)⁻¹) ^ (n - m) ≤ testDeficiencyMass g (cantorPrefix w n) := by
  rw [hU (2 * m + 2), Set.mem_iUnion] at hw
  obtain ⟨i, hi⟩ := hw
  rcases hgi : g (2 * m + 2) i with _ | z
  · rw [hgi] at hi; simp at hi
  rw [hgi] at hi
  refine ⟨max z.length m, le_max_right _ _, ?_⟩
  set n := max z.length m with hn
  have hmn : m ≤ n := le_max_right _ _
  have hz : cantorPrefix w z.length = z := (isCantorPrefix_iff_cantorPrefix_eq z w).1 hi
  have hzp : z <+: cantorPrefix w n := by
    have hmono := cantorPrefix_mono w (le_max_left z.length m)
    rwa [hz] at hmono
  have hsub : cantorCylinder (cantorPrefix w n) ⊆ U (2 * m + 2) := by
    intro v hv
    rw [hU (2 * m + 2)]
    exact Set.mem_iUnion.2 ⟨i, by rw [hgi]; exact cantorCylinder_subset_of_prefix hzp hv⟩
  have hlow : ((2 : ℝ≥0∞)⁻¹) ^ n ≤ coverMass g (2 * m + 2) (cantorPrefix w n) := by
    have hle := le_coverMass_of_subset hU (2 * m + 2) (cantorPrefix w n) hsub
    rwa [cantorPrefix_length] at hle
  have hcast : ((2 ^ m : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ m := by push_cast; ring
  have hsplit : ((2 : ℝ≥0∞)⁻¹) ^ n = ((2 : ℝ≥0∞)⁻¹) ^ m * ((2 : ℝ≥0∞)⁻¹) ^ (n - m) := by
    rw [← pow_add]
    congr 1
    omega
  have hterm : ((2 : ℝ≥0∞)⁻¹) ^ (n - m)
      ≤ ((2 ^ m : ℕ) : ℝ≥0∞) * coverMass g (2 * m + 2) (cantorPrefix w n) := by
    calc ((2 : ℝ≥0∞)⁻¹) ^ (n - m)
        = (2 : ℝ≥0∞) ^ m * (((2 : ℝ≥0∞)⁻¹) ^ m * ((2 : ℝ≥0∞)⁻¹) ^ (n - m)) := by
          rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
            one_pow, one_mul]
      _ = (2 : ℝ≥0∞) ^ m * ((2 : ℝ≥0∞)⁻¹) ^ n := by rw [hsplit]
      _ ≤ ((2 ^ m : ℕ) : ℝ≥0∞) * coverMass g (2 * m + 2) (cantorPrefix w n) := by
          rw [hcast]; exact mul_le_mul_right hlow _
  exact hterm.trans
    (ENNReal.le_tsum (f := fun m => ((2 ^ m : ℕ) : ℝ≥0∞) * coverMass g (2 * m + 2)
      (cantorPrefix w n)) m)

/-! ### The criterion -/

/-- **Converse half of the Levin-Schnorr criterion (a priori form).** If the prefixes of `w`
satisfy `KA (w ↾ n) ≥ n - c` for a single constant `c` and all `n`, then `w` is Martin-Löf
random for the uniform measure. -/
theorem isMartinLofRandom_of_exists_const_le_KA_cantorPrefix {w : CantorSeq}
    (h : ∃ c : ℝ, ∀ n : ℕ, (n : ℝ) ≤ KA (cantorPrefix w n) + c) :
    IsMartinLofRandom uniformMeasure w := by
  obtain ⟨c₀, hc₀⟩ := h
  intro U hUtest hmem
  obtain ⟨⟨g, hg, hU⟩, hsmall⟩ := hUtest
  obtain ⟨C, hCtop, hC⟩ := exists_const_mul_universalContinuousSemimeasure_ge
    (testDeficiencyMass_children hU) (testDeficiencyMass_nil_le_one hU hsmall)
    (isLSC_testDeficiencyMass hg)
  have hmemU : ∀ k, w ∈ U k := fun k => Set.mem_iInter.1 hmem k
  have key : ∀ m : ℕ, (m : ℝ) ≤ Real.logb 2 C.toReal + c₀ := by
    intro m
    obtain ⟨n, hmn, hle⟩ := exists_le_testDeficiencyMass_cantorPrefix hU (hmemU (2 * m + 2))
    have hdom : (2 : ℝ≥0∞)⁻¹ ^ (n - m)
        ≤ C * universalContinuousSemimeasure (cantorPrefix w n) := hle.trans (hC _)
    have hKA := KA_le_nat_add_log_of_inv_two_pow_le (cantorPrefix w n) (n - m) C hCtop hdom
    have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by
      rw [Nat.cast_sub hmn]
    rw [hcast] at hKA
    have hn := hc₀ n
    linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (Real.logb 2 C.toReal + c₀)
  exact absurd (key M) (not_le.2 hM)

/-- **Levin-Schnorr criterion for a priori complexity.** A sequence is Martin-Löf random for
the uniform measure if and only if the a priori complexity of its length-`n` prefix is at
least `n - c` for a constant `c` independent of `n`. -/
theorem isMartinLofRandom_iff_exists_const_le_KA_cantorPrefix (w : CantorSeq) :
    IsMartinLofRandom uniformMeasure w ↔
      ∃ c : ℝ, ∀ n : ℕ, (n : ℝ) ≤ KA (cantorPrefix w n) + c := by
  refine ⟨fun hw => ?_, isMartinLofRandom_of_exists_const_le_KA_cantorPrefix⟩
  obtain ⟨c, hc⟩ := exists_const_le_KA_cantorPrefix_of_isMartinLofRandom hw
  exact ⟨(c : ℝ), hc⟩

end Kolmogorov
