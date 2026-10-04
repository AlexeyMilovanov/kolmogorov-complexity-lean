/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.MonotoneComplexity.TwoSidedMeasureRepresentation
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveNull
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveOpenNormalForm
import KolmogorovMathlib.AlgorithmicRandomness.LevelStrings
import KolmogorovMathlib.AlgorithmicRandomness.Disjointify
import KolmogorovMathlib.AlgorithmicRandomness.StageComputable
import Mathlib.Order.BourbakiWitt
import KolmogorovMathlib.MonotoneComplexity.Dimension.Basic

/-!
# Lemma 1 of SUV §5.9.3 (p. 182): a null difference of effectively open sets

> "**Lemma 1.** Let `μ` be a computable measure on `Ω`, and let `U ⊆ V` be two
> effectively open sets such that `μ(V \ U) = 0`.  Then `V \ U` is an effectively
> null set (= does not contain random sequences)."
>
> "*Proof.* It is enough to consider one interval `I` in the set `V` (and replace
> `U` by its intersection with `I`).  Enumerating the intervals that form the set
> `U`, we cover more and more points in `I`.  By continuity the measure of the
> covered part converges to the measure of the interval `I` (since `V \ U` has
> zero measure).  Therefore, we can wait until the remaining part of `I` has
> measure less than `ε` for any given `ε` and find a cover of `I \ U` by a
> (finite) family of intervals with small total measure."  (SUV p. 182)

This module is the machinery of that proof, in the form Chapter 3's interfaces
want; the theorem itself (`isEffectivelyNull_diff_of_measure_eq_zero`) is the
frozen statement in `Dimension/ChangeOfMeasure.lean`.

The source's "remaining part of the interval `I` after `s` steps" is
`diffStage h v L`: the finite union of the cylinders `Ω_y` of the strings `y` of
length `l(v) + L` that extend `v` and are covered by none of the first `L`
intervals of the enumeration `h` of `U`.  Three facts about it carry the proof:

* `sdiff_subset_diffStage` — it always contains `Ω_v \ U`, so it *is* a cover;
* `diffStage_antitone` — it shrinks with `L`;
* `diffStage_subset_sdiff` — it is contained in `Ω_v` minus the first `s`
  intervals as soon as `L` is at least `s` and at least the lengths of those
  intervals, so (continuity from above) its measure tends to `μ(Ω_v \ U)`.

The source's "we can wait until" is not an unbounded search here: the cover
`diffCover` of `Ω_v \ U` of measure `≤ 2^{-n}` is the union of the stages
`diffStage h v L` over the levels *certified* by the dyadic approximation of `μ`
at some precision `t` — a decidable condition on `(L, t)`.  Since the stages
shrink, that union is the smallest certified stage, hence has measure `≤ 2^{-n}`;
and by the three facts above some level is certified.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ## The remaining part of an interval after finitely many steps -/

/-- The strings of length `l(v) + L` inside `Ω_v` that are covered by none of the
first `L` intervals of the enumeration `h`. -/
def diffLevelList (h : ℕ → Option BitString) (v : BitString) (L : ℕ) : List BitString :=
  (levelList (v.length + L)).filter fun y => normalFormIsPrefixB v y && !prefixSeen h y L

/-- The level-`L` list below `v` consists of the extensions of `v` by `L` bits that avoid all cover
strings enumerated before stage `L`. -/
lemma mem_diffLevelList {h : ℕ → Option BitString} {v : BitString} {L : ℕ} {y : BitString} :
    y ∈ diffLevelList h v L ↔
      y.length = v.length + L ∧ v <+: y ∧ ¬ ∃ j < L, ∃ z, h j = some z ∧ z <+: y := by
  simp only [diffLevelList, List.mem_filter, mem_levelList, Bool.and_eq_true,
    normalFormIsPrefixB_iff, Bool.not_eq_eq_eq_not, Bool.not_true, ← prefixSeen_spec,
    Bool.not_eq_true]

/-- The level-`L` list below `v` has no repetitions. -/
lemma nodup_diffLevelList (h : ℕ → Option BitString) (v : BitString) (L : ℕ) :
    (diffLevelList h v L).Nodup :=
  (nodup_levelList _).filter _

/-- The finite union of the cylinders of `diffLevelList`: the source's "remaining
part of the interval `I`". -/
def diffStage (h : ℕ → Option BitString) (v : BitString) (L : ℕ) : Set CantorSeq :=
  ⋃ y ∈ (diffLevelList h v L).toFinset, cantorCylinder y

/-- The stage-`L` approximation to the uncovered part of the cylinder of `v` is measurable. -/
lemma measurableSet_diffStage (h : ℕ → Option BitString) (v : BitString) (L : ℕ) :
    MeasurableSet (diffStage h v L) :=
  Finset.measurableSet_biUnion _ fun y _ => measurableSet_cantorCylinder y

/-- **The covering property.**  Whatever the level, the stage set contains the
part of `Ω_v` that the enumeration `h` never covers. -/
lemma sdiff_subset_diffStage (h : ℕ → Option BitString) (v : BitString) (L : ℕ) :
    cantorCylinder v \ (⋃ j, coverSet h j) ⊆ diffStage h v L := by
  rintro x ⟨hxv, hxU⟩
  have hyx : x ∈ cantorCylinder (cantorPrefix x (v.length + L)) :=
    mem_cantorCylinder_cantorPrefix x _
  have hvy : v <+: cantorPrefix x (v.length + L) := by
    have hv : cantorPrefix x v.length = v := (isCantorPrefix_iff_cantorPrefix_eq v x).1 hxv
    have hmono := cantorPrefix_mono x (Nat.le_add_right v.length L)
    rwa [hv] at hmono
  have hcov : ¬ ∃ j < L, ∃ z, h j = some z ∧ z <+: cantorPrefix x (v.length + L) := by
    rintro ⟨j, -, z, hjz, hzy⟩
    refine hxU (Set.mem_iUnion.2 ⟨j, ?_⟩)
    rw [coverSet, hjz]
    exact cantorCylinder_subset_of_prefix hzy hyx
  refine Set.mem_biUnion (Finset.mem_coe.1 ?_) hyx
  simpa [List.mem_toFinset] using
    mem_diffLevelList.2 ⟨cantorPrefix_length x _, hvy, hcov⟩

/-- **The shrinking property.**  As soon as the level is at least `s` and at
least the length of each of the first `s` intervals, the stage set is contained
in `Ω_v` minus those `s` intervals. -/
lemma diffStage_subset_sdiff {h : ℕ → Option BitString} {v : BitString} {s L : ℕ}
    (hsL : s ≤ L) (hlen : ∀ j < s, ∀ z, h j = some z → z.length ≤ v.length + L) :
    diffStage h v L ⊆ cantorCylinder v \ ⋃ j ∈ Finset.range s, coverSet h j := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 hx
  rw [List.mem_toFinset] at hy
  obtain ⟨hylen, hvy, hcov⟩ := mem_diffLevelList.1 hy
  refine ⟨cantorCylinder_subset_of_prefix hvy hxy, ?_⟩
  intro hmem
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 hmem
  rw [Finset.mem_range] at hj
  cases hjz : h j with
  | none => rw [coverSet, hjz] at hxj; simp at hxj
  | some z =>
      rw [coverSet, hjz] at hxj
      have hzy : z <+: y := by
        refine prefix_of_isCantorPrefix hxj hxy ?_
        rw [hylen]
        exact hlen j hj z hjz
      exact hcov ⟨j, lt_of_lt_of_le hj hsL, z, hjz, hzy⟩

/-- The stages shrink as the level grows. -/
lemma diffStage_antitone (h : ℕ → Option BitString) (v : BitString) :
    Antitone (diffStage h v) := by
  refine antitone_nat_of_succ_le fun L => ?_
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 hx
  rw [List.mem_toFinset] at hy
  obtain ⟨hylen, hvy, hcov⟩ := mem_diffLevelList.1 hy
  have hpre : y.take (v.length + L) <+: y := List.take_prefix _ _
  have hvy' : v <+: y.take (v.length + L) := by
    obtain ⟨w, hw⟩ := hvy
    have h1 : y.take v.length = v := by rw [← hw, List.take_left]
    have h3 : (y.take (v.length + L)).take v.length = y.take v.length := by
      rw [List.take_take, min_eq_left (by omega)]
    have h2 : y.take v.length <+: y.take (v.length + L) := by
      rw [← h3]
      exact List.take_prefix _ _
    rwa [h1] at h2
  have hlen' : (y.take (v.length + L)).length = v.length + L := by
    rw [List.length_take, hylen]
    omega
  refine Set.mem_biUnion (Finset.mem_coe.1 ?_) (cantorCylinder_subset_of_prefix hpre hxy)
  refine (List.mem_toFinset).2 (mem_diffLevelList.2 ⟨hlen', hvy', ?_⟩)
  rintro ⟨j, hj, z, hjz, hzy⟩
  exact hcov ⟨j, by omega, z, hjz, hzy.trans hpre⟩

/-- The measure of a stage set is the sum of the masses of its (disjoint)
cylinders. -/
lemma measure_diffStage (μ : Measure CantorSeq) (h : ℕ → Option BitString) (v : BitString)
    (L : ℕ) :
    μ (diffStage h v L) = ((diffLevelList h v L).map (cantorMass μ)).sum := by
  have hd : ((diffLevelList h v L).toFinset : Set BitString).Pairwise
      (Function.onFun Disjoint cantorCylinder) := by
    intro y hy z hz hne
    rw [Finset.mem_coe, List.mem_toFinset] at hy hz
    obtain ⟨hylen, -, -⟩ := mem_diffLevelList.1 hy
    obtain ⟨hzlen, -, -⟩ := mem_diffLevelList.1 hz
    refine cantorCylinder_disjoint_of_incompatible ?_ ?_
    · exact fun hpre => hne (List.IsPrefix.eq_of_length hpre (by rw [hylen, hzlen]))
    · exact fun hpre => hne (List.IsPrefix.eq_of_length hpre (by rw [hylen, hzlen])).symm
  have hm : ∀ y ∈ (diffLevelList h v L).toFinset, MeasurableSet (cantorCylinder y) :=
    fun y _ => measurableSet_cantorCylinder y
  rw [diffStage, measure_biUnion_finset hd hm,
    List.sum_toFinset _ (nodup_diffLevelList h v L)]
  rfl

/-- The union of two effectively open sets is effectively open (the two
enumerations interleaved).  Used by SUV Theorem 123(a) for the preimage of
`Σ_{z0} ∪ Σ_{z1}`. -/
lemma isEffectiveOpen_union {A B : Set CantorSeq} (hA : IsEffectiveOpen A)
    (hB : IsEffectiveOpen B) : IsEffectiveOpen (A ∪ B) := by
  obtain ⟨fa, hfa, hAeq⟩ := hA
  obtain ⟨fb, hfb, hBeq⟩ := hB
  refine ⟨fun i => bif decide (i % 2 = 0) then fa (i / 2) else fb (i / 2), ?_, ?_⟩
  · have hpar : Computable fun i : ℕ => decide (i % 2 = 0) :=
      (PrimrecPred.decide (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id
        (Primrec.const 2)) (Primrec.const 0))).to_comp
    have hhalf : Computable fun i : ℕ => i / 2 :=
      (Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp
    exact Computable.cond hpar (hfa.comp hhalf) (hfb.comp hhalf)
  · ext x
    simp only [Set.mem_union, Set.mem_iUnion, hAeq, hBeq]
    constructor
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · refine ⟨2 * i, ?_⟩
        have h1 : (2 * i) % 2 = 0 := by omega
        have h2 : (2 * i) / 2 = i := by omega
        simpa [h1, h2] using hi
      · refine ⟨2 * i + 1, ?_⟩
        have h1 : (2 * i + 1) % 2 = 1 := by omega
        have h2 : (2 * i + 1) / 2 = i := by omega
        simpa [h1, h2] using hi
    · rintro ⟨i, hi⟩
      by_cases hpar : i % 2 = 0
      · exact Or.inl ⟨i / 2, by simpa [hpar] using hi⟩
      · exact Or.inr ⟨i / 2, by simpa [hpar] using hi⟩

/-! ## Certified stages -/

/-- The dyadic numerator certifying the mass of a stage set at precision `t`:
the approximations of the masses of its cylinders, plus one unit of error each. -/
def diffStageNum (a : BitString → ℕ → ℕ) (h : ℕ → Option BitString) (v : BitString)
    (L t : ℕ) : ℕ :=
  ((diffLevelList h v L).map fun y => a y t).sum + (diffLevelList h v L).length

/-- The level `L` is *certified* for the accuracy `n` at precision `t`. -/
def diffCert (a : BitString → ℕ → ℕ) (h : ℕ → Option BitString) (v : BitString)
    (n L t : ℕ) : Bool :=
  decide (diffStageNum a h v L t * 2 ^ n ≤ 2 ^ t)

/-- Reading a dyadic comparison back as an inequality of numerators. -/
lemma mul_le_of_dyadicValue_le {N m t : ℕ} (hle : dyadicValue N t ≤ dyadicValue 1 m) :
    N * 2 ^ m ≤ 2 ^ t := by
  by_contra hcon
  push Not at hcon
  have h1 : dyadicValue (2 ^ t) (t + m) < dyadicValue (N * 2 ^ m) (t + m) :=
    dyadicValue_lt_of_lt _ hcon
  rw [← dyadicValue_scale N t m] at h1
  rw [Nat.add_comm t m, show (2 : ℕ) ^ t = 1 * 2 ^ t from (one_mul _).symm,
    ← dyadicValue_scale 1 m t] at h1
  exact absurd hle (not_le.2 h1)

/-- The masses of a list of cylinders are below the dyadic value of the
approximation numerator with one unit of error per cylinder. -/
lemma list_mass_le_dyadicValue {μ : Measure CantorSeq} {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s) (t : ℕ) (l : List BitString) :
    (l.map (cantorMass μ)).sum ≤ dyadicValue ((l.map fun y => a y t).sum + l.length) t := by
  induction l with
  | nil => simp [dyadicValue]
  | cons y l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hstep : cantorMass μ y + (l.map (cantorMass μ)).sum
          ≤ (dyadicValue (a y t) t + dyadicValue 1 t)
            + dyadicValue ((l.map fun y => a y t).sum + l.length) t :=
        add_le_add (ha y t).2 ih
      refine hstep.trans (le_of_eq ?_)
      rw [← dyadicValue_add, ← dyadicValue_add]
      congr 1
      omega

/-- The converse estimate, with two units of error per cylinder. -/
lemma dyadicValue_le_list_mass {μ : Measure CantorSeq} {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s) (t : ℕ) (l : List BitString) :
    dyadicValue ((l.map fun y => a y t).sum + l.length) t
      ≤ (l.map (cantorMass μ)).sum + dyadicValue (2 * l.length) t := by
  induction l with
  | nil => simp [dyadicValue]
  | cons y l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hsplit : dyadicValue ((a y t + (l.map fun y => a y t).sum) + (l.length + 1)) t
          = dyadicValue (a y t) t
            + (dyadicValue ((l.map fun y => a y t).sum + l.length) t + dyadicValue 1 t) := by
        rw [← dyadicValue_add, ← dyadicValue_add]
        congr 1
        omega
      rw [hsplit]
      have hstep : dyadicValue (a y t) t
            + (dyadicValue ((l.map fun y => a y t).sum + l.length) t + dyadicValue 1 t)
          ≤ (cantorMass μ y + dyadicValue 1 t)
            + (((l.map (cantorMass μ)).sum + dyadicValue (2 * l.length) t)
              + dyadicValue 1 t) :=
        add_le_add (ha y t).1 (add_le_add ih le_rfl)
      refine hstep.trans (le_of_eq ?_)
      have hnum : dyadicValue 1 t + (dyadicValue (2 * l.length) t + dyadicValue 1 t)
          = dyadicValue (2 * (l.length + 1)) t := by
        rw [← dyadicValue_add, ← dyadicValue_add]
        congr 1
        omega
      calc (cantorMass μ y + dyadicValue 1 t)
            + (((l.map (cantorMass μ)).sum + dyadicValue (2 * l.length) t) + dyadicValue 1 t)
          = (cantorMass μ y + (l.map (cantorMass μ)).sum)
            + (dyadicValue 1 t + (dyadicValue (2 * l.length) t + dyadicValue 1 t)) := by
            ring
        _ = (cantorMass μ y + (l.map (cantorMass μ)).sum)
            + dyadicValue (2 * (l.length + 1)) t := by rw [hnum]

/-- Soundness of the certificate: if `a` approximates the Cantor mass of `μ` to within one
dyadic unit at every string and stage, and `diffCert a h v n L t = true`, then the stage-`L`
difference set has small measure, `μ (diffStage h v L) ≤ dyadicValue 1 n`. -/
lemma measure_diffStage_le_of_diffCert {μ : Measure CantorSeq} {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (h : ℕ → Option BitString) (v : BitString) {n L t : ℕ}
    (hcert : diffCert a h v n L t = true) :
    μ (diffStage h v L) ≤ dyadicValue 1 n := by
  have hnum : μ (diffStage h v L) ≤ dyadicValue (diffStageNum a h v L t) t := by
    rw [measure_diffStage, diffStageNum]
    exact list_mass_le_dyadicValue ha t _
  refine hnum.trans (dyadicValue_le_cross ?_)
  rw [one_mul]
  simpa [diffCert] using hcert

/-- **Completeness of the certificate**: a stage set of small measure is
certified at some precision. -/
lemma exists_diffCert {μ : Measure CantorSeq} {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (h : ℕ → Option BitString) (v : BitString) {n L : ℕ}
    (hsmall : μ (diffStage h v L) ≤ dyadicValue 1 (n + 2)) :
    ∃ t, diffCert a h v n L t = true := by
  refine ⟨2 * (diffLevelList h v L).length * 2 ^ (n + 2), ?_⟩
  set t := 2 * (diffLevelList h v L).length * 2 ^ (n + 2) with ht
  have herr : dyadicValue (2 * (diffLevelList h v L).length) t ≤ dyadicValue 1 (n + 2) := by
    refine dyadicValue_le_cross ?_
    rw [one_mul, ← ht]
    exact le_of_lt Nat.lt_two_pow_self
  have hmain : dyadicValue (diffStageNum a h v L t) t ≤ dyadicValue 1 n := by
    have h1 : dyadicValue (diffStageNum a h v L t) t
        ≤ μ (diffStage h v L) + dyadicValue (2 * (diffLevelList h v L).length) t := by
      rw [measure_diffStage, diffStageNum]
      exact dyadicValue_le_list_mass ha t _
    have h2 : dyadicValue 1 (n + 2) + dyadicValue 1 (n + 2) = dyadicValue 1 (n + 1) := by
      rw [← dyadicValue_add, dyadicValue_scale 1 (n + 1) 1]
      norm_num
    calc dyadicValue (diffStageNum a h v L t) t
        ≤ μ (diffStage h v L) + dyadicValue (2 * (diffLevelList h v L).length) t := h1
      _ ≤ dyadicValue 1 (n + 2) + dyadicValue 1 (n + 2) := add_le_add hsmall herr
      _ = dyadicValue 1 (n + 1) := h2
      _ ≤ dyadicValue 1 n := dyadicValue_antitone_stage 1 (Nat.le_succ n)
  simpa [diffCert] using mul_le_of_dyadicValue_le hmain

/-! ## The cover of `Ω_v \ U` by the certified stages -/

/-- The union of the certified stages: the cover of `Ω_v \ U` of measure at most
`2^{-n}` that the source obtains by waiting. -/
def diffCover (a : BitString → ℕ → ℕ) (h : ℕ → Option BitString) (v : BitString) (n : ℕ) :
    Set CantorSeq :=
  ⋃ L, ⋃ t, ⋃ (_ : diffCert a h v n L t = true), diffStage h v L

/-- The cover produced at precision `n` has measure at most `2 ^ (-n)`. -/
lemma measure_diffCover_le {μ : Measure CantorSeq} {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (h : ℕ → Option BitString) (v : BitString) (n : ℕ) :
    μ (diffCover a h v n) ≤ dyadicValue 1 n := by
  classical
  by_cases hex : ∃ L, ∃ t, diffCert a h v n L t = true
  · obtain ⟨t₀, ht₀⟩ := Nat.find_spec hex
    have hsub : diffCover a h v n ⊆ diffStage h v (Nat.find hex) := by
      refine Set.iUnion_subset fun L => Set.iUnion_subset fun t =>
        Set.iUnion_subset fun hc => ?_
      exact diffStage_antitone h v (Nat.find_le ⟨t, hc⟩)
    exact (measure_mono hsub).trans (measure_diffStage_le_of_diffCert ha h v ht₀)
  · have hempty : diffCover a h v n ⊆ (∅ : Set CantorSeq) := by
      intro x hx
      obtain ⟨L, hL⟩ := Set.mem_iUnion.1 hx
      obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hL
      obtain ⟨hc, -⟩ := Set.mem_iUnion.1 ht
      exact absurd ⟨L, t, hc⟩ hex
    calc μ (diffCover a h v n) ≤ μ (∅ : Set CantorSeq) := measure_mono hempty
      _ = 0 := measure_empty
      _ ≤ dyadicValue 1 n := zero_le

/-- Once a certificate exists, the part of the cylinder of `v` left uncovered by `h` is contained in
the constructed cover. -/
lemma sdiff_subset_diffCover {a : BitString → ℕ → ℕ} {h : ℕ → Option BitString}
    {v : BitString} {n : ℕ} (hex : ∃ L t, diffCert a h v n L t = true) :
    cantorCylinder v \ (⋃ j, coverSet h j) ⊆ diffCover a h v n := by
  obtain ⟨L, t, hc⟩ := hex
  refine (sdiff_subset_diffStage h v L).trans ?_
  intro x hx
  exact Set.mem_iUnion.2 ⟨L, Set.mem_iUnion.2 ⟨t, Set.mem_iUnion.2 ⟨hc, hx⟩⟩⟩

/-! ## The cover is effectively open -/

/-- The interval enumeration of `diffCover`: the index `i` codes a level, a
precision and a position in the list of that stage. -/
def diffCoverEnum (a : BitString → ℕ → ℕ) (h : ℕ → Option BitString) (v : BitString)
    (n i : ℕ) : Option BitString :=
  bif diffCert a h v n (Nat.unpair i).1 (Nat.unpair (Nat.unpair i).2).1 then
    (diffLevelList h v (Nat.unpair i).1)[(Nat.unpair (Nat.unpair i).2).2]?
  else none

/-- The constructed cover is the union of the cylinders of its own enumeration. -/
lemma diffCover_eq_iUnion (a : BitString → ℕ → ℕ) (h : ℕ → Option BitString) (v : BitString)
    (n : ℕ) : diffCover a h v n = ⋃ i, coverSet (diffCoverEnum a h v n) i := by
  ext x
  constructor
  · intro hx
    obtain ⟨L, hL⟩ := Set.mem_iUnion.1 hx
    obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hL
    obtain ⟨hc, hxs⟩ := Set.mem_iUnion.1 ht
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 hxs
    rw [List.mem_toFinset] at hy
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hy
    refine Set.mem_iUnion.2 ⟨Nat.pair L (Nat.pair t k), ?_⟩
    rw [coverSet, diffCoverEnum]
    simp only [Nat.unpair_pair, hc, Bool.cond_true, hk]
    exact hxy
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    rw [coverSet] at hi
    cases he : diffCoverEnum a h v n i with
    | none => rw [he] at hi; simp at hi
    | some y =>
        rw [he] at hi
        simp only [Option.elim_some] at hi
        rw [diffCoverEnum] at he
        cases hc : diffCert a h v n (Nat.unpair i).1 (Nat.unpair (Nat.unpair i).2).1 with
        | false => rw [hc] at he; simp at he
        | true =>
            rw [hc] at he
            simp only [Bool.cond_true] at he
            have hy : y ∈ diffLevelList h v (Nat.unpair i).1 := List.mem_of_getElem? he
            refine Set.mem_iUnion.2 ⟨(Nat.unpair i).1,
              Set.mem_iUnion.2 ⟨(Nat.unpair (Nat.unpair i).2).1, Set.mem_iUnion.2 ⟨hc, ?_⟩⟩⟩
            exact Set.mem_biUnion (Finset.mem_coe.1 ((List.mem_toFinset).2 hy)) hi

/-- The prefix half of the `diffLevelList` filter. -/
private lemma computable_diffLevelPrefix :
    Computable fun r : (BitString × ℕ) × BitString => normalFormIsPrefixB r.1.1 r.2 :=
  primrec₂_normalFormIsPrefixB.to_comp.comp (Computable.fst.comp Computable.fst) Computable.snd

/-- The tuple handed to `computable_prefixSeen`.  Naming it (with its type
written out) keeps the `Computable.pair` nest from being elaborated against a
metavariable-headed target. -/
private lemma computable_diffLevelSeenArg :
    Computable fun r : (BitString × ℕ) × BitString =>
      (((0, r.2) : ℕ × BitString), r.1.2) :=
  Computable.pair (Computable.pair (Computable.const 0) Computable.snd)
    (Computable.snd.comp Computable.fst)

/-- The "already seen" half of the `diffLevelList` filter. -/
private lemma computable_diffLevelSeen {h : ℕ → Option BitString} (hh : Computable h) :
    Computable fun r : (BitString × ℕ) × BitString => prefixSeen h r.2 r.1.2 := by
  have hfam : Computable₂ fun (_ : ℕ) (i : ℕ) => h i := hh.comp Computable.snd
  exact ((computable_prefixSeen (f := fun _ : ℕ => h) hfam).comp
    computable_diffLevelSeenArg).of_eq fun _ => rfl

/-- The filter predicate of `diffLevelList`.  The two halves and the `cond` that
joins them are separate declarations: assembling them together with the
`List.filter` layer is what made this proof expensive. -/
private lemma computable_diffLevelPred {h : ℕ → Option BitString} (hh : Computable h) :
    Computable₂ fun (q : BitString × ℕ) (y : BitString) =>
      normalFormIsPrefixB q.1 y && !prefixSeen h y q.2 := by
  refine (Computable.cond (computable_diffLevelSeen hh) (Computable.const false)
    computable_diffLevelPrefix).of_eq fun r => ?_
  cases hb : prefixSeen h r.2 r.1.2 <;> simp [hb]

/-- For a computable cover enumeration the level lists are computable in the base string and the
level. -/
lemma computable_diffLevelList {h : ℕ → Option BitString} (hh : Computable h) :
    Computable fun q : BitString × ℕ => diffLevelList h q.1 q.2 := by
  have hlevel : Computable fun q : BitString × ℕ => levelList (q.1.length + q.2) :=
    computable_levelList.comp
      (Primrec.nat_add.to_comp.comp (Computable.list_length.comp Computable.fst) Computable.snd)
  exact computable_list_filter hlevel (computable_diffLevelPred hh)

/-- For computable data the numeric stage value of the difference construction is computable. -/
lemma computable_diffStageNum {a : BitString → ℕ → ℕ} (ha : Computable₂ a)
    {h : ℕ → Option BitString} (hh : Computable h) :
    Computable fun q : (BitString × ℕ) × ℕ => diffStageNum a h q.1.1 q.1.2 q.2 := by
  have hlist : Computable fun q : (BitString × ℕ) × ℕ => diffLevelList h q.1.1 q.1.2 :=
    (computable_diffLevelList hh).comp Computable.fst
  have hsum : Computable fun q : (BitString × ℕ) × ℕ =>
      ((diffLevelList h q.1.1 q.1.2).map fun y => a y q.2).sum :=
    computable_list_sum_map hlist (ha.comp Computable.snd (Computable.snd.comp Computable.fst))
  refine (Primrec.nat_add.to_comp.comp hsum (Computable.list_length.comp hlist)).of_eq
    fun q => ?_
  rfl

/-- For computable data the certificate test of the difference construction is computable. -/
lemma computable_diffCert {a : BitString → ℕ → ℕ} (ha : Computable₂ a)
    {h : ℕ → Option BitString} (hh : Computable h) :
    Computable fun q : (BitString × ℕ) × (ℕ × ℕ) => diffCert a h q.1.1 q.1.2 q.2.1 q.2.2 := by
  have hnum : Computable fun q : (BitString × ℕ) × (ℕ × ℕ) =>
      diffStageNum a h q.1.1 q.2.1 q.2.2 := by
    refine ((computable_diffStageNum ha hh).comp
      (Computable.pair
        (Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.fst.comp Computable.snd))
        (Computable.snd.comp Computable.snd))).of_eq fun q => ?_
    rfl
  have hpow : Computable fun n : ℕ => 2 ^ n := primrec_two_pow_aux.to_comp
  have hle : Computable₂ fun m n : ℕ => decide (m ≤ n) :=
    (PrimrecPred.decide Primrec.nat_le).to_comp
  refine (hle.comp
    (Primrec.nat_mul.to_comp.comp hnum (hpow.comp (Computable.snd.comp Computable.fst)))
    (hpow.comp (Computable.snd.comp Computable.snd))).of_eq fun q => ?_
  rfl

/-- For computable data the enumeration of the constructed cover is computable. -/
lemma computable_diffCoverEnum {a : BitString → ℕ → ℕ} (ha : Computable₂ a)
    {h : ℕ → Option BitString} (hh : Computable h) :
    Computable fun q : (BitString × ℕ) × ℕ => diffCoverEnum a h q.1.1 q.1.2 q.2 := by
  have hL : Computable fun q : (BitString × ℕ) × ℕ => (Nat.unpair q.2).1 :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have ht : Computable fun q : (BitString × ℕ) × ℕ => (Nat.unpair (Nat.unpair q.2).2).1 :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp Primrec.snd)))).to_comp
  have hk : Computable fun q : (BitString × ℕ) × ℕ => (Nat.unpair (Nat.unpair q.2).2).2 :=
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp Primrec.snd)))).to_comp
  have hcert : Computable fun q : (BitString × ℕ) × ℕ =>
      diffCert a h q.1.1 q.1.2 (Nat.unpair q.2).1 (Nat.unpair (Nat.unpair q.2).2).1 := by
    refine ((computable_diffCert ha hh).comp
      (Computable.pair Computable.fst (Computable.pair hL ht))).of_eq fun q => ?_
    rfl
  have hlist : Computable fun q : (BitString × ℕ) × ℕ =>
      diffLevelList h q.1.1 (Nat.unpair q.2).1 := by
    refine ((computable_diffLevelList hh).comp
      (Computable.pair (Computable.fst.comp Computable.fst) hL)).of_eq fun q => ?_
    rfl
  have hget : Computable fun q : (BitString × ℕ) × ℕ =>
      (diffLevelList h q.1.1 (Nat.unpair q.2).1)[(Nat.unpair (Nat.unpair q.2).2).2]? := by
    refine (Computable.list_getElem?.comp hlist hk).of_eq fun q => ?_
    rfl
  refine (Computable.cond hcert hget (Computable.const none)).of_eq fun q => ?_
  rfl

/-- **The source's "we can wait until".**  If `Ω_v \ U` is null, then every
accuracy is certified at some level. -/
lemma exists_diffCert_of_measure_eq_zero {μ : Measure CantorSeq} [IsProbabilityMeasure μ]
    {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (h : ℕ → Option BitString) (v : BitString)
    (hzero : μ (cantorCylinder v \ ⋃ j, coverSet h j) = 0) (n : ℕ) :
    ∃ L t, diffCert a h v n L t = true := by
  classical
  set A : ℕ → Set CantorSeq :=
    fun s => cantorCylinder v \ ⋃ j ∈ Finset.range s, coverSet h j with hA
  have hmeasA : ∀ s, MeasurableSet (A s) := by
    intro s
    exact (measurableSet_cantorCylinder v).diff
      (Finset.measurableSet_biUnion _ fun j _ => measurableSet_coverSet h j)
  have hanti : Antitone A := by
    intro s s' hss x hx
    refine ⟨hx.1, ?_⟩
    intro hmem
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 hmem
    rw [Finset.mem_range] at hj
    exact hx.2 (Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 (lt_of_lt_of_le hj hss), hxj⟩)
  have hinter : (⋂ s, A s) = cantorCylinder v \ ⋃ j, coverSet h j := by
    ext x
    constructor
    · intro hx
      have hx0 := Set.mem_iInter.1 hx 0
      refine ⟨hx0.1, ?_⟩
      rintro hmem
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
      exact (Set.mem_iInter.1 hx (j + 1)).2
        (Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 (by omega), hj⟩)
    · rintro ⟨hv, hnot⟩
      refine Set.mem_iInter.2 fun s => ⟨hv, fun hmem => ?_⟩
      obtain ⟨j, -, hxj⟩ := Set.mem_iUnion₂.1 hmem
      exact hnot (Set.mem_iUnion.2 ⟨j, hxj⟩)
  have hlim : μ (⋂ s, A s) = ⨅ s, μ (A s) :=
    hanti.measure_iInter (fun s => (hmeasA s).nullMeasurableSet) ⟨0, measure_ne_top μ _⟩
  have hpos : (0 : ℝ≥0∞) < dyadicValue 1 (n + 2) := by
    rw [dyadicValue_one_eq_inv_two_pow']
    exact pos_iff_ne_zero.2 (pow_ne_zero _ (ENNReal.inv_ne_zero.2 (by norm_num)))
  have hiInf : (⨅ s, μ (A s)) < dyadicValue 1 (n + 2) := by
    rw [← hlim, hinter, hzero]
    exact hpos
  obtain ⟨s, hs⟩ := iInf_lt_iff.1 hiInf
  refine ⟨s + maxLen h s, ?_⟩
  have hsub : diffStage h v (s + maxLen h s) ⊆ A s := by
    refine diffStage_subset_sdiff (Nat.le_add_right _ _) ?_
    intro j hj z hjz
    have h1 : lenOf h j ≤ maxLen h s := lenOf_le_maxLen h hj
    have h2 : lenOf h j = z.length := by simp [lenOf, hjz]
    omega
  exact exists_diffCert ha h v ((measure_mono hsub).trans (le_of_lt hs))

end Kolmogorov
