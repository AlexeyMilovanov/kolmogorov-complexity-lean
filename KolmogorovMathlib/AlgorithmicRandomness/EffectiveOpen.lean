import KolmogorovMathlib.AlgorithmicRandomness.ComputableMeasure
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Effectively open sets and effectively null sets

`IsEffectiveOpen` is a union of a computably enumerated family of cylinders,
`IsUniformlyEffectiveOpen` the same uniformly in a parameter, and `IsEffectivelyNull A μ` says
`A` is contained in a uniformly effectively open family whose `n`-th member has measure at
most `2 ^ (-n)`.  These are the sets a Martin-Löf test is built from.

Besides the basic consequences (`IsEffectiveOpen.isOpen`, `.measurableSet`,
`IsEffectivelyNull.measure_eq_zero`), the module provides the two normalisations later
arguments need: `IsEffectivelyNull_of_rational_bound`, which accepts any computable sequence
of rational bounds that decreases fast enough, and `IsUniformlyEffectiveOpen_length_bound`,
which re-enumerates a family so that the strings used for its `n`-th member all have length at
least `n`.  The latter goes through `filterLength`, which refines each emitted string to the
required length using `union_extensions`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal Filter Topology

/-- A subset of Cantor space is effectively open when it is the union of a computably enumerated
family of cylinders. -/
def IsEffectiveOpen (U : Set CantorSeq) : Prop :=
  ∃ f : ℕ → Option BitString, Computable f ∧
    U = ⋃ i, (f i).elim ∅ cantorCylinder

/-- A sequence of subsets of Cantor space is uniformly effectively open when the cylinders making
up its members are enumerated by a single computable function of the index and the stage. -/
def IsUniformlyEffectiveOpen (U : ℕ → Set CantorSeq) : Prop :=
  ∃ f : ℕ → ℕ → Option BitString, Computable₂ f ∧
    ∀ n, U n = ⋃ i, (f n i).elim ∅ cantorCylinder

/-- A set is effectively null for `μ` when it is contained in a uniformly effectively open family
whose `n`-th member has measure at most `2^{-n}`. -/
def IsEffectivelyNull (μ : Measure CantorSeq) (A : Set CantorSeq) : Prop :=
  ∃ U : ℕ → Set CantorSeq, IsUniformlyEffectiveOpen U ∧
    A ⊆ ⋂ n, U n ∧ ∀ n, μ (U n) ≤ dyadicValue 1 n

/-- An effectively open set is open. -/
lemma IsEffectiveOpen.isOpen {U : Set CantorSeq} (h : IsEffectiveOpen U) :
    IsOpen U := by
  rcases h with ⟨f, hcomp, hU⟩
  rw [hU]
  apply isOpen_iUnion
  intro i
  cases f i
  · exact isOpen_empty
  · exact isOpen_cantorCylinder _

/-- An effectively open set is measurable. -/
lemma IsEffectiveOpen.measurableSet {U : Set CantorSeq} (h : IsEffectiveOpen U) :
    MeasurableSet U := by
  rcases h with ⟨f, hcomp, hU⟩
  rw [hU]
  apply MeasurableSet.iUnion
  intro i
  cases f i
  · exact MeasurableSet.empty
  · exact measurableSet_cantorCylinder _

/-- An effectively null set has measure zero. -/
lemma IsEffectivelyNull.measure_eq_zero {μ : Measure CantorSeq} {A : Set CantorSeq}
    (h : IsEffectivelyNull μ A) :
    μ A = 0 := by
  rcases h with ⟨U, hU, hA, hbound⟩
  apply le_antisymm _ bot_le
  have h_lt : (2 : ℝ≥0∞)⁻¹ < 1 := by
    rw [ENNReal.inv_lt_one]
    norm_num
  apply ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h_lt)
  filter_upwards
  intro n
  calc
    μ A ≤ μ (⋂ m, U m) := measure_mono hA
    _ ≤ μ (U n) := measure_mono (Set.iInter_subset _ _)
    _ ≤ dyadicValue 1 n := hbound n
    _ = (2:ℝ≥0∞)⁻¹ ^ n := by
      unfold dyadicValue
      have : ((1 : ℕ) : ℝ≥0∞) = 1 := by norm_num
      rw [this, div_eq_mul_inv, one_mul]
      exact ENNReal.inv_pow

/-- Effective nullity may be certified by any computable sequence of rational bounds decreasing
at least as fast as `2^{-n}`. -/
lemma IsEffectivelyNull_of_rational_bound (μ : Measure CantorSeq) (A : Set CantorSeq)
    (U : ℕ → Set CantorSeq) (hU : IsUniformlyEffectiveOpen U) (hA : A ⊆ ⋂ n, U n)
    (e : ℕ → ℚ) (he_comp : Computable e)
    (he_tendsto : ∀ n, (e n : ℝ) ≤ 2⁻¹ ^ n)
    (h_bound : ∀ n, μ (U n) ≤ ENNReal.ofReal (e n)) :
    IsEffectivelyNull μ A := by
  have _ := he_comp
  use U
  refine ⟨hU, hA, ?_⟩
  intro n
  have h1 : dyadicValue 1 n = (2 : ℝ≥0∞)⁻¹ ^ n := by
    unfold dyadicValue
    have : ((1 : ℕ) : ℝ≥0∞) = 1 := by norm_num
    rw [this, div_eq_mul_inv, one_mul]
    exact ENNReal.inv_pow
  rw [h1]
  apply le_trans (h_bound n)
  have h2 : ENNReal.ofReal (e n) ≤ ENNReal.ofReal (2⁻¹ ^ n) :=
    ENNReal.ofReal_le_ofReal (he_tendsto n)
  apply le_trans h2
  have h3 : ENNReal.ofReal (2⁻¹ ^ n) = (2 : ℝ≥0∞)⁻¹ ^ n := by
    have h_pos : (0 : ℝ) ≤ 2⁻¹ := by norm_num
    rw [ENNReal.ofReal_pow h_pos]
    have h_inner : ENNReal.ofReal (2⁻¹) = (2 : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
      have : ENNReal.ofReal 2 = 2 := by norm_num
      rw [this]
    rw [h_inner]
  rw [h3]

/-- A cylinder is the union of the two cylinders obtained by appending one further bit. -/
lemma union_extensions_one (s : BitString) :
    (⋃ (b : Bool), cantorCylinder (s ++ [b])) = cantorCylinder s := by
  ext x
  simp only [Set.mem_iUnion, cantorCylinder, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨b, hb⟩
    rw [Kolmogorov.isCantorPrefix_append_singleton] at hb
    exact hb.1
  · intro hs
    use x s.length
    rw [Kolmogorov.isCantorPrefix_append_singleton]
    exact ⟨hs, rfl⟩

/-- A cylinder is the union of the cylinders of all its extensions by `m` further bits. -/
lemma union_extensions (s : BitString) (m : ℕ) :
    (⋃ (y : BitString) (_ : y.length = m), cantorCylinder (s ++ y)) = cantorCylinder s := by
  induction m generalizing s with
  | zero =>
    ext x
    simp only [Set.mem_iUnion, cantorCylinder, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy, hpre⟩
      cases y with
      | nil =>
        simp only [List.append_nil] at hpre
        exact hpre
      | cons _ _ => contradiction
    · intro hpre
      use []
      simp only [List.length_nil, List.append_nil]
      exact ⟨trivial, hpre⟩
  | succ m ih =>
    rw [← union_extensions_one s]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨y, hy, hpre⟩
      cases y with
      | nil => contradiction
      | cons b y' =>
        use b
        have h1 : s ++ (b :: y') = (s ++ [b]) ++ y' := by
          simp only [List.append_assoc, List.singleton_append]
        rw [h1] at hpre
        have h2 : y'.length = m := by injection hy
        have h3 : x ∈ (⋃ (y : BitString) (_ : y.length = m), cantorCylinder ((s ++ [b]) ++ y)) := by
          simp only [Set.mem_iUnion]
          use y', h2
        rw [ih (s ++ [b])] at h3
        exact h3
    · rintro ⟨b, hb⟩
      have h3 : x ∈ (⋃ (y : BitString) (_ : y.length = m), cantorCylinder ((s ++ [b]) ++ y)) := by
        rw [ih (s ++ [b])]
        exact hb
      simp only [Set.mem_iUnion] at h3
      rcases h3 with ⟨y', hy', hpre⟩
      use b :: y'
      have h1 : s ++ (b :: y') = (s ++ [b]) ++ y' := by
        simp only [List.append_assoc, List.singleton_append]
      have h2 : (b :: y').length = m + 1 := by simp only [List.length_cons, hy']
      exact ⟨h2, by rw [h1]; exact hpre⟩

/-- Re-enumeration of an effectively open family in which every emitted string is refined to
length at least `n`, leaving the union unchanged. -/
def filterLength (f : ℕ → ℕ → Option BitString) (n i : ℕ) : Option BitString :=
  let j := (Nat.unpair i).1
  let k := (Nat.unpair i).2
  (f n j).bind fun s =>
    bif decide (n ≤ s.length) then
      bif k == 0 then some s else none
    else
      (Encodable.decode₂ BitString k).bind fun y =>
        bif decide (y.length = n - s.length) then some (s ++ y) else none

/-- The length-refined re-enumeration is computable when the original enumeration is. -/
lemma filter_length_computable {f : ℕ → ℕ → Option BitString} (hf : Computable₂ f) :
    Computable (fun (p : ℕ × ℕ) =>
      let n := p.1
      let i := p.2
      let j := (Nat.unpair i).1
      let k := (Nat.unpair i).2
      (f n j).bind fun s =>
        bif decide (n ≤ s.length) then
          bif k == 0 then some s else none
        else
          (Encodable.decode₂ BitString k).bind fun y =>
            bif decide (y.length = n - s.length) then some (s ++ y) else none) := by
  have h_j : Computable (fun (p : ℕ × ℕ) => (Nat.unpair p.2).1) :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have h_k : Computable (fun (p : ℕ × ℕ) => (Nat.unpair p.2).2) :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have h_n : Computable (fun (p : ℕ × ℕ) => p.1) := (Primrec.fst.comp Primrec.id).to_comp
  have h_fnj : Computable (fun (p : ℕ × ℕ) => f p.1 (Nat.unpair p.2).1) :=
    hf.comp h_n h_j
  apply Computable.option_bind h_fnj
  have hc_s : Computable (fun (ps : (ℕ × ℕ) × BitString) => ps.2) :=
    (Primrec.snd.comp Primrec.id).to_comp
  have hc_n : Computable (fun (ps : (ℕ × ℕ) × BitString) => ps.1.1) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.id)).to_comp
  have hc_k : Computable (fun (ps : (ℕ × ℕ) × BitString) => (Nat.unpair ps.1.2).2) :=
    h_k.comp (Primrec.fst.comp Primrec.id).to_comp
  
  have h_cond1 : Computable (fun ps : (ℕ × ℕ) × BitString => decide (ps.1.1 ≤ ps.2.length)) := by
    have h_eq : (fun ps : (ℕ × ℕ) × BitString => decide (ps.1.1 ≤ ps.2.length)) =
                (fun ps : (ℕ × ℕ) × BitString => ps.1.1 - ps.2.length == 0) := by
      ext ps
      revert ps
      intro ⟨⟨n, i⟩, s⟩
      dsimp
      cases h2 : decide (n ≤ s.length) <;> cases h3 : n - s.length == 0
      · rfl
      · exact False.elim (by simp_all; omega)
      · exact False.elim (by simp_all)
      · rfl
    rw [h_eq]
    exact (Primrec.beq.comp (Primrec.nat_sub.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))
      (Primrec.list_length.comp Primrec.snd)) (Primrec.const 0)).to_comp
  
  have h_then1 : Computable (fun ps : (ℕ × ℕ) × BitString =>
      bif (Nat.unpair ps.1.2).2 == 0 then some ps.2 else none) := by
    have h_k_eq : Computable (fun ps : (ℕ × ℕ) × BitString => (Nat.unpair ps.1.2).2 == 0) :=
      (Primrec.beq.comp (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.id)))) (Primrec.const 0)).to_comp
    apply Computable.cond h_k_eq
    · exact (Primrec.option_some.comp Primrec.snd).to_comp
    · exact (Primrec.const none).to_comp
  have h_else1 : Computable (fun ps : (ℕ × ℕ) × BitString =>
      (Encodable.decode₂ BitString (Nat.unpair ps.1.2).2).bind fun y =>
        bif decide (y.length = ps.1.1 - ps.2.length) then some (ps.2 ++ y) else none) := by
    have h_dec : Computable (fun ps : (ℕ × ℕ) × BitString =>
        Encodable.decode₂ BitString (Nat.unpair ps.1.2).2) :=
      (Primrec.decode₂.comp (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))).to_comp
    apply Computable.option_bind h_dec
    have hc_y : Computable (fun (psy : ((ℕ × ℕ) × BitString) × BitString) => psy.2) :=
      (Primrec.snd.comp Primrec.id).to_comp
    have hc_s' : Computable (fun (psy : ((ℕ × ℕ) × BitString) × BitString) => psy.1.2) :=
      (Primrec.snd.comp (Primrec.fst.comp Primrec.id)).to_comp
    have hc_n' : Computable (fun (psy : ((ℕ × ℕ) × BitString) × BitString) => psy.1.1.1) :=
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))).to_comp
    have hc_cond2 : Computable (fun psy : ((ℕ × ℕ) × BitString) × BitString =>
        decide (psy.2.length = psy.1.1.1 - psy.1.2.length)) := by
      have h_eq : (fun psy : ((ℕ × ℕ) × BitString) × BitString =>
          decide (psy.2.length = psy.1.1.1 - psy.1.2.length)) =
          (fun psy : ((ℕ × ℕ) × BitString) × BitString =>
          psy.2.length == psy.1.1.1 - psy.1.2.length) := by
        ext psy
        revert psy
        intro ⟨⟨⟨n, i⟩, s⟩, y⟩
        dsimp
        rfl
      rw [h_eq]
      exact (Primrec.beq.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.nat_sub.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id)))
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))).to_comp
    have h_then2 : Computable (fun psy : ((ℕ × ℕ) × BitString) × BitString =>
        some (psy.1.2 ++ psy.2)) :=
      (Primrec.option_some.comp (Primrec.list_append.comp (Primrec.snd.comp
        (Primrec.fst.comp Primrec.id)) Primrec.snd)).to_comp
    have h_else2 : Computable (fun psy : ((ℕ × ℕ) × BitString) × BitString => @none BitString) :=
      (Primrec.const none).to_comp
    exact Computable.cond hc_cond2 h_then2 h_else2
  exact Computable.cond h_cond1 h_then1 h_else1

/-- Every string emitted by the length-refined enumeration for index `n` has length at
least `n`. -/
lemma filter_length_bound (f : ℕ → ℕ → Option BitString) (n i : ℕ) (s : BitString) :
    filterLength f n i = some s → n ≤ s.length := by
  intro h
  dsimp [filterLength] at h
  cases hf : f n (Nat.unpair i).1 with
  | none =>
    rw [hf] at h
    simp only [Option.bind_none] at h
    contradiction
  | some s_orig =>
    rw [hf] at h
    simp only [Option.bind_some] at h
    cases h_le : decide (n ≤ s_orig.length) with
    | false =>
      rw [h_le] at h
      simp only [cond_false] at h
      cases hy : Encodable.decode₂ BitString (Nat.unpair i).2 with
      | none =>
        rw [hy] at h
        simp only [Option.bind_none] at h
        contradiction
      | some y =>
        rw [hy] at h
        simp only [Option.bind_some] at h
        cases h_dec : decide (y.length = n - s_orig.length) with
        | false =>
          rw [h_dec] at h
          simp only [cond_false] at h
          contradiction
        | true =>
          rw [h_dec] at h
          simp only [cond_true, Option.some.injEq] at h
          have h1 : y.length = n - s_orig.length := of_decide_eq_true h_dec
          rw [← h]
          simp only [List.length_append]
          omega
    | true =>
      rw [h_le] at h
      simp only [cond_true] at h
      cases h_k : (Nat.unpair i).2 == 0 with
      | false =>
        rw [h_k] at h
        simp only [cond_false] at h
        contradiction
      | true =>
        rw [h_k] at h
        simp only [cond_true, Option.some.injEq] at h
        have h1 : n ≤ s_orig.length := of_decide_eq_true h_le
        rw [← h]
        exact h1

/-- The length-refined enumeration covers the same open set as the original one. -/
lemma filter_length_union (f : ℕ → ℕ → Option BitString) (n : ℕ) :
    (⋃ i, (filterLength f n i).elim ∅ cantorCylinder) = ⋃ j, (f n j).elim ∅ cantorCylinder := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    use (Nat.unpair i).1
    dsimp [filterLength] at hi
    cases hf : f n (Nat.unpair i).1 with
    | none =>
      rw [hf] at hi
      simp only [Option.bind_none, Option.elim_none] at hi
      contradiction
    | some s_orig =>
      rw [hf] at hi
      simp only [Option.bind_some] at hi
      cases h_le : decide (n ≤ s_orig.length) with
      | false =>
        rw [h_le] at hi
        simp only [cond_false] at hi
        cases hy : Encodable.decode₂ BitString (Nat.unpair i).2 with
        | none =>
          rw [hy] at hi
          simp only [Option.bind_none, Option.elim_none] at hi
          contradiction
        | some y =>
          rw [hy] at hi
          simp only [Option.bind_some] at hi
          cases h_dec : decide (y.length = n - s_orig.length) with
          | false =>
            rw [h_dec] at hi
            simp only [cond_false, Option.elim_none] at hi
            contradiction
          | true =>
            rw [h_dec] at hi
            simp only [cond_true, Option.elim_some] at hi
            have h_subset : cantorCylinder (s_orig ++ y) ⊆ cantorCylinder s_orig :=
              cantorCylinder_subset_of_prefix (List.prefix_append s_orig y)
            exact h_subset hi
      | true =>
        rw [h_le] at hi
        simp only [cond_true] at hi
        cases h_k : (Nat.unpair i).2 == 0 with
        | false =>
          rw [h_k] at hi
          simp only [cond_false, Option.elim_none] at hi
          contradiction
        | true =>
          rw [h_k] at hi
          simp only [cond_true, Option.elim_some] at hi
          exact hi
  · rintro ⟨j, hj⟩
    cases hf : f n j with
    | none =>
      rw [hf] at hj
      simp only [Option.elim_none] at hj
      contradiction
    | some s_orig =>
      rw [hf] at hj
      simp only [Option.elim_some] at hj
      cases h_le : decide (n ≤ s_orig.length) with
      | false =>
        have h3 : x ∈ (⋃ (y : BitString) (_ : y.length = n - s_orig.length),
            cantorCylinder (s_orig ++ y)) := by
          rw [union_extensions s_orig (n - s_orig.length)]
          exact hj
        simp only [Set.mem_iUnion] at h3
        rcases h3 with ⟨y, hy, hpre⟩
        have h_encode : ∃ k, Encodable.decode₂ BitString k = some y :=
          ⟨Encodable.encode y, Encodable.encodek₂ y⟩
        rcases h_encode with ⟨k, hk⟩
        use Nat.pair j k
        dsimp [filterLength]
        simp only [Nat.unpair_pair, hf, Option.bind_some]
        rw [h_le]
        simp only [cond_false, hk, Option.bind_some]
        have h_dec : decide (y.length = n - s_orig.length) = true := decide_eq_true hy
        rw [h_dec]
        simp only [cond_true, Option.elim_some]
        exact hpre
      | true =>
        use Nat.pair j 0
        dsimp [filterLength]
        simp only [Nat.unpair_pair, hf, Option.bind_some]
        rw [h_le]
        simp only [cond_true, BEq.rfl, Option.elim_some]
        exact hj

/-- Every uniformly effectively open family may be enumerated so that the strings used for the
`n`-th member all have length at least `n`. -/
lemma IsUniformlyEffectiveOpen_length_bound (U : ℕ → Set CantorSeq)
    (h : IsUniformlyEffectiveOpen U) :
    ∃ g : ℕ → ℕ → Option BitString, Computable₂ g ∧
      (∀ n, U n = ⋃ i, (g n i).elim ∅ cantorCylinder) ∧
      (∀ n i s, g n i = some s → n ≤ s.length) := by
  rcases h with ⟨f, hcomp, hU⟩
  use filterLength f
  refine ⟨filter_length_computable hcomp, ?_, filter_length_bound f⟩
  intro n
  rw [filter_length_union]
  exact hU n

end Kolmogorov
