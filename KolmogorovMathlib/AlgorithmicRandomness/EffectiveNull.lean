import KolmogorovMathlib.AlgorithmicRandomness.EffectiveOpen

/-!
# Effectively null sets: basic closure properties

This module develops elementary closure properties of the effective open sets
and of the effectively null sets of SUV Chapter 3.2, culminating in the
countable-union theorem: the union of a uniformly effectively null family of
sets is effectively null.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- The empty set is effectively open. -/
lemma isEffectiveOpen_empty : IsEffectiveOpen (∅ : Set CantorSeq) := by
  refine ⟨fun _ => none, (Primrec.const none).to_comp, ?_⟩
  simp

/-- Every cylinder is effectively open. -/
lemma isEffectiveOpen_cantorCylinder (x : BitString) :
    IsEffectiveOpen (cantorCylinder x) := by
  refine ⟨fun _ => some x, (Primrec.const (some x)).to_comp, ?_⟩
  simp only [Option.elim_some]
  exact (Set.iUnion_const _).symm

/-- A subset of an effectively null set is effectively null. -/
lemma IsEffectivelyNull.mono {μ : Measure CantorSeq} {A B : Set CantorSeq}
    (h : IsEffectivelyNull μ B) (hAB : A ⊆ B) : IsEffectivelyNull μ A := by
  obtain ⟨U, hU, hB, hbound⟩ := h
  exact ⟨U, hU, hAB.trans hB, hbound⟩

/-- A family `A : ℕ → Set CantorSeq` is *uniformly effectively null* for `μ` if
there is a single uniformly effective open family `W` such that, for every `k`,
the sets `W (Nat.pair k n)` witness that `A k` is effectively null. -/
def IsUniformlyEffectivelyNull (μ : Measure CantorSeq) (A : ℕ → Set CantorSeq) : Prop :=
  ∃ W : ℕ → Set CantorSeq, IsUniformlyEffectiveOpen W ∧
    (∀ k, A k ⊆ ⋂ n, W (Nat.pair k n)) ∧
    (∀ k n, μ (W (Nat.pair k n)) ≤ dyadicValue 1 n)

/-- Every member of a uniformly effectively null family is effectively null. -/
lemma IsUniformlyEffectivelyNull.isEffectivelyNull {μ : Measure CantorSeq}
    {A : ℕ → Set CantorSeq} (h : IsUniformlyEffectivelyNull μ A) (k : ℕ) :
    IsEffectivelyNull μ (A k) := by
  obtain ⟨W, ⟨f, hf, hWeq⟩, hsub, hbound⟩ := h
  refine ⟨fun n => W (Nat.pair k n), ⟨fun n i => f (Nat.pair k n) i, ?_, ?_⟩,
    hsub k, fun n => hbound k n⟩
  · have h1 : Computable fun p : ℕ × ℕ => Nat.pair k p.1 :=
      (Primrec₂.natPair.comp (Primrec.const k) Primrec.fst).to_comp
    exact hf.comp h1 (Primrec.snd.to_comp)
  · intro n
    exact hWeq (Nat.pair k n)

/-- The empty set is effectively null for every measure. -/
lemma isEffectivelyNull_empty (μ : Measure CantorSeq) :
    IsEffectivelyNull μ (∅ : Set CantorSeq) := by
  refine ⟨fun _ => ∅, ⟨fun _ _ => none, (Primrec.const none).to_comp, fun _ => by simp⟩,
    Set.empty_subset _, fun n => ?_⟩
  simp

/-- The shifted union family used to combine countably many effectively null
sets. -/
lemma isUniformlyEffectiveOpen_shifted_iUnion {W : ℕ → Set CantorSeq}
    (hW : IsUniformlyEffectiveOpen W) :
    IsUniformlyEffectiveOpen (fun n => ⋃ k, W (Nat.pair k (n + k + 1))) := by
  obtain ⟨f, hf, hWeq⟩ := hW
  refine ⟨fun n i => f (Nat.pair (Nat.unpair i).1 (n + (Nat.unpair i).1 + 1))
      (Nat.unpair i).2, ?_, ?_⟩
  · have h1 : Computable fun p : ℕ × ℕ =>
        Nat.pair (Nat.unpair p.2).1 (p.1 + (Nat.unpair p.2).1 + 1) :=
      (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
        (Primrec.succ.comp (Primrec.nat_add.comp Primrec.fst
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))).to_comp
    have h2 : Computable fun p : ℕ × ℕ => (Nat.unpair p.2).2 :=
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    exact hf.comp h1 h2
  · intro n
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      rw [hWeq] at hk
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hk
      exact ⟨Nat.pair k j, by simpa [Nat.unpair_pair] using hj⟩
    · rintro ⟨i, hi⟩
      refine ⟨(Nat.unpair i).1, ?_⟩
      rw [hWeq]
      exact Set.mem_iUnion.2 ⟨(Nat.unpair i).2, hi⟩

/-- Shifting the levels of a doubly indexed family so that the `k`-th component contributes at
most `2^{-(n+k+1)}` makes the union over `k` have measure at most `2^{-n}`. -/
lemma measure_shifted_iUnion_le {μ : Measure CantorSeq} {W : ℕ → Set CantorSeq}
    (hbound : ∀ k n, μ (W (Nat.pair k n)) ≤ dyadicValue 1 n) (n : ℕ) :
    μ (⋃ k, W (Nat.pair k (n + k + 1))) ≤ dyadicValue 1 n := by
  refine (measure_iUnion_le _).trans ?_
  have hterm : ∀ k, μ (W (Nat.pair k (n + k + 1))) ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + k + 1) := by
    intro k
    simpa [dyadicValue_one_eq_inv_two_pow'] using hbound k (n + k + 1)
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  have hgeom : ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + k + 1)
      = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) * ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k := by
    rw [ENNReal.tsum_mul_left.symm]
    refine tsum_congr fun k => ?_
    rw [← pow_add]
    ring_nf
  rw [hgeom, ENNReal.tsum_geometric, dyadicValue_one_eq_inv_two_pow']
  have h2 : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
    rw [ENNReal.sub_eq_of_eq_add (by simp) ?_]
    · rw [ENNReal.inv_two_add_inv_two]
  rw [h2, pow_succ]
  rw [mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]

/-- The union of a uniformly effectively null family of sets is effectively null.
(This closure property is used in the construction of the universal test of SUV
Theorem 28, which is `exists_universal_martinLof_test`.) -/
theorem IsUniformlyEffectivelyNull.isEffectivelyNull_iUnion {μ : Measure CantorSeq}
    {A : ℕ → Set CantorSeq} (h : IsUniformlyEffectivelyNull μ A) :
    IsEffectivelyNull μ (⋃ k, A k) := by
  obtain ⟨W, hW, hsub, hbound⟩ := h
  refine ⟨fun n => ⋃ k, W (Nat.pair k (n + k + 1)),
    isUniformlyEffectiveOpen_shifted_iUnion hW, ?_,
    fun n => measure_shifted_iUnion_le hbound n⟩
  refine Set.iUnion_subset fun k => ?_
  refine fun x hx => Set.mem_iInter.2 fun n => ?_
  exact Set.mem_iUnion.2 ⟨k, Set.mem_iInter.1 (hsub k hx) (n + k + 1)⟩

/-- The union of two effectively null sets is effectively null. -/
theorem IsEffectivelyNull.union {μ : Measure CantorSeq} {A B : Set CantorSeq}
    (hA : IsEffectivelyNull μ A) (hB : IsEffectivelyNull μ B) :
    IsEffectivelyNull μ (A ∪ B) := by
  obtain ⟨U, ⟨f, hf, hUeq⟩, hAU, hAbound⟩ := hA
  obtain ⟨V, ⟨g, hg, hVeq⟩, hBV, hBbound⟩ := hB
  have huniform : IsUniformlyEffectivelyNull μ (fun k => if k = 0 then A else B) := by
    refine ⟨fun m => if (Nat.unpair m).1 = 0 then U (Nat.unpair m).2 else V (Nat.unpair m).2,
      ⟨fun m i => bif (Nat.unpair m).1 == 0 then f (Nat.unpair m).2 i else g (Nat.unpair m).2 i,
        ?_, ?_⟩, ?_, ?_⟩
    · have hcond : Computable fun p : ℕ × ℕ => (Nat.unpair p.1).1 == 0 :=
        (Primrec.beq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
          (Primrec.const 0)).to_comp
      have hsnd : Computable fun p : ℕ × ℕ => (Nat.unpair p.1).2 :=
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)).to_comp
      exact Computable.cond hcond (hf.comp hsnd Computable.snd) (hg.comp hsnd Computable.snd)
    · intro m
      by_cases hm : (Nat.unpair m).1 = 0
      · simp only [hm, beq_self_eq_true, cond_true]
        exact hUeq _
      · have hbeq : ((Nat.unpair m).1 == 0) = false := beq_eq_false_iff_ne.2 hm
        simp only [hm, hbeq, cond_false]
        exact hVeq _
    · intro k
      by_cases hk : k = 0
      · subst hk
        simpa only [if_pos rfl, Nat.unpair_pair] using hAU
      · simpa only [if_neg hk, Nat.unpair_pair] using hBV
    · intro k n
      by_cases hk : k = 0
      · subst hk
        simpa only [Nat.unpair_pair, if_pos rfl] using hAbound n
      · simpa only [Nat.unpair_pair, if_neg hk] using hBbound n
  refine huniform.isEffectivelyNull_iUnion.mono ?_
  rintro x (hx | hx)
  · exact Set.mem_iUnion.2 ⟨0, by simpa using hx⟩
  · exact Set.mem_iUnion.2 ⟨1, by simpa using hx⟩

/-- The length-`n` prefix of `w`, defined by recursion so that it is manifestly
computable from `w`. -/
def prefixList (w : CantorSeq) : ℕ → BitString
  | 0 => []
  | n + 1 => prefixList w n ++ [w n]

/-- The prefix of length `n + 1` is the prefix of length `n` extended by the `n`-th bit. -/
lemma cantorPrefix_succ (w : CantorSeq) (n : ℕ) :
    cantorPrefix w (n + 1) = cantorPrefix w n ++ [w n] := by
  change (List.ofFn fun i : Fin (n + 1) => w i) = (List.ofFn fun i : Fin n => w i) ++ [w n]
  rw [List.ofFn_succ_last]
  rfl

/-- The list of the first `n` bits of `w` is its length-`n` prefix. -/
lemma prefixList_eq_cantorPrefix (w : CantorSeq) (n : ℕ) :
    prefixList w n = cantorPrefix w n := by
  induction n with
  | zero => simp [prefixList, cantorPrefix]
  | succ k ih => rw [prefixList, ih, cantorPrefix_succ]

/-- The prefixes of a computable sequence form a computable function of their length. -/
lemma computable_prefixList {w : CantorSeq} (hw : Computable w) :
    Computable (prefixList w) := by
  have hstep : Computable (fun q : ℕ × (ℕ × BitString) => q.2.2 ++ [w q.2.1]) :=
    Computable.list_append.comp (Computable.snd.comp Computable.snd)
      (Computable.list_cons.comp (hw.comp (Computable.fst.comp Computable.snd))
        (Computable.const []))
  have hrec : Computable (fun p : ℕ =>
      Nat.rec (motive := fun _ => BitString) ([] : BitString)
        (fun n ih => (fun (_ : ℕ) (q : ℕ × BitString) => q.2 ++ [w q.1]) p (n, ih)) p) :=
    Computable.nat_rec Computable.id (Computable.const []) hstep.to₂
  refine hrec.of_eq (fun n => ?_)
  induction n with
  | zero => rfl
  | succ k ih => simp only [prefixList]; rw [← ih]

/-- A sequence belongs to the cylinder of each of its own prefixes. -/
lemma mem_cantorCylinder_cantorPrefix (w : CantorSeq) (n : ℕ) :
    w ∈ cantorCylinder (cantorPrefix w n) := by
  have h : cantorPrefix w (cantorPrefix w n).length = cantorPrefix w n := by
    rw [cantorPrefix_length]
  exact (isCantorPrefix_iff_cantorPrefix_eq _ w).2 h

/-- The singleton of a computable sequence is effectively null for the uniform
measure: computable sequences are never Martin-Lof random. -/
theorem isEffectivelyNull_singleton_of_computable {w : CantorSeq} (hw : Computable w) :
    IsEffectivelyNull uniformMeasure {w} := by
  refine ⟨fun n => cantorCylinder (cantorPrefix w n),
    ⟨fun n _ => some (prefixList w n), ?_, ?_⟩, ?_, ?_⟩
  · exact (Computable.option_some.comp
      ((computable_prefixList hw).comp Computable.fst)).to₂
  · intro n
    simp only [prefixList_eq_cantorPrefix, Option.elim_some]
    exact (Set.iUnion_const _).symm
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_iInter.2 fun n => mem_cantorCylinder_cantorPrefix x n
  · intro n
    have h : uniformMeasure (cantorCylinder (cantorPrefix w n)) = (2 : ℝ≥0∞)⁻¹ ^ n := by
      have h1 := cantorMass_uniformMeasure (cantorPrefix w n)
      rwa [cantorMass, cantorPrefix_length] at h1
    rw [h, dyadicValue_one_eq_inv_two_pow']

end Kolmogorov
