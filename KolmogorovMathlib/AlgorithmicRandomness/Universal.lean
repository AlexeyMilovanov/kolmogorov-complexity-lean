import KolmogorovMathlib.AlgorithmicRandomness.Enumeration
import KolmogorovMathlib.AlgorithmicRandomness.Trim

/-!
# The largest effectively null set

Combining the effective enumeration of all uniformly effective open families
(`candEnum`), the disjointification (`disjEnum`) and the trimming construction
(`trimEnum`), we build a single uniformly effective open family `univSet a`
that contains, at the appropriate index, every effectively null set.

This is the construction behind SUV Theorem 28.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- The `m`-th candidate family: the `m`-th effectively open set, disjointified
and trimmed so that its measure is at most `2⁻ⁿ`, where `n = (unpair m).2`. -/
def univEnum (a : BitString → ℕ → ℕ) (m : ℕ) (k : ℕ) : Option BitString :=
  trimEnum (disjEnum (candEnum m))
    (trimWeight a (disjEnum (candEnum m)) (Nat.unpair m).2) k

/-- The effectively open set enumerated by `univEnum a m`. -/
def univSet (a : BitString → ℕ → ℕ) (m : ℕ) : Set CantorSeq :=
  ⋃ k, coverSet (univEnum a m) k

/-- Disjointifying the candidate enumeration keeps it computable in the index and the stage. -/
lemma computable₂_disjCandEnum : Computable₂ (fun m i => disjEnum (candEnum m) i) :=
  computable_disjEnum computable₂_candEnum

/-- The enumeration underlying the universal test is computable whenever the measure
approximation it is built from is. -/
lemma computable₂_univEnum {a : BitString → ℕ → ℕ} (ha : Computable₂ a) :
    Computable₂ (univEnum a) := by
  have hL : Computable (fun m : ℕ => (Nat.unpair m).2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp
  exact computable_trimEnum computable₂_disjCandEnum
    (computable_trimWeight ha computable₂_disjCandEnum hL)

/-- The sets enumerated by the universal construction form a uniformly effectively open
family. -/
lemma isUniformlyEffectiveOpen_univSet {a : BitString → ℕ → ℕ} (ha : Computable₂ a) :
    IsUniformlyEffectiveOpen (univSet a) :=
  ⟨univEnum a, computable₂_univEnum ha, fun _ => rfl⟩

variable {μ : Measure CantorSeq}

/-- The `m`-th set of the universal construction has measure at most `2^{-k}`, where `k` is the
second component of the pairing of `m`. -/
lemma measure_univSet_le {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s) (m : ℕ) :
    μ (univSet a m) ≤ dyadicValue 1 (Nat.unpair m).2 :=
  measure_iUnion_trimEnum_le ha (disjEnum (candEnum m)) (Nat.unpair m).2

/-- If the `m`-th candidate set is small enough, trimming leaves it unchanged. -/
lemma univSet_eq_of_measure_le {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s) {m : ℕ}
    (hsmall : μ (⋃ j, coverSet (candEnum m) j) ≤ (2 : ℝ≥0∞)⁻¹ ^ ((Nat.unpair m).2 + 2)) :
    univSet a m = ⋃ j, coverSet (candEnum m) j := by
  have htsum : (∑' j, (disjEnum (candEnum m) j).elim 0 (cantorMass μ))
      ≤ (2 : ℝ≥0∞)⁻¹ ^ ((Nat.unpair m).2 + 2) := by
    rw [tsum_measure_disjEnum]
    exact hsmall
  have heq : ∀ k, univEnum a m k = disjEnum (candEnum m) k := fun k =>
    trimEnum_eq_self_of_tsum_le ha htsum k
  unfold univSet
  calc (⋃ k, coverSet (univEnum a m) k) = ⋃ k, coverSet (disjEnum (candEnum m)) k := by
        refine Set.iUnion_congr fun k => ?_
        rw [coverSet, coverSet, heq k]
    _ = ⋃ j, coverSet (candEnum m) j := coverSet_disjEnum_iUnion _

/-- The candidate universal test. -/
def universalTest (a : BitString → ℕ → ℕ) (n : ℕ) : Set CantorSeq :=
  ⋃ k, univSet a (Nat.pair k (n + k + 1))

/-- The levels of the universal Martin-Löf test form a uniformly effectively open family. -/
lemma isUniformlyEffectiveOpen_universalTest {a : BitString → ℕ → ℕ} (ha : Computable₂ a) :
    IsUniformlyEffectiveOpen (universalTest a) :=
  isUniformlyEffectiveOpen_shifted_iUnion (isUniformlyEffectiveOpen_univSet ha)

/-- The `n`-th level of the universal Martin-Löf test has measure at most `2^{-n}`. -/
lemma measure_universalTest_le {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s) (n : ℕ) :
    μ (universalTest a n) ≤ dyadicValue 1 n := by
  have hbound : ∀ k n, μ (univSet a (Nat.pair k n)) ≤ dyadicValue 1 n := by
    intro k n
    have h := measure_univSet_le ha (Nat.pair k n)
    rwa [Nat.unpair_pair] at h
  exact measure_shifted_iUnion_le hbound n

end Kolmogorov
