/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.ProbabilisticGenerator
import KolmogorovMathlib.Foundation.PrimrecExtras

/-!
# The copying generator

This module builds the probabilistic generator that copies its fair-coin input
bits directly to the output (SUV Chapter 5, Problem 120), and computes the
continuous tree semimeasure it generates: `a(x) = 2^(-|x|)`.

In particular the defining inequality of a continuous tree semimeasure
`a(x) ≥ a(x0) + a(x1)` is an *equality* here, and the total mass on each level
of the tree is exactly `1`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- Boolean prefix test used to witness computability of the lower graph of the
copying generator: `prefixCheckBool (p, y)` is `true` exactly when `y` is a
prefix of `p`. -/
def prefixCheckBool (q : BitString × BitString) : Bool :=
  decide (q.2 = q.1.take q.2.length)

/-- The Boolean test accepts exactly the pairs whose second component is a prefix of the first. -/
lemma prefixCheckBool_eq_true_iff (q : BitString × BitString) :
    prefixCheckBool q = true ↔ q.2 <+: q.1 := by
  rw [prefixCheckBool, decide_eq_true_iff, List.prefix_iff_eq_take]

/-- The Boolean prefix test is computable. -/
lemma computable_prefixCheckBool : Computable prefixCheckBool := by
  obtain ⟨_, h⟩ : PrimrecPred fun q : BitString × BitString => q.2 = q.1.take q.2.length :=
    Primrec.eq.comp Primrec.snd
      (Primrec.list_take.comp Primrec.fst (Primrec.list_length.comp Primrec.snd))
  exact (h.of_eq fun q => by simp [prefixCheckBool]).to_comp

/-- The lower graph of the copying generator is recursively enumerable. -/
lemma copyLowerGraph_re : IsRE fun q : BitString × BitString => q.2 <+: q.1 :=
  isRE_of_computable_bool _ prefixCheckBool prefixCheckBool_eq_true_iff computable_prefixCheckBool

/-- The generator that copies the fair-coin input sequence to the output. -/
def copyGenerator : ProbabilisticGenerator where
  output w := .infinite w
  lowerGraph p y := y <+: p
  lowerGraph_re := copyLowerGraph_re
  lowerGraph_sound := by
    intro p y hy w hw
    exact BitStream.IsCantorPrefix.of_prefix hy hw
  lowerGraph_complete := by
    intro w y hy
    exact ⟨y, hy, List.prefix_rfl⟩

/-- The inputs on which the copying generator outputs a stream extending `x` form the cylinder of
`x`. -/
@[simp] lemma copyGenerator_preimage (x : BitString) :
    copyGenerator.output ⁻¹' bitStreamCylinder x = cantorCylinder x := rfl

/-- The copying generator generates the uniform (Lebesgue) semimeasure
`a(x) = 2^(-|x|)`. -/
theorem copyGenerator_semimeasure (x : BitString) :
    generatedTreeSemimeasure copyGenerator x = (2 : ℝ≥0∞)⁻¹ ^ x.length := by
  rw [generatedTreeSemimeasure, copyGenerator_preimage, uniformMeasure_cantorCylinder]

/-- For the copying generator the semimeasure inequality is an equality: the
generated semimeasure is a measure on the tree. -/
theorem copyGenerator_children_eq (x : BitString) :
    generatedTreeSemimeasure copyGenerator (x ++ [false])
        + generatedTreeSemimeasure copyGenerator (x ++ [true])
      = generatedTreeSemimeasure copyGenerator x := by
  simp only [copyGenerator_semimeasure, List.length_append, List.length_singleton]
  rw [pow_succ, ← two_mul, ← mul_assoc, mul_comm (2 : ℝ≥0∞) _, mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

/-- There are `2 ^ n` strings of length `n`. -/
lemma card_exactLengthPrograms_toFinset (n : ℕ) :
    (exactLengthPrograms n).toFinset.card = 2 ^ n := by
  rw [List.toFinset_card_of_nodup (exactLengthPrograms_nodup n), length_exactLengthPrograms]

/-- The total mass of the copying generator's semimeasure on level `n` of the
binary tree is exactly `1`. -/
theorem copyGenerator_sum_level_eq_one (n : ℕ) :
    ∑ y ∈ (exactLengthPrograms n).toFinset, generatedTreeSemimeasure copyGenerator y = 1 := by
  have h : ∀ y ∈ (exactLengthPrograms n).toFinset,
      generatedTreeSemimeasure copyGenerator y = (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro y hy
    rw [copyGenerator_semimeasure,
      exactLengthPrograms_length_eq n y (List.mem_toFinset.mp hy)]
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_exactLengthPrograms_toFinset,
    nsmul_eq_mul]
  push_cast
  rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]

/-- Problem 120: although every level has mass exactly one, summing the copying
generator's continuous semimeasure over all finite strings diverges. -/
theorem copyGenerator_tsum_eq_top :
    ∑' x : BitString, generatedTreeSemimeasure copyGenerator x = ⊤ := by
  let levelWords (n : ℕ) := {x // x ∈ (exactLengthPrograms n).toFinset}
  let forgetLevel : (Σ n, levelWords n) → BitString := fun z => z.2.1
  have hinj : Function.Injective forgetLevel := by
    rintro ⟨n, x, hx⟩ ⟨m, y, hy⟩ hxy
    have hn : n = m := by
      have hxlen := exactLengthPrograms_length_eq n x (List.mem_toFinset.mp hx)
      have hylen := exactLengthPrograms_length_eq m y (List.mem_toFinset.mp hy)
      have hlen : x.length = y.length := by
        simpa [forgetLevel] using congrArg List.length hxy
      omega
    subst m
    have hxy' : x = y := by simpa [forgetLevel] using hxy
    subst y
    rfl
  apply top_unique
  calc
    ⊤ = ∑' _n : ℕ, (1 : ℝ≥0∞) :=
      (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ = ∑' n : ℕ, ∑' x : levelWords n,
        generatedTreeSemimeasure copyGenerator x := by
      apply tsum_congr
      intro n
      rw [Finset.tsum_subtype]
      exact (copyGenerator_sum_level_eq_one n).symm
    _ = ∑' z : Σ n, levelWords n,
        generatedTreeSemimeasure copyGenerator z.2 :=
      (ENNReal.tsum_sigma' (fun z : Σ n, levelWords n =>
        generatedTreeSemimeasure copyGenerator z.2)).symm
    _ ≤ ∑' x : BitString, generatedTreeSemimeasure copyGenerator x :=
      ENNReal.tsum_comp_le_tsum_of_injective hinj _

end Kolmogorov
