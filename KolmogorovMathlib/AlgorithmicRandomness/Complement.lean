import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveLaws

/-!
# Bit-complement conservation (SUV Chapter 3, Problem 81)

Flipping every bit of a sequence preserves Martin-Löf randomness with respect to
the uniform measure on Cantor space.

The argument goes through the Solovay-test characterisation
`not_isMartinLofRandom_iff_solovay_test`.  The complement map on Cantor space is
an involution which sends the cylinder `cantorCylinder s` onto
`cantorCylinder (s.map not)`, and the uniform mass of a cylinder depends only on
the length of its defining string.  Hence complementing every string of a
Solovay test yields another Solovay test with exactly the same total mass and
exactly the same set of hit indices.

Main declarations:

* `Kolmogorov.complementSeq` — the bitwise complement of a Cantor sequence.
* `Kolmogorov.isMartinLofRandom_uniform_complement` — complementing preserves
  uniform ML-randomness.
* `Kolmogorov.isMartinLofRandom_uniform_complement_iff` — the two-sided form.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-- The bitwise complement of a Cantor sequence. -/
def complementSeq (x : CantorSeq) : CantorSeq := fun n => !x n

/-- The bitwise complement of a sequence flips the bit at every position. -/
@[simp] lemma complementSeq_apply (x : CantorSeq) (n : ℕ) :
    complementSeq x n = !x n := rfl

/-- Bitwise complementation of Cantor sequences is an involution. -/
@[simp] lemma complementSeq_complementSeq (x : CantorSeq) :
    complementSeq (complementSeq x) = x := by
  funext n; simp

/-- Complementing the bits of a string maps the corresponding cylinder onto the
cylinder of the complemented string. -/
lemma mem_cantorCylinder_complementSeq (s : BitString) (x : CantorSeq) :
    complementSeq x ∈ cantorCylinder s ↔ x ∈ cantorCylinder (s.map not) := by
  constructor
  · intro h i hi
    have hi' : i < s.length := by simpa using hi
    have hxi := h i hi'
    simp only [complementSeq_apply] at hxi
    rw [List.getElem_map]
    cases hb : x i <;> rw [hb] at hxi <;> simp_all
  · intro h i hi
    have hi' : i < (s.map not).length := by simpa using hi
    have hxi := h i hi'
    rw [List.getElem_map] at hxi
    simp only [complementSeq_apply]
    cases hb : x i <;> rw [hb] at hxi <;> simp_all

/-- Complementing every bit of a string leaves its uniform cylinder mass
unchanged. -/
lemma cantorMass_uniformMeasure_map_not (s : BitString) :
    cantorMass uniformMeasure (s.map not) = cantorMass uniformMeasure s := by
  rw [cantorMass_uniformMeasure, cantorMass_uniformMeasure, List.length_map]

/-- Complementing every bit of a list of booleans is primitive recursive. -/
lemma primrec_map_not : Primrec (fun l : BitString => l.map not) :=
  Primrec.list_map Primrec.id (Primrec₂.mk ((Primrec.dom_bool _).comp Primrec.snd))

/-- Complementing a Solovay test string by string preserves computability. -/
lemma computable_complementTest {f : ℕ → Option BitString} (hf : Computable f) :
    Computable (fun i => (f i).map (List.map not)) :=
  Computable.option_map hf (primrec_map_not.comp Primrec.snd).to₂.to_comp

/-- **SUV Chapter 3, Problem 81.** Flipping every bit of a uniformly ML-random
sequence yields a uniformly ML-random sequence. -/
theorem isMartinLofRandom_uniform_complement {x : CantorSeq}
    (hx : IsMartinLofRandom uniformMeasure x) :
    IsMartinLofRandom uniformMeasure (complementSeq x) := by
  by_contra hnot
  rw [not_isMartinLofRandom_iff_solovay_test isComputableMeasure_uniform] at hnot
  obtain ⟨f, hfc, hfsum, hfinf⟩ := hnot
  have hxnot : ¬ IsMartinLofRandom uniformMeasure x := by
    rw [not_isMartinLofRandom_iff_solovay_test isComputableMeasure_uniform]
    refine ⟨fun i => (f i).map (List.map not), computable_complementTest hfc, ?_, ?_⟩
    · refine lt_of_le_of_lt (le_of_eq ?_) hfsum
      refine tsum_congr fun i => ?_
      cases hfi : f i with
      | none => simp [hfi]
      | some s => simp [hfi, cantorMass_uniformMeasure_map_not]
    · refine hfinf.mono ?_
      intro i hi
      simp only [Set.mem_setOf_eq] at hi ⊢
      cases hfi : f i with
      | none => rw [hfi] at hi; simp at hi
      | some s =>
          rw [hfi] at hi
          simp only [Option.elim_some] at hi
          simp only [Option.map_some, Option.elim_some]
          exact (mem_cantorCylinder_complementSeq s x).1 hi
  exact hxnot hx

/-- The two-sided form of Problem 81: a sequence is uniformly ML-random iff its
bitwise complement is. -/
theorem isMartinLofRandom_uniform_complement_iff (x : CantorSeq) :
    IsMartinLofRandom uniformMeasure (complementSeq x) ↔
      IsMartinLofRandom uniformMeasure x := by
  refine ⟨fun h => ?_, isMartinLofRandom_uniform_complement⟩
  simpa using isMartinLofRandom_uniform_complement h

end Kolmogorov
