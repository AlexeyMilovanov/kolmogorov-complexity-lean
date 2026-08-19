import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseTruncation
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.OmegaEquivalence

/-!
# Finite-set symmetry for the add-noise truncation

This file isolates the sound symmetry-of-information contribution to the hard
direction of VS40 `rem:add-noise`.  The canonical first-coordinate truncation
is computable from the original finite-set code.  Plain symmetry of information
therefore bounds the complexity of the truncation plus the information needed
to reconstruct the original model from it.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- The canonical first-coordinate truncation has constant ordinary
conditional complexity given the original canonical finite-set code. -/
theorem finiteSetFstTruncation_condK_from_B
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ (B : Finset BitString) (hB : B.Nonempty),
      condK V
        (codedUniformOn (finiteSetFstTruncation B)
          (finiteSetFstTruncation_nonempty hB)).code
        (codedUniformOn B hB).code ≤
      (C : ENat) := by
  let g : BitString → BitString →. BitString := fun y _p ↦
    Part.some (finiteSetFstTruncationCode y)
  have hg : Partrec (fun q : BitString × BitString ↦ g q.1 q.2) := by
    have h1 : Computable (fun q : BitString × BitString ↦
        finiteSetFstTruncationCode q.1) :=
      finiteSetFstTruncationCode_computable.comp Computable.fst
    exact h1.partrec
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le V hV g hg
  refine ⟨C, fun B hB ↦ ?_⟩
  have h_some :
      finiteSetFstTruncationCode (codedUniformOn B hB).code ∈
        g (codedUniformOn B hB).code [] := ⟨trivial, rfl⟩
  have h_bound := hC (codedUniformOn B hB).code []
    (finiteSetFstTruncationCode (codedUniformOn B hB).code) h_some
  rw [finiteSetFstTruncationCode_codedUniformOn B hB] at h_bound
  simpa using h_bound

/-- Finite-set Kolmogorov–Levin inequality specialized to the canonical
first-coordinate truncation `A` of `B`:
`C(A) + C(B | [A]) ≤ C(B) + O(log N)` whenever `C(B) ≤ N`. -/
theorem finiteSetFstTruncation_plainSetComplexity_symmetry
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (B : Finset BitString) (hB : B.Nonempty) (N : ℕ),
      plainSetComplexity V B hB ≤ (N : ENat) →
      plainSetComplexity V (finiteSetFstTruncation B)
        (finiteSetFstTruncation_nonempty hB) +
        condK V (codedUniformOn B hB).code
          (codedUniformOn (finiteSetFstTruncation B)
            (finiteSetFstTruncation_nonempty hB)).code ≤
      plainSetComplexity V B hB + (logSlack c N : ENat) := by
  obtain ⟨C1, hC1⟩ := plainK_add_condK_symmetry V U hV hU
  obtain ⟨C2, hC2⟩ := finiteSetFstTruncation_condK_from_B V hV
  obtain ⟨C3, hC3⟩ :=
    finiteSetFstTruncation_plainSetComplexity_le V hV
  obtain ⟨C, hC⟩ := logSlack_linear_bound C1 1 (C2 + C3)
  refine ⟨C + C2, fun B hB N hN ↦ ?_⟩
  let A := finiteSetFstTruncation B
  let hA := finiteSetFstTruncation_nonempty hB
  have hA_le : plainSetComplexity V A hA ≤
      plainSetComplexity V B hB + (C3 : ENat) := hC3 B hB
  let N' := N + C2 + C3
  have hA_le_N : plainSetComplexity V A hA ≤ (N' : ENat) := by
    calc
      plainSetComplexity V A hA
          ≤ plainSetComplexity V B hB + (C3 : ENat) := hA_le
      _ ≤ (N : ENat) + (C3 : ENat) := by gcongr
      _ = ((N + C3 : ℕ) : ENat) := by push_cast; rfl
      _ ≤ (N' : ENat) := by exact_mod_cast (by omega)
  have hB_le_N : plainSetComplexity V B hB ≤ (N' : ENat) := by
    calc
      plainSetComplexity V B hB ≤ (N : ENat) := hN
      _ ≤ (N' : ENat) := by exact_mod_cast (by omega)
  have h_cond_le : condK V (codedUniformOn A hA).code
      (codedUniformOn B hB).code ≤ (N' : ENat) := by
    calc
      condK V (codedUniformOn A hA).code (codedUniformOn B hB).code
          ≤ (C2 : ENat) := hC2 B hB
      _ ≤ (N' : ENat) := by exact_mod_cast (by omega)
  have h_symm := hC1 (codedUniformOn B hB).code
    (codedUniformOn A hA).code N' hB_le_N hA_le_N h_cond_le
  have h_arith : (C2 : ENat) + (logSlack C1 N' : ENat) ≤
      (logSlack (C + C2) N : ENat) := by
    have h1 : logSlack C1 N' ≤ logSlack C N := by
      have hh := hC N
      have heq : 1 * N + (C2 + C3) = N' := by omega
      rwa [heq] at hh
    have h2 : (C2 : ENat) + (logSlack C1 N' : ENat) ≤
        (C2 : ENat) + (logSlack C N : ENat) := by gcongr
    have h3 : (C2 : ENat) + (logSlack C N : ENat) ≤
        (logSlack (C + C2) N : ENat) := by
      have h : logSlack C N + C2 ≤ logSlack (C + C2) N :=
        logSlack_add_const_le C C2 N
      exact_mod_cast (by omega)
    exact h2.trans h3
  calc
    plainSetComplexity V A hA +
          condK V (codedUniformOn B hB).code (codedUniformOn A hA).code
        ≤ plainSetComplexity V B hB +
            condK V (codedUniformOn A hA).code (codedUniformOn B hB).code +
            (logSlack C1 N' : ENat) := h_symm
    _ ≤ plainSetComplexity V B hB + (C2 : ENat) +
          (logSlack C1 N' : ENat) := by
        gcongr
        simpa only [A] using hC2 B hB
    _ = plainSetComplexity V B hB +
          ((C2 : ENat) + (logSlack C1 N' : ENat)) := by abel
    _ ≤ plainSetComplexity V B hB +
          (logSlack (C + C2) N : ENat) := by gcongr

end Kolmogorov
