import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileCardinality
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoise

namespace Kolmogorov

def auxiliaryProfile (P : Set (Nat × Nat)) (mp kp : Nat) : Set (Nat × Nat) :=
  {q | (q.1 ≤ mp ∧ (q.1, q.2 + (kp - mp)) ∈ P) ∨ mp ≤ q.1}

lemma auxiliaryProfile_isAdmissible (P : Set (Nat × Nat)) (kp mp : ℕ)
    (hadm : IsAdmissibleProfileSet P) (_hkP : k_P P = (kp : ENat))
    (hmP : m_P P kp = (mp : ENat)) :
    IsAdmissibleProfileSet (auxiliaryProfile P mp kp) := by
  have hmp_mem : (mp, kp - mp) ∈ P := m_P_mem_of_eq P kp mp hmP
  have hUp : IsUpperSet P := hadm.isUpperSet
  have hstep := hadm.step
  refine ⟨⟨(mp, 0), ?_⟩, ?_, ?_⟩
  · simp [auxiliaryProfile]
  · intro ⟨a1, b1⟩ ⟨a2, b2⟩ hle hmem
    rcases Prod.mk_le_mk.mp hle with ⟨ha, hb⟩
    simp only [auxiliaryProfile, Set.mem_ofPred_eq] at hmem ⊢
    rcases hmem with ⟨ha1_le, hP⟩ | hmp_le
    · rcases Nat.lt_or_ge mp a2 with hlt | hge
      · right; omega
      · left
        refine ⟨by omega, ?_⟩
        apply hUp (Prod.mk_le_mk.mpr ⟨ha, by omega⟩) hP
    · right; omega
  · intro a b c habc
    simp only [auxiliaryProfile, Set.mem_ofPred_eq] at habc ⊢
    rcases habc with ⟨ha_le, hP⟩ | hmp_le
    · rcases Nat.lt_or_ge mp (a + b) with hlt | hge
      · right; omega
      · left
        refine ⟨by omega, ?_⟩
        have hP' : (a, b + (c + (kp - mp))) ∈ P := by
          have heq : b + c + (kp - mp) = b + (c + (kp - mp)) := by omega
          rwa [← heq]
        exact hstep a b (c + (kp - mp)) hP'
    · right; omega

end Kolmogorov
