import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UniformDeficiencyBound
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.OrdinalBits
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CanonicalImage
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FullCube
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardConditional
import KolmogorovMathlib.AlgorithmicStatistics.CodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting

open ENNReal

namespace Kolmogorov

theorem strongModelPairImage_exists
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ x A (hA : A.Nonempty) n epsilon,
      x.length = n → x ∈ A → IsStrongSetModel T x A hA epsilon →
      ∃ (B : Finset BitString) (hB : B.Nonempty),
        strongModelOrdinalBitsPair A hA x ∈ B ∧
        B.card ≤ 2 ^ n ∧
        totalCondK T (codedUniformOn B hB).code
          (codedUniformOn (stringsOfLength n)
            (codedStringsOfLength_nonempty n)).code ≤
          ((epsilon + c : Nat) : ENat) := by
  obtain ⟨c_equiv, hc_equiv⟩ := strong_model_equivalent_fixed_ordinal_pair T hT
  obtain ⟨c_img, hc_img⟩ := totalCondK_canonicalImage_le T hT
  refine ⟨c_equiv + c_img, ?_⟩
  intro x A hA n epsilon hxn hxA hstrong
  have h_eq_within := hc_equiv x A hA epsilon hxA hstrong
  have h_backward : totalCondK T (strongModelOrdinalBitsPair A hA x) x ≤
      (epsilon + c_equiv : ENat) := h_eq_within.2
  have h_total := (totalCondK_le_iff T (strongModelOrdinalBitsPair A hA x) x
    (epsilon + c_equiv)).mp h_backward
  obtain ⟨p, hp_total, hp_len, hp_prod⟩ := h_total
  have h_canon := hc_img hp_total (stringsOfLength n) (codedStringsOfLength_nonempty n)
  obtain ⟨B, hB, hfwd, hback, hcard, hcomp⟩ := h_canon
  have hx_in_S : x ∈ stringsOfLength n := by
    rw [memStringsOfLength]
    exact hxn
  have hy_ex := hfwd x hx_in_S
  obtain ⟨y, hy_in_B, hprod_y⟩ := hy_ex
  have y_eq : y = strongModelOrdinalBitsPair A hA x := Part.mem_unique hprod_y hp_prod
  subst y_eq
  refine ⟨B, hB, hy_in_B, ?_, ?_⟩
  · calc B.card ≤ (stringsOfLength n).card := hcard
      _ = 2 ^ n := by rw [cardStringsOfLength]
  · calc totalCondK T (codedUniformOn B hB).code
          (codedUniformOn (stringsOfLength n) (codedStringsOfLength_nonempty n)).code
      ≤ (programLength p : ENat) + (c_img : ENat) := hcomp
      _ ≤ (epsilon + c_equiv : ENat) + (c_img : ENat) := by
        gcongr
        exact_mod_cast hp_len
      _ = ((epsilon + (c_equiv + c_img) : Nat) : ENat) := by
        exact_mod_cast (show epsilon + c_equiv + c_img = epsilon + (c_equiv + c_img) by omega)

theorem plainK_codedUniformOn_image_le
    (V T : Map) (hV : isOptimalConditional V) (hT : isDecompressor T) :
    ∃ c : Nat, ∀ n (B : Finset BitString) (hB : B.Nonempty) (m : Nat),
      totalCondK T (codedUniformOn B hB).code
        (codedUniformOn (stringsOfLength n)
          (codedStringsOfLength_nonempty n)).code ≤ (m : ENat) →
      plainK V (codedUniformOn B hB).code ≤ ((m + logSlack c n : Nat) : ENat) := by
  obtain ⟨cCube, hCube⟩ := plainSetComplexity_fullCube_le_logSlack V hV
  obtain ⟨cSim, hSim⟩ := hV.2 T hT
  obtain ⟨cTwo, hTwo⟩ := plainK_two_stage V hV
  let c := 3 * cCube + cSim + cTwo
  refine ⟨c, ?_⟩
  intro n B hB m hcomp
  have hcub : plainK V (codedUniformOn (stringsOfLength n)
      (codedStringsOfLength_nonempty n)).code ≤ ((logSlack cCube n : Nat) : ENat) := by
    exact hCube n
  have hcond : condK V (codedUniformOn B hB).code
      (codedUniformOn (stringsOfLength n) (codedStringsOfLength_nonempty n)).code ≤
      ((m + cSim : Nat) : ENat) := by
    calc condK V (codedUniformOn B hB).code
          (codedUniformOn (stringsOfLength n) (codedStringsOfLength_nonempty n)).code
        ≤ condK T (codedUniformOn B hB).code
            (codedUniformOn (stringsOfLength n) (codedStringsOfLength_nonempty n)).code
            + (cSim : ENat) := hSim _ _
      _ ≤ totalCondK T (codedUniformOn B hB).code
            (codedUniformOn (stringsOfLength n) (codedStringsOfLength_nonempty n)).code
            + (cSim : ENat) := by
        gcongr
        exact condK_le_totalCondK T _ _
      _ ≤ (m : ENat) + (cSim : ENat) := by gcongr
      _ = ((m + cSim : Nat) : ENat) := by push_cast; rfl
  have hraw := hTwo (codedUniformOn B hB).code
    (codedUniformOn (stringsOfLength n) (codedStringsOfLength_nonempty n)).code
    (logSlack cCube n) (m + cSim) hcub hcond
  refine hraw.trans ?_
  have hbits : (Nat.bits (logSlack cCube n)).length ≤ logSlack cCube n := length_natBits_le_self _
  unfold logSlack at hbits ⊢
  exact_mod_cast (show
    (cCube * (Nat.bits n).length + cCube) + (m + cSim) +
      2 * (Nat.bits (cCube * (Nat.bits n).length + cCube)).length + cTwo ≤
      m + (c * (Nat.bits n).length + c) by
    generalize hl : (Nat.bits (cCube * (Nat.bits n).length + cCube)).length = l at hbits ⊢
    dsimp [c]
    rw [add_mul, add_mul, Nat.mul_assoc]
    omega)

end Kolmogorov
