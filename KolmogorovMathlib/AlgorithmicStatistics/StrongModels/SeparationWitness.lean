import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoiseHalfPlane
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.NoiseAssembly
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AntistochasticExistence
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.NormalPair
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CylinderRealization
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SeparationCylinderTotal
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.HereditaryAssembly

namespace Kolmogorov

open Encodable

lemma antistochastic_plainProfile_close_to_upperRegion (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (n k epsilon : Nat) (y : BitString),
      IsAntistochastic V n k epsilon y →
      ProfileSetsWithinNeighborhood
        (plainDescriptionProfileSet V y)
        {q | k ≤ q.1 ∨ n ≤ q.1 + q.2}
        (epsilon + logSlack c n) := by
  obtain ⟨cCylinder, hCylinder⟩ :=
    plainSetComplexity_cylinder_le V hV
  obtain ⟨cSingleton, hSingleton⟩ :=
    plainSetComplexity_singleton_le_plainK V hV
  obtain ⟨cLength, hLength⟩ := plainKLeLength V hV
  let c := cCylinder + cSingleton + cLength + 1
  refine ⟨c, ?_⟩
  intro n k epsilon y hAnti
  have hyLength : y.length = n := hAnti.1
  have hyComplexity : plainK V y = (k : ENat) := hAnti.2.1
  constructor
  · rintro ⟨i, j⟩ hij
    rcases hAnti.2.2 i j hij with hRight | hAbove
    · refine ⟨(max i k, j), ?_, ?_⟩
      · exact Or.inl (Nat.le_max_right i k)
      · unfold natPairLInfDistance
        apply max_le
        · omega
        · omega
    · refine ⟨(i, j + epsilon), ?_, ?_⟩
      · exact Or.inr (by omega)
      · unfold natPairLInfDistance
        apply max_le <;> omega
  · rintro ⟨i, j⟩ (hRight | hAbove)
    · let hS : ({y} : Finset BitString).Nonempty :=
        Finset.singleton_nonempty y
      refine ⟨(i + cSingleton, j), ?_, ?_⟩
      · refine ⟨{y}, hS, Finset.mem_singleton.mpr rfl, ?_, Nat.one_le_two_pow⟩
        calc
          plainSetComplexity V {y} hS
              ≤ plainK V y + (cSingleton : ENat) := hSingleton y
          _ = ((k + cSingleton : Nat) : ENat) := by
            rw [hyComplexity]
            norm_cast
          _ ≤ ((i + cSingleton : Nat) : ENat) := by
            exact_mod_cast (show k + cSingleton ≤ i + cSingleton by omega)
      · have hSlack : cSingleton ≤ logSlack c n := by
          unfold logSlack
          dsimp [c]
          omega
        unfold natPairLInfDistance
        apply max_le <;> omega
    · by_cases hin : i ≤ n
      · let u := y.take i
        have huLength : u.length = i := by
          dsimp [u]
          simp [hyLength, hin]
        have hu : u.length ≤ n := by omega
        have hyu : y ∈ cylinder n u := by
          rw [mem_cylinder]
          exact ⟨hyLength, List.take_prefix i y⟩
        let j' := max j (n - i)
        refine ⟨(i + logSlack cCylinder n, j'), ?_, ?_⟩
        · refine ⟨cylinder n u, ⟨y, hyu⟩, hyu, ?_, ?_⟩
          · have hPlain := hCylinder n u y hu hyu
            rw [huLength] at hPlain
            simpa only [Nat.cast_add] using hPlain
          · rw [cylinder_card n u hu, huLength]
            exact Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _)
        · have hCylinderSlack :
              logSlack cCylinder n ≤ logSlack c n :=
            logSlack_mono_left (by
              dsimp [c]
              omega) n
          unfold natPairLInfDistance
          apply max_le <;> omega
      · let hS : ({y} : Finset BitString).Nonempty :=
          Finset.singleton_nonempty y
        refine ⟨(i + cLength + cSingleton, j), ?_, ?_⟩
        · refine ⟨{y}, hS, Finset.mem_singleton.mpr rfl, ?_, Nat.one_le_two_pow⟩
          calc
            plainSetComplexity V {y} hS
                ≤ plainK V y + (cSingleton : ENat) := hSingleton y
            _ ≤ ((n + cLength + cSingleton : Nat) : ENat) := by
              calc
                plainK V y + (cSingleton : ENat)
                    ≤ ((y.length : Nat) : ENat) + (cLength : ENat) +
                        (cSingleton : ENat) := add_le_add (hLength y) le_rfl
                _ = ((n + cLength + cSingleton : Nat) : ENat) := by
                  rw [hyLength]
                  rfl
            _ ≤ ((i + cLength + cSingleton : Nat) : ENat) := by
              exact_mod_cast (show n + cLength + cSingleton ≤
                i + cLength + cSingleton by omega)
        · have hSlack : cLength + cSingleton ≤ logSlack c n := by
            unfold logSlack
            dsimp [c]
            omega
          unfold natPairLInfDistance
          apply max_le <;> omega

lemma separationGrayProfile_admissible (k : Nat) :
    IsAdmissibleProfileSet (separationGrayProfile k) := by
  refine ⟨⟨(3 * k, 0), (separationGrayProfile_endpoints k).2.2⟩,
    separationGrayProfile_isUpperSet k, ?_⟩
  intro a b c hab
  unfold separationGrayProfile at hab ⊢
  rcases hab with hab | hab
  · by_cases hle : a + b ≤ k
    · exact Or.inl ⟨hle, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

lemma k_P_separationGrayProfile (k : Nat) :
    k_P (separationGrayProfile k) = ((3 * k : Nat) : ENat) := by
  apply le_antisymm
  · apply sInf_le
    exact ⟨3 * k, rfl, (separationGrayProfile_endpoints k).2.2⟩
  · apply le_sInf
    rintro _ ⟨t, rfl, ht⟩
    unfold separationGrayProfile at ht
    change (t ≤ k ∧ 4 * k ≤ t + 0) ∨
      (k ≤ t ∧ 3 * k ≤ t + 0) at ht
    exact_mod_cast (show 3 * k ≤ t by omega)

lemma m_P_separationGrayProfile (k : Nat) :
    m_P (separationGrayProfile k) (3 * k) = (k : ENat) := by
  apply le_antisymm
  · apply sInf_le
    exact ⟨k, rfl, by
      have hsub : 3 * k - k = 2 * k := by omega
      rw [hsub]
      exact (separationGrayProfile_endpoints k).2.1⟩
  · apply le_sInf
    rintro _ ⟨t, rfl, ht⟩
    unfold separationGrayProfile at ht
    change (t ≤ k ∧ 4 * k ≤ t + (3 * k - t)) ∨
      (k ≤ t ∧ 3 * k ≤ t + (3 * k - t)) at ht
    exact_mod_cast (show k ≤ t by omega)

lemma auxiliaryProfile_separationGrayProfile (k : Nat) :
    auxiliaryProfile (separationGrayProfile k) k (3 * k) =
      {q : Nat × Nat | k ≤ q.1 ∨ 2 * k ≤ q.1 + q.2} := by
  ext ⟨i, j⟩
  simp only [auxiliaryProfile, separationGrayProfile, Set.mem_ofPred_eq]
  omega

lemma upperRegion_breakpoint_near (n k k' e : Nat)
    (hkk' : k ≤ k' + e) (hk'k : k' ≤ k + e) :
    ProfileSetsWithinNeighborhood
      {q : Nat × Nat | k ≤ q.1 ∨ n ≤ q.1 + q.2}
      {q : Nat × Nat | k' ≤ q.1 ∨ n ≤ q.1 + q.2} e := by
  constructor
  · rintro ⟨i, j⟩ (hi | hij)
    · refine ⟨(max i k', j), Or.inl (Nat.le_max_right _ _), ?_⟩
      unfold natPairLInfDistance
      apply max_le <;> omega
    · exact ⟨(i, j), Or.inr hij, by simp [natPairLInfDistance]⟩
  · rintro ⟨i, j⟩ (hi | hij)
    · refine ⟨(max i k, j), Or.inl (Nat.le_max_right _ _), ?_⟩
      unfold natPairLInfDistance
      apply max_le <;> omega
    · exact ⟨(i, j), Or.inr hij, by simp [natPairLInfDistance]⟩

lemma addNoiseProfileTransform_antistochastic_eq_separationGrayProfile :
    ∀ k : Nat,
      AddNoiseProfileTransform {q : Nat × Nat | k ≤ q.1 ∨ 2 * k ≤ q.1 + q.2} k (3 * k) (2 * k) =
      separationGrayProfile k := by
  intro k
  ext q
  simp only [AddNoiseProfileTransform, separationGrayProfile, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨i, j, hik, hanti, rfl⟩ | ⟨hki, hsum⟩)
    · rcases hanti with hki | hsum
      · right
        constructor <;> omega
      · left
        constructor <;> omega
    · right
      constructor <;> omega
  · rintro (⟨hqk, hsum⟩ | ⟨hkq, hsum⟩)
    · left
      refine ⟨q.1, q.2 - 2 * k, hqk, Or.inr ?_, ?_⟩
      · omega
      · apply Prod.ext
        · simp
        · simp only
          omega
    · by_cases hq : q.1 = k
      · left
        refine ⟨k, q.2 - 2 * k, le_rfl, Or.inl le_rfl, ?_⟩
        apply Prod.ext
        · simpa
        · simp only
          omega
      · right
        exact ⟨by omega, hsum⟩

lemma hereditaryStrongTransportStrength_logSlack_absorb (c a b : Nat) :
    ∃ C : Nat, ∀ n : Nat,
      hereditaryStrongTransportStrength c (logSlack a n) (logSlack b n) ≤ logSlack C n := by
  obtain ⟨bAB, hAB⟩ := logSlack_le_add_const (a + b)
  obtain ⟨cOuter₁, hOuter₁⟩ := logSlack_linear_bound c 1 bAB
  let cFirst := a + b + cOuter₁
  let cArg := cFirst + a + c
  obtain ⟨bArg, hArg⟩ := logSlack_le_add_const cArg
  obtain ⟨cOuter₂, hOuter₂⟩ := logSlack_linear_bound c 1 bArg
  let C := cArg + cOuter₂
  refine ⟨C, ?_⟩
  intro n
  let e := logSlack a n
  let s := logSlack b n
  let first := e + s + logSlack c (e + s)
  have hes : e + s = logSlack (a + b) n := by
    dsimp [e, s]
    exact logSlack_add_const a b n
  have hNested₁ : logSlack c (e + s) ≤ logSlack cOuter₁ n := by
    rw [hes]
    calc
      logSlack c (logSlack (a + b) n)
          ≤ logSlack c (n + bAB) :=
        logSlack_mono_right c (hAB n)
      _ = logSlack c (1 * n + bAB) := by rw [one_mul]
      _ ≤ logSlack cOuter₁ n := hOuter₁ n
  have hFirst : first ≤ logSlack cFirst n := by
    dsimp [first]
    calc
      e + s + logSlack c (e + s)
          ≤ logSlack (a + b) n + logSlack cOuter₁ n := by
        rw [hes]
        gcongr
        simpa [hes] using hNested₁
      _ = logSlack cFirst n := by
        dsimp [cFirst]
        rw [logSlack_add_const]
  have hInner : first + e + c ≤ logSlack cArg n := by
    calc
      first + e + c
          ≤ logSlack cFirst n + logSlack a n + c := by
        dsimp [e]
        omega
      _ = logSlack (cFirst + a) n + c := by
        rw [logSlack_add_const]
      _ ≤ logSlack cArg n := by
        dsimp [cArg]
        exact logSlack_add_const_le (cFirst + a) c n
  have hNested₂ : logSlack c (first + e + c) ≤ logSlack cOuter₂ n := by
    calc
      logSlack c (first + e + c)
          ≤ logSlack c (logSlack cArg n) :=
        logSlack_mono_right c hInner
      _ ≤ logSlack c (n + bArg) :=
        logSlack_mono_right c (hArg n)
      _ = logSlack c (1 * n + bArg) := by rw [one_mul]
      _ ≤ logSlack cOuter₂ n := hOuter₂ n
  have hNested₂' :
      logSlack c (first + (e + c)) ≤ logSlack cOuter₂ n := by
    simpa [Nat.add_assoc] using hNested₂
  change first + (e + c) + logSlack c (first + e + c) ≤ logSlack C n
  calc
    first + (e + c) + logSlack c (first + e + c)
        ≤ logSlack cFirst n + (logSlack a n + c) +
            logSlack cOuter₂ n := by
      dsimp [e]
      exact Nat.add_le_add
        (Nat.add_le_add hFirst le_rfl)
        (by simpa [e, Nat.add_assoc] using hNested₂')
    _ = (logSlack (cFirst + a) n + c) + logSlack cOuter₂ n := by
      rw [← Nat.add_assoc, logSlack_add_const]
    _ ≤ logSlack cArg n + logSlack cOuter₂ n := by
      gcongr
      dsimp [cArg]
      exact logSlack_add_const_le (cFirst + a) c n
    _ = logSlack C n := by
      dsimp [C]
      rw [logSlack_add_const]

private lemma noiseProfileRadius_logSlack_bound (p a b n : Nat) :
    p * (3 * logSlack a n + logSlack b n) + logSlack p n ≤
      logSlack (3 * p * a + p * b + p) n := by
  unfold logSlack
  nlinarith [Nat.zero_le ((Nat.bits n).length)]

private lemma normalPairDelta_logSlack_bound (p a q n : Nat) :
    p * (logSlack a n + q) + logSlack p n ≤
      logSlack (p * a + p * q + p) n := by
  have hEq :
      logSlack (p * a + p * q + p) n =
        p * (logSlack a n + q) + logSlack p n +
          p * q * (Nat.bits n).length := by
    unfold logSlack
    ring
  rw [hEq]
  exact Nat.le_add_right _ _

private lemma normalTransportDelta_logSlack_bound (a b c d n : Nat) :
    (2 * logSlack a n + c) + logSlack b n +
        (2 * logSlack a n + d) ≤
      logSlack (4 * a + c + b + d) n := by
  unfold logSlack
  nlinarith [Nat.zero_le ((Nat.bits n).length)]

lemma exists_separation_witness_core
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ cSlack : Nat, ∀ k : Nat, 0 < k →
      ∃ y z : BitString,
        let x := y ++ z
        let A := cylinder (4 * k) y
        y.length = 2 * k ∧
        z.length = 2 * k ∧
        x.length = 4 * k ∧
        ProfileSetsWithinNeighborhood
          (plainDescriptionProfileSet V x)
          (separationGrayProfile k)
          (logSlack cSlack (4 * k)) ∧
        IsNormalString V T x
          (logSlack cSlack (4 * k))
          (logSlack cSlack (4 * k)) ∧
        ∃ hA : A.Nonempty,
        x ∈ A ∧
        IsStrongSetModel T x A hA (logSlack cSlack (4 * k)) ∧
        (k : ENat) ≤ plainSetComplexity V A hA + (logSlack cSlack (4 * k) : ENat) ∧
        plainSetComplexity V A hA ≤ (k + logSlack cSlack (4 * k) : ENat) ∧
        finiteSetLogCard A = 2 * k ∧
        TotalEquivalentWithin T y (codedUniformOn A hA).code
          (logSlack cSlack (4 * k)) := by
  classical
  let U : Map := Classical.choose exists_isOptimalPrefixConditional
  have hU : IsOptimalPrefixConditional U :=
    Classical.choose_spec exists_isOptimalPrefixConditional
  obtain ⟨cHead, hHead⟩ := exists_normal_antistochastic V T hV hT
  obtain ⟨cAnti, hAnti⟩ :=
    antistochastic_plainProfile_close_to_upperRegion V hV
  obtain ⟨cNoise, hNoise⟩ := exists_noise_finset_near_profile V U hV hU
  obtain ⟨cPairNormal, hPairNormal⟩ :=
    normal_pair_of_conditionally_random_tail V U T hV hU hT
  obtain ⟨cPairEq, hPairEq⟩ :=
    fixedSplit_append_pairCode_totalEquivalent T hT
  obtain ⟨cPlainEq, hPlainEq⟩ :=
    totalEquivalentWithin_plainProfiles V T hV hT
  obtain ⟨cNormPlain, cNormStrong, hNormTransport⟩ :=
    normality_of_totalEquivalentWithin V T hV hT
  let cPairStrength := cHead + cPairNormal
  let cPairDelta :=
    cPairNormal * cHead + cPairNormal * cNoise + cPairNormal
  obtain ⟨cNormStrength, hNormStrength⟩ :=
    hereditaryStrongTransportStrength_logSlack_absorb
      cNormStrong cPairEq cPairStrength
  let cNormDelta :=
    4 * cPairEq + cNormPlain + cPairDelta + cNormStrong
  let cPairProfile :=
    3 * cNoise * cHead + cNoise * cAnti + cNoise
  let cProfile := cPairProfile + 2 * cPairEq + cPlainEq
  obtain ⟨cCylinderStrong, hCylinderStrong⟩ :=
    cylinder_isStrongSetModel T hT
  obtain ⟨cCylinderEq, hCylinderEq⟩ :=
    separationCylinder_totalEquivalent_prefix T hT
  obtain ⟨cSim, hSim⟩ := hV.2 T hT.1
  obtain ⟨cGap, hGap⟩ := plainK_forward_gap_of_condK V hV
  obtain ⟨bHead, hbHead⟩ := logSlack_le_add_const cHead
  obtain ⟨cGapUp, hGapUp⟩ := logSlack_linear_bound cGap 2 bHead
  let cAUpper := cHead + cCylinderEq + cSim + cGapUp
  obtain ⟨bAUpper, hbAUpper⟩ := logSlack_le_add_const cAUpper
  obtain ⟨cGapLow, hGapLow⟩ :=
    logSlack_linear_bound cGap 2 bAUpper
  let cALower := cHead + cCylinderEq + cSim + cGapLow
  let cSlack := cNormStrength + cNormDelta + cProfile +
    cCylinderStrong + cCylinderEq + cAUpper + cALower + 1
  refine ⟨cSlack, ?_⟩
  intro k hk
  set N := 4 * k with hN
  have hk2 : k < 2 * k := by omega
  obtain ⟨y, kx, hyLength, hyAnti, hkLower, hkUpper, hyNormal⟩ :=
    hHead (2 * k) k hk2
  set headSlack := logSlack cHead (2 * k) with hHeadSlack
  have hkLower' : k ≤ kx + headSlack := by simpa [headSlack] using hkLower
  have hkUpper' : kx ≤ k + headSlack := by simpa [headSlack] using hkUpper
  have hHeadRegion :=
    hAnti (2 * k) kx headSlack y (by simpa [headSlack] using hyAnti)
  have hBreak :=
    upperRegion_breakpoint_near (2 * k) kx k headSlack hkUpper' hkLower'
  set headRadius := 2 * headSlack + logSlack cAnti (2 * k) with hHeadRadius
  have hHeadAux :
      ProfileSetsWithinNeighborhood
        (plainDescriptionProfileSet V y)
        (auxiliaryProfile (separationGrayProfile k) k (3 * k))
        headRadius := by
    rw [auxiliaryProfile_separationGrayProfile]
    refine (hHeadRegion.trans hBreak).mono ?_
    dsimp [headRadius]
    omega
  have hyComplexity : plainK V y = (kx : ENat) := hyAnti.2.1
  obtain ⟨R, hRne, hRmem, _hRcard⟩ :=
    hNoise (separationGrayProfile k) (3 * k) k y
      headRadius headSlack kx
      (separationGrayProfile_admissible k)
      (k_P_separationGrayProfile k)
      (m_P_separationGrayProfile k)
      hyComplexity hkUpper' hkLower' hHeadAux
  obtain ⟨z, hzR⟩ := hRne
  obtain ⟨hzLength, hzRandom, hPairProfile⟩ := hRmem z hzR
  have hzLength' : z.length = 2 * k := by omega
  have hxyLength : (y ++ z).length = N := by
    rw [List.length_append, hyLength, hzLength']
    dsimp [N]
    ring
  have hNsum : y.length + z.length = N := by
    rw [hyLength, hzLength']
    dsimp [N]
    ring
  have hHeadSlackN : headSlack ≤ logSlack cHead N := by
    dsimp [headSlack, N]
    exact logSlack_mono_right cHead (by omega)
  have hAntiSlackN :
      logSlack cAnti (2 * k) ≤ logSlack cAnti N := by
    dsimp [N]
    exact logSlack_mono_right cAnti (by omega)
  have hPairProfileRadius :
      cNoise * (headRadius + headSlack) +
          logSlack cNoise (y.length + (3 * k - k)) ≤
        logSlack cPairProfile N := by
    rw [hyLength]
    have hsub : 3 * k - k = 2 * k := by omega
    rw [hsub]
    have hsum : 2 * k + 2 * k = N := by dsimp [N]; ring
    rw [hsum]
    calc
      cNoise * (headRadius + headSlack) + logSlack cNoise N
          ≤ cNoise *
              (3 * logSlack cHead N + logSlack cAnti N) +
                logSlack cNoise N := by
            apply Nat.add_le_add_right
            apply Nat.mul_le_mul_left
            dsimp [headRadius]
            omega
      _ ≤ logSlack cPairProfile N := by
        dsimp [cPairProfile]
        exact noiseProfileRadius_logSlack_bound cNoise cHead cAnti N
  have hPairProfile' :
      ProfileSetsWithinNeighborhood
        (plainDescriptionProfileSet V (pairCode y z))
        (separationGrayProfile k)
        (logSlack cPairProfile N) :=
    hPairProfile.mono hPairProfileRadius
  have hAppendPair := hPairEq y z
  rw [hNsum] at hAppendPair
  have hAppendPairProfile := hPlainEq (y ++ z) (pairCode y z)
    (logSlack cPairEq N) hAppendPair
  have hEqProfileRadius :
      2 * logSlack cPairEq N + cPlainEq ≤
        logSlack (2 * cPairEq + cPlainEq) N := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits N).length)]
  have hAppendPairProfile' :=
    hAppendPairProfile.mono hEqProfileRadius
  have hAppendProfile :
      ProfileSetsWithinNeighborhood
        (plainDescriptionProfileSet V (y ++ z))
        (separationGrayProfile k)
        (logSlack cProfile N) := by
    refine (hAppendPairProfile'.trans hPairProfile').mono ?_
    rw [logSlack_add_const]
    apply logSlack_mono_left
    dsimp [cProfile]
    omega
  have hPairNormalRaw :=
    hPairNormal y z (2 * k) headSlack headSlack cNoise
      (by simpa [headSlack] using hyNormal) hzLength'
      (by simpa [show 3 * k - k = 2 * k by omega] using hzRandom)
  have hPairStrengthBound :
      headSlack + logSlack cPairNormal (y.length + 2 * k) ≤
        logSlack cPairStrength N := by
    rw [hyLength]
    dsimp [cPairStrength]
    have hsum : 2 * k + 2 * k = N := by dsimp [N]; ring
    rw [hsum]
    calc
      headSlack + logSlack cPairNormal N
          ≤ logSlack cHead N + logSlack cPairNormal N := by
        gcongr
      _ = logSlack (cHead + cPairNormal) N :=
        logSlack_add_const _ _ _
  have hPairDeltaBound :
      cPairNormal * (headSlack + cNoise) +
          logSlack cPairNormal (y.length + 2 * k) ≤
        logSlack cPairDelta N := by
    rw [hyLength]
    have hsum : 2 * k + 2 * k = N := by dsimp [N]; ring
    rw [hsum]
    calc
      cPairNormal * (headSlack + cNoise) + logSlack cPairNormal N
          ≤ cPairNormal * (logSlack cHead N + cNoise) +
              logSlack cPairNormal N := by gcongr
      _ ≤ logSlack cPairDelta N := by
        dsimp [cPairDelta]
        exact normalPairDelta_logSlack_bound cPairNormal cHead cNoise N
  have hPairNormal' :
      IsNormalString V T (pairCode y z)
        (logSlack cPairStrength N) (logSlack cPairDelta N) :=
    (hPairNormalRaw.mono_delta hPairDeltaBound).mono_epsilon
      hPairStrengthBound
  have hNormalTransported :=
    hNormTransport (pairCode y z) (y ++ z)
      (logSlack cPairEq N) (logSlack cPairStrength N)
      (logSlack cPairDelta N) hAppendPair.symm hPairNormal'
  have hNormalStrengthBound :
      hereditaryStrongTransportStrength cNormStrong
          (logSlack cPairEq N) (logSlack cPairStrength N) ≤
        logSlack cNormStrength N := hNormStrength N
  have hNormalDeltaBound :
      (2 * logSlack cPairEq N + cNormPlain) +
          logSlack cPairDelta N +
          (2 * logSlack cPairEq N + cNormStrong) ≤
        logSlack cNormDelta N := by
    dsimp [cNormDelta]
    exact normalTransportDelta_logSlack_bound
      cPairEq cPairDelta cNormPlain cNormStrong N
  have hAppendNormal :
      IsNormalString V T (y ++ z)
        (logSlack cNormStrength N) (logSlack cNormDelta N) :=
    (hNormalTransported.mono_delta hNormalDeltaBound).mono_epsilon
      hNormalStrengthBound
  let x := y ++ z
  let A := cylinder N y
  have hyN : y.length ≤ N := by rw [hyLength]; dsimp [N]; omega
  have hxA : x ∈ A := by
    dsimp [x, A]
    rw [mem_cylinder]
    exact ⟨hxyLength, List.prefix_append y z⟩
  let hA : A.Nonempty := ⟨x, hxA⟩
  have hAStrong :
      IsStrongSetModel T x A hA (logSlack cCylinderStrong N) := by
    simpa [x, A, hA] using hCylinderStrong N y x hyN hxA
  have hAEqCodeY :
      TotalEquivalentWithin T (codedUniformOn A hA).code y
        (logSlack cCylinderEq N) := by
    simpa [A, hA] using hCylinderEq y N hyN
  have hAYCond :
      condK V (codedUniformOn A hA).code y ≤
        ((logSlack cCylinderEq N + cSim : Nat) : ENat) := by
    calc
      condK V (codedUniformOn A hA).code y
          ≤ condK T (codedUniformOn A hA).code y + (cSim : ENat) :=
        hSim _ _
      _ ≤ totalCondK T (codedUniformOn A hA).code y + (cSim : ENat) := by
        gcongr
        exact condK_le_totalCondK T _ _
      _ ≤ (logSlack cCylinderEq N : ENat) + (cSim : ENat) := by
        gcongr
        exact hAEqCodeY.1
      _ = ((logSlack cCylinderEq N + cSim : Nat) : ENat) := by
        push_cast
        rfl
  have hYACond :
      condK V y (codedUniformOn A hA).code ≤
        ((logSlack cCylinderEq N + cSim : Nat) : ENat) := by
    calc
      condK V y (codedUniformOn A hA).code
          ≤ condK T y (codedUniformOn A hA).code + (cSim : ENat) :=
        hSim _ _
      _ ≤ totalCondK T y (codedUniformOn A hA).code + (cSim : ENat) := by
        gcongr
        exact condK_le_totalCondK T _ _
      _ ≤ (logSlack cCylinderEq N : ENat) + (cSim : ENat) := by
        gcongr
        exact hAEqCodeY.2
      _ = ((logSlack cCylinderEq N + cSim : Nat) : ENat) := by
        push_cast
        rfl
  have hACodeFinite : plainK V (codedUniformOn A hA).code ≠ ⊤ :=
    condK_ne_top_of_optimal V hV _ []
  let aA := (plainK V (codedUniformOn A hA).code).toNat
  have hAComplexity :
      plainSetComplexity V A hA = (aA : ENat) := by
    unfold plainSetComplexity
    exact (ENat.natCast_toNat hACodeFinite).symm
  let headBudget := k + headSlack
  have hkxBudget : kx ≤ headBudget := by
    dsimp [headBudget]
    exact hkUpper'
  have hGapUpArg : logSlack cGap headBudget ≤ logSlack cGapUp N := by
    calc
      logSlack cGap headBudget
          ≤ logSlack cGap (2 * N + bHead) := by
        apply logSlack_mono_right
        dsimp [headBudget]
        have hh := hbHead N
        omega
      _ ≤ logSlack cGapUp N := hGapUp N
  have hAUpperNat : aA ≤ k + logSlack cAUpper N := by
    have hraw := hGap y (codedUniformOn A hA).code headBudget kx aA
      (logSlack cCylinderEq N + cSim) hyComplexity
      (by simpa [plainSetComplexity] using hAComplexity)
      hkxBudget hAYCond
    calc
      aA ≤ kx + (logSlack cCylinderEq N + cSim) +
          logSlack cGap headBudget := hraw
      _ ≤ k + headSlack + (logSlack cCylinderEq N + cSim) +
          logSlack cGapUp N := by omega
      _ ≤ k + logSlack cHead N +
          (logSlack cCylinderEq N + logSlack cSim N) +
          logSlack cGapUp N := by
        have hcSim : cSim ≤ logSlack cSim N := const_le_logSlack le_rfl
        omega
      _ = k + logSlack cAUpper N := by
        dsimp [cAUpper]
        unfold logSlack
        ring
  let lowerBudget := 2 * N + bAUpper
  have haLowerBudget : aA ≤ lowerBudget := by
    have hlog := hbAUpper N
    dsimp [lowerBudget]
    omega
  have hGapLowArg : logSlack cGap lowerBudget ≤ logSlack cGapLow N := by
    dsimp [lowerBudget]
    exact hGapLow N
  have hALowerNat : k ≤ aA + logSlack cALower N := by
    have hraw := hGap (codedUniformOn A hA).code y lowerBudget aA kx
      (logSlack cCylinderEq N + cSim)
      (by simpa [plainSetComplexity] using hAComplexity)
      hyComplexity haLowerBudget hYACond
    calc
      k ≤ kx + headSlack := hkLower'
      _ ≤ aA + (logSlack cCylinderEq N + cSim) +
          logSlack cGap lowerBudget + headSlack := by omega
      _ ≤ aA + (logSlack cCylinderEq N + logSlack cSim N) +
          logSlack cGapLow N + logSlack cHead N := by
        have hcSim : cSim ≤ logSlack cSim N := const_le_logSlack le_rfl
        omega
      _ = aA + logSlack cALower N := by
        dsimp [cALower]
        unfold logSlack
        ring
  have hACard : finiteSetLogCard A = 2 * k := by
    unfold A finiteSetLogCard
    rw [cylinder_card N y hyN, hyLength]
    have hsub : N - 2 * k = 2 * k := by dsimp [N]; omega
    rw [hsub]
    simp
  have hProfileFinal :
      ProfileSetsWithinNeighborhood
        (plainDescriptionProfileSet V x) (separationGrayProfile k)
        (logSlack cSlack N) := by
    simpa [x] using hAppendProfile.mono
      (logSlack_mono_left (by dsimp [cSlack]; omega) N)
  have hNormalFinal :
      IsNormalString V T x (logSlack cSlack N) (logSlack cSlack N) := by
    refine (hAppendNormal.mono_delta ?_).mono_epsilon ?_ <;>
      apply logSlack_mono_left <;> dsimp [cSlack] <;> omega
  have hStrongFinal :
      IsStrongSetModel T x A hA (logSlack cSlack N) :=
    hAStrong.mono (logSlack_mono_left (by dsimp [cSlack]; omega) N)
  have hUpperFinal :
      plainSetComplexity V A hA ≤
        ((k + logSlack cSlack N : Nat) : ENat) := by
    rw [hAComplexity]
    exact_mod_cast hAUpperNat.trans
      (Nat.add_le_add_left
        (logSlack_mono_left (by dsimp [cSlack]; omega) N) k)
  have hLowerFinal :
      (k : ENat) ≤ plainSetComplexity V A hA +
        (logSlack cSlack N : ENat) := by
    rw [hAComplexity]
    exact_mod_cast hALowerNat.trans
      (Nat.add_le_add_left
        (logSlack_mono_left (by dsimp [cSlack]; omega) N) aA)
  have hEqFinal :
      TotalEquivalentWithin T y (codedUniformOn A hA).code
        (logSlack cSlack N) :=
    hAEqCodeY.symm.mono
      (logSlack_mono_left (by dsimp [cSlack]; omega) N)
  refine ⟨y, z, ?_⟩
  dsimp only
  refine ⟨hyLength, hzLength', hxyLength, hProfileFinal, hNormalFinal, hA, hxA,
    hStrongFinal, hLowerFinal, hUpperFinal, hACard, ?_⟩
  simpa [N] using hEqFinal

end Kolmogorov
