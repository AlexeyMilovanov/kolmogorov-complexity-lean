import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainProfile
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongProfile
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CurveBridges
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileBridges
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CylinderRealization
import KolmogorovMathlib.Restricted.FamilyCurve

namespace Kolmogorov

open CodedFiniteDistribution

lemma logSlack_le_sqrtSlack_linear :
    ∃ C : ℕ → ℕ, (∀ c, C c ≤ 2 * c + 1) ∧ ∀ c n, logSlack c n ≤ sqrtSlack (C c) n := by
  refine ⟨fun c => c, fun c => by dsimp; omega, ?_⟩
  intro c n
  unfold logSlack sqrtSlack
  have hbits : (Nat.bits n).length ≤
      Nat.sqrt (n * (Nat.bits n).length) := by
    apply Nat.le_sqrt.mpr
    have hle : (Nat.bits n).length ≤ n := length_natBits_le n
    nlinarith
  nlinarith

lemma logSlack_length_le_sqrtSlack_linear :
    ∃ C : ℕ → ℕ → ℕ, (∀ c cRun, C c cRun ≤ c * (cRun + 1) + c) ∧
      ∀ c cRun n xlen, xlen ≤ n + logSlack cRun n →
        logSlack c xlen ≤ sqrtSlack (C c cRun) n := by
  refine ⟨fun c cRun => c * (cRun + 2), fun c cRun => by ring_nf; rfl, ?_⟩
  intro c cRun n xlen hxlen
  let L := (Nat.bits n).length
  let S := Nat.sqrt (n * L)
  have hLS : L ≤ S := by
    dsimp [L, S]
    apply Nat.le_sqrt.mpr
    have hle : (Nat.bits n).length ≤ n := length_natBits_le n
    nlinarith
  have hxBits :
      (Nat.bits xlen).length ≤
        L + (Nat.bits (logSlack cRun n)).length + 1 := by
    exact (length_natBits_mono hxlen).trans
      (by simpa [L] using length_natBits_add_le n (logSlack cRun n))
  have hslackBits :
      (Nat.bits (logSlack cRun n)).length ≤ cRun * L + cRun := by
    exact (length_natBits_le (logSlack cRun n)).trans_eq (by
      simp [logSlack, L])
  have hxBits' :
      (Nat.bits xlen).length ≤ (cRun + 1) * S + cRun + 1 := by
    calc
      (Nat.bits xlen).length
          ≤ L + (Nat.bits (logSlack cRun n)).length + 1 := hxBits
      _ ≤ L + (cRun * L + cRun) + 1 := by gcongr
      _ = (cRun + 1) * L + cRun + 1 := by ring
      _ ≤ (cRun + 1) * S + cRun + 1 := by gcongr
  unfold logSlack sqrtSlack
  dsimp [L, S] at hLS hxBits hslackBits hxBits' ⊢
  calc
    c * (Nat.bits xlen).length + c
        ≤ c * ((cRun + 1) * Nat.sqrt
            (n * (Nat.bits n).length) + cRun + 1) + c := by
          gcongr
    _ ≤ c * (cRun + 2) * Nat.sqrt
          (n * (Nat.bits n).length) + c * (cRun + 2) := by
          nlinarith [Nat.zero_le (c * Nat.sqrt
            (n * (Nat.bits n).length))]

/-- Logarithmic strength at a logarithmically padded length folds back into a
logarithmic strength at the original length, with a constant linear in the
padding constant. -/
lemma logSlack_length_le_logSlack_linear :
    ∃ C : ℕ → ℕ → ℕ, (∀ c cRun, C c cRun ≤ c * (cRun + 1) + c) ∧
      ∀ c cRun n xlen, xlen ≤ n + logSlack cRun n →
        logSlack c xlen ≤ logSlack (C c cRun) n := by
  refine ⟨fun c cRun => c * (cRun + 2), fun c cRun => by ring_nf; rfl, ?_⟩
  intro c cRun n xlen hxlen
  let L := (Nat.bits n).length
  have hxBits :
      (Nat.bits xlen).length ≤
        L + (Nat.bits (logSlack cRun n)).length + 1 := by
    exact (length_natBits_mono hxlen).trans
      (by simpa [L] using length_natBits_add_le n (logSlack cRun n))
  have hslackBits :
      (Nat.bits (logSlack cRun n)).length ≤ cRun * L + cRun := by
    exact (length_natBits_le (logSlack cRun n)).trans_eq (by
      simp [logSlack, L])
  unfold logSlack
  dsimp [L] at hxBits hslackBits ⊢
  have hxBits' :
      (Nat.bits xlen).length ≤
        (cRun + 1) * (Nat.bits n).length + cRun + 1 := by
    calc
      (Nat.bits xlen).length
          ≤ (Nat.bits n).length +
              (Nat.bits (logSlack cRun n)).length + 1 := hxBits
      _ ≤ (Nat.bits n).length +
              (cRun * (Nat.bits n).length + cRun) + 1 := by
            gcongr
      _ = (cRun + 1) * (Nat.bits n).length + cRun + 1 := by
            ring
  nlinarith [Nat.zero_le (c * cRun * (Nat.bits n).length)]

theorem fullFamilyCurve_to_plainProfile
    (V U : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
  ∃ c, ∀ x k t Δ,
    t k = 0 →
    RestrictedProfileWithinCurve fullFamily U x k t Δ →
    ProfileSetsWithinNeighborhood
      (plainDescriptionProfileSet V x)
      {q | FamilyCurveTarget k t q.1 q.2}
      (Δ + logSlack c k) := by
  obtain ⟨cToPrefix, hToPrefix⟩ :=
    inDescriptionProfile_of_inPlainDescriptionProfile V U hV hU
  obtain ⟨cToPlain, hToPlain⟩ :=
    inPlainDescriptionProfile_of_inDescriptionProfile V U hV hU
  refine ⟨cToPrefix + cToPlain, ?_⟩
  intro x k t Δ htk hcurve
  have hrestricted :=
    restrictedProfileWithinCurve_neighborhood fullFamily U x k t Δ htk hcurve
  constructor
  · rintro q hq
    by_cases hqk : q.1 ≤ k
    · have hpref :
          InDescriptionProfile U x
            (q.1 + logSlack cToPrefix q.1) q.2 :=
        hToPrefix x q.1 q.2 hq
      have hfull :
          InDescriptionProfileIn fullFamily U x
            (q.1 + logSlack cToPrefix q.1) q.2 :=
        (inDescriptionProfileIn_fullFamily_iff U x _ _).mpr hpref
      obtain ⟨r, hr, hdr⟩ := hrestricted.1
        (q.1 + logSlack cToPrefix q.1, q.2) (by
          exact hfull)
      refine ⟨r, hr, (natPairLInfDistance_triangle q
        (q.1 + logSlack cToPrefix q.1, q.2) r).trans ?_⟩
      have hlog :
          logSlack cToPrefix q.1 ≤
            logSlack (cToPrefix + cToPlain) k :=
        (logSlack_mono_right cToPrefix hqk).trans
          (logSlack_mono_left (Nat.le_add_right _ _) k)
      have hshift :
          natPairLInfDistance q
            (q.1 + logSlack cToPrefix q.1, q.2) =
              logSlack cToPrefix q.1 := by
        simp [natPairLInfDistance]
      rw [hshift]
      omega
    · refine ⟨q, ?_, by simp [natPairLInfDistance]⟩
      exact fun h => False.elim (hqk h)
  · intro q hq
    obtain ⟨r, hr, hdr⟩ := hrestricted.2 q hq
    have hpref : InDescriptionProfile U x r.1 r.2 :=
      (inDescriptionProfileIn_fullFamily_iff U x _ _).mp hr
    have hplain :
        InPlainDescriptionProfile V x (r.1 + cToPlain) r.2 :=
      hToPlain x r.1 r.2 hpref
    refine ⟨(r.1 + cToPlain, r.2), hplain,
      (natPairLInfDistance_triangle q r
        (r.1 + cToPlain, r.2)).trans ?_⟩
    have hc :
        cToPlain ≤ logSlack (cToPrefix + cToPlain) k := by
      unfold logSlack
      nlinarith [Nat.zero_le ((Nat.bits k).length)]
    have hshift :
        natPairLInfDistance r (r.1 + cToPlain, r.2) =
          cToPlain := by
      simp [natPairLInfDistance]
    rw [hshift]
    omega

theorem plainK_lower_of_curve_neighborhood
    (V : Map) (hV : isOptimalConditional V) :
  ∃ c : Nat, ∀ x k t Δ,
    t k = 0 →
    (∀ i < k, t (i + 1) < t i) →
    ProfileSetsWithinNeighborhood
      (plainDescriptionProfileSet V x)
      {q | FamilyCurveTarget k t q.1 q.2} Δ →
    (k : ENat) ≤ plainK V x + ((2 * Δ + c : Nat) : ENat) := by
  obtain ⟨c, hc⟩ := plainSetComplexity_singleton_le_plainK V hV
  refine ⟨c, ?_⟩
  intro x k t Δ htk hstrict hclose
  by_cases htop : plainK V x = ⊤
  · rw [htop]
    simp
  · obtain ⟨kx, hkx⟩ : ∃ kx : Nat, plainK V x = (kx : ENat) :=
      (ENat.ne_top_iff_exists.mp htop).imp fun m hm => hm.symm
    have hsingleton :
        InPlainDescriptionProfile V x (kx + c) 0 := by
      refine ⟨{x}, Finset.singleton_nonempty x,
        Finset.mem_singleton.mpr rfl, ?_, by simp⟩
      simpa [hkx] using hc x
    obtain ⟨q, hq, hdq⟩ := hclose.1 (kx + c, 0) hsingleton
    have hq1 : q.1 ≤ kx + c + Δ := by
      unfold natPairLInfDistance at hdq
      omega
    have hq2 : q.2 ≤ Δ := by
      unfold natPairLInfDistance at hdq
      omega
    have hkNat : k ≤ kx + 2 * Δ + c := by
      by_cases hqk : q.1 ≤ k
      · have htq : t q.1 ≤ q.2 := hq hqk
        have hrem : k - q.1 ≤ t q.1 :=
          restricted_curve_remaining_le hstrict htk hqk
        omega
      · omega
    rw [hkx]
    exact_mod_cast (show k ≤ kx + (2 * Δ + c) by omega)

theorem cylinderCurve_to_strongProfile_neighborhood
    (V U T : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) :
  ∃ c, ∀ x k t Δ δ,
    t k = 0 →
    RestrictedProfileWithinCurve cylinderFamily U x k t Δ →
    ProfileSetsWithinNeighborhood
      (plainDescriptionProfileSet V x)
      {q | FamilyCurveTarget k t q.1 q.2} δ →
    ProfileSetsWithinNeighborhood
      (strongDescriptionProfileSet V T x (logSlack c x.length))
      {q | FamilyCurveTarget k t q.1 q.2}
      (δ + Δ + c) := by
  obtain ⟨c, hc⟩ :=
    cylinderProfile_to_strongProfile V U T hV hU hT
  refine ⟨c, ?_⟩
  intro x k t Δ δ htk hcurve hplain
  have hcylinder :=
    restrictedProfileWithinCurve_neighborhood cylinderFamily U x k t Δ
      htk hcurve
  constructor
  · intro q hq
    have hqplain :
        q ∈ plainDescriptionProfileSet V x :=
      strongDescriptionProfileSet_subset_plain V T x (logSlack c x.length) hq
    obtain ⟨r, hr, hdr⟩ := hplain.1 q hqplain
    exact ⟨r, hr, hdr.trans (by omega)⟩
  · intro q hq
    obtain ⟨r, hr, hdr⟩ := hcylinder.2 q hq
    have hstrong :
        InStrongDescriptionProfile V T x (logSlack c x.length)
          (r.1 + c) r.2 :=
      hc x r.1 r.2 hr
    refine ⟨(r.1 + c, r.2), hstrong,
      (natPairLInfDistance_triangle q r (r.1 + c, r.2)).trans ?_⟩
    have hshift :
        natPairLInfDistance r (r.1 + c, r.2) = c := by
      simp [natPairLInfDistance]
    rw [hshift]
    omega

theorem stat_any_curve_1_of_joint_prefix_realization
    (V U T : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) :
  ∃ cPost, ∀ cRun, ∃ cOut,
    cOut ≤ cPost * (cRun + 1) ∧
    ∀ n k t x n',
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i < k, t (i + 1) < t i) →
      x.length = n' →
      n ≤ n' →
      n' ≤ n + logSlack cRun n →
      KPPlain U x ≤ (k + sqrtSlack cRun n : ENat) →
      RestrictedProfileWithinCurve cylinderFamily U x k t
        (sqrtSlack cRun n) →
      RestrictedProfileWithinCurve fullFamily U x k t
        (sqrtSlack cRun n) →
      plainK V x ≤ (k + sqrtSlack cOut n : ENat) ∧
      (k : ENat) ≤ plainK V x + (sqrtSlack cOut n : ENat) ∧
      ProfileSetsWithinNeighborhood
        (plainDescriptionProfileSet V x)
        {q | FamilyCurveTarget k t q.1 q.2}
        (sqrtSlack cOut n) ∧
      ProfileSetsWithinNeighborhood
        (strongDescriptionProfileSet V T x (logSlack cOut n))
        {q | FamilyCurveTarget k t q.1 q.2}
        (sqrtSlack cOut n) := by
  obtain ⟨cPlainK, hPlainK⟩ :=
    plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  obtain ⟨cFull, hFull⟩ :=
    fullFamilyCurve_to_plainProfile V U hV hU
  obtain ⟨cLower, hLower⟩ :=
    plainK_lower_of_curve_neighborhood V hV
  obtain ⟨cStrong, hStrong⟩ :=
    cylinderCurve_to_strongProfile_neighborhood V U T hV hU hT
  obtain ⟨CLog, _hCLogBound, hCLog⟩ :=
    logSlack_le_sqrtSlack_linear
  obtain ⟨CLength, hCLengthBound, hCLength⟩ :=
    logSlack_length_le_logSlack_linear
  let cLog := CLog cFull
  let cPost :=
    2 * (cPlainK + cFull + cLower + cStrong + cLog + 1)
  refine ⟨cPost, ?_⟩
  intro cRun
  let cOut := cPost * (cRun + 1)
  refine ⟨cOut, le_rfl, ?_⟩
  intro n k t x n' hkn _ht0 htk hstrict hxlen _hnlen hnlenUpper
    hKP hCylinder hFullCurve
  let Δ := sqrtSlack cRun n
  let δPlain := Δ + logSlack cFull k
  have hcPostOne : 1 ≤ cPost := by
    dsimp [cPost]
    omega
  have hcPostTwo : 2 ≤ cPost := by
    dsimp [cPost]
    omega
  have hcPostPlainK : cPlainK ≤ cPost := by
    dsimp [cPost]
    omega
  have hcPostLog : cLog ≤ cPost := by
    dsimp [cPost]
    omega
  have hcPostLower : 2 * cLog + cLower ≤ cPost := by
    dsimp [cPost]
    omega
  have hcPostStrong : cLog + cStrong ≤ cPost := by
    dsimp [cPost]
    omega
  have hcPostTwiceStrong : 2 * cStrong ≤ cPost := by
    dsimp [cPost]
    omega
  have hOutUpper : cRun + cPlainK ≤ cOut := by
    calc
      cRun + cPlainK
          ≤ cPost * cRun + cPost :=
        Nat.add_le_add
          (by simpa using Nat.mul_le_mul_right cRun hcPostOne)
          hcPostPlainK
      _ = cOut := by dsimp [cOut]; ring
  have hOutPlain : cRun + cLog ≤ cOut := by
    calc
      cRun + cLog
          ≤ cPost * cRun + cPost :=
        Nat.add_le_add
          (by simpa using Nat.mul_le_mul_right cRun hcPostOne)
          hcPostLog
      _ = cOut := by dsimp [cOut]; ring
  have hOutLower :
      2 * cRun + (2 * cLog + cLower) ≤ cOut := by
    calc
      2 * cRun + (2 * cLog + cLower)
          ≤ cPost * cRun + cPost :=
        Nat.add_le_add (Nat.mul_le_mul_right cRun hcPostTwo) hcPostLower
      _ = cOut := by dsimp [cOut]; ring
  have hOutStrong :
      2 * cRun + (cLog + cStrong) ≤ cOut := by
    calc
      2 * cRun + (cLog + cStrong)
          ≤ cPost * cRun + cPost :=
        Nat.add_le_add (Nat.mul_le_mul_right cRun hcPostTwo) hcPostStrong
      _ = cOut := by dsimp [cOut]; ring
  have hOutStrength : CLength cStrong cRun ≤ cOut := by
    have hLength :
        CLength cStrong cRun ≤ cStrong * (cRun + 1) + cStrong :=
      hCLengthBound cStrong cRun
    calc
      CLength cStrong cRun
          ≤ cStrong * (cRun + 1) + cStrong := hLength
      _ ≤ 2 * cStrong * (cRun + 1) := by
        nlinarith
      _ ≤ cPost * (cRun + 1) :=
        Nat.mul_le_mul_right (cRun + 1) hcPostTwiceStrong
      _ = cOut := rfl
  have hLog : logSlack cFull k ≤ sqrtSlack cLog n := by
    exact (logSlack_mono_right cFull hkn).trans (by
      simpa [cLog] using hCLog cFull n)
  have hPlain :
      ProfileSetsWithinNeighborhood
        (plainDescriptionProfileSet V x)
        {q | FamilyCurveTarget k t q.1 q.2}
        δPlain :=
    hFull x k t Δ htk hFullCurve
  have hPlainRadius : δPlain ≤ sqrtSlack cOut n := by
    calc
      δPlain
          ≤ sqrtSlack cRun n + sqrtSlack cLog n := by
        dsimp [δPlain, Δ]
        gcongr
      _ = sqrtSlack (cRun + cLog) n := sqrtSlack_add cRun cLog n
      _ ≤ sqrtSlack cOut n := sqrtSlack_mono_left hOutPlain n
  have hLowerRadius :
      2 * δPlain + cLower ≤ sqrtSlack cOut n := by
    calc
      2 * δPlain + cLower
          ≤ 2 * sqrtSlack (cRun + cLog) n + cLower := by
        have hδ :
            δPlain ≤ sqrtSlack (cRun + cLog) n := by
          calc
            δPlain
                ≤ sqrtSlack cRun n + sqrtSlack cLog n := by
              dsimp [δPlain, Δ]
              gcongr
            _ = sqrtSlack (cRun + cLog) n :=
              sqrtSlack_add cRun cLog n
        nlinarith
      _ = sqrtSlack (2 * cRun + 2 * cLog) n + cLower := by
        unfold sqrtSlack
        ring
      _ ≤ sqrtSlack cOut n :=
        sqrtSlack_add_const_le n (by
          simpa [Nat.add_assoc] using hOutLower)
  have hStrongRadius :
      δPlain + Δ + cStrong ≤ sqrtSlack cOut n := by
    calc
      δPlain + Δ + cStrong
          ≤ sqrtSlack (cRun + cLog) n +
              sqrtSlack cRun n + cStrong := by
        dsimp [δPlain, Δ]
        have hδ :
            sqrtSlack cRun n + logSlack cFull k ≤
              sqrtSlack (cRun + cLog) n := by
          calc
            sqrtSlack cRun n + logSlack cFull k
                ≤ sqrtSlack cRun n + sqrtSlack cLog n := by gcongr
            _ = sqrtSlack (cRun + cLog) n :=
              sqrtSlack_add cRun cLog n
        omega
      _ = sqrtSlack (2 * cRun + cLog) n + cStrong := by
        rw [sqrtSlack_add]
        congr 2
        omega
      _ ≤ sqrtSlack cOut n :=
        sqrtSlack_add_const_le n (by
          simpa [Nat.add_assoc] using hOutStrong)
  have hUpperSlack :
      sqrtSlack cRun n + cPlainK ≤ sqrtSlack cOut n :=
    sqrtSlack_add_const_le n hOutUpper
  have hPlainUpper :
      plainK V x ≤ (k + sqrtSlack cOut n : ENat) := by
    calc
      plainK V x
          ≤ KPPlain U x + (cPlainK : ENat) := hPlainK x
      _ ≤ (k + sqrtSlack cRun n : ENat) + (cPlainK : ENat) := by
        gcongr
      _ ≤ (k + sqrtSlack cOut n : ENat) := by
        exact_mod_cast (show
          k + sqrtSlack cRun n + cPlainK ≤
            k + sqrtSlack cOut n by omega)
  have hPlainLower :
      (k : ENat) ≤ plainK V x + (sqrtSlack cOut n : ENat) := by
    have hraw :=
      hLower x k t δPlain htk hstrict hPlain
    exact hraw.trans (by
      gcongr)
  have hStrength :
      logSlack cStrong x.length ≤ logSlack cOut n := by
    have hfold :
        logSlack cStrong x.length ≤
          logSlack (CLength cStrong cRun) n :=
      hCLength cStrong cRun n x.length (by
        rw [hxlen]
        exact hnlenUpper)
    exact hfold.trans
      (logSlack_mono_left hOutStrength n)
  have hStrongOld :
      ProfileSetsWithinNeighborhood
        (strongDescriptionProfileSet V T x
          (logSlack cStrong x.length))
        {q | FamilyCurveTarget k t q.1 q.2}
        (δPlain + Δ + cStrong) :=
    hStrong x k t Δ δPlain htk hCylinder hPlain
  have hStrongFinal :
      ProfileSetsWithinNeighborhood
        (strongDescriptionProfileSet V T x (logSlack cOut n))
        {q | FamilyCurveTarget k t q.1 q.2}
        (sqrtSlack cOut n) := by
    constructor
    · intro q hq
      have hqPlain :
          q ∈ plainDescriptionProfileSet V x :=
        strongDescriptionProfileSet_subset_plain V T x
          (logSlack cOut n) hq
      obtain ⟨r, hr, hdr⟩ := hPlain.1 q hqPlain
      exact ⟨r, hr, hdr.trans (hPlainRadius.trans le_rfl)⟩
    · intro q hq
      obtain ⟨r, hr, hdr⟩ := hStrongOld.2 q hq
      have hr' :
          r ∈ strongDescriptionProfileSet V T x (logSlack cOut n) :=
        strongDescriptionProfileSet_mono_epsilon V T x hStrength hr
      exact ⟨r, hr', hdr.trans hStrongRadius⟩
  exact ⟨hPlainUpper, hPlainLower,
    hPlain.mono hPlainRadius, hStrongFinal⟩

end Kolmogorov
