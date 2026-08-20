import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T3BoundaryReplay

/-!
# Profile assembly for the interior T3 construction

The smaller-quota run gives its model an additional `delta` bits of ordinary
plain complexity.  This module propagates exactly that visible loss through
the already-proved Figure 6 profile arguments.  In particular, `delta` is not
hidden in a logarithmic constant.
-/

namespace Kolmogorov

/-- The T3 avoiding model gives the source's upper complexity endpoint
`plainK x ≤ k + delta + O(log n)`. -/
theorem t3_avoiding_set_plainK_upper
    (V : Map) (hV : isOptimalConditional V) :
    ∀ cA : Nat, ∃ cK : Nat,
      ∀ (n k epsilon delta : Nat) (A : Finset BitString)
        (hA : A.Nonempty) (x : BitString),
      epsilon ≤ k →
      delta ≤ k - epsilon →
      k ≤ n →
      A.card = 2 ^ (k - epsilon) →
      x ∈ A →
      x.length = n →
      plainSetComplexity V A hA ≤
        (epsilon + delta + logSlack cA n : ENat) →
      plainK V x ≤
        (k + delta + logSlack cK n : ENat) := by
  let U : Map := Classical.choose exists_isOptimalPrefixConditional
  have hU : IsOptimalPrefixConditional U :=
    Classical.choose_spec exists_isOptimalPrefixConditional
  obtain ⟨cTwo, hTwo⟩ :=
    plainK_le_of_inPlainDescriptionProfile V U hV hU
  intro cA
  obtain ⟨bA, hbA⟩ := logSlack_le_add_const cA
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cTwo 4 bA
  refine ⟨cA + cFold, ?_⟩
  intro n k epsilon delta A hA x hepsilon hdelta hkn
      hAcard hxA hxlen hAcomplexity
  have hprofile :
      InPlainDescriptionProfile V x
        (epsilon + delta + logSlack cA n) (k - epsilon) := by
    refine ⟨A, hA, hxA, hAcomplexity, ?_⟩
    rw [hAcard]
  have htwo :=
    hTwo x n (epsilon + delta + logSlack cA n)
      (k - epsilon) hxlen hprofile
  have harg :
      n + (epsilon + delta + logSlack cA n) +
          (k - epsilon) ≤ 4 * n + bA := by
    have hAlog := hbA n
    omega
  have hslack :
      logSlack cTwo
          (n + (epsilon + delta + logSlack cA n) +
            (k - epsilon)) ≤
        logSlack cFold n :=
    (logSlack_mono_right cTwo harg).trans (hFold n)
  calc
    plainK V x
        ≤ (epsilon + delta + logSlack cA n) +
            (k - epsilon) +
            logSlack cTwo
              (n + (epsilon + delta + logSlack cA n) +
                (k - epsilon)) := htwo
    _ ≤ (k + delta + logSlack (cA + cFold) n : Nat) := by
      exact_mod_cast (show
        (epsilon + delta + logSlack cA n) + (k - epsilon) +
            logSlack cTwo
              (n + (epsilon + delta + logSlack cA n) +
                (k - epsilon)) ≤
          k + delta + logSlack (cA + cFold) n by
        rw [← logSlack_add_const]
        omega)

/-- Positive ordinary Figure 6 geometry with the additional T3 loss kept as
the explicit summand `delta` in the neighborhood radius. -/
theorem t3_polygon_to_plainProfile
    (V : Map) (hV : isOptimalConditional V) :
    ∀ cA cK : Nat, ∃ c : Nat,
      ∀ (n k epsilon delta : Nat) (A : Finset BitString)
        (hA : A.Nonempty) (x : BitString),
      epsilon ≤ k →
      delta ≤ k - epsilon →
      k ≤ n →
      A.card = 2 ^ (k - epsilon) →
      x ∈ A →
      x.length = n →
      plainSetComplexity V A hA ≤
        (epsilon + delta + logSlack cA n : ENat) →
      plainK V x ≤
        (k + delta + logSlack cK n : ENat) →
      ∀ q ∈ t1PlainPolygon n k epsilon,
        ∃ q' ∈ plainDescriptionProfileSet V x,
          natPairLInfDistance q q' ≤
            delta + logSlack c n := by
  obtain ⟨cCube, hCube⟩ :=
    plainSetComplexity_fullCube_le_logSlack V hV
  obtain ⟨cSingleton, hSingleton⟩ :=
    plainSetComplexity_singleton_le_plainK V hV
  obtain ⟨cShift, hShift⟩ :=
    inPlainDescriptionProfile_shift V hV
  intro cA cK
  let c := cCube + cSingleton + cShift + cA + cK
  refine ⟨c, ?_⟩
  intro n k epsilon delta A hA x hepsilon _hdelta hkn
      hAcard hxA hxlen hAcomplexity hKupper q hq
  let radius := delta + logSlack c n
  have hfull :
      InPlainDescriptionProfile V x (logSlack cCube n) n := by
    refine ⟨stringsOfLength n, codedStringsOfLength_nonempty n,
      (memStringsOfLength n x).mpr hxlen, hCube n, ?_⟩
    rw [cardStringsOfLength]
  have hmiddle :
      InPlainDescriptionProfile V x
        (epsilon + delta + logSlack cA n) (k - epsilon) := by
    refine ⟨A, hA, hxA, hAcomplexity, ?_⟩
    rw [hAcard]
  have hCubeShift :
      logSlack cCube n + logSlack cShift n ≤
        logSlack c n := by
    rw [logSlack_add_const]
    dsimp [c]
    exact logSlack_mono_left (by omega) n
  have hAShift :
      logSlack cA n + logSlack cShift n ≤
        logSlack c n := by
    rw [logSlack_add_const]
    dsimp [c]
    exact logSlack_mono_left (by omega) n
  have hKSingleton :
      logSlack cK n + cSingleton ≤ logSlack c n := by
    calc
      logSlack cK n + cSingleton
          ≤ logSlack cK n + logSlack cSingleton n := by
        gcongr
        simp [logSlack]
      _ = logSlack (cK + cSingleton) n :=
        logSlack_add_const cK cSingleton n
      _ ≤ logSlack c n := by
        dsimp [c]
        exact logSlack_mono_left (by omega) n
  by_cases hqepsilon : q.1 < epsilon
  · have hqsum : n ≤ q.1 + q.2 := by
      unfold t1PlainPolygon at hq
      simpa [hqepsilon] using hq
    have hqN : q.1 ≤ n := by omega
    have hshiftSlack :
        logSlack cShift q.1 ≤ logSlack cShift n :=
      logSlack_mono_right cShift hqN
    have hcomplexity :
        logSlack cCube n + q.1 + logSlack cShift q.1 ≤
          q.1 + radius := by
      dsimp [radius]
      omega
    have hshifted :=
      hShift x (logSlack cCube n) n q.1 hfull
    have hprofile :
        InPlainDescriptionProfile V x (q.1 + radius) q.2 := by
      refine (hshifted.mono_i hcomplexity).mono_j ?_
      omega
    refine ⟨(q.1 + radius, q.2), hprofile, ?_⟩
    simp [natPairLInfDistance, radius]
  · have hqepsilon' : epsilon ≤ q.1 := by omega
    have hqsum : k ≤ q.1 + q.2 := by
      unfold t1PlainPolygon at hq
      simpa [hqepsilon] using hq
    by_cases hqk : q.1 ≤ k
    · let s := q.1 - epsilon
      have hsN : s ≤ n := by
        dsimp [s]
        omega
      have hshiftSlack :
          logSlack cShift s ≤ logSlack cShift n :=
        logSlack_mono_right cShift hsN
      have hsadd : epsilon + s = q.1 := by
        dsimp [s]
        omega
      have hcomplexity :
          epsilon + delta + logSlack cA n + s +
              logSlack cShift s ≤ q.1 + radius := by
        dsimp [radius]
        omega
      have hsize : k - epsilon - s ≤ q.2 := by
        dsimp [s]
        omega
      have hshifted :=
        hShift x (epsilon + delta + logSlack cA n)
          (k - epsilon) s hmiddle
      have hprofile :
          InPlainDescriptionProfile V x (q.1 + radius) q.2 :=
        (hshifted.mono_i hcomplexity).mono_j hsize
      refine ⟨(q.1 + radius, q.2), hprofile, ?_⟩
      simp [natPairLInfDistance, radius]
    · have hkq : k < q.1 := by omega
      have hsingletonComplexity :
          plainSetComplexity V {x}
              (Finset.singleton_nonempty x) ≤
            (q.1 + radius : Nat) := by
        calc
          plainSetComplexity V {x} (Finset.singleton_nonempty x)
              ≤ plainK V x + (cSingleton : ENat) :=
            hSingleton x
          _ ≤ (k + delta + logSlack cK n : ENat) +
                (cSingleton : ENat) := by gcongr
          _ ≤ (q.1 + radius : Nat) := by
            exact_mod_cast (show
              k + delta + logSlack cK n + cSingleton ≤
                q.1 + radius by
              dsimp [radius]
              omega)
      have hprofile :
          InPlainDescriptionProfile V x (q.1 + radius) q.2 := by
        refine ⟨{x}, Finset.singleton_nonempty x,
          Finset.mem_singleton.mpr rfl, hsingletonComplexity, ?_⟩
        simpa using Nat.one_le_two_pow
      refine ⟨(q.1 + radius, q.2), hprofile, ?_⟩
      simp [natPairLInfDistance, radius]

/-- The complete ordinary T3 profile consequence for a nonexceptional member
of the smaller-quota avoiding model. -/
theorem t3_avoiding_set_plain_profile_bounds
    (V : Map) (hV : isOptimalConditional V) :
    ∀ cA : Nat, ∃ cProfile : Nat,
      ∀ (n k epsilon delta : Nat) (A : Finset BitString)
        (hA : A.Nonempty) (x : BitString),
      epsilon ≤ k →
      delta ≤ k - epsilon →
      k + 4 ≤ n →
      A.card = 2 ^ (k - epsilon) →
      x ∈ A →
      x.length = n →
      plainSetComplexity V A hA ≤
        (epsilon + delta + logSlack cA n : ENat) →
      ¬ T1BMarked V n epsilon x →
      ¬ T1DMarked V n k x →
      (k : ENat) ≤ plainK V x ∧
      plainK V x ≤
        (k + delta + logSlack cProfile n : ENat) ∧
      ProfileSetsWithinNeighborhood
        (plainDescriptionProfileSet V x)
        (t1PlainPolygon n k epsilon)
        (delta + logSlack cProfile n) := by
  intro cA
  obtain ⟨cK, hK⟩ :=
    t3_avoiding_set_plainK_upper V hV cA
  obtain ⟨cTo, hTo⟩ :=
    t1_plainProfile_to_polygon V hV
  obtain ⟨cFrom, hFrom⟩ :=
    t3_polygon_to_plainProfile V hV cA cK
  let cProfile := cK + cTo + cFrom
  refine ⟨cProfile, ?_⟩
  intro n k epsilon delta A hA x hepsilon hdelta hkn
      hAcard hxA hxlen hAcomplexity hnotB hnotD
  have hKlower : (k : ENat) ≤ plainK V x :=
    t1_not_dMarked_plainK_lower hxlen hnotD
  have hKupper :=
    hK n k epsilon delta A hA x hepsilon hdelta (by omega)
      hAcard hxA hxlen hAcomplexity
  have hKslack :
      logSlack cK n ≤ logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hToslack :
      logSlack cTo n ≤ delta + logSlack cProfile n := by
    have h := logSlack_mono_left (show cTo ≤ cProfile by
      dsimp [cProfile]
      omega) n
    omega
  have hFromslack :
      delta + logSlack cFrom n ≤
        delta + logSlack cProfile n := by
    gcongr
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  refine ⟨hKlower, hKupper.trans ?_, ?_⟩
  · exact_mod_cast (Nat.add_le_add_left hKslack (k + delta))
  · constructor
    · intro q hq
      obtain ⟨q', hq', hdist⟩ :=
        hTo n k epsilon x hepsilon hkn hxlen
          hnotB hnotD q hq
      exact ⟨q', hq', hdist.trans hToslack⟩
    · intro q hq
      obtain ⟨q', hq', hdist⟩ :=
        hFrom n k epsilon delta A hA x hepsilon hdelta
          (by omega) hAcard hxA hxlen hAcomplexity
          hKupper q hq
      exact ⟨q', hq', hdist.trans hFromslack⟩

/-- The singleton endpoint with the T3 upper-complexity loss made explicit.
The strength threshold remains uniform and independent of `delta`. -/
theorem t3_singleton_strong_profile_endpoint
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ cStrength : Nat, ∀ cK : Nat, ∃ cProfile : Nat,
      ∀ (x : BitString) (n k epsilon delta : Nat),
      plainK V x ≤
        (k + delta + logSlack cK n : ENat) →
      cStrength ≤ epsilon →
      (k + delta + logSlack cProfile n, 0) ∈
        strongDescriptionProfileSet V T x epsilon := by
  obtain ⟨cPlain, hPlain⟩ :=
    plainSetComplexity_singleton_le_plainK V hV
  obtain ⟨cStrength, hStrong⟩ :=
    singleton_isStrongSetModel T hT
  refine ⟨cStrength, fun cK => ⟨cK + cPlain, ?_⟩⟩
  intro x n k epsilon delta hK hStrength
  change InStrongDescriptionProfile V T x epsilon
    (k + delta + logSlack (cK + cPlain) n) 0
  refine ⟨{x}, Finset.singleton_nonempty x, ?_, ?_⟩
  · refine ⟨Finset.mem_singleton.mpr rfl, ?_, by simp⟩
    calc
      plainSetComplexity V {x} (Finset.singleton_nonempty x)
          ≤ plainK V x + (cPlain : ENat) := hPlain x
      _ ≤ (k + delta + logSlack cK n : ENat) +
          (cPlain : ENat) := by gcongr
      _ ≤ (k + delta + logSlack (cK + cPlain) n : Nat) := by
        exact_mod_cast (show
          k + delta + logSlack cK n + cPlain ≤
            k + delta + logSlack (cK + cPlain) n by
          unfold logSlack
          nlinarith [Nat.zero_le (Nat.bits n).length])
  · exact (hStrong x).mono hStrength

/-- All Figure 6 conclusions for one nonexceptional member of a T3 avoiding
model.  The run's `C`-mark budget already includes the logarithmic strength
shift used in the symmetric strong-profile direction. -/
theorem t3_goodElement_of_avoiding_set_at_strength
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ cDesc cStrengthMin cEndpoint : Nat,
      ∀ cStrength : Nat, cStrengthMin ≤ cStrength →
      ∀ cA : Nat, ∃ cProfile : Nat, cA ≤ cProfile ∧
        ∀ (n k epsilon delta : Nat) (A : Finset BitString)
          (hA : A.Nonempty) (x : BitString),
        cEndpoint ≤ epsilon →
        epsilon ≤ k →
        delta ≤ k - epsilon →
        k + 4 ≤ n →
        A.card = 2 ^ (k - epsilon) →
        x ∈ A →
        x.length = n →
        plainSetComplexity V A hA ≤
          (epsilon + delta + logSlack cA n : ENat) →
        ¬ T1BMarked V n epsilon x →
        ¬ T1CMarked V n k
          (epsilon + logSlack (cStrength + cDesc) n) x →
        ¬ T1DMarked V n k x →
        T3GoodElement V T x n k epsilon delta
          cStrength cProfile := by
  obtain ⟨cDesc, cStrongProfile, hStrong⟩ :=
    t1_not_cMarked_strongProfile_to_polygon V T hV hT
  obtain ⟨cShiftStrength, cShiftProfile, hShifted⟩ :=
    t1_shifted_fullCube_strong_profile V T hV hT
  obtain ⟨cSingletonStrength, hSingleton⟩ :=
    t3_singleton_strong_profile_endpoint V T hV hT
  let cStrengthMin := max cShiftStrength cSingletonStrength
  refine ⟨cDesc, cStrengthMin, cStrengthMin, ?_⟩
  intro cStrength hStrength cA
  obtain ⟨cPlain, hPlain⟩ :=
    t3_avoiding_set_plain_profile_bounds V hV cA
  obtain ⟨cSingletonProfile, hSingletonEndpoint⟩ :=
    hSingleton cPlain
  let cProfile :=
    cA + cPlain + cStrongProfile + cShiftProfile +
      cSingletonProfile
  refine ⟨cProfile, by dsimp [cProfile]; omega, ?_⟩
  intro n k epsilon delta A hA x hEndpoint hepsilon hdelta
      hkn hAcard hxA hxlen hAcomplexity hnotB hnotC hnotD
  obtain ⟨hKlower, hKupper, hPlainNeighborhood⟩ :=
    hPlain n k epsilon delta A hA x hepsilon hdelta hkn
      hAcard hxA hxlen hAcomplexity hnotB hnotD
  have hPlainSlack :
      delta + logSlack cPlain n ≤
        delta + logSlack cProfile n := by
    gcongr
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hStrongSlack :
      logSlack cStrongProfile n ≤
        delta + logSlack cProfile n := by
    have h := logSlack_mono_left
      (show cStrongProfile ≤ cProfile by
        dsimp [cProfile]
        omega) n
    omega
  have hShiftSlack :
      logSlack cShiftProfile n ≤
        delta + logSlack cProfile n := by
    have h := logSlack_mono_left
      (show cShiftProfile ≤ cProfile by
        dsimp [cProfile]
        omega) n
    omega
  have hSingletonSlack :
      logSlack cSingletonProfile n ≤
        logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hShiftStrength0 : cShiftStrength ≤ epsilon :=
    (Nat.le_max_left _ _).trans hEndpoint
  have hSingletonStrength0 : cSingletonStrength ≤ epsilon :=
    (Nat.le_max_right _ _).trans hEndpoint
  have hShiftBudget :
      epsilon + logSlack cShiftStrength n ≤
        epsilon + logSlack cStrength n := by
    exact Nat.add_le_add_left
      (logSlack_mono_left
        ((Nat.le_max_left _ _).trans hStrength) n) epsilon
  have hnotC' :
      ¬ T1CMarked V n k
        ((epsilon + logSlack cStrength n) +
          logSlack cDesc n) x := by
    have hbudget :
        (epsilon + logSlack cStrength n) +
            logSlack cDesc n =
          epsilon + logSlack (cStrength + cDesc) n := by
      rw [Nat.add_assoc, logSlack_add_const]
    rwa [hbudget]
  have hStrongDirected :=
    hStrong n k (epsilon + logSlack cStrength n) x
      hkn hxlen hnotC'
  have hSingletonBase :=
    hSingletonEndpoint x n k epsilon delta hKupper
      hSingletonStrength0
  have hSingletonFinal :
      (k + delta + logSlack cSingletonProfile n, 0) ∈
        strongDescriptionProfileSet V T x
          (epsilon + logSlack cStrength n) :=
    hSingletonBase.mono_epsilon (Nat.le_add_right _ _)
  unfold T3GoodElement
  refine ⟨hxlen, hKlower, hKupper.trans ?_,
    hPlainNeighborhood.mono hPlainSlack, ?_⟩
  · exact_mod_cast
      (Nat.add_le_add_left
        (logSlack_mono_left (show cPlain ≤ cProfile by
          dsimp [cProfile]
          omega) n) (k + delta))
  · constructor
    · intro q hq
      obtain ⟨q', hq', hdist⟩ := hStrongDirected q hq
      exact ⟨q', hq', hdist.trans hStrongSlack⟩
    · intro q hq
      by_cases hqk : k ≤ q.1
      · have hprofile :
            (q.1 + (delta + logSlack cProfile n), q.2) ∈
              strongDescriptionProfileSet V T x
                (epsilon + logSlack cStrength n) :=
          (hSingletonFinal.mono_i (by
            have hs := hSingletonSlack
            omega)).mono_j (Nat.zero_le _)
        refine ⟨(q.1 + (delta + logSlack cProfile n), q.2),
          hprofile, ?_⟩
        simp [natPairLInfDistance]
      · have hqsum : n ≤ q.1 + q.2 := by
          unfold t1StrongPolygon at hq
          rcases hq with hq | hq
          · exact False.elim (hqk hq)
          · exact hq
        have hqi : q.1 ≤ n := by omega
        have hbase :=
          hShifted x n epsilon q.1 hxlen hShiftStrength0 hqi
        have hbase' :
            (q.1 + logSlack cShiftProfile n, n - q.1) ∈
              strongDescriptionProfileSet V T x
                (epsilon + logSlack cStrength n) :=
          hbase.mono_epsilon hShiftBudget
        have hprofile :
            (q.1 + (delta + logSlack cProfile n), q.2) ∈
              strongDescriptionProfileSet V T x
                (epsilon + logSlack cStrength n) :=
          (hbase'.mono_i (by omega)).mono_j (by omega)
        refine ⟨(q.1 + (delta + logSlack cProfile n), q.2),
          hprofile, ?_⟩
        simp [natPairLInfDistance]

/-- Fixed-strength corollary of
`t3_goodElement_of_avoiding_set_at_strength`. -/
theorem t3_goodElement_of_avoiding_set
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ cDesc cStrength cEndpoint : Nat,
      ∀ cA : Nat, ∃ cProfile : Nat, cA ≤ cProfile ∧
        ∀ (n k epsilon delta : Nat) (A : Finset BitString)
          (hA : A.Nonempty) (x : BitString),
        cEndpoint ≤ epsilon →
        epsilon ≤ k →
        delta ≤ k - epsilon →
        k + 4 ≤ n →
        A.card = 2 ^ (k - epsilon) →
        x ∈ A →
        x.length = n →
        plainSetComplexity V A hA ≤
          (epsilon + delta + logSlack cA n : ENat) →
        ¬ T1BMarked V n epsilon x →
        ¬ T1CMarked V n k
          (epsilon + logSlack (cStrength + cDesc) n) x →
        ¬ T1DMarked V n k x →
        T3GoodElement V T x n k epsilon delta
          cStrength cProfile := by
  obtain ⟨cDesc, cStrength, cEndpoint, hGood⟩ :=
    t3_goodElement_of_avoiding_set_at_strength V T hV hT
  exact ⟨cDesc, cStrength, cEndpoint,
    hGood cStrength le_rfl⟩

/-- Interior (`k + 4 ≤ n`) form with its internally selected strength
constant. -/
theorem t3_interior_with_strength_floor
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T)
    (cStrengthFloor : Nat) :
  ∃ c0 cStrength cProfile : Nat,
    cStrengthFloor ≤ cStrength ∧
    ∀ n k epsilon delta,
      c0 ≤ epsilon →
      epsilon ≤ k →
      delta ≤ k - epsilon →
      k + 4 ≤ n →
      Nonempty
        (T3Witness V T n k epsilon delta cStrength cProfile) := by
  obtain ⟨cDesc, cStrengthMin, cEndpoint, hGood⟩ :=
    t3_goodElement_of_avoiding_set_at_strength V T hV hT
  let cStrength := max cStrengthMin cStrengthFloor
  obtain ⟨cCore, cA, hCore⟩ :=
    exists_t3_avoiding_set_core V hV (cStrength + cDesc)
  obtain ⟨cProfile, hcAProfile, hProfile⟩ :=
    hGood cStrength (by
      dsimp [cStrength]
      exact Nat.le_max_left _ _) cA
  refine ⟨max cCore cEndpoint, cStrength, cProfile, ?_, ?_⟩
  · dsimp [cStrength]
    exact Nat.le_max_right _ _
  · intro n k epsilon delta hc0 hepsilon hdelta hkn
    have hCore0 : cCore ≤ epsilon :=
      (Nat.le_max_left _ _).trans hc0
    have hEndpoint : cEndpoint ≤ epsilon :=
      (Nat.le_max_right _ _).trans hc0
    obtain ⟨A, hA, bad, hAcube, hAcard, hbadSub, hbadCard,
        hAcomplexity, havoid⟩ :=
      hCore n k epsilon delta hCore0 hepsilon hdelta hkn
    have hAcomplexity' :
        plainSetComplexity V A hA ≤
          (epsilon + delta + logSlack cProfile n : ENat) :=
      hAcomplexity.trans (by
        exact_mod_cast (Nat.add_le_add_left
          (logSlack_mono_left hcAProfile n) (epsilon + delta)))
    refine ⟨{
      A := A
      A_nonempty := hA
      A_subset_cube := hAcube
      A_card := hAcard
      A_complexity := hAcomplexity'
      exceptional := bad
      exceptional_subset := hbadSub
      exceptional_card := hbadCard
      good := ?_ }⟩
    intro x hx
    obtain ⟨hxlen, hnotB, hnotC, hnotD⟩ := havoid x hx
    exact hProfile n k epsilon delta A hA x hEndpoint
      hepsilon hdelta hkn hAcard (Finset.mem_sdiff.mp hx).1
      hxlen hAcomplexity hnotB hnotC hnotD

/-- Full T3 witness construction in the interior range of the executable
smaller-quota run.  This is the public theorem's entire non-boundary case. -/
theorem t3_interior
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c0 cStrength cProfile : Nat,
      ∀ n k epsilon delta : Nat,
        c0 ≤ epsilon →
        epsilon ≤ k →
        delta ≤ k - epsilon →
        k + 4 ≤ n →
        Nonempty
          (T3Witness V T n k epsilon delta
            cStrength cProfile) := by
  obtain ⟨cDesc, cStrength, cEndpoint, hGood⟩ :=
    t3_goodElement_of_avoiding_set V T hV hT
  obtain ⟨cCore, cA, hCore⟩ :=
    exists_t3_avoiding_set_core V hV (cStrength + cDesc)
  obtain ⟨cProfile, hcAProfile, hProfile⟩ := hGood cA
  refine ⟨max cCore cEndpoint, cStrength, cProfile, ?_⟩
  intro n k epsilon delta hc0 hepsilon hdelta hkn
  have hCore0 : cCore ≤ epsilon :=
    (Nat.le_max_left _ _).trans hc0
  have hEndpoint : cEndpoint ≤ epsilon :=
    (Nat.le_max_right _ _).trans hc0
  obtain ⟨A, hA, bad, hAcube, hAcard, hbadSub, hbadCard,
      hAcomplexity, havoid⟩ :=
    hCore n k epsilon delta hCore0 hepsilon hdelta hkn
  have hAcomplexity' :
      plainSetComplexity V A hA ≤
        (epsilon + delta + logSlack cProfile n : ENat) :=
    hAcomplexity.trans (by
      exact_mod_cast (Nat.add_le_add_left
        (logSlack_mono_left hcAProfile n) (epsilon + delta)))
  refine ⟨{
    A := A
    A_nonempty := hA
    A_subset_cube := hAcube
    A_card := hAcard
    A_complexity := hAcomplexity'
    exceptional := bad
    exceptional_subset := hbadSub
    exceptional_card := hbadCard
    good := ?_ }⟩
  intro x hx
  obtain ⟨hxlen, hnotB, hnotC, hnotD⟩ := havoid x hx
  exact hProfile n k epsilon delta A hA x hEndpoint
    hepsilon hdelta hkn hAcard (Finset.mem_sdiff.mp hx).1
    hxlen hAcomplexity hnotB hnotC hnotD

/-- At `delta = 0`, taking the whole initial model as exceptional closes the
exact boundary case; consequently the pointwise good-element obligation is
vacuous. -/
theorem t3_delta_zero
    (V T : Map) (hV : isOptimalConditional V) :
    ∃ cProfile, ∀ cStrength n k epsilon,
      epsilon ≤ k →
      k ≤ n →
      Nonempty
        (T3Witness V T n k epsilon 0 cStrength cProfile) := by
  obtain ⟨cProfile, hComplexity⟩ :=
    plainSetComplexity_t3InitialCurrent_le V hV
  refine ⟨cProfile, ?_⟩
  intro cStrength n k epsilon hepsilon hkn
  let A := (t1InitialCurrent n k epsilon).toFinset
  have hLength := t1InitialCurrent_length hepsilon hkn
  have hCard : A.card = 2 ^ (k - epsilon) := by
    dsimp [A]
    rw [List.toFinset_card_of_nodup
      (t1InitialCurrent_nodup n k epsilon)]
    exact hLength
  have hA : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have : A.card = 0 := by simp [hEmpty]
    rw [hCard] at this
    have hPos := Nat.two_pow_pos (k - epsilon)
    omega
  have hAComplexity :
      plainSetComplexity V A hA ≤
        (epsilon + 0 + logSlack cProfile n : ENat) :=
    hComplexity n k epsilon 0 hepsilon (by omega) hkn hA
  refine ⟨{
    A := A
    A_nonempty := hA
    A_subset_cube := t1InitialCurrent_subset_stringsOfLength n k epsilon
    A_card := hCard
    A_complexity := hAComplexity
    exceptional := A
    exceptional_subset := Finset.Subset.rfl
    exceptional_card := ?_
    good := ?_ }⟩
  · simp [hCard]
  · intro x hx
    simp [A] at hx

theorem t3_boundary_goodElement_at_strength
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
  ∃ c0 cStrengthMin : Nat, ∀ cA,
    ∃ cProfile, cA ≤ cProfile ∧
    ∀ (cStrength n k epsilon delta : Nat) (x : BitString),
      cStrengthMin ≤ cStrength →
      c0 ≤ epsilon →
      epsilon ≤ k →
      k ≤ n →
      n < k + 4 →
      x.length = n →
      (k : ENat) ≤ plainK V x →
      plainK V x ≤
        (k + delta + logSlack cA n : ENat) →
      T3GoodElement V T x n k epsilon delta
        cStrength cProfile := by
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  let cK := cLen + 4
  obtain ⟨c0, cStrengthMin, hPointwise⟩ :=
    t1_boundary_pointwise_profile V T hV hT
  obtain ⟨cBoundaryProfile, _hcKProfile, hBoundaryProfile⟩ :=
    hPointwise cK
  refine ⟨c0, cStrengthMin, ?_⟩
  intro cA
  let cProfile := cA + cBoundaryProfile
  refine ⟨cProfile, by dsimp [cProfile]; omega, ?_⟩
  intro cStrength n k epsilon delta x hStrength hc0
      hepsilon hkn hboundary hxlen hKlower hKupper
  have hLiteral :
      plainK V x ≤ (k + logSlack cK n : ENat) := by
    calc
      plainK V x ≤ (n : ENat) + (cLen : ENat) := by
        simpa [hxlen] using hLen x
      _ ≤ (k + logSlack cK n : Nat) := by
        exact_mod_cast (show n + cLen ≤ k + logSlack cK n by
          dsimp [cK]
          unfold logSlack
          omega)
  obtain ⟨hPlain, hStrong⟩ :=
    hBoundaryProfile cStrength n k epsilon x hStrength hc0
      hepsilon hkn hboundary hxlen hKlower hLiteral
  have hProfileSlack :
      logSlack cBoundaryProfile n ≤
        delta + logSlack cProfile n := by
    have hmono := logSlack_mono_left
      (show cBoundaryProfile ≤ cProfile by
        dsimp [cProfile]
        omega) n
    omega
  unfold T3GoodElement
  refine ⟨hxlen, hKlower, hKupper.trans ?_,
    hPlain.mono hProfileSlack, hStrong.mono hProfileSlack⟩
  exact_mod_cast
    (Nat.add_le_add_left
      (logSlack_mono_left (show cA ≤ cProfile by
        dsimp [cProfile]
        omega) n) (k + delta))

theorem t3_boundary_at_strength
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
  ∃ cStrengthMin, ∀ cStrength,
    cStrengthMin ≤ cStrength →
    ∃ c0 cProfile, ∀ n k epsilon delta,
      0 < delta →
      c0 ≤ epsilon →
      epsilon ≤ k →
      k ≤ n →
      delta ≤ k - epsilon →
      n < k + 4 →
      Nonempty
        (T3Witness V T n k epsilon delta cStrength cProfile) := by
  obtain ⟨q, hq⟩ := Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨cTerminal, hTerminal⟩ :=
    exists_t3BoundaryD_terminal_model V hV
  obtain ⟨cA, hReplay⟩ :=
    plainSetComplexity_t3BoundaryDRun_current_le V hV q hq
  obtain ⟨cK, hKupper⟩ :=
    t3_avoiding_set_plainK_upper V hV cA
  obtain ⟨cGood0, cStrengthMin, hGoodFamily⟩ :=
    t3_boundary_goodElement_at_strength V T hV hT
  obtain ⟨cProfile, hInputProfile, hGood⟩ :=
    hGoodFamily (max cA cK)
  refine ⟨cStrengthMin, ?_⟩
  intro cStrength hStrength
  refine ⟨max cTerminal cGood0, cProfile, ?_⟩
  intro n k epsilon delta _hdeltaPos hc0 hepsilon hkn
      hdelta hboundary
  have hTerminal0 : cTerminal ≤ epsilon :=
    (Nat.le_max_left _ _).trans hc0
  have hGood0 : cGood0 ≤ epsilon :=
    (Nat.le_max_right _ _).trans hc0
  obtain ⟨t, A, bad, hAeq, _hbadEq, hAcube, hAcard,
      hbadSub, hbadCard, hKlower, _hwidth⟩ :=
    hTerminal hq n k epsilon delta hTerminal0 hepsilon hdelta hkn
  have hA : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hzero : A.card = 0 := by simp [hEmpty]
    rw [hAcard] at hzero
    exact (Nat.two_pow_pos (k - epsilon)).ne' hzero
  have hRunA :
      (t3BoundaryDRun q n k epsilon delta t).current.toFinset.Nonempty := by
    rw [← hAeq]
    exact hA
  have hAcomplexityBase :
      plainSetComplexity V A hA ≤
        (epsilon + delta + logSlack cA n : ENat) := by
    simpa [hAeq] using
      hReplay n k epsilon delta t hRunA hepsilon hdelta hkn
  have hAcomplexity :
      plainSetComplexity V A hA ≤
        (epsilon + delta + logSlack cProfile n : ENat) :=
    hAcomplexityBase.trans (by
      exact_mod_cast (Nat.add_le_add_left
        (logSlack_mono_left
          ((Nat.le_max_left _ _).trans hInputProfile) n)
        (epsilon + delta)))
  refine ⟨{
    A := A
    A_nonempty := hA
    A_subset_cube := hAcube
    A_card := hAcard
    A_complexity := hAcomplexity
    exceptional := bad
    exceptional_subset := hbadSub
    exceptional_card := le_of_lt hbadCard
    good := ?_ }⟩
  intro x hx
  have hxA : x ∈ A := (Finset.mem_sdiff.mp hx).1
  have hxlen : x.length = n :=
    (memStringsOfLength n x).mp (hAcube hxA)
  have hKupperBase :
      plainK V x ≤
        (k + delta + logSlack cK n : ENat) :=
    hKupper n k epsilon delta A hA x hepsilon hdelta hkn
      hAcard hxA hxlen hAcomplexityBase
  have hKupperInput :
      plainK V x ≤
        (k + delta + logSlack (max cA cK) n : ENat) :=
    hKupperBase.trans (by
      exact_mod_cast (Nat.add_le_add_left
        (logSlack_mono_left (Nat.le_max_right _ _) n)
        (k + delta)))
  exact hGood cStrength n k epsilon delta x hStrength hGood0
    hepsilon hkn hboundary hxlen (hKlower x hx) hKupperInput

def T3Witness.mono_profile
    {V T : Map}
    {n k epsilon delta cStrength cProfile cProfile' : Nat}
    (hProfile : cProfile ≤ cProfile')
    (w : T3Witness V T n k epsilon delta cStrength cProfile) :
    T3Witness V T n k epsilon delta cStrength cProfile' := by
  have hSlack : logSlack cProfile n ≤ logSlack cProfile' n :=
    logSlack_mono_left hProfile n
  refine {
    A := w.A
    A_nonempty := w.A_nonempty
    A_subset_cube := w.A_subset_cube
    A_card := w.A_card
    A_complexity := w.A_complexity.trans ?_
    exceptional := w.exceptional
    exceptional_subset := w.exceptional_subset
    exceptional_card := w.exceptional_card
    good := ?_ }
  · exact_mod_cast
      (Nat.add_le_add_left hSlack (epsilon + delta))
  · intro x hx
    obtain ⟨hxlen, hKlower, hKupper, hPlain, hStrong⟩ :=
      w.good x hx
    unfold T3GoodElement
    refine ⟨hxlen, hKlower, hKupper.trans ?_,
      hPlain.mono ?_, hStrong.mono ?_⟩
    · exact_mod_cast
        (Nat.add_le_add_left hSlack (k + delta))
    · exact Nat.add_le_add_left hSlack delta
    · exact Nat.add_le_add_left hSlack delta

theorem t3
    (V T : Map)
    (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    T3Statement V T := by
  obtain ⟨cZeroProfile, hZero⟩ :=
    t3_delta_zero V T hV
  obtain ⟨cBoundaryStrengthMin, hBoundaryFamily⟩ :=
    t3_boundary_at_strength V T hV hT
  obtain ⟨cInterior0, cStrength, cInteriorProfile,
      hStrength, hInterior⟩ :=
    t3_interior_with_strength_floor V T hV hT
      cBoundaryStrengthMin
  obtain ⟨cBoundary0, cBoundaryProfile, hBoundary⟩ :=
    hBoundaryFamily cStrength hStrength
  let c0 := max cInterior0 cBoundary0
  let cProfile :=
    max cZeroProfile (max cInteriorProfile cBoundaryProfile)
  refine ⟨c0, cStrength, cProfile, ?_⟩
  intro n k epsilon delta hc0 hepsilon hkn hdelta
  by_cases hdeltaZero : delta = 0
  · subst delta
    obtain ⟨w⟩ := hZero cStrength n k epsilon hepsilon hkn
    exact ⟨w.mono_profile (by
      dsimp [cProfile]
      exact Nat.le_max_left _ _)⟩
  · have hdeltaPos : 0 < delta := Nat.pos_of_ne_zero hdeltaZero
    by_cases hInteriorRange : k + 4 ≤ n
    · obtain ⟨w⟩ := hInterior n k epsilon delta
        ((Nat.le_max_left _ _).trans hc0) hepsilon hdelta
        hInteriorRange
      exact ⟨w.mono_profile (by
        dsimp [cProfile]
        exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _))⟩
    · obtain ⟨w⟩ := hBoundary n k epsilon delta hdeltaPos
        ((Nat.le_max_right _ _).trans hc0) hepsilon hkn hdelta
        (by omega)
      exact ⟨w.mono_profile (by
        dsimp [cProfile]
        exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _))⟩

end Kolmogorov
