import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongProfile
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FullCube
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileBridges
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.Restricted.HammingGap
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingPredicates
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CylinderRealization
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation.Part01

/-!
# Separating the plain and the strong profile: the statements

What the marking construction of `Separation/Part01` yields.
`t1_polygon_to_plainProfile` and `t1_avoiding_set_plain_profile_bounds` give the plain side —
a string of a low-complexity avoiding set has complexity `k + O(log n)` and its plain profile
traces the dashed polygon — and `t1_not_cMarked_strongProfile_to_polygon` and
`t1_avoiding_set_profile_bounds` add the strong side, so a string escaping all three marks has
both profiles under control.  `card_le_two_pow_of_shift` is the size bound for the shifted
model used there.

The module also fixes the vocabulary around antistochasticity: `IsAntistochastic`,
`AntistochasticExistenceStatement`, `PropAntistochasticIsNormal` and the proposition
`prop_antistochastic_is_normal`, that an antistochastic string is normal.
`standardEnumeratorCode` and the `finiteSetLogCard_standardBlock_*` lemmas connect these to
the standard blocks, and the fixed-split pair machinery at the end
(`fixedSplitPairDecompressor`, `appendDecodedPair`,
`fixedSplit_append_pairCode_totalEquivalent`) shows a fixed split of a concatenation and the
repository's pair encoding are total-equivalent.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- Positive ordinary Figure 6 geometry.  The full cube traces the first
diagonal, the avoiding set traces the second, and the singleton covers the
right-hand ray. -/
theorem t1_polygon_to_plainProfile
    (V : Map) (hV : isOptimalConditional V) :
    ∀ cA cK : Nat, ∃ c : Nat,
      ∀ (n k epsilon : Nat) (A : Finset BitString)
        (hA : A.Nonempty) (x : BitString),
      epsilon ≤ k →
      k ≤ n →
      A.card = 2 ^ (k - epsilon) →
      x ∈ A →
      x.length = n →
      plainSetComplexity V A hA ≤
        (epsilon + logSlack cA n : ENat) →
      plainK V x ≤ (k + logSlack cK n : ENat) →
      ∀ q ∈ t1PlainPolygon n k epsilon,
        ∃ q' ∈ plainDescriptionProfileSet V x,
          natPairLInfDistance q q' ≤ logSlack c n := by
  obtain ⟨cCube, hCube⟩ :=
    plainSetComplexity_fullCube_le_logSlack V hV
  obtain ⟨cSingleton, hSingleton⟩ :=
    plainSetComplexity_singleton_le_plainK V hV
  obtain ⟨cShift, hShift⟩ :=
    inPlainDescriptionProfile_shift V hV
  intro cA cK
  let c := cCube + cSingleton + cShift + cA + cK
  refine ⟨c, ?_⟩
  intro n k epsilon A hA x hepsilon hkn hAcard hxA hxlen
      hAcomplexity hKupper q hq
  let delta := logSlack c n
  have hfull :
      InPlainDescriptionProfile V x (logSlack cCube n) n := by
    refine ⟨stringsOfLength n, codedStringsOfLength_nonempty n,
      (mem_stringsOfLength n x).mpr hxlen, hCube n, ?_⟩
    rw [card_stringsOfLength]
  have hmiddle :
      InPlainDescriptionProfile V x
        (epsilon + logSlack cA n) (k - epsilon) := by
    refine ⟨A, hA, hxA, hAcomplexity, ?_⟩
    rw [hAcard]
  have hCubeShift :
      logSlack cCube n + logSlack cShift n ≤ delta := by
    rw [logSlack_add_const]
    dsimp [delta, c]
    exact logSlack_mono_left (by omega) n
  have hAShift :
      logSlack cA n + logSlack cShift n ≤ delta := by
    rw [logSlack_add_const]
    dsimp [delta, c]
    exact logSlack_mono_left (by omega) n
  have hKSingleton :
      logSlack cK n + cSingleton ≤ delta := by
    calc
      logSlack cK n + cSingleton
          ≤ logSlack cK n + logSlack cSingleton n := by
        gcongr
        simp [logSlack]
      _ = logSlack (cK + cSingleton) n :=
        logSlack_add_const cK cSingleton n
      _ ≤ delta := by
        dsimp [delta, c]
        exact logSlack_mono_left (by omega) n
  by_cases hqepsilon : q.1 < epsilon
  · have hqsum : n ≤ q.1 + q.2 := by
      unfold t1PlainPolygon at hq
      simpa [hqepsilon] using hq
    have hqN : q.1 ≤ n := by
      omega
    have hshiftSlack :
        logSlack cShift q.1 ≤ logSlack cShift n :=
      logSlack_mono_right cShift hqN
    have hcomplexity :
        logSlack cCube n + q.1 + logSlack cShift q.1 ≤
          q.1 + delta := by
      omega
    have hshifted :=
      hShift x (logSlack cCube n) n q.1 hfull
    have hprofile :
        InPlainDescriptionProfile V x (q.1 + delta) q.2 := by
      refine (hshifted.mono_i hcomplexity).mono_j ?_
      omega
    refine ⟨(q.1 + delta, q.2), hprofile, ?_⟩
    unfold natPairLInfDistance
    simp [delta]
  · have hqepsilon' : epsilon ≤ q.1 := by
      omega
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
          epsilon + logSlack cA n + s +
              logSlack cShift s ≤ q.1 + delta := by
        omega
      have hsize :
          k - epsilon - s ≤ q.2 := by
        dsimp [s]
        omega
      have hshifted :=
        hShift x (epsilon + logSlack cA n)
          (k - epsilon) s hmiddle
      have hprofile :
          InPlainDescriptionProfile V x (q.1 + delta) q.2 :=
        (hshifted.mono_i hcomplexity).mono_j hsize
      refine ⟨(q.1 + delta, q.2), hprofile, ?_⟩
      unfold natPairLInfDistance
      simp [delta]
    · have hkq : k < q.1 := by
        omega
      have hsingletonComplexity :
          plainSetComplexity V {x} (Finset.singleton_nonempty x) ≤
            (q.1 + delta : Nat) := by
        calc
          plainSetComplexity V {x} (Finset.singleton_nonempty x)
              ≤ plainK V x + (cSingleton : ENat) :=
            hSingleton x
          _ ≤ (k + logSlack cK n : ENat) +
                (cSingleton : ENat) := by
            gcongr
          _ ≤ (q.1 + delta : Nat) := by
            exact_mod_cast (show
              k + logSlack cK n + cSingleton ≤
                q.1 + delta by
              omega)
      have hprofile :
          InPlainDescriptionProfile V x (q.1 + delta) q.2 := by
        refine ⟨{x}, Finset.singleton_nonempty x,
          Finset.mem_singleton.mpr rfl, hsingletonComplexity, ?_⟩
        simpa using Nat.one_le_two_pow
      refine ⟨(q.1 + delta, q.2), hprofile, ?_⟩
      unfold natPairLInfDistance
      simp [delta]

/-- Complete ordinary part of the avoiding-set argument: complexity is
`k+O(log n)` and the ordinary description profile is two-sided
logarithmically close to the dashed Figure 6 polygon. -/
theorem t1_avoiding_set_plain_profile_bounds
    (V : Map) (hV : isOptimalConditional V) :
    ∀ cA : Nat, ∃ cProfile : Nat,
      ∀ (n k epsilon : Nat) (A : Finset BitString)
        (hA : A.Nonempty) (x : BitString),
      epsilon ≤ k →
      k + 4 ≤ n →
      A.card = 2 ^ (k - epsilon) →
      x ∈ A →
      x.length = n →
      plainSetComplexity V A hA ≤
        (epsilon + logSlack cA n : ENat) →
      ¬ T1BMarked V n epsilon x →
      ¬ T1DMarked V n k x →
      (k : ENat) ≤ plainK V x ∧
      plainK V x ≤ (k + logSlack cProfile n : ENat) ∧
      ProfileSetsWithinNeighborhood
        (plainDescriptionProfileSet V x)
        (t1PlainPolygon n k epsilon)
        (logSlack cProfile n) := by
  intro cA
  obtain ⟨cK, hK⟩ :=
    t1_avoiding_set_plainK_upper V hV cA
  obtain ⟨cTo, hTo⟩ :=
    t1_plainProfile_to_polygon V hV
  obtain ⟨cFrom, hFrom⟩ :=
    t1_polygon_to_plainProfile V hV cA cK
  let cProfile := cK + cTo + cFrom
  refine ⟨cProfile, ?_⟩
  intro n k epsilon A hA x hepsilon hkn hAcard hxA hxlen
      hAcomplexity hnotB hnotD
  have hKlower : (k : ENat) ≤ plainK V x := by
    unfold T1DMarked at hnotD
    push_neg at hnotD
    exact hnotD hxlen
  have hKupper :=
    hK n k epsilon A hA x hepsilon (by omega)
      hAcard hxA hxlen hAcomplexity
  have hKslack :
      logSlack cK n ≤ logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hToslack :
      logSlack cTo n ≤ logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hFromslack :
      logSlack cFrom n ≤ logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  refine ⟨hKlower, hKupper.trans ?_, ?_⟩
  · exact_mod_cast (Nat.add_le_add_left hKslack k)
  · constructor
    · intro q hq
      obtain ⟨q', hq', hdist⟩ :=
        hTo n k epsilon x hepsilon hkn hxlen
          hnotB hnotD q hq
      exact ⟨q', hq', hdist.trans hToslack⟩
    · intro q hq
      obtain ⟨q', hq', hdist⟩ :=
        hFrom n k epsilon A hA x hepsilon (by omega)
          hAcard hxA hxlen hAcomplexity hKupper q hq
      exact ⟨q', hq', hdist.trans hFromslack⟩

/-- **The shifted model is small.**  Shifting a set `S` of positive size at the level
`min s (log₂ |S|)` produces a set `B` with `|B| * 2 ^ (min s (log₂ |S|)) ≤ |S|`.  If `|S|`
is at most `2 ^ j`, then `|B|` is at most `2 ^ (j - s)`: either the shift used the whole
`s`, and the factor `2 ^ s` is divided out, or the logarithm of `|S|` ran out first and `B`
is a singleton. -/
private lemma card_le_two_pow_of_shift {cardS cardB s j e : ℕ}
    (hSpos : 0 < cardS) (hSle : cardS ≤ 2 ^ j)
    (hBmul : cardB * 2 ^ (min s (Nat.log 2 cardS)) ≤ cardS)
    (hje : j - s ≤ e) : cardB ≤ 2 ^ e := by
  have hrPow : 2 ^ Nat.log 2 cardS ≤ cardS :=
    Nat.pow_le_of_le_log hSpos.ne' (Nat.le_refl _)
  by_cases hsr : s ≤ Nat.log 2 cardS
  · have hiEq : min s (Nat.log 2 cardS) = s := Nat.min_eq_left hsr
    rw [hiEq] at hBmul
    have hsPow : 2 ^ s ≤ cardS :=
      (Nat.pow_le_pow_right (by norm_num) hsr).trans hrPow
    have hsj : s ≤ j :=
      (Nat.pow_le_pow_iff_right (by norm_num)).mp (hsPow.trans hSle)
    have hmul : cardB * 2 ^ s ≤ 2 ^ (j - s) * 2 ^ s := by
      rw [← pow_add, Nat.sub_add_cancel hsj]
      exact hBmul.trans hSle
    exact (Nat.le_of_mul_le_mul_right hmul (pow_pos (by norm_num) s)).trans
      (Nat.pow_le_pow_right (by norm_num) hje)
  · have hrs : Nat.log 2 cardS < s := by omega
    have hiEq : min s (Nat.log 2 cardS) = Nat.log 2 cardS := Nat.min_eq_right hrs.le
    rw [hiEq] at hBmul
    have hlt : cardB * 2 ^ Nat.log 2 cardS < 2 * 2 ^ Nat.log 2 cardS := by
      calc cardB * 2 ^ Nat.log 2 cardS ≤ cardS := hBmul
        _ < 2 ^ (Nat.log 2 cardS + 1) :=
            Nat.lt_pow_succ_log_self (by norm_num) cardS
        _ = 2 * 2 ^ Nat.log 2 cardS := by rw [pow_succ]; ring
    have hBone : cardB ≤ 1 := by
      have := Nat.lt_of_mul_lt_mul_right hlt
      omega
    exact hBone.trans (Nat.one_le_pow _ _ (by norm_num))

/-- Strong-profile exclusion supplied by the absence of a source `C` mark.
A point far from both solid-polygon boundary pieces is shifted to a model of
plain complexity at most `k` and size at most `2^(n-k-4)`; Lemma `l1` then
turns its strength witness into exactly the code-profile witness forbidden by
`T1CMarked`. -/
theorem t1_not_cMarked_strongProfile_to_polygon
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ cDesc cProfile : Nat,
      ∀ (n k epsilon : Nat) (x : BitString),
      k + 4 ≤ n →
      x.length = n →
      ¬ T1CMarked V n k
        (epsilon + logSlack cDesc n) x →
      ∀ q ∈ strongDescriptionProfileSet V T x epsilon,
        ∃ q' ∈ t1StrongPolygon n k,
          natPairLInfDistance q q' ≤ logSlack cProfile n := by
  obtain ⟨cShift, hShift⟩ :=
    strong_description_shift V hV T hT
  obtain ⟨cL1, hL1⟩ :=
    strange_string_lemma_1 V T hV hT
  let cDesc := cShift + cL1
  let cProfile := cShift + 5
  refine ⟨cDesc, cProfile, ?_⟩
  intro n k epsilon x hkn hxlen hnotC q hq
  let delta := logSlack cProfile n
  let shiftSlack := logSlack cShift n
  have hshiftDelta : shiftSlack + 4 ≤ delta := by
    dsimp [shiftSlack, delta, cProfile]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits n).length]
  by_cases hpolygon : q ∈ t1StrongPolygon n k
  · exact ⟨q, hpolygon, by simp [natPairLInfDistance]⟩
  · have hqk : q.1 < k := by
      unfold t1StrongPolygon at hpolygon
      simp only [Set.mem_setOf_eq, not_or, not_le] at hpolygon
      exact hpolygon.1
    have hqsum : q.1 + q.2 < n := by
      unfold t1StrongPolygon at hpolygon
      simp only [Set.mem_setOf_eq, not_or, not_le] at hpolygon
      exact hpolygon.2
    by_cases hknear : k ≤ q.1 + delta
    · let q' : Nat × Nat := (k, q.2)
      refine ⟨q', ?_, ?_⟩
      · unfold t1StrongPolygon
        simp [q']
      · unfold natPairLInfDistance
        simp only [q', Nat.sub_self, zero_add]
        omega
    · by_cases hnnear : n ≤ q.1 + q.2 + delta
      · let q' : Nat × Nat := (q.1, n - q.1)
        refine ⟨q', ?_, ?_⟩
        · unfold t1StrongPolygon
          simp only [Set.mem_setOf_eq, q']
          exact Or.inr (by omega)
        · unfold natPairLInfDistance
          simp only [q', Nat.sub_self, zero_add]
          omega
      · have hkfar : q.1 + delta < k := by
          omega
        have hnfar : q.1 + q.2 + delta < n := by
          omega
        obtain ⟨S, hS, hPlain, hStrong⟩ := hq
        let s := k - q.1 - shiftSlack
        have hsPos : 0 < s := by
          dsimp [s]
          omega
        have hsN : s ≤ n := by
          dsimp [s]
          omega
        let r := Nat.log 2 S.card
        let i := min s r
        have hScardPos : 0 < S.card := hS.card_pos
        have hrPow : 2 ^ r ≤ S.card := by
          dsimp [r]
          exact Nat.pow_le_of_le_log hScardPos.ne'
            (Nat.le_refl _)
        have hiR : i ≤ r := Nat.min_le_right _ _
        have hiS : i ≤ s := Nat.min_le_left _ _
        have hiPow : 2 ^ i ≤ S.card :=
          (Nat.pow_le_pow_right (by norm_num) hiR).trans hrPow
        obtain ⟨B, hxB, hBStrong, hBmul, hBcomp⟩ :=
          hShift x S hPlain.1 epsilon hStrong i hiPow
        let hB : B.Nonempty := ⟨x, hxB⟩
        have hiN : i ≤ n := hiS.trans hsN
        have hiSlack :
            logSlack cShift i ≤ shiftSlack := by
          exact logSlack_mono_right cShift hiN
        have hsadd :
            q.1 + shiftSlack + s = k := by
          dsimp [s]
          omega
        have hBcomplexity :
            plainSetComplexity V B hB ≤ (k : ENat) := by
          calc
            plainSetComplexity V B hB
                ≤ plainSetComplexity V S hS +
                    (i : ENat) +
                    (logSlack cShift i : ENat) := hBcomp
            _ ≤ (q.1 : ENat) + (i : ENat) +
                  (logSlack cShift i : ENat) := by
              gcongr
              exact hPlain.2.1
            _ ≤ (k : ENat) := by
              exact_mod_cast (show
                q.1 + i + logSlack cShift i ≤ k by
                omega)
        have hBcard :
            B.card ≤ 2 ^ (n - k - 4) :=
          card_le_two_pow_of_shift hScardPos hPlain.2.2 hBmul (by omega)
        have hcodeProfile :=
          hL1 x B hB (epsilon + logSlack cShift i) n
            hxlen hxB hBStrong
        have hcodeBudget :
            epsilon + logSlack cShift i + logSlack cL1 n ≤
              epsilon + logSlack cDesc n := by
          have hsum :
              logSlack cShift n + logSlack cL1 n =
                logSlack cDesc n := by
            dsimp [cDesc]
            exact logSlack_add_const cShift cL1 n
          omega
        have hcodeProfile' :
            InPlainDescriptionProfile V (codedUniformOn B hB).code
              (epsilon + logSlack cDesc n) n :=
          hcodeProfile.mono_i hcodeBudget
        exact (hnotC ⟨hxlen, B, hB, hxB, hBcomplexity,
          hBcard, hcodeProfile'⟩).elim

/-- A string of a low-complexity set `A` of size `2 ^ (k - epsilon)` that escapes all three T1
markings has plain complexity between `k` and `k` plus a logarithmic term, its plain description
profile lies within logarithmic distance of the T1 plain polygon, and its strong profile is
covered by the T1 strong polygon. -/
theorem t1_avoiding_set_profile_bounds
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ cDesc cEndpoint : Nat, ∀ cA : Nat, ∃ cProfile : Nat,
      ∀ (n k epsilon : Nat) (A : Finset BitString)
        (hA : A.Nonempty) (x : BitString),
      cEndpoint ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      A ⊆ stringsOfLength n →
      A.card = 2 ^ (k - epsilon) →
      x ∈ A →
      x.length = n →
      plainSetComplexity V A hA ≤ (epsilon + logSlack cA n : ENat) →
      ¬ T1BMarked V n epsilon x →
      ¬ T1CMarked V n k (epsilon + logSlack cDesc n) x →
      ¬ T1DMarked V n k x →
      (k : ENat) ≤ plainK V x ∧
      plainK V x ≤ (k + logSlack cProfile n : ENat) ∧
      ProfileSetsWithinNeighborhood
        (plainDescriptionProfileSet V x)
        (t1PlainPolygon n k epsilon)
        (logSlack cProfile n) ∧
      (∀ q ∈ strongDescriptionProfileSet V T x epsilon,
        ∃ q' ∈ t1StrongPolygon n k,
          natPairLInfDistance q q' ≤ logSlack cProfile n) ∧
      (logSlack cProfile n, n) ∈
        strongDescriptionProfileSet V T x epsilon ∧
      (k + logSlack cProfile n, 0) ∈
        strongDescriptionProfileSet V T x epsilon := by
  obtain ⟨cDesc, cStrongProfile, hStrong⟩ :=
    t1_not_cMarked_strongProfile_to_polygon V T hV hT
  obtain ⟨cFullStrength, cFullProfile, hFull⟩ :=
    t1_fullCube_strong_profile_endpoint V T hV hT
  obtain ⟨cSingletonStrength, hSingleton⟩ :=
    t1_singleton_strong_profile_endpoint V T hV hT
  refine ⟨cDesc, max cFullStrength cSingletonStrength, ?_⟩
  intro cA
  obtain ⟨cPlain, hPlain⟩ :=
    t1_avoiding_set_plain_profile_bounds V hV cA
  obtain ⟨cSingletonProfile, hSingletonEndpoint⟩ :=
    hSingleton cPlain
  let cProfile :=
    cPlain + cStrongProfile + cFullProfile + cSingletonProfile
  refine ⟨cProfile, ?_⟩
  intro n k epsilon A hA x hEndpoint hepsilon hkn _hAcube
      hAcard hxA hxlen hAcomplexity hnotB hnotC hnotD
  obtain ⟨hKlower, hKupper, hPlainNeighborhood⟩ :=
    hPlain n k epsilon A hA x hepsilon hkn hAcard hxA
      hxlen hAcomplexity hnotB hnotD
  have hPlainSlack :
      logSlack cPlain n ≤ logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hStrongSlack :
      logSlack cStrongProfile n ≤ logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hFullSlack :
      logSlack cFullProfile n ≤ logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hSingletonSlack :
      logSlack cSingletonProfile n ≤ logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hFullStrength : cFullStrength ≤ epsilon :=
    (Nat.le_max_left _ _).trans hEndpoint
  have hSingletonStrength : cSingletonStrength ≤ epsilon :=
    (Nat.le_max_right _ _).trans hEndpoint
  have hStrongDirected :=
    hStrong n k epsilon x hkn hxlen hnotC
  have hFullEndpoint :=
    hFull x n epsilon hxlen hFullStrength
  have hSingletonEndpoint :=
    hSingletonEndpoint x n k epsilon hKupper
      hSingletonStrength
  refine ⟨hKlower, hKupper.trans ?_,
    hPlainNeighborhood.mono hPlainSlack, ?_, ?_, ?_⟩
  · exact_mod_cast (Nat.add_le_add_left hPlainSlack k)
  · intro q hq
    obtain ⟨q', hq', hdist⟩ := hStrongDirected q hq
    exact ⟨q', hq', hdist.trans hStrongSlack⟩
  · exact hFullEndpoint.mono_i hFullSlack
  · exact hSingletonEndpoint.mono_i
      (Nat.add_le_add_left hSingletonSlack k)

/-! ### Normal strings and standard descriptions -/

/-- A string `x` of length `n` and ordinary plain complexity exactly `k` is
`epsilon`-antistochastic when every point `(m,l)` of its ordinary plain profile
satisfies the source disjunction `m > k - epsilon` or
`m + l > n - epsilon`.

The truncated subtractions are retained literally.  Replacing, for example,
`k - epsilon < m` by `k < m + epsilon` is not equivalent when `epsilon > k`. -/
def IsAntistochastic (V : Map) (n k epsilon : Nat) (x : BitString) : Prop :=
  x.length = n ∧
  plainK V x = (k : ENat) ∧
  ∀ m l, InPlainDescriptionProfile V x m l →
    k - epsilon < m ∨ n - epsilon < m + l

/-- The source claim preceding the normality proposition: antistochastic
strings exist at every nontrivial pair `k < n`, with logarithmic error in both
the antistochasticity and the displayed ordinary complexity. -/
def AntistochasticExistenceStatement (V : Map) : Prop :=
  ∃ c : Nat, ∀ n k, k < n →
    ∃ (x : BitString) (kx : Nat),
      x.length = n ∧
      IsAntistochastic V n kx (logSlack c n) x ∧
      k ≤ kx + logSlack c n ∧
      kx ≤ k + logSlack c n

/-- Source-faithful interface for the proposition that an antistochastic
string is normal. -/
def PropAntistochasticIsNormal (V T : Map) : Prop :=
  ∃ c : Nat, ∀ (x : BitString) (n k epsilon : Nat),
    IsAntistochastic V n k epsilon x →
    IsNormalString V T x (logSlack c n)
      (epsilon + logSlack c n)

/-- The antistochastic-normality proposition from the source.  A plain-profile
point to the right of the antistochastic breakpoint is covered by the strong
singleton model.  Every remaining point is covered, up to the displayed
`epsilon` vertical error, by the cylinder fixing its first `i` bits. -/
theorem prop_antistochastic_is_normal
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    PropAntistochasticIsNormal V T := by
  obtain ⟨cCylinderPlain, hCylinderPlain⟩ :=
    plainSetComplexity_cylinder_le V hV
  obtain ⟨cCylinderStrong, hCylinderStrong⟩ :=
    cylinder_isStrongSetModel T hT
  obtain ⟨cSingletonPlain, hSingletonPlain⟩ :=
    plainSetComplexity_singleton_le_plainK V hV
  obtain ⟨cSingletonStrong, hSingletonStrong⟩ :=
    singleton_isStrongSetModel T hT
  obtain ⟨cLength, hLength⟩ := plainK_le_length V hV
  let c := cCylinderPlain + cCylinderStrong + cSingletonPlain +
    cSingletonStrong + cLength + 1
  refine ⟨c, ?_⟩
  intro x n k epsilon hAnti
  have hxLength : x.length = n := hAnti.1
  have hxComplexity : plainK V x = (k : ENat) := hAnti.2.1
  unfold IsNormalString
  constructor
  · rintro ⟨i, j⟩ hij
    have hDichotomy := hAnti.2.2 i j hij
    rcases hDichotomy with hRight | hAbove
    · let hSingleton : ({x} : Finset BitString).Nonempty :=
        Finset.singleton_nonempty x
      refine ⟨(i + epsilon + cSingletonPlain, j), ?_, ?_⟩
      · refine ⟨{x}, hSingleton, ?_, ?_⟩
        · refine ⟨Finset.mem_singleton.mpr rfl, ?_, ?_⟩
          · calc
              plainSetComplexity V {x} hSingleton
                  ≤ plainK V x + (cSingletonPlain : ENat) :=
                hSingletonPlain x
              _ = ((k + cSingletonPlain : Nat) : ENat) := by
                rw [hxComplexity]
                norm_cast
              _ ≤ ((i + epsilon + cSingletonPlain : Nat) : ENat) := by
                exact_mod_cast (show k + cSingletonPlain ≤
                  i + epsilon + cSingletonPlain by omega)
          · exact Nat.one_le_two_pow
        · exact (hSingletonStrong x).mono (by
            exact (show cSingletonStrong ≤ logSlack c n by
              unfold logSlack c
              omega))
      · have hError : epsilon + cSingletonPlain ≤
          epsilon + logSlack c n := by
            gcongr
            unfold logSlack c
            omega
        unfold natPairLInfDistance
        exact max_le (by omega) (by omega)
    · by_cases hin : i ≤ n
      · let u := x.take i
        have huLength : u.length = i := by
          dsimp [u]
          simp [hxLength, hin]
        have hu : u.length ≤ n := by omega
        have hxu : x ∈ cylinder n u := by
          rw [mem_cylinder]
          exact ⟨hxLength, List.take_prefix i x⟩
        let j' := max j (n - i)
        refine ⟨(i + logSlack cCylinderPlain n, j'), ?_, ?_⟩
        · refine ⟨cylinder n u, ⟨x, hxu⟩, ?_, ?_⟩
          · refine ⟨hxu, ?_, ?_⟩
            · have hPlain := hCylinderPlain n u x hu hxu
              rw [huLength] at hPlain
              simpa only [Nat.cast_add] using hPlain
            · rw [cylinder_card n u hu, huLength]
              exact Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _)
          · exact (hCylinderStrong n u x hu hxu).mono
              (logSlack_mono_left (by
                dsimp [c]
                omega) n)
        · unfold natPairLInfDistance
          have hj' : j' - j ≤ epsilon := by
            dsimp [j']
            omega
          have hPlainSlack :
              logSlack cCylinderPlain n ≤ logSlack c n :=
            logSlack_mono_left (by
              dsimp [c]
              omega) n
          have hError :
              natPairLInfDistance (i, j)
                (i + logSlack cCylinderPlain n, j') ≤
                  epsilon + logSlack c n := by
            unfold natPairLInfDistance
            exact max_le (by omega) (by omega)
          exact hError
      · let hSingleton : ({x} : Finset BitString).Nonempty :=
          Finset.singleton_nonempty x
        refine ⟨(i + cLength + cSingletonPlain, j), ?_, ?_⟩
        · refine ⟨{x}, hSingleton, ?_, ?_⟩
          · refine ⟨Finset.mem_singleton.mpr rfl, ?_, Nat.one_le_two_pow⟩
            calc
              plainSetComplexity V {x} hSingleton
                  ≤ plainK V x + (cSingletonPlain : ENat) :=
                hSingletonPlain x
              _ ≤ ((n + cLength + cSingletonPlain : Nat) : ENat) := by
                calc
                  plainK V x + (cSingletonPlain : ENat)
                      ≤ ((x.length : Nat) : ENat) + (cLength : ENat) +
                          (cSingletonPlain : ENat) :=
                    add_le_add (hLength x) le_rfl
                  _ = ((n + cLength + cSingletonPlain : Nat) : ENat) := by
                    rw [hxLength]
                    rfl
              _ ≤ ((i + cLength + cSingletonPlain : Nat) : ENat) := by
                exact_mod_cast (show n + cLength + cSingletonPlain ≤
                  i + cLength + cSingletonPlain by omega)
          · exact (hSingletonStrong x).mono (by
              unfold logSlack c
              omega)
        · have hError : cLength + cSingletonPlain ≤
            epsilon + logSlack c n := by
              unfold logSlack c
              omega
          unfold natPairLInfDistance
          exact max_le (by omega) (by omega)
  · intro q hq
    exact ⟨q, strongDescriptionProfileSet_subset_plain V T x
      (logSlack c n) hq, by simp [natPairLInfDistance]⟩

/-- Canonical bitstring representing the code of a program that enumerates a
bounded-complexity list.  Its ordinary complexity is the source term `C(q)`. -/
def standardEnumeratorCode (q : Nat.Partrec.Code) : BitString :=
  Nat.bits (Encodable.encode q)

/-- A genuine standard block has the exact source log-cardinality parameter
`j` under the chapter's ceiling-log convention. -/
theorem finiteSetLogCard_standardBlock_of_mem
    (q : Nat.Partrec.Code) (m j : Nat) (x : BitString)
    (hx : x ∈ standardBlock q m j x) :
    finiteSetLogCard (standardBlock q m j x) = j := by
  unfold finiteSetLogCard
  rw [card_standardBlock_of_mem q m j x hx]
  simp

/-- Generalization to any string for a nonempty standard block. -/
theorem finiteSetLogCard_standardBlock_of_nonempty
    (q : Nat.Partrec.Code) (m j : Nat) (z : BitString)
    (hB : (standardBlock q m j z).Nonempty) :
    finiteSetLogCard (standardBlock q m j z) = j := by
  obtain ⟨w, hw⟩ := hB
  unfold finiteSetLogCard
  have h_card : (standardBlock q m j z).card = 2 ^ j :=
    card_standardBlock_of_mem q m j w hw
  rw [h_card]
  simp


/-- Source-faithful interface for VS40 Lemma `l4`.

`IsCodeFor q V` says that `q` supplies an enumeration of exactly the strings
output by `V`; `standardBlock q m j []` is therefore a standard model obtained
from the bound-`m` enumeration.  The coefficient on `C(q)` is explicit because
the source error is `O(C(q) + log n)`, not coefficient-one. -/
def Lemma4Statement (V T : Map) : Prop :=
  ∃ c : Nat, ∀ (q : Nat.Partrec.Code), IsCodeFor q V →
    ∀ m j y (hB : (standardBlock q m j []).Nonempty) n,
      n = max y.length m →
      min
          (plainK V
            (codedUniformOn (standardBlock q m j []) hB).code)
          ((m - y.length : Nat) : ENat) ≤
        totalCondK T
            (codedUniformOn (standardBlock q m j []) hB).code y +
          (c : ENat) * plainK V (standardEnumeratorCode q) +
          (logSlack c n : ENat)

/-- The first element of a finite set has bounded total conditional complexity given the code of the
uniform distribution on that set, with a constant independent of the set. -/
theorem totalCondK_headI_canonicalFinsetList_le
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c, ∀ (S : Finset BitString) (hS : S.Nonempty),
      totalCondK T (canonicalFinsetList S).headI
        (codedUniformOn S hS).code ≤ (c : ENat) := by
  have H : Computable (fun w =>
      ((decodeDistributionData w).map CodedDistributionEntry.point).headI) :=
    (Primrec.list_headI.comp (Primrec.list_map decodeDistributionData_primrec
      (entry_point_primrec.comp Primrec.snd).to₂)).to_comp
  obtain ⟨c, hc⟩ := totalCondK_map_self_le_const T hT _ H
  use c
  intro S hS
  have hc' := hc (codedUniformOn S hS).code
  have h_code : (codedUniformOn S hS).code =
      codedDistributionDataCode (codedUniformOn S hS).data := rfl
  rw [h_code, decodeDistributionData_code] at hc'
  have h_data : (codedUniformOn S hS).data =
      (canonicalFinsetList S).map (fun x =>
        { point := x,
          mass := ratMassInvNat S.card (Finset.Nonempty.card_pos hS) }) := rfl
  have h_map : (codedUniformOn S hS).data.map
      CodedDistributionEntry.point = canonicalFinsetList S := by
    rw [h_data, List.map_map]
    have H_id : (CodedDistributionEntry.point ∘ fun (x : BitString) =>
        ({ point := x, mass :=
          ratMassInvNat S.card (Finset.Nonempty.card_pos hS) } :
            CodedDistributionEntry)) = id := by
      rfl
    rw [H_id, List.map_id]
  rw [h_map] at hc'
  exact hc'

/-- The gray ordinary-profile region from Figure 4 in the source.  Its lower
boundary joins `(0,4*k)` to `(k,2*k)` and then `(3*k,0)`. -/
def separationGrayProfile (k : Nat) : Set (Nat × Nat) :=
  {q | (q.1 ≤ k ∧ 4 * k ≤ q.1 + q.2) ∨
    (k ≤ q.1 ∧ 3 * k ≤ q.1 + q.2)}

/-- The Figure 4 region is upward closed in both profile coordinates. -/
theorem separationGrayProfile_isUpperSet (k : Nat) :
    IsUpperSet (separationGrayProfile k) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨hi, hj⟩ hq
  rcases hq with hq | hq
  · by_cases hik : i' ≤ k
    · exact Or.inl ⟨hik, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

/-- The three boundary points from Figure 4 lie in the gray region. -/
theorem separationGrayProfile_endpoints (k : Nat) :
    (0, 4 * k) ∈ separationGrayProfile k ∧
    (k, 2 * k) ∈ separationGrayProfile k ∧
    (3 * k, 0) ∈ separationGrayProfile k := by
  unfold separationGrayProfile
  simp only [Set.mem_setOf_eq]
  refine ⟨Or.inl ⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩

/-- Left of the vertical line `i = k`, the gray separation profile consists of the points with
`4 * k ≤ i + j`. -/
theorem separationGrayProfile_left_iff
    {k i j : Nat} (hi : i < k) :
    (i, j) ∈ separationGrayProfile k ↔ 4 * k ≤ i + j := by
  unfold separationGrayProfile
  simp only [Set.mem_setOf_eq]
  omega

/-- Right of the vertical line `i = k`, the gray separation profile consists of the points with
`3 * k ≤ i + j`. -/
theorem separationGrayProfile_right_iff
    {k i j : Nat} (hi : k ≤ i) :
    (i, j) ∈ separationGrayProfile k ↔ 3 * k ≤ i + j := by
  unfold separationGrayProfile
  simp only [Set.mem_setOf_eq]
  omega


/-- Source-faithful interface for VS40 Theorem `thm:separation`.

The natural constant `cSeparation` represents the reciprocal of the source's
positive real separation constant: `k ≤ cSeparation * M` says that the maximum
`M` of the four displayed quantities is `Omega(k)`. -/
def ThmSeparationStatement (V T : Map) : Prop :=
  ∃ cSlack cSeparation k0 : Nat,
    0 < cSeparation ∧
    ∀ k, k0 ≤ k →
      ∃ x : BitString, x.length = 4 * k ∧
        ProfileSetsWithinNeighborhood
          (plainDescriptionProfileSet V x)
          (separationGrayProfile k)
          (logSlack cSlack (4 * k)) ∧
        IsNormalString V T x
          (logSlack cSlack (4 * k))
          (logSlack cSlack (4 * k)) ∧
        (∃ (A : Finset BitString) (hA : A.Nonempty),
          x ∈ A ∧
          IsStrongSetModel T x A hA (logSlack cSlack (4 * k)) ∧
          (k : ENat) ≤
            plainSetComplexity V A hA +
              (logSlack cSlack (4 * k) : ENat) ∧
          plainSetComplexity V A hA ≤
            (k + logSlack cSlack (4 * k) : ENat) ∧
          finiteSetLogCard A = 2 * k) ∧
        (∀ (q : Nat.Partrec.Code), IsCodeFor q V →
          ∀ (m : Nat), plainK V x ≤ (m : ENat) →
          ∀ j (hxB : x ∈ standardBlock q m j x),
            let B := standardBlock q m j x
            let hB : B.Nonempty := ⟨x, hxB⟩
            k ≤ cSeparation *
              max (totalCondK T (codedUniformOn B hB).code x).toNat
                (max (plainK V (standardEnumeratorCode q)).toNat
                  (natPairLInfDistance
                    ((plainSetComplexity V B hB).toNat,
                      finiteSetLogCard B)
                    (k, 2 * k))))

/-- Interpret a program as a split point and split the displayed context into
the corresponding pair.  This is total even when the split point exceeds the
context length. -/
def fixedSplitPairCode (input : BitString × BitString) : BitString :=
  pairCode
    (input.2.take (decodeBits input.1))
    (input.2.drop (decodeBits input.1))

/-- Splitting a string at a given position and pairing the two halves is primitive recursive. -/
theorem fixedSplitPairCode_primrec :
    Primrec fixedSplitPairCode := by
  unfold fixedSplitPairCode
  exact pairCode_primrec.comp
    (Primrec.list_take.comp Primrec.snd
      (primrec_decodeBits.comp Primrec.fst))
    (Primrec.list_drop.comp Primrec.snd
      (primrec_decodeBits.comp Primrec.fst))

/-- The machine that splits its condition at the position given by the program and outputs the pair
code of the two halves. -/
noncomputable def fixedSplitPairDecompressor : Map :=
  fun input => Part.some (fixedSplitPairCode input)

/-- The fixed-split pairing machine is a decompressor. -/
theorem fixedSplitPairDecompressor_partrec :
    isDecompressor fixedSplitPairDecompressor :=
  Computable.partrec fixedSplitPairCode_primrec.to_comp

/-- Every program halts under the fixed-split pairing machine, so it is total. -/
theorem fixedSplitPairDecompressor_total (p : BitString) :
    IsTotalProgram fixedSplitPairDecompressor p := by
  intro w
  trivial

/-- Given the length of `y` as program and `y ++ z` as condition, the fixed-split pairing machine
outputs the pair code of `y` and `z`. -/
theorem fixedSplitPairDecompressor_produces (y z : BitString) :
    produces fixedSplitPairDecompressor (Nat.bits y.length) (y ++ z)
      (pairCode y z) := by
  unfold produces fixedSplitPairDecompressor fixedSplitPairCode
  simp

/-- Decode a pair and concatenate its components. -/
def appendDecodedPair (w : BitString) : BitString :=
  decodeFirst w ++ decodeSecond w

/-- Decoding a pair code and concatenating its two components is computable. -/
theorem appendDecodedPair_computable : Computable appendDecodedPair := by
  unfold appendDecodedPair
  exact (Primrec.list_append.comp
    decodeFirst_primrec decodeSecond_primrec).to_comp

/-- Decoding and concatenating the pair code of `y` and `z` returns `y ++ z`. -/
@[simp] theorem appendDecodedPair_pairCode (y z : BitString) :
    appendDecodedPair (pairCode y z) = y ++ z := by
  unfold appendDecodedPair
  rw [decodeFirst_pairCode, decodeSecond_pairCode]

/-- A fixed split concatenation and the repository pair encoding contain the
same total information.  The reverse map carries only the split position. -/
theorem fixedSplit_append_pairCode_totalEquivalent
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ C, ∀ y z,
      TotalEquivalentWithin T
        (y ++ z) (pairCode y z)
        (logSlack C (y.length + z.length)) := by
  obtain ⟨cAppend, hAppend⟩ :=
    totalCondK_map_self_le_const T hT
      appendDecodedPair appendDecodedPair_computable
  obtain ⟨cSplit, hSplit⟩ :=
    hT.2 fixedSplitPairDecompressor
      fixedSplitPairDecompressor_partrec
  let C := cAppend + cSplit + 1
  refine ⟨C, fun y z => ?_⟩
  constructor
  · calc
      totalCondK T (y ++ z) (pairCode y z) =
          totalCondK T (appendDecodedPair (pairCode y z))
            (pairCode y z) := by rw [appendDecodedPair_pairCode]
      _ ≤ (cAppend : ENat) := hAppend (pairCode y z)
      _ ≤ (logSlack C (y.length + z.length) : Nat) := by
        exact_mod_cast (show
          cAppend ≤ logSlack C (y.length + z.length) by
            dsimp [C]
            unfold logSlack
            omega)
  · have hbits :
        (Nat.bits y.length).length ≤
          (Nat.bits (y.length + z.length)).length :=
      length_natBits_mono (Nat.le_add_right _ _)
    have hbudget :
        (Nat.bits y.length).length + cSplit ≤
          logSlack C (y.length + z.length) := by
      dsimp [C]
      unfold logSlack
      nlinarith
        [Nat.zero_le (Nat.bits (y.length + z.length)).length]
    calc
      totalCondK T (pairCode y z) (y ++ z) ≤
          totalCondK fixedSplitPairDecompressor
              (pairCode y z) (y ++ z) + (cSplit : ENat) :=
        hSplit (pairCode y z) (y ++ z)
      _ ≤ ((Nat.bits y.length).length : ENat) +
          (cSplit : ENat) := by
        gcongr
        exact totalCondK_le_programLength
          (fixedSplitPairDecompressor_total (Nat.bits y.length))
          (fixedSplitPairDecompressor_produces y z)
      _ ≤ (logSlack C (y.length + z.length) : ENat) := by
        exact_mod_cast hbudget

end Kolmogorov
