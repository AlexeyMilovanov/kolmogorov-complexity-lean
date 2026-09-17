import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Core

/-!
# The strange-string profile theorem

The source states the strong-profile conclusion at strength `epsilon` while
suppressing logarithmic terms.  The description-shift argument used to fill
the solid boundary spends `O(log n)` additional total conditional complexity,
so the kernel-facing symmetric statement exposes that loss explicitly.

The exact-`epsilon` profile-to-polygon direction remains available in
`t1_profile_bounds_of_optimal`.
-/

namespace Kolmogorov

/-- There are constants `cStrength` and `cProfile` such that for every string `x` of length `n`,
every `epsilon ≥ cStrength` and every `i ≤ n`, the point `(i + logSlack cProfile n, n - i)` lies
in `strongDescriptionProfileSet V T x (epsilon + logSlack cStrength n)`.  Both the complexity
coordinate and the strength budget carry an explicit `O(log n)` loss: the membership point is
`i + logSlack cProfile n`, not `i`, and the strength is `epsilon + logSlack cStrength n`. -/
theorem t1_shifted_fullCube_strong_profile
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ cStrength cProfile : Nat, ∀ (x : BitString) (n epsilon i : Nat),
      x.length = n →
      cStrength ≤ epsilon →
      i ≤ n →
      (i + logSlack cProfile n, n - i) ∈
        strongDescriptionProfileSet V T x (epsilon + logSlack cStrength n) := by
  obtain ⟨cShift, hShift⟩ :=
    strong_description_shift V hV T hT
  obtain ⟨cBase, hBase⟩ :=
    fullCube_isStrongSetModel_const T hT
  obtain ⟨cPlain, hPlain⟩ :=
    plainSetComplexity_fullCube_le_logSlack V hV
  let cStrength := cBase + cShift + 1
  let cProfile := cPlain + cShift + 2
  refine ⟨cStrength, cProfile, ?_⟩
  intro x n epsilon i hxlen hcStrength hin
  let S := stringsOfLength n
  have hS : x ∈ S := by
    rw [mem_stringsOfLength]
    exact hxlen
  have hBase_x : IsStrongSetModel T x S ⟨x, hS⟩ cBase := by
    have h1 := hBase x
    revert h1
    rw [hxlen]
    exact id
  have hS_card : S.card = 2^n := card_stringsOfLength n
  have hi_le : 2^i ≤ S.card := by
    rw [hS_card]
    exact Nat.pow_le_pow_right (by omega) hin
  obtain ⟨S', hS'x, hS'strong, hS'size, hS'complex⟩ :=
    hShift x S hS cBase hBase_x i hi_le
  change InStrongDescriptionProfile V T x (epsilon + logSlack cStrength n) _ _
  refine ⟨S', ⟨x, hS'x⟩, ⟨hS'x, ?_, ?_⟩, ?_⟩
  · have h1 : plainSetComplexity V S ⟨x, hS⟩ ≤ (logSlack cPlain n : ENat) := hPlain n
    have h2 : (logSlack cPlain n : ENat) + (i : ENat) + (logSlack cShift i : ENat)
        ≤ (i + logSlack cProfile n : ENat) := by
      unfold logSlack
      have : (cPlain * (Nat.bits n).length + cPlain) + i + (cShift * (Nat.bits i).length + cShift)
          ≤ i + (cProfile * (Nat.bits n).length + cProfile) := by
        calc
          (cPlain * (Nat.bits n).length + cPlain) + i +
                (cShift * (Nat.bits i).length + cShift)
            ≤ (cPlain * (Nat.bits n).length + cPlain) + i +
                (cShift * (Nat.bits n).length + cShift) := by
              gcongr
              exact length_natBits_mono hin
          _ = i + ((cPlain + cShift) * (Nat.bits n).length + (cPlain + cShift)) := by ring
          _ ≤ i + ((cPlain + cShift + 2) * (Nat.bits n).length + (cPlain + cShift + 2)) := by
              nlinarith [Nat.zero_le (Nat.bits n).length]
      exact_mod_cast this
    calc
      plainSetComplexity V S' ⟨x, hS'x⟩
        ≤ plainSetComplexity V S ⟨x, hS⟩ + (i : ENat) + (logSlack cShift i : ENat) := hS'complex
      _ ≤ (logSlack cPlain n : ENat) + (i : ENat) + (logSlack cShift i : ENat) := by gcongr
      _ ≤ (i + logSlack cProfile n : ENat) := h2
  · have h2_mul : S'.card * 2^i ≤ 2^(n - i) * 2^i := by
      calc
        S'.card * 2^i ≤ S.card := hS'size
        _ = 2^n := hS_card
        _ = 2^(n - i) * 2^i := by
          rw [← Nat.pow_add]
          congr 1
          omega
    exact Nat.le_of_mul_le_mul_right h2_mul (by positivity)
  · have h1 : cBase + logSlack cShift i ≤ epsilon + logSlack cStrength n := by
      unfold logSlack
      have : cBase + (cShift * (Nat.bits i).length + cShift) ≤
          epsilon +
            (cStrength * (Nat.bits n).length + cStrength) := by
        calc
          cBase + (cShift * (Nat.bits i).length + cShift)
            ≤ cBase + (cShift * (Nat.bits n).length + cShift) := by
              gcongr
              exact length_natBits_mono hin
          _ ≤ epsilon + ((cBase + cShift + 1) * (Nat.bits n).length + (cBase + cShift + 1)) := by
              nlinarith [Nat.zero_le (Nat.bits n).length]
      exact this
    exact hS'strong.mono h1

/-- On the interior range `k + 4 ≤ n`, a single string realizes both the ordinary profile and
the strong profile at any prescribed strength floor (SUV Theorem `t1`). -/
theorem t1_strange_string_interior_with_strength_floor
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) (cStrengthFloor : Nat) :
    ∃ c0 cStrength cProfile : Nat, cStrengthFloor ≤ cStrength ∧
      ∀ n k epsilon : Nat,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      ∃ x : BitString,
        x.length = n ∧
        (k : ENat) ≤ plainK V x ∧
        plainK V x ≤ (k + logSlack cProfile n : ENat) ∧
        ProfileSetsWithinNeighborhood
          (plainDescriptionProfileSet V x)
          (t1PlainPolygon n k epsilon)
          (logSlack cProfile n) ∧
        ProfileSetsWithinNeighborhood
          (strongDescriptionProfileSet V T x
            (epsilon + logSlack cStrength n))
          (t1StrongPolygon n k)
          (logSlack cProfile n) := by
  obtain ⟨cShiftStrength, cShiftProfile, hShifted⟩ :=
    t1_shifted_fullCube_strong_profile V T hV hT
  obtain ⟨cSingletonStrength, hSingleton⟩ :=
    t1_singleton_strong_profile_endpoint V T hV hT
  let cEndpointStrength :=
    max cShiftStrength cSingletonStrength
  let cStrength := max cEndpointStrength cStrengthFloor
  obtain ⟨cDesc, cStrongProfile, hStrong⟩ :=
    t1_not_cMarked_strongProfile_to_polygon V T hV hT
  obtain ⟨cCore, cA, hCore⟩ :=
    exists_t1_avoiding_set_core V hV (cStrength + cDesc)
  obtain ⟨cPlain, hPlain⟩ :=
    t1_avoiding_set_plain_profile_bounds V hV cA
  obtain ⟨cSingletonProfile, hSingletonEndpoint⟩ :=
    hSingleton cPlain
  let cProfile :=
    cPlain + cStrongProfile + cShiftProfile + cSingletonProfile
  refine ⟨max cCore cStrength, cStrength, cProfile, ?_⟩
  refine ⟨Nat.le_max_right _ _, ?_⟩
  intro n k epsilon hc0 hepsilon hkn
  have hCore0 : cCore ≤ epsilon :=
    (Nat.le_max_left _ _).trans hc0
  have hStrength0 : cStrength ≤ epsilon :=
    (Nat.le_max_right _ _).trans hc0
  have hShiftStrength0 : cShiftStrength ≤ epsilon :=
    ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _)).trans
      hStrength0
  have hSingletonStrength0 : cSingletonStrength ≤ epsilon :=
    ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _)).trans
      hStrength0
  obtain ⟨A, hA, x, hAcube, hAcard, hxA, hxlen,
      hAcomplexity, hnotB, hnotC, hnotD⟩ :=
    hCore n k epsilon hCore0 hepsilon hkn
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
  have hShiftSlack :
      logSlack cShiftProfile n ≤ logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hSingletonSlack :
      logSlack cSingletonProfile n ≤ logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hShiftBudget :
      epsilon + logSlack cShiftStrength n ≤
        epsilon + logSlack cStrength n := by
    exact Nat.add_le_add_left
      (logSlack_mono_left
        ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _)) n)
      epsilon
  have hnotC' :
      ¬ T1CMarked V n k
        ((epsilon + logSlack cStrength n) + logSlack cDesc n) x := by
    have hbudget :
        (epsilon + logSlack cStrength n) + logSlack cDesc n =
          epsilon + logSlack (cStrength + cDesc) n := by
      rw [Nat.add_assoc, logSlack_add_const]
    rw [hbudget]
    exact hnotC
  have hStrongDirected :=
    hStrong n k (epsilon + logSlack cStrength n) x
      hkn hxlen hnotC'
  have hSingletonBase :=
    hSingletonEndpoint x n k epsilon hKupper
      hSingletonStrength0
  have hSingletonFinal :
      (k + logSlack cSingletonProfile n, 0) ∈
        strongDescriptionProfileSet V T x
          (epsilon + logSlack cStrength n) :=
    hSingletonBase.mono_epsilon (Nat.le_add_right _ _)
  refine ⟨x, hxlen, hKlower, hKupper.trans ?_,
    hPlainNeighborhood.mono hPlainSlack, ?_⟩
  · exact_mod_cast (Nat.add_le_add_left hPlainSlack k)
  · constructor
    · intro q hq
      obtain ⟨q', hq', hdist⟩ := hStrongDirected q hq
      exact ⟨q', hq', hdist.trans hStrongSlack⟩
    · intro q hq
      by_cases hqk : k ≤ q.1
      · have hprofile :
            (q.1 + logSlack cProfile n, q.2) ∈
              strongDescriptionProfileSet V T x
                (epsilon + logSlack cStrength n) :=
          (hSingletonFinal.mono_i (by omega)).mono_j (Nat.zero_le _)
        refine ⟨(q.1 + logSlack cProfile n, q.2), hprofile, ?_⟩
        simp [natPairLInfDistance]
      · have hqsum : n ≤ q.1 + q.2 := by
          unfold t1StrongPolygon at hq
          rcases hq with hq | hq
          · exact False.elim (hqk hq)
          · exact hq
        have hqi : q.1 ≤ n := by
          omega
        have hbase :=
          hShifted x n epsilon q.1 hxlen hShiftStrength0 hqi
        have hbase' :
            (q.1 + logSlack cShiftProfile n, n - q.1) ∈
              strongDescriptionProfileSet V T x
                (epsilon + logSlack cStrength n) :=
          hbase.mono_epsilon hShiftBudget
        have hprofile :
            (q.1 + logSlack cProfile n, q.2) ∈
              strongDescriptionProfileSet V T x
                (epsilon + logSlack cStrength n) :=
          (hbase'.mono_i (by omega)).mono_j (by omega)
        refine ⟨(q.1 + logSlack cProfile n, q.2), hprofile, ?_⟩
        simp [natPairLInfDistance]

/-- There are constants `c0`, `cStrength`, `cProfile` such that for all `n`, `k`, `epsilon` with
`c0 ≤ epsilon ≤ k` and `k + 4 ≤ n` there is a string `x` of length `n` with
`k ≤ plainK V x ≤ k + logSlack cProfile n` whose plain description profile set lies within
`logSlack cProfile n` of `t1PlainPolygon n k epsilon`, and whose strong description profile set
at strength `epsilon + logSlack cStrength n` lies within `logSlack cProfile n` of
`t1StrongPolygon n k`. -/
theorem t1_strange_string_interior
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c0 cStrength cProfile : Nat, ∀ n k epsilon : Nat,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      ∃ x : BitString,
        x.length = n ∧
        (k : ENat) ≤ plainK V x ∧
        plainK V x ≤ (k + logSlack cProfile n : ENat) ∧
        ProfileSetsWithinNeighborhood
          (plainDescriptionProfileSet V x)
          (t1PlainPolygon n k epsilon)
          (logSlack cProfile n) ∧
        ProfileSetsWithinNeighborhood
          (strongDescriptionProfileSet V T x
            (epsilon + logSlack cStrength n))
          (t1StrongPolygon n k)
          (logSlack cProfile n) := by
  obtain ⟨c0, cStrength, cProfile, _hFloor, h⟩ :=
    t1_strange_string_interior_with_strength_floor V T hV hT 0
  exact ⟨c0, cStrength, cProfile,
    fun n k epsilon hc0 hepsilon hkn =>
      h n k epsilon hc0 hepsilon hkn⟩

/-- Every plain description profile point for an unmarked boundary string lies near
the plain polygon. -/
private theorem t1_plain_profile_subset_plain_polygon_boundary
    (V : Map) (cD : Nat)
    (hD : ∀ (n k : Nat) (x : BitString) (a b : Nat),
      x.length = n → k ≤ n → ¬ T1DMarked V n k x →
      InPlainDescriptionProfile V x a b → k ≤ a + b + logSlack cD n)
    {n k epsilon : Nat} {x : BitString} (hxlen : x.length = n) (hkn : k ≤ n)
    (hboundary : n < k + 4)
    (hnotD : ¬ T1DMarked V n k x) {q : Nat × Nat}
    (hq : q ∈ plainDescriptionProfileSet V x) :
    ∃ q' ∈ t1PlainPolygon n k epsilon, natPairLInfDistance q q' ≤ logSlack cD n + 3 := by
  by_cases hpolygon : q ∈ t1PlainPolygon n k epsilon
  · exact ⟨q, hpolygon, by simp [natPairLInfDistance]⟩
  · have hline := hD n k x q.1 q.2 hxlen hkn hnotD hq
    by_cases hqepsilon : q.1 < epsilon
    · have hsum : q.1 + q.2 < n := by
        unfold t1PlainPolygon at hpolygon
        simpa [hqepsilon] using hpolygon
      let q' : Nat × Nat := (q.1, n - q.1)
      refine ⟨q', ?_, ?_⟩
      · unfold t1PlainPolygon
        simp only [Set.mem_ofPred_eq, q', if_pos hqepsilon]
        omega
      · unfold natPairLInfDistance
        simp only [q', Nat.sub_self, zero_add]
        have hqle : q.2 ≤ n - q.1 := by omega
        have hgap : (n - q.1) - q.2 = n - (q.1 + q.2) := by omega
        rw [Nat.sub_eq_zero_of_le hqle, zero_add, hgap]
        omega
    · have hsum : q.1 + q.2 < k := by
        unfold t1PlainPolygon at hpolygon
        simp only [Set.mem_ofPred_eq, if_neg hqepsilon, not_le] at hpolygon
        exact hpolygon
      let q' : Nat × Nat := (q.1, k - q.1)
      refine ⟨q', ?_, ?_⟩
      · unfold t1PlainPolygon
        simp only [Set.mem_ofPred_eq, q', if_neg hqepsilon]
        omega
      · unfold natPairLInfDistance
        simp only [q', Nat.sub_self, zero_add]
        have hqle : q.2 ≤ k - q.1 := by omega
        have hgap : (k - q.1) - q.2 = k - (q.1 + q.2) := by omega
        rw [Nat.sub_eq_zero_of_le hqle, zero_add, hgap]
        omega

/-- Every strong description profile point for an unmarked boundary string lies near
the strong polygon. -/
private theorem t1_strong_profile_subset_strong_polygon_boundary
    (V T : Map) (cD : Nat)
    (hD : ∀ (n k : Nat) (x : BitString) (a b : Nat),
      x.length = n → k ≤ n → ¬ T1DMarked V n k x →
      InPlainDescriptionProfile V x a b → k ≤ a + b + logSlack cD n)
    {n k epsilon : Nat} {x : BitString} (hxlen : x.length = n) (hkn : k ≤ n)
    (hboundary : n < k + 4)
    (hnotD : ¬ T1DMarked V n k x) {q : Nat × Nat}
    (hq : q ∈ strongDescriptionProfileSet V T x epsilon) :
    ∃ q' ∈ t1StrongPolygon n k, natPairLInfDistance q q' ≤ logSlack cD n + 3 := by
  by_cases hpolygon : q ∈ t1StrongPolygon n k
  · exact ⟨q, hpolygon, by simp [natPairLInfDistance]⟩
  · have hplain : q ∈ plainDescriptionProfileSet V x :=
      strongDescriptionProfileSet_subset_plain V T x _ hq
    have hline := hD n k x q.1 q.2 hxlen hkn hnotD hplain
    have hqsum : q.1 + q.2 < n := by
      unfold t1StrongPolygon at hpolygon
      simp only [Set.mem_ofPred_eq, not_or, not_le] at hpolygon
      exact hpolygon.2
    let q' : Nat × Nat := (q.1, n - q.1)
    refine ⟨q', ?_, ?_⟩
    · unfold t1StrongPolygon
      simp only [Set.mem_ofPred_eq, q']
      exact Or.inr (by omega)
    · unfold natPairLInfDistance
      simp only [q', Nat.sub_self, zero_add]
      have hqle : q.2 ≤ n - q.1 := by omega
      have hgap : (n - q.1) - q.2 = n - (q.1 + q.2) := by omega
      rw [Nat.sub_eq_zero_of_le hqle, zero_add, hgap]
      omega

/-- For a boundary string, every point in the plain polygon lies near the plain profile set. -/
private theorem t1_plain_polygon_subset_plain_profile_boundary
    (V : Map) (cPlainSingleton cA cProfile : Nat)
    (hPlainSingleton : ∀ x, plainSetComplexity V {x} (Finset.singleton_nonempty x) ≤
      plainK V x + (cPlainSingleton : ENat))
    {cCube cPlainShift : Nat}
    (hPlainShift : ∀ (x : BitString) (a b i : Nat),
      InPlainDescriptionProfile V x a b →
      InPlainDescriptionProfile V x (a + i + logSlack cPlainShift i) (b - i))
    {n k epsilon : Nat} {x : BitString} (hkn : k ≤ n)
    (hboundary : n < k + 4)
    (hKupper : plainK V x ≤ (k + logSlack cA n : ENat))
    (hASingletonSlack : logSlack cA n + cPlainSingleton ≤ logSlack cProfile n)
    (hCubeShiftSlack : logSlack cCube n + logSlack cPlainShift n ≤ logSlack cProfile n)
    (hThree : 3 ≤ logSlack cProfile n)
    (hFullPlain : (logSlack cCube n, n) ∈ plainDescriptionProfileSet V x)
    {q : Nat × Nat} (hq : q ∈ t1PlainPolygon n k epsilon) :
    ∃ q' ∈ plainDescriptionProfileSet V x, natPairLInfDistance q q' ≤ logSlack cProfile n := by
  by_cases hqk : k ≤ q.1
  · have hsingletonComplexity :
        plainSetComplexity V {x} (Finset.singleton_nonempty x) ≤
          (q.1 + logSlack cProfile n : Nat) := by
      calc
        plainSetComplexity V {x} (Finset.singleton_nonempty x)
            ≤ plainK V x + (cPlainSingleton : ENat) := hPlainSingleton x
        _ ≤ (k + logSlack cA n : ENat) + (cPlainSingleton : ENat) := by gcongr
        _ ≤ (q.1 + logSlack cProfile n : Nat) := by
          exact_mod_cast (show k + logSlack cA n + cPlainSingleton ≤
            q.1 + logSlack cProfile n by omega)
    have hprofile : (q.1 + logSlack cProfile n, q.2) ∈ plainDescriptionProfileSet V x := by
      refine ⟨{x}, Finset.singleton_nonempty x, Finset.mem_singleton.mpr rfl,
        hsingletonComplexity, ?_⟩
      simpa using Nat.one_le_two_pow
    refine ⟨(q.1 + logSlack cProfile n, q.2), hprofile, ?_⟩
    simp [natPairLInfDistance]
  · have hqi : q.1 ≤ n := by omega
    have hshifted := hPlainShift x (logSlack cCube n) n q.1 hFullPlain
    have hshifted' : (q.1 + logSlack cProfile n, q.2 + 3) ∈ plainDescriptionProfileSet V x := by
      refine (hshifted.mono_i ?_).mono_j ?_
      · have hshiftSlack : logSlack cPlainShift q.1 ≤ logSlack cPlainShift n :=
          logSlack_mono_right cPlainShift hqi
        omega
      · unfold t1PlainPolygon at hq
        by_cases hqepsilon : q.1 < epsilon
        · simp only [Set.mem_ofPred_eq, if_pos hqepsilon] at hq; omega
        · simp only [Set.mem_ofPred_eq, if_neg hqepsilon] at hq; omega
    refine ⟨(q.1 + logSlack cProfile n, q.2 + 3), hshifted', ?_⟩
    unfold natPairLInfDistance
    rw [Nat.sub_eq_zero_of_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      Nat.sub_eq_zero_of_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    simp only [zero_add]
    exact max_le (le_refl _) hThree

/-- For a boundary string, every point in the strong polygon lies near the strong profile set. -/
private theorem t1_strong_polygon_subset_strong_profile_boundary
    (V T : Map) {cShiftStrength cShiftProfile cProfile cStrength : Nat}
    (hStrongShift : ∀ (x : BitString) (n epsilon i : Nat),
      x.length = n → cShiftStrength ≤ epsilon → i ≤ n →
      (i + logSlack cShiftProfile n, n - i) ∈
        strongDescriptionProfileSet V T x (epsilon + logSlack cShiftStrength n))
    {n k epsilon : Nat} {x : BitString} (hxlen : x.length = n) (hkn : k ≤ n)
    (hboundary : n < k + 4)
    {cStrongSingletonProfile : Nat}
    (hStrongSingletonFinal : (k + logSlack cStrongSingletonProfile n, 0) ∈
      strongDescriptionProfileSet V T x (epsilon + logSlack cStrength n))
    (hShiftProfileSlack : logSlack cShiftProfile n ≤ logSlack cProfile n)
    (hStrongSingletonSlack : logSlack cStrongSingletonProfile n ≤ logSlack cProfile n)
    (hShiftStrength0 : cShiftStrength ≤ epsilon)
    (hShiftBudget : epsilon + logSlack cShiftStrength n ≤ epsilon + logSlack cStrength n)
    {q : Nat × Nat} (hq : q ∈ t1StrongPolygon n k) :
    ∃ q' ∈ strongDescriptionProfileSet V T x (epsilon + logSlack cStrength n),
      natPairLInfDistance q q' ≤ logSlack cProfile n := by
  by_cases hqk : k ≤ q.1
  · have hprofile : (q.1 + logSlack cProfile n, q.2) ∈
        strongDescriptionProfileSet V T x (epsilon + logSlack cStrength n) :=
      (hStrongSingletonFinal.mono_i (by omega)).mono_j (Nat.zero_le _)
    refine ⟨(q.1 + logSlack cProfile n, q.2), hprofile, ?_⟩
    simp [natPairLInfDistance]
  · have hqsum : n ≤ q.1 + q.2 := by
      unfold t1StrongPolygon at hq
      rcases hq with hq | hq
      · exact False.elim (hqk hq)
      · exact hq
    have hqi : q.1 ≤ n := by omega
    have hbase := hStrongShift x n epsilon q.1 hxlen hShiftStrength0 hqi
    have hbase' : (q.1 + logSlack cShiftProfile n, n - q.1) ∈
        strongDescriptionProfileSet V T x (epsilon + logSlack cStrength n) :=
      hbase.mono_epsilon hShiftBudget
    have hprofile : (q.1 + logSlack cProfile n, q.2) ∈
        strongDescriptionProfileSet V T x (epsilon + logSlack cStrength n) :=
      (hbase'.mono_i (by omega)).mono_j (by omega)
    refine ⟨(q.1 + logSlack cProfile n, q.2), hprofile, ?_⟩
    simp [natPairLInfDistance]

/-- Pointwise profile bounds for a nonexceptional member of a finite-width boundary
model. -/
theorem t1_boundary_pointwise_profile
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
  ∃ c0 cStrengthMin : Nat, ∀ cA,
    ∃ cProfile, cA ≤ cProfile ∧
    ∀ (cStrength n k epsilon : Nat) (x : BitString),
      cStrengthMin ≤ cStrength →
      c0 ≤ epsilon →
      epsilon ≤ k →
      k ≤ n →
      n < k + 4 →
      x.length = n →
      (k : ENat) ≤ plainK V x →
      plainK V x ≤
        (k + logSlack cA n : ENat) →
      ProfileSetsWithinNeighborhood
        (plainDescriptionProfileSet V x)
        (t1PlainPolygon n k epsilon)
        (logSlack cProfile n) ∧
      ProfileSetsWithinNeighborhood
        (strongDescriptionProfileSet V T x
          (epsilon + logSlack cStrength n))
        (t1StrongPolygon n k)
        (logSlack cProfile n) := by
  obtain ⟨cD, hD⟩ :=
    t1_not_dMarked_plain_profile_lower V hV
  obtain ⟨cCube, hCube⟩ :=
    plainSetComplexity_fullCube_le_logSlack V hV
  obtain ⟨cPlainShift, hPlainShift⟩ :=
    inPlainDescriptionProfile_shift V hV
  obtain ⟨cPlainSingleton, hPlainSingleton⟩ :=
    plainSetComplexity_singleton_le_plainK V hV
  obtain ⟨cShiftStrength, cShiftProfile, hStrongShift⟩ :=
    t1_shifted_fullCube_strong_profile V T hV hT
  obtain ⟨cSingletonStrength, hStrongSingleton⟩ :=
    t1_singleton_strong_profile_endpoint V T hV hT
  let cStrengthMin := max cShiftStrength cSingletonStrength
  refine ⟨cStrengthMin, cStrengthMin, ?_⟩
  intro cA
  obtain ⟨cStrongSingletonProfile, hStrongSingletonEndpoint⟩ :=
    hStrongSingleton cA
  let cProfile := cD + cCube + cPlainShift + cPlainSingleton +
    cA + cShiftProfile + cStrongSingletonProfile + 10
  refine ⟨cProfile, by dsimp [cProfile]; omega, ?_⟩
  intro cStrength n k epsilon x hStrength hc0 hepsilon hkn
      hboundary hxlen hKlower hKupper
  have hnotD : ¬ T1DMarked V n k x := by
    unfold T1DMarked
    push Not
    intro _
    exact hKlower
  have hDSlack :
      logSlack cD n ≤ logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hDThreeSlack :
      logSlack cD n + 3 ≤ logSlack cProfile n := by
    dsimp [cProfile]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits n).length]
  have hCubeShiftSlack :
      logSlack cCube n + logSlack cPlainShift n ≤
        logSlack cProfile n := by
    rw [logSlack_add_const]
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hASingletonSlack :
      logSlack cA n + cPlainSingleton ≤
        logSlack cProfile n := by
    calc
      logSlack cA n + cPlainSingleton
          ≤ logSlack cA n + logSlack cPlainSingleton n := by
        gcongr
        simp [logSlack]
      _ = logSlack (cA + cPlainSingleton) n :=
        logSlack_add_const cA cPlainSingleton n
      _ ≤ logSlack cProfile n := by
        dsimp [cProfile]
        exact logSlack_mono_left (by omega) n
  have hShiftProfileSlack :
      logSlack cShiftProfile n ≤ logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hStrongSingletonSlack :
      logSlack cStrongSingletonProfile n ≤
        logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hThree : 3 ≤ logSlack cProfile n := by
    dsimp [cProfile]
    unfold logSlack
    omega
  have hShiftStrength0 : cShiftStrength ≤ epsilon :=
    (Nat.le_max_left _ _).trans hc0
  have hSingletonStrength0 : cSingletonStrength ≤ epsilon :=
    (Nat.le_max_right _ _).trans hc0
  have hShiftBudget :
      epsilon + logSlack cShiftStrength n ≤
        epsilon + logSlack cStrength n := by
    exact Nat.add_le_add_left
      (logSlack_mono_left
        ((Nat.le_max_left _ _).trans hStrength) n)
      epsilon
  have hFullPlain :
      (logSlack cCube n, n) ∈
        plainDescriptionProfileSet V x := by
    refine ⟨stringsOfLength n, codedStringsOfLength_nonempty n,
      (mem_stringsOfLength n x).mpr hxlen, hCube n, ?_⟩
    rw [card_stringsOfLength]
  have hStrongSingletonBase :=
    hStrongSingletonEndpoint x n k epsilon hKupper
      hSingletonStrength0
  have hStrongSingletonFinal :
      (k + logSlack cStrongSingletonProfile n, 0) ∈
        strongDescriptionProfileSet V T x
          (epsilon + logSlack cStrength n) :=
    hStrongSingletonBase.mono_epsilon (by
      have hbase : epsilon ≤ epsilon + logSlack cStrength n :=
        Nat.le_add_right _ _
      exact hbase)
  constructor
  · constructor
    · intro q hq
      obtain ⟨q', hq', hdist⟩ :=
        t1_plain_profile_subset_plain_polygon_boundary V cD hD hxlen hkn
          hboundary hnotD hq
      exact ⟨q', hq', hdist.trans hDThreeSlack⟩
    · intro q hq
      exact t1_plain_polygon_subset_plain_profile_boundary V cPlainSingleton cA cProfile
        hPlainSingleton hPlainShift hkn hboundary hKupper hASingletonSlack
        hCubeShiftSlack hThree hFullPlain hq
  · constructor
    · intro q hq
      obtain ⟨q', hq', hdist⟩ :=
        t1_strong_profile_subset_strong_polygon_boundary V T cD hD hxlen hkn
          hboundary hnotD hq
      exact ⟨q', hq', hdist.trans hDThreeSlack⟩
    · intro q hq
      exact t1_strong_polygon_subset_strong_profile_boundary V T hStrongShift hxlen hkn
        hboundary hStrongSingletonFinal hShiftProfileSlack hStrongSingletonSlack hShiftStrength0
        hShiftBudget hq

/-- The finite-width boundary case `k ≤ n < k + 4`, proved from a
length-`n` incompressible string and the fact that the two Figure 6 polygons
are then at constant distance. -/
theorem t1_strange_string_boundary_case
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c0 cStrength cProfile : Nat, ∀ n k epsilon : Nat,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k ≤ n →
      n < k + 4 →
      ∃ x : BitString,
        x.length = n ∧
        (k : ENat) ≤ plainK V x ∧
        plainK V x ≤ (k + logSlack cProfile n : ENat) ∧
        ProfileSetsWithinNeighborhood
          (plainDescriptionProfileSet V x)
          (t1PlainPolygon n k epsilon)
          (logSlack cProfile n) ∧
        ProfileSetsWithinNeighborhood
          (strongDescriptionProfileSet V T x
            (epsilon + logSlack cStrength n))
          (t1StrongPolygon n k)
          (logSlack cProfile n) := by
  obtain ⟨cLen, hLen⟩ := plainK_le_length V hV
  let cK := cLen + 4
  obtain ⟨c0, cStrengthMin, hBoundaryPointwise⟩ :=
    t1_boundary_pointwise_profile V T hV hT
  obtain ⟨cProfile, hcAProfile, hPointwise⟩ :=
    hBoundaryPointwise cK
  refine ⟨c0, cStrengthMin, cProfile, ?_⟩
  intro n k epsilon hc0 hepsilon hkn hboundary
  obtain ⟨x, hxlen, hKlowerN⟩ :=
    exists_incompressible_string V [] n
  have hKlower : (k : ENat) ≤ plainK V x := by
    have hkn' : (k : ENat) ≤ (n : ENat) := by
      exact_mod_cast hkn
    exact hkn'.trans hKlowerN
  have hKupper :
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
    hPointwise cStrengthMin n k epsilon x (by omega)
      hc0 hepsilon hkn hboundary hxlen hKlower hKupper
  have hSlack : (k + logSlack cK n : ENat) ≤ (k + logSlack cProfile n : ENat) := by
    exact_mod_cast Nat.add_le_add_left (logSlack_mono_left hcAProfile n) k
  exact ⟨x, hxlen, hKlower, hKupper.trans hSlack, hPlain, hStrong⟩

/-- In the finite-width boundary regime, the dashed Figure 6 polygon lies
within three cells of the solid polygon. -/
theorem t1PlainPolygon_to_t1StrongPolygon_boundary
    {n k epsilon : Nat} (hkn : k ≤ n) (hboundary : n < k + 4) :
    ∀ q ∈ t1PlainPolygon n k epsilon,
      ∃ q' ∈ t1StrongPolygon n k,
        natPairLInfDistance q q' ≤ 3 := by
  intro q hq
  by_cases hsolid : q ∈ t1StrongPolygon n k
  · exact ⟨q, hsolid, by simp [natPairLInfDistance]⟩
  · have hsolid' : q.1 < k ∧ q.1 + q.2 < n := by
      unfold t1StrongPolygon at hsolid
      simpa only [Set.mem_ofPred_eq, not_or, not_le] using hsolid
    have hqepsilon : ¬ q.1 < epsilon := by
      intro hlt
      unfold t1PlainPolygon at hq
      simp only [Set.mem_ofPred_eq, if_pos hlt] at hq
      omega
    have hkline : k ≤ q.1 + q.2 := by
      unfold t1PlainPolygon at hq
      simpa [hqepsilon] using hq
    let q' : Nat × Nat := (q.1, n - q.1)
    refine ⟨q', ?_, ?_⟩
    · unfold t1StrongPolygon
      simp only [Set.mem_ofPred_eq, q']
      exact Or.inr (by omega)
    · unfold natPairLInfDistance
      simp only [q', Nat.sub_self, zero_add]
      have hqle : q.2 ≤ n - q.1 := by
        omega
      have hgap :
          (n - q.1) - q.2 = n - (q.1 + q.2) := by
        omega
      rw [Nat.sub_eq_zero_of_le hqle, zero_add, hgap]
      omega

/-- VS40 Section 7, Theorem `t1`, with the logarithmic increase in the
strongness budget made explicit.  The ordinary profile is compared at the
original `epsilon`, while the complete strong profile is realized at
`epsilon + O(log n)`. -/
theorem t1_strange_string
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c0 cStrength cProfile : Nat, ∀ n k epsilon : Nat,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k ≤ n →
      ∃ x : BitString,
        x.length = n ∧
        (k : ENat) ≤ plainK V x ∧
        plainK V x ≤ (k + logSlack cProfile n : ENat) ∧
        ProfileSetsWithinNeighborhood
          (plainDescriptionProfileSet V x)
          (t1PlainPolygon n k epsilon)
          (logSlack cProfile n) ∧
        ProfileSetsWithinNeighborhood
          (strongDescriptionProfileSet V T x
            (epsilon + logSlack cStrength n))
          (t1StrongPolygon n k)
          (logSlack cProfile n) := by
  obtain ⟨cBoundary0, cBoundaryStrength, cBoundaryProfile,
      hBoundary⟩ :=
    t1_strange_string_boundary_case V T hV hT
  obtain ⟨cInterior0, cStrength, cInteriorProfile,
      hBoundaryStrength, hInterior⟩ :=
    t1_strange_string_interior_with_strength_floor V T hV hT
      cBoundaryStrength
  let cProfile := cInteriorProfile + cBoundaryProfile + 3
  refine ⟨max cInterior0 cBoundary0, cStrength, cProfile, ?_⟩
  intro n k epsilon hc0 hepsilon hkn
  have hInterior0 : cInterior0 ≤ epsilon :=
    (Nat.le_max_left _ _).trans hc0
  have hBoundary0 : cBoundary0 ≤ epsilon :=
    (Nat.le_max_right _ _).trans hc0
  have hInteriorSlack :
      logSlack cInteriorProfile n ≤
        logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  have hBoundarySlack :
      logSlack cBoundaryProfile n ≤
        logSlack cProfile n := by
    dsimp [cProfile]
    exact logSlack_mono_left (by omega) n
  by_cases hinterior : k + 4 ≤ n
  · obtain ⟨x, hxlen, hKlower, hKupper,
        hPlain, hStrong⟩ :=
      hInterior n k epsilon hInterior0 hepsilon hinterior
    refine ⟨x, hxlen, hKlower, hKupper.trans ?_,
      hPlain.mono hInteriorSlack,
      hStrong.mono hInteriorSlack⟩
    exact_mod_cast (Nat.add_le_add_left hInteriorSlack k)
  · have hboundary : n < k + 4 := by
      omega
    obtain ⟨x, hxlen, hKlower, hKupper,
        hPlain, hStrongOld⟩ :=
      hBoundary n k epsilon hBoundary0 hepsilon hkn hboundary
    have hStrengthBudget :
        epsilon + logSlack cBoundaryStrength n ≤
          epsilon + logSlack cStrength n := by
      exact Nat.add_le_add_left
        (logSlack_mono_left hBoundaryStrength n) epsilon
    have hBoundaryPlusThree :
        logSlack cBoundaryProfile n + 3 ≤
          logSlack cProfile n := by
      dsimp [cProfile]
      unfold logSlack
      nlinarith [Nat.zero_le (Nat.bits n).length]
    refine ⟨x, hxlen, hKlower, hKupper.trans ?_,
      hPlain.mono hBoundarySlack, ?_⟩
    · exact_mod_cast (Nat.add_le_add_left hBoundarySlack k)
    · constructor
      · intro q hq
        have hqPlain : q ∈ plainDescriptionProfileSet V x :=
          strongDescriptionProfileSet_subset_plain V T x _ hq
        obtain ⟨r, hrPlainPolygon, hqr⟩ :=
          hPlain.1 q hqPlain
        obtain ⟨s, hsStrongPolygon, hrs⟩ :=
          t1PlainPolygon_to_t1StrongPolygon_boundary hkn
            hboundary r hrPlainPolygon
        refine ⟨s, hsStrongPolygon,
          (natPairLInfDistance_triangle q r s).trans ?_⟩
        exact (Nat.add_le_add hqr hrs).trans
          hBoundaryPlusThree
      · intro q hq
        obtain ⟨r, hr, hdist⟩ := hStrongOld.2 q hq
        exact ⟨r, hr.mono_epsilon hStrengthBudget,
          hdist.trans hBoundarySlack⟩

end Kolmogorov
