import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongProfile
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FullCube
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileBridges
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingPredicates
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CylinderRealization
import KolmogorovMathlib.Restricted.HammingGap.Part01
import KolmogorovMathlib.Restricted.HammingGap
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock

/-!
# Separating the plain and the strong profile: the geometry

The separation theorem exhibits a string whose plain description profile and strong
description profile differ.  The two profiles are compared against the two polygons of VS40
Figure 6; this part sets up their geometry and the marking construction that places a string
outside the dashed one.

`t1PlainPolygon_mono`, `t1StrongPolygon_mono`, `t1PlainPolygon_antitone_epsilon` and
`t1PlainPolygon_antitone_n` are the monotonicity properties of the two polygons.
`t1_plainProfile_to_polygon` is the exclusion this part proves — every actual plain profile
point lies, up to logarithmic slack, inside the dashed polygon — through the two
mark-absence lemmas `t1_not_bMarked_plain_profile_lower` and
`t1_not_dMarked_plain_profile_lower` and the shift `inPlainDescriptionProfile_shift`.

The marking construction is counted by `t1_marked_union_count_lt_half` and
`exists_sparse_intersection_subset`, a finite probabilistic-method lemma.
`strange_string_lemma_1` (VS40 Lemma `l1`) is proved here as well, with the plain
decompressor `plainFullCubeImageDecompressor` and the coding core
`inPlainDescriptionProfile_of_totalReducesWithin_from_length`.
-/



namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- Plain decompressor used in Lemma `l1`.  A program is framed as
`plainAdviceCode p (Nat.bits n)`, so the varying total program `p` is stored
verbatim and only the logarithmic length advice is self-delimited.  The
decompressor runs `p` on every string of length `n` and returns the canonical
code of the resulting finite image. -/
noncomputable def plainFullCubeImageDecompressor (T : Map) : Map :=
  fun input =>
    totalProgramImageCode T
      (decodePlainAdviceProgram input.1,
        canonicalFinsetList
          (stringsOfLength
            (decodeBits (decodePlainAdviceData input.1))))

/-- The decompressor that runs a total program over the full cube and returns the code of its
image is a decompressor. -/
theorem plainFullCubeImageDecompressor_partrec
    (T : Map) (hT : isDecompressor T) :
    isDecompressor (plainFullCubeImageDecompressor T) := by
  have hn : Computable
      (fun input : BitString × BitString =>
        decodeBits (decodePlainAdviceData input.1)) :=
    decodeBits_computable.comp
      (decodePlainAdviceData_computable.comp Computable.fst)
  have hall : Computable
      (fun input : BitString × BitString =>
        allStrings (decodeBits (decodePlainAdviceData input.1))) :=
    allStrings_primrec.to_comp.comp hn
  have hcanonical : Computable
      (fun input : BitString × BitString =>
        canonicalFinsetList
          (stringsOfLength
            (decodeBits (decodePlainAdviceData input.1)))) := by
    simpa [stringsOfLength] using
      canonicalFinsetList_toFinset_primrec.to_comp.comp hall
  have hinput : Computable
      (fun input : BitString × BitString =>
        (decodePlainAdviceProgram input.1,
          canonicalFinsetList
            (stringsOfLength
              (decodeBits (decodePlainAdviceData input.1))))) :=
    (decodePlainAdviceProgram_computable.comp Computable.fst).pair
      hcanonical
  unfold plainFullCubeImageDecompressor
  exact Partrec.comp (totalProgramImageCode_partrec T hT) hinput

/-- The advice code pairing a total program `p` with the length `n` describes, under the
full-cube image decompressor, any code of the image of `p` on the strings of length `n`. -/
theorem plainFullCubeImageDecompressor_produces
    {T : Map} {p : BitString} {n : Nat} {Bcode : BitString}
    (hcode : Bcode ∈
      totalProgramImageCode T
        (p, canonicalFinsetList (stringsOfLength n))) :
    produces (plainFullCubeImageDecompressor T)
      (plainAdviceCode p (Nat.bits n)) [] Bcode := by
  change Bcode ∈
    totalProgramImageCode T
      (decodePlainAdviceProgram (plainAdviceCode p (Nat.bits n)),
        canonicalFinsetList
          (stringsOfLength
            (decodeBits
              (decodePlainAdviceData
                (plainAdviceCode p (Nat.bits n))))))
  simpa [decodeBits_natBits] using hcode

/-- Generic coding core for Lemma `l1`.

If the canonical code `y = [A]` of a finite set is total-computable from a
length-`n` string `x` by an `epsilon`-bit program, then `y` belongs to a finite
set of at most `2^n` canonical codes whose ordinary plain complexity is
`epsilon + O(log n)`.

The coefficient of `epsilon` is exactly one.  This is why the proof uses
`plainAdviceCode`: pairing the varying program as the first component of an
ordinary `pairCode` would incorrectly charge `2 * epsilon`. -/
theorem inPlainDescriptionProfile_of_totalReducesWithin_from_length
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon n : Nat),
      x.length = n →
      TotalReducesWithin T x y epsilon →
      InPlainDescriptionProfile V y (epsilon + logSlack c n) n := by
  obtain ⟨cInv, hInv⟩ :=
    hV.2 (plainFullCubeImageDecompressor T)
      (plainFullCubeImageDecompressor_partrec T hT.1)
  refine ⟨cInv + 4, ?_⟩
  intro x y epsilon n hxlen hred
  obtain ⟨p, hpTotal, hpLen, hpxy⟩ :=
    (totalReducesWithin_iff T x y epsilon).mp hred
  have hxCube : x ∈ stringsOfLength n := by
    rw [mem_stringsOfLength]
    exact hxlen
  obtain ⟨ys, hB, _hys, hcode, hforward, _hbackward, hcard⟩ :=
    exists_totalProgramCanonicalImage hpTotal
      (stringsOfLength n) (codedStringsOfLength_nonempty n)
  have hyB : y ∈ ys.toFinset := by
    obtain ⟨y', hy', hpy'⟩ := hforward x hxCube
    have hyy' : y = y' := Part.mem_unique hpxy hpy'
    simpa [hyy'] using hy'
  refine ⟨ys.toFinset, hB, hyB, ?_, ?_⟩
  · unfold plainSetComplexity
    have hprod :
        produces (plainFullCubeImageDecompressor T)
          (plainAdviceCode p (Nat.bits n)) []
          (codedUniformOn ys.toFinset hB).code :=
      plainFullCubeImageDecompressor_produces hcode
    calc
      plainK V (codedUniformOn ys.toFinset hB).code
          ≤ condK (plainFullCubeImageDecompressor T)
              (codedUniformOn ys.toFinset hB).code [] +
              (cInv : ENat) :=
        hInv _ _
      _ ≤ ((plainAdviceCode p (Nat.bits n)).length : ENat) +
            (cInv : ENat) := by
        gcongr
        exact sInf_le
          ⟨plainAdviceCode p (Nat.bits n), hprod, rfl⟩
      _ ≤ ((epsilon + logSlack (cInv + 4) n : Nat) : ENat) := by
        apply Nat.cast_le.mpr
        rw [length_plainAdviceCode]
        have hsmall :
            (Nat.bits (Nat.bits n).length).length ≤
              (Nat.bits n).length :=
          length_natBits_le (Nat.bits n).length
        change p.length ≤ epsilon at hpLen
        unfold logSlack
        calc
          p.length + (Nat.bits n).length +
                2 * (Nat.bits (Nat.bits n).length).length + 1 + cInv
              ≤ epsilon + 3 * (Nat.bits n).length + 1 + cInv := by
            omega
          _ ≤ epsilon +
                ((cInv + 4) * (Nat.bits n).length + (cInv + 4)) := by
            have hmul :
                3 * (Nat.bits n).length ≤
                  (cInv + 4) * (Nat.bits n).length :=
              Nat.mul_le_mul_right (Nat.bits n).length (by omega)
            omega
  · rw [card_stringsOfLength] at hcard
    exact hcard

/-- `strange_string_lemma_1` (Lemma `l1` in VS40).

If `S` is an `epsilon`-strong statistic for a length-`n` string `x`, its
canonical finite-set code has an `(epsilon + O(log n), n)` ordinary plain
description. -/
theorem strange_string_lemma_1
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ (x : BitString) (S : Finset BitString)
      (hS : S.Nonempty) (epsilon n : Nat),
      x.length = n →
      x ∈ S →
      IsStrongSetModel T x S hS epsilon →
      InPlainDescriptionProfile V (codedUniformOn S hS).code
        (epsilon + logSlack c n) n := by
  obtain ⟨c, hc⟩ :=
    inPlainDescriptionProfile_of_totalReducesWithin_from_length
      V T hV hT
  refine ⟨c, ?_⟩
  intro x S hS epsilon n hxlen _hx hstrong
  exact hc x (codedUniformOn S hS).code epsilon n hxlen hstrong

/-! ### Finite counting leaf for the marking construction

The proof of Theorem `t1` first bounds the strings covered by its three marked
families.  The source's displayed estimate is valid away from the two
right-hand boundary cases, namely when both `epsilon` and `k` are at least four
below `n`.  Those side conditions are explicit here; the eventual public
theorem must absorb the omitted boundary cases into its uniform constants
rather than silently use truncated subtraction as ordinary subtraction. -/

/-- The arithmetic core of the first `t1` union bound:
two families contribute at most `2^(n-3)` strings each, the low-complexity
singletons contribute at most `2^(n-4)`, and their sum is below half of the
length-`n` cube. -/
theorem t1_marked_union_count_lt_half
    (n k epsilon : Nat)
    (hεn : epsilon + 4 ≤ n)
    (hkn : k + 4 ≤ n) :
    2 ^ (epsilon + 1) * 2 ^ (n - epsilon - 4) +
        2 ^ (k + 1) * 2 ^ (n - k - 4) + 2 ^ k <
      2 ^ (n - 1) := by
  have hεexp : epsilon + 1 + (n - epsilon - 4) = n - 3 := by
    omega
  have hkexp : k + 1 + (n - k - 4) = n - 3 := by
    omega
  have hk4 : k ≤ n - 4 := by
    omega
  have hkpow : 2 ^ k ≤ 2 ^ (n - 4) :=
    Nat.pow_le_pow_right (by norm_num) hk4
  rw [← pow_add, hεexp, ← pow_add, hkexp]
  calc
    2 ^ (n - 3) + 2 ^ (n - 3) + 2 ^ k
        ≤ 2 ^ (n - 3) + 2 ^ (n - 3) + 2 ^ (n - 4) := by
          omega
    _ = 5 * 2 ^ (n - 4) := by
          have hn3 : n - 3 = (n - 4) + 1 := by
            omega
          rw [hn3, pow_succ]
          ring
    _ < 8 * 2 ^ (n - 4) := by
          exact Nat.mul_lt_mul_of_pos_right (by norm_num)
            (pow_pos (by norm_num) _)
    _ = 2 ^ (n - 1) := by
          have hn1 : n - 1 = (n - 4) + 3 := by
            omega
          rw [hn1, pow_add]
          norm_num
          rw [mul_comm]

/-- Finite probabilistic-method lemma used by the `t1` marking construction.
The integer hypothesis is the denominator-cleared form of the source's union
bound. -/
theorem exists_sparse_intersection_subset
    {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒞 : Finset (Finset α)) (N s t : Nat)
    (hN : N ≤ U.card)
    (hsmall : ∀ C ∈ 𝒞, C ⊆ U ∧ C.card ≤ s)
    (hcount :
      𝒞.card * Nat.choose N (t + 1) * s ^ (t + 1) <
        (U.card - t) ^ (t + 1)) :
    ∃ A ⊆ U, A.card = N ∧
      ∀ C ∈ 𝒞, (A ∩ C).card ≤ t := by
  by_cases hrN : t + 1 ≤ N
  · have htU : t < U.card := by
      by_contra h
      have hzero : U.card - t = 0 := by omega
      rw [hzero] at hcount
      simp at hcount
    have hfactorial :
        (t + 1).factorial *
            (𝒞.card * Nat.choose N (t + 1) * Nat.choose s (t + 1)) <
          (t + 1).factorial * Nat.choose U.card (t + 1) := by
      calc
        (t + 1).factorial *
              (𝒞.card * Nat.choose N (t + 1) * Nat.choose s (t + 1))
            = 𝒞.card * Nat.choose N (t + 1) *
                Nat.descFactorial s (t + 1) := by
              rw [Nat.descFactorial_eq_factorial_mul_choose]
              ring
        _ ≤ 𝒞.card * Nat.choose N (t + 1) * s ^ (t + 1) := by
              gcongr
              exact Nat.descFactorial_le_pow s (t + 1)
        _ < (U.card - t) ^ (t + 1) := hcount
        _ = (U.card + 1 - (t + 1)) ^ (t + 1) := by
              congr 1
              omega
        _ ≤ Nat.descFactorial U.card (t + 1) :=
              Nat.pow_sub_le_descFactorial U.card (t + 1)
        _ = (t + 1).factorial * Nat.choose U.card (t + 1) :=
              Nat.descFactorial_eq_factorial_mul_choose _ _
    have hchoose :
        𝒞.card * Nat.choose N (t + 1) * Nat.choose s (t + 1) <
          Nat.choose U.card (t + 1) :=
      (Nat.mul_lt_mul_left (Nat.factorial_pos (t + 1))).mp hfactorial
    have hfillPos :
        0 < Nat.choose (U.card - (t + 1)) (N - (t + 1)) :=
      Nat.choose_pos (Nat.sub_le_sub_right hN (t + 1))
    have hmul := Nat.mul_lt_mul_of_pos_right hchoose hfillPos
    have hbad :
        𝒞.card * Nat.choose s (t + 1) *
            Nat.choose (U.card - (t + 1)) (N - (t + 1)) <
          Nat.choose U.card N := by
      apply (Nat.mul_lt_mul_right (Nat.choose_pos hrN)).mp
      calc
        (𝒞.card * Nat.choose s (t + 1) *
              Nat.choose (U.card - (t + 1)) (N - (t + 1))) *
              Nat.choose N (t + 1)
            = (𝒞.card * Nat.choose N (t + 1) *
                Nat.choose s (t + 1)) *
                Nat.choose (U.card - (t + 1)) (N - (t + 1)) := by
              ring
        _ < Nat.choose U.card (t + 1) *
              Nat.choose (U.card - (t + 1)) (N - (t + 1)) := hmul
        _ = Nat.choose U.card N * Nat.choose N (t + 1) := by
              rw [← Nat.choose_mul hrN]
    have hsum :
        (∑ C ∈ 𝒞, ∑ k ∈ Finset.Ico (t + 1) (N + 1),
              Nat.choose C.card k *
                Nat.choose (U.card - C.card) (N - k)) <
          Nat.choose U.card N := by
      calc
        (∑ C ∈ 𝒞, ∑ k ∈ Finset.Ico (t + 1) (N + 1),
              Nat.choose C.card k *
                Nat.choose (U.card - C.card) (N - k))
            ≤ ∑ _C ∈ 𝒞,
                Nat.choose s (t + 1) *
                  Nat.choose (U.card - (t + 1)) (N - (t + 1)) := by
              apply Finset.sum_le_sum
              intro C hC
              refine (per_ball_bad_le C.card U.card N t
                (Finset.card_le_card (hsmall C hC).1)).trans ?_
              gcongr
              exact (hsmall C hC).2
        _ = 𝒞.card * Nat.choose s (t + 1) *
              Nat.choose (U.card - (t + 1)) (N - (t + 1)) := by
              simp
              ring
        _ < Nat.choose U.card N := hbad
    obtain ⟨A, hAU, hAcard, hA⟩ :=
      exists_subset_inter_le_of_counting_bound U N t 𝒞
        (fun C hC => (hsmall C hC).1) hsum
    refine ⟨A, hAU, hAcard, ?_⟩
    intro C hC
    simpa [Finset.inter_comm] using hA C hC
  · obtain ⟨A, hAU, hAcard⟩ := Finset.exists_subset_card_eq hN
    refine ⟨A, hAU, hAcard, ?_⟩
    intro C _hC
    have hinter : (A ∩ C).card ≤ A.card :=
      Finset.card_le_card Finset.inter_subset_left
    omega

/-! ### Figure 6 geometry -/

/-- The dashed Figure 6 polygon is upward closed in both coordinates when
`k ≤ n`.  The side condition is needed only when increasing the first
coordinate crosses the breakpoint `epsilon`: the boundary then changes from
`i + j = n` to `i + j = k`. -/
theorem t1PlainPolygon_mono
    {n k epsilon : Nat} {p q : Nat × Nat}
    (hkn : k ≤ n)
    (hp : p ∈ t1PlainPolygon n k epsilon)
    (h₁ : p.1 ≤ q.1) (h₂ : p.2 ≤ q.2) :
    q ∈ t1PlainPolygon n k epsilon := by
  unfold t1PlainPolygon at hp ⊢
  by_cases hq : q.1 < epsilon
  · have hpε : p.1 < epsilon := h₁.trans_lt hq
    simp only [Set.mem_setOf_eq, if_pos hpε] at hp
    simp only [Set.mem_setOf_eq, if_pos hq]
    omega
  · simp only [Set.mem_setOf_eq, if_neg hq]
    by_cases hpε : p.1 < epsilon
    · simp only [Set.mem_setOf_eq, if_pos hpε] at hp
      omega
    · simp only [Set.mem_setOf_eq, if_neg hpε] at hp
      omega

/-- The solid Figure 6 polygon is upward closed in both coordinates. -/
theorem t1StrongPolygon_mono
    {n k : Nat} {p q : Nat × Nat}
    (hp : p ∈ t1StrongPolygon n k)
    (h₁ : p.1 ≤ q.1) (h₂ : p.2 ≤ q.2) :
    q ∈ t1StrongPolygon n k := by
  unfold t1StrongPolygon at hp ⊢
  rcases hp with hp | hp
  · exact Or.inl (hp.trans h₁)
  · exact Or.inr (by omega)

/-- Increasing the breakpoint `epsilon` can only shrink the dashed polygon,
provided its post-breakpoint boundary `k` lies below the pre-breakpoint
boundary `n`. -/
theorem t1PlainPolygon_antitone_epsilon
    {n k epsilon epsilon' : Nat} {p : Nat × Nat}
    (hkn : k ≤ n) (hε : epsilon ≤ epsilon')
    (hp : p ∈ t1PlainPolygon n k epsilon') :
    p ∈ t1PlainPolygon n k epsilon := by
  unfold t1PlainPolygon at hp ⊢
  by_cases hpε : p.1 < epsilon
  · have hpε' : p.1 < epsilon' := hpε.trans_le hε
    simpa [hpε, hpε'] using hp
  · by_cases hpε' : p.1 < epsilon'
    · simp only [Set.mem_setOf_eq, if_pos hpε'] at hp
      simp only [Set.mem_setOf_eq, if_neg hpε]
      omega
    · simpa [hpε, hpε'] using hp

/-- Increasing the ambient length can only shrink the dashed Figure 6 polygon. -/
theorem t1PlainPolygon_antitone_n
    {n n' k epsilon : Nat} (hn : n ≤ n') :
    t1PlainPolygon n' k epsilon ⊆
      t1PlainPolygon n k epsilon := by
  intro q hq
  unfold t1PlainPolygon at hq ⊢
  by_cases h : q.1 < epsilon
  · simp only [Set.mem_setOf_eq, if_pos h] at hq ⊢
    exact Nat.le_trans hn hq
  · simp only [Set.mem_setOf_eq, if_neg h] at hq ⊢
    exact hq

/-- Increasing either boundary parameter can only shrink the solid Figure 6
polygon. -/
theorem t1StrongPolygon_antitone_params
    {n n' k k' : Nat} (hn : n ≤ n') (hk : k ≤ k') :
    t1StrongPolygon n' k' ⊆
      t1StrongPolygon n k := by
  intro q hq
  unfold t1StrongPolygon at hq ⊢
  rcases hq with hk' | hn'
  · left
    omega
  · right
    omega

/-- Under `epsilon ≤ k ≤ n`, the solid Figure 6 polygon lies inside the
dashed polygon. -/
theorem t1StrongPolygon_subset_t1PlainPolygon
    {n k epsilon : Nat}
    (hε : epsilon ≤ k) (hkn : k ≤ n) :
    t1StrongPolygon n k ⊆ t1PlainPolygon n k epsilon := by
  intro p hp
  unfold t1StrongPolygon at hp
  unfold t1PlainPolygon
  by_cases hpε : p.1 < epsilon
  · simp only [Set.mem_setOf_eq, if_pos hpε]
    rcases hp with hp | hp
    · omega
    · exact hp
  · simp only [Set.mem_setOf_eq, if_neg hpε]
    rcases hp with hp | hp
    · omega
    · omega

/-- The full length cube supplies the left endpoint of the strong Figure 6
profile once the fixed strength budget dominates its uniform total-decoder
constant. -/
theorem t1_fullCube_strong_profile_endpoint
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ cStrength cProfile : Nat, ∀ (x : BitString) (n epsilon : Nat),
      x.length = n →
      cStrength ≤ epsilon →
      (logSlack cProfile n, n) ∈
        strongDescriptionProfileSet V T x epsilon := by
  obtain ⟨cProfile, hPlain⟩ :=
    plainSetComplexity_fullCube_le_logSlack V hV
  obtain ⟨cStrength, hStrong⟩ :=
    fullCube_isStrongSetModel_const T hT
  refine ⟨cStrength, cProfile, ?_⟩
  intro x n epsilon hxlen hStrength
  change InStrongDescriptionProfile V T x epsilon
    (logSlack cProfile n) n
  refine ⟨stringsOfLength n, codedStringsOfLength_nonempty n, ?_, ?_⟩
  · refine ⟨?_, hPlain n, ?_⟩
    · exact (mem_stringsOfLength n x).mpr hxlen
    · rw [card_stringsOfLength]
  · simpa only [hxlen] using
      (hStrong x).mono hStrength

/-- A singleton supplies the right endpoint of the strong Figure 6 profile.
The strength threshold is uniform, while the profile slack absorbs the given
upper bound for `plainK x`. -/
theorem t1_singleton_strong_profile_endpoint
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ cStrength : Nat, ∀ cK : Nat, ∃ cProfile : Nat,
      ∀ (x : BitString) (n k epsilon : Nat),
      plainK V x ≤ (k + logSlack cK n : ENat) →
      cStrength ≤ epsilon →
      (k + logSlack cProfile n, 0) ∈
        strongDescriptionProfileSet V T x epsilon := by
  obtain ⟨cPlain, hPlain⟩ :=
    plainSetComplexity_singleton_le_plainK V hV
  obtain ⟨cStrength, hStrong⟩ :=
    singleton_isStrongSetModel T hT
  refine ⟨cStrength, fun cK => ⟨cK + cPlain, ?_⟩⟩
  intro x n k epsilon hK hStrength
  change InStrongDescriptionProfile V T x epsilon
    (k + logSlack (cK + cPlain) n) 0
  refine ⟨{x}, Finset.singleton_nonempty x, ?_, ?_⟩
  · refine ⟨Finset.mem_singleton.mpr rfl, ?_, by simp⟩
    calc
      plainSetComplexity V {x} (Finset.singleton_nonempty x)
          ≤ plainK V x + (cPlain : ENat) := hPlain x
      _ ≤ (k + logSlack cK n : ENat) + (cPlain : ENat) := by
        gcongr
      _ ≤ (k + logSlack (cK + cPlain) n : Nat) := by
        exact_mod_cast (show
          k + logSlack cK n + cPlain ≤
            k + logSlack (cK + cPlain) n by
          unfold logSlack
          nlinarith [Nat.zero_le (Nat.bits n).length])
  · exact (hStrong x).mono hStrength

/-- The low-complexity avoiding set gives the source's upper bound
`plainK x ≤ k + O(log n)` by the ordinary two-part member decoder. -/
theorem t1_avoiding_set_plainK_upper
    (V : Map) (hV : isOptimalConditional V) :
    ∀ cA : Nat, ∃ cK : Nat,
      ∀ (n k epsilon : Nat) (A : Finset BitString)
        (hA : A.Nonempty) (x : BitString),
      epsilon ≤ k →
      k ≤ n →
      A.card = 2 ^ (k - epsilon) →
      x ∈ A →
      x.length = n →
      plainSetComplexity V A hA ≤
        (epsilon + logSlack cA n : ENat) →
      plainK V x ≤ (k + logSlack cK n : ENat) := by
  let U : Map := Classical.choose exists_isOptimalPrefixConditional
  have hU : IsOptimalPrefixConditional U :=
    Classical.choose_spec exists_isOptimalPrefixConditional
  obtain ⟨cTwo, hTwo⟩ :=
    plainK_le_of_inPlainDescriptionProfile V U hV hU
  intro cA
  obtain ⟨bA, hbA⟩ := logSlack_le_add_const cA
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cTwo 3 bA
  refine ⟨cA + cFold, ?_⟩
  intro n k epsilon A hA x hepsilon hkn hAcard hxA hxlen
      hAcomplexity
  have hprofile :
      InPlainDescriptionProfile V x
        (epsilon + logSlack cA n) (k - epsilon) := by
    refine ⟨A, hA, hxA, hAcomplexity, ?_⟩
    rw [hAcard]
  have htwo :=
    hTwo x n (epsilon + logSlack cA n) (k - epsilon)
      hxlen hprofile
  have harg :
      n + (epsilon + logSlack cA n) + (k - epsilon) ≤
        3 * n + bA := by
    have hAlog := hbA n
    omega
  have hslack :
      logSlack cTwo
          (n + (epsilon + logSlack cA n) + (k - epsilon)) ≤
        logSlack cFold n :=
    (logSlack_mono_right cTwo harg).trans (hFold n)
  calc
    plainK V x
        ≤ (epsilon + logSlack cA n) + (k - epsilon) +
            logSlack cTwo
              (n + (epsilon + logSlack cA n) + (k - epsilon)) :=
      htwo
    _ ≤ (k + logSlack (cA + cFold) n : Nat) := by
      exact_mod_cast (show
        (epsilon + logSlack cA n) + (k - epsilon) +
            logSlack cTwo
              (n + (epsilon + logSlack cA n) + (k - epsilon)) ≤
          k + logSlack (cA + cFold) n by
        rw [← logSlack_add_const]
        omega)

/-- Ordinary-plain counterpart of the set-level strong description shift.
When the requested split is no larger than the actual model, the canonical
chunk containing `x` divides cardinality by `2^i` and charges only
`i + O(log i)` ordinary plain bits. -/
theorem plain_description_shift_set
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀
      (x : BitString) (S : Finset BitString) (hS : S.Nonempty)
      (i : Nat), x ∈ S → 2 ^ i ≤ S.card →
      ∃ (S' : Finset BitString) (hS' : S'.Nonempty),
        x ∈ S' ∧
        S'.card * 2 ^ i ≤ S.card ∧
        plainSetComplexity V S' hS' ≤
          plainSetComplexity V S hS +
            (i : ENat) + (logSlack c i : ENat) := by
  obtain ⟨cPlain, hPlain⟩ :=
    plainSetComplexity_descriptionChunk_succ V hV
  let c := cPlain + 10
  refine ⟨c, ?_⟩
  intro x S hS i hx hi
  let S' := descriptionChunk S x (i + 1)
  have hxS' : x ∈ S' :=
    mem_descriptionChunk S x (i + 1) hx
  let hS' : S'.Nonempty := ⟨x, hxS'⟩
  refine ⟨S', hS', hxS',
    card_descriptionChunk_succ_mul_pow_le S x i hi, ?_⟩
  have hbits :
      (Nat.bits (i + 1)).length ≤
        (Nat.bits i).length + 2 := by
    simpa using length_natBits_add_le i 1
  have hslack :
      1 + 2 * (Nat.bits (i + 1)).length + cPlain ≤
        logSlack c i := by
    unfold logSlack c
    nlinarith [Nat.zero_le (Nat.bits i).length]
  have hcost :
      i + 1 + 2 * (Nat.bits (i + 1)).length + cPlain ≤
        i + logSlack c i := by
    omega
  calc
    plainSetComplexity V S' hS'
        ≤ plainSetComplexity V S hS +
            ((i + 1 + 2 * (Nat.bits (i + 1)).length +
              cPlain : Nat) : ENat) := hPlain S hS x i hx
    _ ≤ plainSetComplexity V S hS +
          ((i + logSlack c i : Nat) : ENat) := by
      gcongr
    _ = plainSetComplexity V S hS +
          (i : ENat) + (logSlack c i : ENat) := by
      push_cast
      rw [add_assoc]

/-- The executable `(i+1)`-address chunk always has the expected dyadic
profile size, including the case where the requested split exceeds the
actual set size (then the chunk is a singleton). -/
theorem card_descriptionChunk_succ_le_pow_sub
    (S : Finset BitString) (x : BitString) (i b : Nat)
    (hcard : S.card ≤ 2 ^ b) :
    (descriptionChunk S x (i + 1)).card ≤ 2 ^ (b - i) := by
  by_cases hib : i < b
  · have h :=
      card_descriptionChunk_le_pow S x (i + 1) b hcard (by omega)
    have hexponent : b - (i + 1) + 1 = b - i := by
      omega
    rw [hexponent] at h
    exact h
  · have hbi : b ≤ i := by omega
    have hpow : 2 ^ b ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by norm_num) hbi
    have hlt : S.card < 2 ^ (i + 1) := by
      calc
        S.card ≤ 2 ^ b := hcard
        _ ≤ 2 ^ i := hpow
        _ < 2 ^ (i + 1) := by
          rw [pow_succ]
          nlinarith [pow_pos (by norm_num : 0 < (2 : Nat)) i]
    have hdiv : S.card / 2 ^ (i + 1) = 0 :=
      Nat.div_eq_of_lt hlt
    calc
      (descriptionChunk S x (i + 1)).card
          ≤ descriptionChunkSize S (i + 1) := by
        unfold descriptionChunk
        exact (List.toFinset_card_le _).trans
          (List.length_take_le _ _)
      _ = 1 := by simp [descriptionChunkSize, hdiv]
      _ = 2 ^ (b - i) := by simp [Nat.sub_eq_zero_of_le hbi]

/-- Profile-level ordinary description shift used by the dashed Figure 6
boundary. It is total over the requested shift: when the original model is
already smaller than the split scale, the canonical chunk is a singleton. -/
theorem inPlainDescriptionProfile_shift
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (x : BitString) (a b i : Nat),
      InPlainDescriptionProfile V x a b →
      InPlainDescriptionProfile V x
        (a + i + logSlack c i) (b - i) := by
  obtain ⟨cPlain, hPlain⟩ :=
    plainSetComplexity_descriptionChunk_succ V hV
  let c := cPlain + 10
  refine ⟨c, ?_⟩
  intro x a b i hprofile
  obtain ⟨S, hS, hxS, hcomp, hcard⟩ := hprofile
  let S' := descriptionChunk S x (i + 1)
  have hxS' : x ∈ S' :=
    mem_descriptionChunk S x (i + 1) hxS
  let hS' : S'.Nonempty := ⟨x, hxS'⟩
  refine ⟨S', hS', hxS', ?_,
    card_descriptionChunk_succ_le_pow_sub S x i b hcard⟩
  have hbits :
      (Nat.bits (i + 1)).length ≤
        (Nat.bits i).length + 2 := by
    simpa using length_natBits_add_le i 1
  have hslack :
      1 + 2 * (Nat.bits (i + 1)).length + cPlain ≤
        logSlack c i := by
    unfold logSlack c
    nlinarith [Nat.zero_le (Nat.bits i).length]
  calc
    plainSetComplexity V S' hS'
        ≤ plainSetComplexity V S hS +
            ((i + 1 + 2 * (Nat.bits (i + 1)).length +
              cPlain : Nat) : ENat) := hPlain S hS x i hxS
    _ ≤ (a : ENat) +
          ((i + 1 + 2 * (Nat.bits (i + 1)).length +
            cPlain : Nat) : ENat) := by
      gcongr
    _ ≤ ((a + i + logSlack c i : Nat) : ENat) := by
      exact_mod_cast (show
        a + (i + 1 + 2 * (Nat.bits (i + 1)).length + cPlain) ≤
          a + i + logSlack c i by
        omega)

/-- Absence of a source `B` mark forces every ordinary description below the
`epsilon` complexity threshold to lie within logarithmic distance of the
diagonal `a+b=n`. -/
theorem t1_not_bMarked_plain_profile_lower
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (n epsilon : Nat) (x : BitString)
      (a b : Nat),
      epsilon + 4 ≤ n →
      x.length = n →
      ¬ T1BMarked V n epsilon x →
      InPlainDescriptionProfile V x a b →
      a < epsilon →
      n ≤ a + b + logSlack c n := by
  obtain ⟨cShift, hShift⟩ :=
    inPlainDescriptionProfile_shift V hV
  refine ⟨cShift + 5, ?_⟩
  intro n epsilon x a b hepsilonN hxlen hnotB hprofile ha
  by_contra hline
  have hgap :
      a + b + logSlack (cShift + 5) n < n := by
    omega
  have hdelta :
      logSlack cShift n + 4 ≤
        logSlack (cShift + 5) n := by
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits n).length]
  obtain ⟨S, hS, hxS, hcomp, hcard⟩ := hprofile
  by_cases hnear : epsilon ≤ a + logSlack cShift n
  · have hb : b ≤ n - epsilon - 4 := by
      omega
    apply hnotB
    refine ⟨hxlen, S, hS, hxS, ?_, ?_⟩
    · exact hcomp.trans (by exact_mod_cast ha.le)
    · exact hcard.trans
        (Nat.pow_le_pow_right (by norm_num) hb)
  · have hfar : a + logSlack cShift n < epsilon := by
      omega
    let s := epsilon - a - logSlack cShift n
    have hsN : s ≤ n := by
      dsimp [s]
      omega
    have hshifted :=
      hShift x a b s ⟨S, hS, hxS, hcomp, hcard⟩
    obtain ⟨B, hB, hxB, hBcomp, hBcard⟩ :=
      hshifted
    have hshiftSlack :
        logSlack cShift s ≤ logSlack cShift n :=
      logSlack_mono_right cShift hsN
    have hsadd :
        a + logSlack cShift n + s = epsilon := by
      dsimp [s]
      omega
    have hcomplexity :
        a + s + logSlack cShift s ≤ epsilon := by
      calc
        a + s + logSlack cShift s
            ≤ a + s + logSlack cShift n := by omega
        _ = epsilon := by omega
    have hsize : b - s ≤ n - epsilon - 4 := by
      omega
    apply hnotB
    refine ⟨hxlen, B, hB, hxB, ?_, ?_⟩
    · exact hBcomp.trans (by exact_mod_cast hcomplexity)
    · exact hBcard.trans
        (Nat.pow_le_pow_right (by norm_num) hsize)

/-- Absence of a source `D` mark, combined with the ordinary two-part member
decoder, forces every ordinary profile point to lie within logarithmic
distance of the sufficiency diagonal `a+b=k`. -/
theorem t1_not_dMarked_plain_profile_lower
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (n k : Nat) (x : BitString) (a b : Nat),
      x.length = n →
      k ≤ n →
      ¬ T1DMarked V n k x →
      InPlainDescriptionProfile V x a b →
      k ≤ a + b + logSlack c n := by
  let U : Map := Classical.choose exists_isOptimalPrefixConditional
  have hU : IsOptimalPrefixConditional U :=
    Classical.choose_spec exists_isOptimalPrefixConditional
  obtain ⟨cTwo, hTwo⟩ :=
    plainK_le_of_inPlainDescriptionProfile V U hV hU
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cTwo 3 0
  refine ⟨cFold, ?_⟩
  intro n k x a b hxlen hkn hnotD hprofile
  by_cases hsum : k ≤ a + b
  · omega
  · have hab : a + b < k := by omega
    have harg : n + a + b ≤ 3 * n := by
      omega
    have hslack :
        logSlack cTwo (n + a + b) ≤
          logSlack cFold n := by
      have hmono :=
        logSlack_mono_right cTwo harg
      simpa using hmono.trans (hFold n)
    have hKlower :
        (k : ENat) ≤ plainK V x :=
      by
        unfold T1DMarked at hnotD
        push_neg at hnotD
        exact hnotD hxlen
    have hKupper :=
      hTwo x n a b hxlen hprofile
    have hbound :
        (k : ENat) ≤
          (a + b + logSlack cFold n : Nat) := by
      calc
        (k : ENat) ≤ plainK V x := hKlower
        _ ≤ (a + b + logSlack cTwo (n + a + b) : Nat) :=
          hKupper
        _ ≤ (a + b + logSlack cFold n : Nat) := by
          exact_mod_cast (Nat.add_le_add_left hslack (a + b))
    exact_mod_cast hbound

/-- Directed ordinary-profile exclusion: every actual ordinary profile point
is logarithmically close to the dashed Figure 6 polygon. -/
theorem t1_plainProfile_to_polygon
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (n k epsilon : Nat) (x : BitString),
      epsilon ≤ k →
      k + 4 ≤ n →
      x.length = n →
      ¬ T1BMarked V n epsilon x →
      ¬ T1DMarked V n k x →
      ∀ q ∈ plainDescriptionProfileSet V x,
        ∃ q' ∈ t1PlainPolygon n k epsilon,
          natPairLInfDistance q q' ≤ logSlack c n := by
  obtain ⟨cB, hB⟩ :=
    t1_not_bMarked_plain_profile_lower V hV
  obtain ⟨cD, hD⟩ :=
    t1_not_dMarked_plain_profile_lower V hV
  refine ⟨cB + cD, ?_⟩
  intro n k epsilon x hepsilon hkn hxlen hnotB hnotD q hq
  have hBq :=
    hB n epsilon x q.1 q.2 (by omega)
      hxlen hnotB hq
  have hDq :=
    hD n k x q.1 q.2 hxlen (by omega)
      hnotD hq
  have hBslack :
      logSlack cB n ≤ logSlack (cB + cD) n :=
    logSlack_mono_left (Nat.le_add_right _ _) n
  have hDslack :
      logSlack cD n ≤ logSlack (cB + cD) n :=
    logSlack_mono_left (Nat.le_add_left _ _) n
  by_cases hpolygon : q ∈ t1PlainPolygon n k epsilon
  · exact ⟨q, hpolygon, by simp [natPairLInfDistance]⟩
  · by_cases hqepsilon : q.1 < epsilon
    · have hsum : q.1 + q.2 < n := by
        unfold t1PlainPolygon at hpolygon
        simp only [Set.mem_setOf_eq, if_pos hqepsilon,
          not_le] at hpolygon
        exact hpolygon
      let q' : Nat × Nat := (q.1, n - q.1)
      refine ⟨q', ?_, ?_⟩
      · unfold t1PlainPolygon
        simp only [Set.mem_setOf_eq, q', if_pos hqepsilon]
        omega
      · unfold natPairLInfDistance
        simp only [q', Nat.sub_self, zero_add]
        omega
    · have hqepsilon' : epsilon ≤ q.1 := by
        omega
      have hsum : q.1 + q.2 < k := by
        unfold t1PlainPolygon at hpolygon
        simp only [Set.mem_setOf_eq, if_neg hqepsilon,
          not_le] at hpolygon
        exact hpolygon
      let q' : Nat × Nat := (q.1, k - q.1)
      refine ⟨q', ?_, ?_⟩
      · unfold t1PlainPolygon
        simp only [Set.mem_setOf_eq, q', if_neg hqepsilon]
        omega
      · unfold natPairLInfDistance
        simp only [q', Nat.sub_self, zero_add]
        omega

end Kolmogorov
