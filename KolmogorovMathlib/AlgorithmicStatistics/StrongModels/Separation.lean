import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongProfile
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FullCube
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileBridges
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.Restricted.HammingGap
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingPredicates
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CylinderRealization
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.StandardDescriptions

/-!
# Strange strings

This file starts the constructive part of VS40 Section 7.  In particular, it
contains the source-exact coding lemma `l1`.  The theorem `t1` is deliberately
not declared yet: its source statement refers to the two polygons in Figure 6,
and a public Lean declaration must first spell out those polygons and the
marking-game construction that realizes them.
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

theorem plainFullCubeImageDecompressor_partrec
    (T : Map) (hT : isDecompressor T) :
    isDecompressor (plainFullCubeImageDecompressor T) := by
  have hn : Computable
      (fun input : BitString × BitString =>
        decodeBits (decodePlainAdviceData input.1)) :=
    decodeBitsComputable.comp
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
    rw [memStringsOfLength]
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
          length_natBits_le_self (Nat.bits n).length
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
  · rw [cardStringsOfLength] at hcard
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
    simp only [Set.mem_ofPred_eq, if_pos hpε] at hp
    simp only [Set.mem_ofPred_eq, if_pos hq]
    omega
  · simp only [Set.mem_ofPred_eq, if_neg hq]
    by_cases hpε : p.1 < epsilon
    · simp only [Set.mem_ofPred_eq, if_pos hpε] at hp
      omega
    · simp only [Set.mem_ofPred_eq, if_neg hpε] at hp
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
    · simp only [Set.mem_ofPred_eq, if_pos hpε'] at hp
      simp only [Set.mem_ofPred_eq, if_neg hpε]
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
  · simp only [Set.mem_ofPred_eq, if_pos h] at hq ⊢
    exact Nat.le_trans hn hq
  · simp only [Set.mem_ofPred_eq, if_neg h] at hq ⊢
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
  · simp only [Set.mem_ofPred_eq, if_pos hpε]
    rcases hp with hp | hp
    · omega
    · exact hp
  · simp only [Set.mem_ofPred_eq, if_neg hpε]
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
    · exact (memStringsOfLength n x).mpr hxlen
    · rw [cardStringsOfLength]
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
        push Not at hnotD
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
        simp only [Set.mem_ofPred_eq, if_pos hqepsilon,
          not_le] at hpolygon
        exact hpolygon
      let q' : Nat × Nat := (q.1, n - q.1)
      refine ⟨q', ?_, ?_⟩
      · unfold t1PlainPolygon
        simp only [Set.mem_ofPred_eq, q', if_pos hqepsilon]
        omega
      · unfold natPairLInfDistance
        simp only [q', Nat.sub_self, zero_add]
        omega
    · have hqepsilon' : epsilon ≤ q.1 := by
        omega
      have hsum : q.1 + q.2 < k := by
        unfold t1PlainPolygon at hpolygon
        simp only [Set.mem_ofPred_eq, if_neg hqepsilon,
          not_le] at hpolygon
        exact hpolygon
      let q' : Nat × Nat := (q.1, k - q.1)
      refine ⟨q', ?_, ?_⟩
      · unfold t1PlainPolygon
        simp only [Set.mem_ofPred_eq, q', if_neg hqepsilon]
        omega
      · unfold natPairLInfDistance
        simp only [q', Nat.sub_self, zero_add]
        omega

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
      (memStringsOfLength n x).mpr hxlen, hCube n, ?_⟩
    rw [cardStringsOfLength]
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
    push Not at hnotD
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
      simp only [Set.mem_ofPred_eq, not_or, not_le] at hpolygon
      exact hpolygon.1
    have hqsum : q.1 + q.2 < n := by
      unfold t1StrongPolygon at hpolygon
      simp only [Set.mem_ofPred_eq, not_or, not_le] at hpolygon
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
          simp only [Set.mem_ofPred_eq, q']
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
            B.card ≤ 2 ^ (n - k - 4) := by
          by_cases hsr : s ≤ r
          · have hiEq : i = s := Nat.min_eq_left hsr
            have hsPow : 2 ^ s ≤ S.card := by
              simpa [hiEq] using hiPow
            have hsB : s ≤ q.2 := by
              have hpows :
                  2 ^ s ≤ 2 ^ q.2 :=
                hsPow.trans hPlain.2.2
              exact
                (Nat.pow_le_pow_iff_right (by norm_num)).mp hpows
            have hmul :
                B.card * 2 ^ s ≤ 2 ^ q.2 := by
              rw [← hiEq]
              exact hBmul.trans hPlain.2.2
            have hquot :
                B.card ≤ 2 ^ (q.2 - s) := by
              have hrewrite :
                  2 ^ q.2 = 2 ^ (q.2 - s) * 2 ^ s := by
                rw [← pow_add]
                congr
                omega
              rw [hrewrite] at hmul
              exact Nat.le_of_mul_le_mul_right hmul
                (pow_pos (by norm_num) s)
            have hexponent :
                q.2 - s ≤ n - k - 4 := by
              omega
            exact hquot.trans
              (Nat.pow_le_pow_right (by norm_num) hexponent)
          · have hrs : r < s := by
              omega
            have hiEq : i = r := Nat.min_eq_right hrs.le
            have hlt :
                B.card * 2 ^ r < 2 * 2 ^ r := by
              calc
                B.card * 2 ^ r
                    ≤ S.card := by simpa [hiEq] using hBmul
                _ < 2 ^ (Nat.log 2 S.card + 1) := by
                  simpa [r] using
                    Nat.lt_pow_succ_log_self
                      (by norm_num : 1 < (2 : Nat)) S.card
                _ = 2 * 2 ^ r := by
                  rw [pow_succ]
                  simp [r, Nat.mul_comm]
            have hBone : B.card ≤ 1 := by
              have : B.card < 2 :=
                Nat.lt_of_mul_lt_mul_right hlt
              omega
            exact hBone.trans (Nat.one_le_pow _ _ (by norm_num))
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

/-! ### S7 Normal strings and standard descriptions drafts -/

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
  obtain ⟨cLength, hLength⟩ := plainKLeLength V hV
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
  simp only [Set.mem_ofPred_eq]
  refine ⟨Or.inl ⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩

theorem separationGrayProfile_left_iff
    {k i j : Nat} (hi : i < k) :
    (i, j) ∈ separationGrayProfile k ↔ 4 * k ≤ i + j := by
  unfold separationGrayProfile
  simp only [Set.mem_ofPred_eq]
  omega

theorem separationGrayProfile_right_iff
    {k i j : Nat} (hi : k ≤ i) :
    (i, j) ∈ separationGrayProfile k ↔ 3 * k ≤ i + j := by
  unfold separationGrayProfile
  simp only [Set.mem_ofPred_eq]
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

theorem fixedSplitPairCode_primrec :
    Primrec fixedSplitPairCode := by
  unfold fixedSplitPairCode
  exact pairCode_primrec.comp
    (Primrec.list_take.comp (primrecDecodeBits.comp Primrec.fst)
      Primrec.snd)
    (Primrec.list_drop.comp (primrecDecodeBits.comp Primrec.fst)
      Primrec.snd)

noncomputable def fixedSplitPairDecompressor : Map :=
  fun input => Part.some (fixedSplitPairCode input)

theorem fixedSplitPairDecompressor_partrec :
    isDecompressor fixedSplitPairDecompressor :=
  Computable.partrec fixedSplitPairCode_primrec.to_comp

theorem fixedSplitPairDecompressor_total (p : BitString) :
    IsTotalProgram fixedSplitPairDecompressor p := by
  intro w
  trivial

theorem fixedSplitPairDecompressor_produces (y z : BitString) :
    produces fixedSplitPairDecompressor (Nat.bits y.length) (y ++ z)
      (pairCode y z) := by
  unfold produces fixedSplitPairDecompressor fixedSplitPairCode
  simp

/-- Decode a pair and concatenate its components. -/
def appendDecodedPair (w : BitString) : BitString :=
  decodeFirst w ++ decodeSecond w

theorem appendDecodedPair_computable : Computable appendDecodedPair := by
  unfold appendDecodedPair
  exact (Primrec.list_append.comp
    decodeFirst_primrec' decodeSecond_primrec').to_comp

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
