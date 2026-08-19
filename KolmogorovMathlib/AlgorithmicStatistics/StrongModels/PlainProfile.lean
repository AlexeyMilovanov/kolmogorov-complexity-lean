import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CanonicalImage
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalReduction
import Mathlib.Order.UpperLower.Basic

/-!
# Plain description profiles and total-equivalence stability

Section 7 uses ordinary *plain* complexity for its description profiles.  This
module deliberately does not reuse the prefix-based `setComplexity` or
`InDescriptionProfile`.  The ordinary optimal machine `V` and the optimal
total-conditional machine `T` remain separate parameters.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- Plain complexity of the canonical code of a nonempty finite set. -/
noncomputable def plainSetComplexity
    (V : Map) (S : Finset BitString) (hS : S.Nonempty) : ENat :=
  plainK V (codedUniformOn S hS).code

/-- A finite-set `(i,j)`-description using ordinary plain complexity. -/
noncomputable def IsPlainIJDescription
    (V : Map) (x : BitString) (S : Finset BitString)
    (hS : S.Nonempty) (i j : Nat) : Prop :=
  x ∈ S ∧ plainSetComplexity V S hS ≤ (i : ENat) ∧
    S.card ≤ 2 ^ j

/-- The source-facing ordinary plain description profile. -/
noncomputable def InPlainDescriptionProfile
    (V : Map) (x : BitString) (i j : Nat) : Prop :=
  ∃ (S : Finset BitString) (hS : S.Nonempty),
    IsPlainIJDescription V x S hS i j

theorem IsPlainIJDescription.mono_i
    {V : Map} {x : BitString} {S : Finset BitString}
    {hS : S.Nonempty} {i i' j : Nat}
    (hii : i ≤ i')
    (h : IsPlainIJDescription V x S hS i j) :
    IsPlainIJDescription V x S hS i' j := by
  exact ⟨h.1, h.2.1.trans (by exact_mod_cast hii), h.2.2⟩

theorem IsPlainIJDescription.mono_j
    {V : Map} {x : BitString} {S : Finset BitString}
    {hS : S.Nonempty} {i j j' : Nat}
    (hjj : j ≤ j')
    (h : IsPlainIJDescription V x S hS i j) :
    IsPlainIJDescription V x S hS i j' := by
  exact ⟨h.1, h.2.1,
    h.2.2.trans (Nat.pow_le_pow_right (by decide) hjj)⟩

theorem InPlainDescriptionProfile.mono_i
    {V : Map} {x : BitString} {i i' j : Nat}
    (hii : i ≤ i')
    (h : InPlainDescriptionProfile V x i j) :
    InPlainDescriptionProfile V x i' j := by
  obtain ⟨S, hS, hdesc⟩ := h
  exact ⟨S, hS, hdesc.mono_i hii⟩

theorem InPlainDescriptionProfile.mono_j
    {V : Map} {x : BitString} {i j j' : Nat}
    (hjj : j ≤ j')
    (h : InPlainDescriptionProfile V x i j) :
    InPlainDescriptionProfile V x i j' := by
  obtain ⟨S, hS, hdesc⟩ := h
  exact ⟨S, hS, hdesc.mono_j hjj⟩

/-- Plain description profile as a subset of the parameter plane. -/
def plainDescriptionProfileSet
    (V : Map) (x : BitString) : Set (Nat × Nat) :=
  {q | InPlainDescriptionProfile V x q.1 q.2}

theorem plainDescriptionProfileSet_isUpperSet
    (V : Map) (x : BitString) :
    IsUpperSet (plainDescriptionProfileSet V x) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨hi, hj⟩ h
  exact h.mono_i hi |>.mono_j hj

/-- The `ℓ∞` distance on the natural parameter plane. -/
def natPairLInfDistance (q q' : Nat × Nat) : Nat :=
  max ((q.1 - q'.1) + (q'.1 - q.1))
    ((q.2 - q'.2) + (q'.2 - q.2))

/-- Symmetric `ℓ∞` `delta`-neighborhood relation between profile sets: every
point of either set lies within distance `delta` of the other set. -/
def ProfileSetsWithinNeighborhood
    (P Q : Set (Nat × Nat)) (delta : Nat) : Prop :=
  (∀ q ∈ P, ∃ q' ∈ Q,
      natPairLInfDistance q q' ≤ delta) ∧
  (∀ q ∈ Q, ∃ q' ∈ P,
      natPairLInfDistance q q' ≤ delta)

/-- Triangle inequality for the concrete natural-valued `ℓ∞` distance. -/
theorem natPairLInfDistance_triangle
    (q r s : Nat × Nat) :
    natPairLInfDistance q s ≤
      natPairLInfDistance q r + natPairLInfDistance r s := by
  unfold natPairLInfDistance
  apply max_le
  · calc
      (q.1 - s.1) + (s.1 - q.1)
          ≤ ((q.1 - r.1) + (r.1 - q.1)) +
              ((r.1 - s.1) + (s.1 - r.1)) := by omega
      _ ≤ max ((q.1 - r.1) + (r.1 - q.1))
              ((q.2 - r.2) + (r.2 - q.2)) +
            max ((r.1 - s.1) + (s.1 - r.1))
              ((r.2 - s.2) + (s.2 - r.2)) :=
        Nat.add_le_add (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  · calc
      (q.2 - s.2) + (s.2 - q.2)
          ≤ ((q.2 - r.2) + (r.2 - q.2)) +
              ((r.2 - s.2) + (s.2 - r.2)) := by omega
      _ ≤ max ((q.1 - r.1) + (r.1 - q.1))
              ((q.2 - r.2) + (r.2 - q.2)) +
            max ((r.1 - s.1) + (s.1 - r.1))
              ((r.2 - s.2) + (s.2 - r.2)) :=
        Nat.add_le_add (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- Every profile set is at distance zero from itself. -/
theorem ProfileSetsWithinNeighborhood.refl
    (P : Set (Nat × Nat)) :
    ProfileSetsWithinNeighborhood P P 0 := by
  constructor <;> intro q hq <;>
    exact ⟨q, hq, by simp [natPairLInfDistance]⟩

theorem ProfileSetsWithinNeighborhood.symm
    {P Q : Set (Nat × Nat)} {delta : Nat}
    (h : ProfileSetsWithinNeighborhood P Q delta) :
    ProfileSetsWithinNeighborhood Q P delta :=
  ⟨h.2, h.1⟩

theorem ProfileSetsWithinNeighborhood.mono
    {P Q : Set (Nat × Nat)} {δ δ' : Nat}
    (hδ : δ ≤ δ')
    (h : ProfileSetsWithinNeighborhood P Q δ) :
    ProfileSetsWithinNeighborhood P Q δ' := by
  constructor
  · intro q hq
    obtain ⟨q', hq', hdist⟩ := h.1 q hq
    exact ⟨q', hq', hdist.trans hδ⟩
  · intro q hq
    obtain ⟨q', hq', hdist⟩ := h.2 q hq
    exact ⟨q', hq', hdist.trans hδ⟩

/-- Profile neighborhoods compose, with additive radii. -/
theorem ProfileSetsWithinNeighborhood.trans
    {P Q R : Set (Nat × Nat)} {delta delta' : Nat}
    (hPQ : ProfileSetsWithinNeighborhood P Q delta)
    (hQR : ProfileSetsWithinNeighborhood Q R delta') :
    ProfileSetsWithinNeighborhood P R (delta + delta') := by
  constructor
  · intro q hq
    obtain ⟨r, hr, hqr⟩ := hPQ.1 q hq
    obtain ⟨s, hs, hrs⟩ := hQR.1 r hr
    refine ⟨s, hs, (natPairLInfDistance_triangle q r s).trans ?_⟩
    exact Nat.add_le_add hqr hrs
  · intro q hq
    obtain ⟨r, hr, hqr⟩ := hQR.2 q hq
    obtain ⟨s, hs, hrs⟩ := hPQ.2 r hr
    refine ⟨s, hs, (natPairLInfDistance_triangle q r s).trans ?_⟩
    have : natPairLInfDistance q r + natPairLInfDistance r s ≤
        delta' + delta :=
      Nat.add_le_add hqr hrs
    simpa [Nat.add_comm] using this

/-- If `R ⊆ Q ⊆ P` and the outer profile sets are within `delta`, then each
adjacent pair is already within the same neighborhood. -/
theorem ProfileSetsWithinNeighborhood.of_sandwich
    {P Q R : Set (Nat × Nat)} {delta : Nat}
    (hRQ : R ⊆ Q) (hQP : Q ⊆ P)
    (hPR : ProfileSetsWithinNeighborhood P R delta) :
    ProfileSetsWithinNeighborhood P Q delta ∧
      ProfileSetsWithinNeighborhood Q R delta := by
  constructor
  · constructor
    · intro q hq
      obtain ⟨r, hr, hdist⟩ := hPR.1 q hq
      exact ⟨r, hRQ hr, hdist⟩
    · intro q hq
      exact ⟨q, hQP hq, by simp [natPairLInfDistance]⟩
  · constructor
    · intro q hq
      obtain ⟨r, hr, hdist⟩ := hPR.1 q (hQP hq)
      exact ⟨r, hr, hdist⟩
    · intro q hq
      exact ⟨q, hRQ hq, by simp [natPairLInfDistance]⟩

/-- A decompressor for the canonical image set.  Its program is
`pairCode p q`: `q` plainly describes the input set code and the varying total
program `p` is then run over all decoded set members.  Putting `p` first makes
the explicit pairing overhead `2 * |p| + 1`. -/
noncomputable def plainCanonicalImageDecompressor
    (D V : Map) : Map :=
  fun input =>
    (V (decodeSecond input.1, [])).bind fun Acode =>
      totalProgramImageCodeFromSetCode D
        (decodeFirst input.1, Acode)

theorem plainCanonicalImageDecompressor_partrec
    (D V : Map) (hD : isDecompressor D)
    (hV : isDecompressor V) :
    isDecompressor (plainCanonicalImageDecompressor D V) := by
  have hfirst :
      Partrec (fun input : BitString × BitString =>
        V (decodeSecond input.1, [])) :=
    Partrec.comp hV
      (Computable.pair
        (decodeSecond_computable.comp Computable.fst)
        (Computable.const []))
  have hsecond :
      Partrec
        (fun input :
            (BitString × BitString) × BitString =>
          totalProgramImageCodeFromSetCode D
            (decodeFirst input.1.1, input.2)) :=
    Partrec.comp
      (totalProgramImageCodeFromSetCode_partrec D hD)
      (Computable.pair
        (decodeFirst_computable.comp
          (Computable.fst.comp Computable.fst))
        Computable.snd)
  exact Partrec.bind hfirst hsecond

lemma plainCanonicalImageDecompressor_produces
    {D V : Map} {p q Acode Bcode : BitString}
    (hA : produces V q [] Acode)
    (hB : produces (totalProgramImageCodeFromSetCode D)
      p Acode Bcode) :
    produces (plainCanonicalImageDecompressor D V)
      (pairCode p q) [] Bcode := by
  unfold produces plainCanonicalImageDecompressor
  rw [Part.mem_bind_iff]
  refine ⟨Acode, ?_, ?_⟩
  · rw [decodeSecond_pairCode]
    exact hA
  · rw [decodeFirst_pairCode]
    exact hB

/-- Uniform plain-complexity accounting for the canonical image code.  The
constant depends only on the fixed machines `D` and `V`, never on the varying
program `p`, the set codes, or the displayed budget. -/
theorem plainK_canonicalImageCode_le
    (D V : Map) (hD : isDecompressor D)
    (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ {p Acode Bcode : BitString} {i : Nat},
      produces (totalProgramImageCodeFromSetCode D)
        p Acode Bcode →
      plainK V Acode ≤ (i : ENat) →
      plainK V Bcode ≤
        (i + 2 * programLength p + c : Nat) := by
  obtain ⟨c, hc⟩ :=
    hV.2 (plainCanonicalImageDecompressor D V)
      (plainCanonicalImageDecompressor_partrec D V hD hV.1)
  refine ⟨c + 1, ?_⟩
  intro p Acode Bcode i himage hAcomp
  obtain ⟨q, hqLen, hq⟩ :=
    (condKLeIff V Acode [] i).mp hAcomp
  change q.length ≤ i at hqLen
  have hprod :
      produces (plainCanonicalImageDecompressor D V)
        (pairCode p q) [] Bcode :=
    plainCanonicalImageDecompressor_produces hq himage
  calc
    plainK V Bcode
        ≤ condK (plainCanonicalImageDecompressor D V)
            Bcode [] + (c : ENat) :=
      hc Bcode []
    _ ≤ ((pairCode p q).length : ENat) + (c : ENat) := by
      gcongr
      exact sInf_le ⟨pairCode p q, hprod, rfl⟩
    _ ≤ ((i + 2 * programLength p + (c + 1) : Nat) : ENat) := by
      rw [length_pairCode]
      exact_mod_cast (show
        p.length + 1 + p.length + q.length + c ≤
          i + 2 * p.length + (c + 1) by omega)

/-- Directed form of Proposition `prop:equivalence`: a total reduction
`x →ε y` shifts the ordinary plain profile by at most `2ε + O(1)` in the
complexity coordinate and does not increase the size coordinate. -/
theorem inPlainDescriptionProfile_of_totalReducesWithin
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon i j : Nat),
      TotalReducesWithin T x y epsilon →
      InPlainDescriptionProfile V x i j →
      InPlainDescriptionProfile V y
        (i + 2 * epsilon + c) j := by
  obtain ⟨c, hcomplexity⟩ :=
    plainK_canonicalImageCode_le T V hT.1 hV
  refine ⟨c, ?_⟩
  intro x y epsilon i j hred hprofile
  obtain ⟨p, hp, hplen, hpxy⟩ :=
    (totalReducesWithin_iff T x y epsilon).mp hred
  obtain ⟨S, hS, hxS, hScomp, hScard⟩ := hprofile
  obtain ⟨ys, hB, himage, hforward, _hbackward, hcard⟩ :=
    exists_totalProgramCanonicalImage_from_code hp S hS
  have hyB : y ∈ ys.toFinset := by
    obtain ⟨y', hy', hpy'⟩ := hforward x hxS
    have : y = y' := Part.mem_unique hpxy hpy'
    simpa [this] using hy'
  refine ⟨ys.toFinset, hB, hyB, ?_, ?_⟩
  · refine (hcomplexity himage hScomp).trans ?_
    exact_mod_cast (show
      i + 2 * programLength p + c ≤
        i + 2 * epsilon + c by omega)
  · exact hcard.trans hScard

/-- Proposition `prop:equivalence`, with the survey's `O(ε)` made explicit.
Total `ε`-equivalence places the two ordinary plain description profiles in a
uniform `(2ε + c)` coordinatewise neighborhood. -/
theorem totalEquivalentWithin_plainProfiles
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon : Nat),
      TotalEquivalentWithin T x y epsilon →
      ProfileSetsWithinNeighborhood
        (plainDescriptionProfileSet V x)
        (plainDescriptionProfileSet V y)
        (2 * epsilon + c) := by
  obtain ⟨c, hshift⟩ :=
    inPlainDescriptionProfile_of_totalReducesWithin V T hV hT
  refine ⟨c, ?_⟩
  intro x y epsilon hequiv
  obtain ⟨hxy, hyx⟩ :=
    (totalEquivalentWithin_iff T x y epsilon).mp hequiv
  constructor
  · rintro ⟨i, j⟩ hij
    refine ⟨(i + 2 * epsilon + c, j), ?_, ?_⟩
    · exact hshift x y epsilon i j hxy hij
    · unfold natPairLInfDistance
      simp
      omega
  · rintro ⟨i, j⟩ hij
    refine ⟨(i + 2 * epsilon + c, j), ?_, ?_⟩
    · exact hshift y x epsilon i j hyx hij
    · unfold natPairLInfDistance
      simp
      omega

end Kolmogorov
