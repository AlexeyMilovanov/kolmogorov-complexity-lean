import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.HereditaryLift
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.HereditaryFamily
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LchLemma
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PropMinHereditary

/-!
# Public hereditary-theorem assembly

The constructive pieces of the source's `G → L → M → M₁ → F` argument live in
`HereditaryLift`, `LchLemma`, and `HereditaryFamily`.  This worker contains only
the unchanged public endpoint while the remaining quantitative assembly is
open.

In particular, we deliberately do not introduce abstract plain-to-total
upgrades or unconditional `A₁ → M₁` bounds here.  Such statements are false
without the partition, descent, membership, and intersection-size hypotheses
that constitute the proof of the theorem.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- Strength budget obtained by transporting a strong description along a
total equivalence, first back to the original datum and then forward through
the canonical image of its model. -/
def hereditaryStrongTransportStrength
    (c epsilon strength : Nat) : Nat :=
  let first := epsilon + strength + logSlack c (epsilon + strength)
  first + (epsilon + c) + logSlack c (first + epsilon + c)

/-- Directed strong-profile transport needed in the hereditary assembly.  A
total equivalence maps the witnessing finite set to its canonical image.  Its
ordinary complexity grows by `2 * epsilon + O(1)`; its strength is the exact
two-composition budget recorded by `hereditaryStrongTransportStrength`.

The reverse total program is essential: it first maps the new datum `y` back
to `x`, after which the original strong program produces the old model code.
The forward total program then canonically maps that model to one containing
`y`. -/
lemma strong_model_of_totalEquivalentWithin
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ x y epsilon strength S (hS : S.Nonempty),
      x ∈ S →
      TotalEquivalentWithin T x y epsilon →
      IsStrongSetModel T x S hS strength →
      ∃ B, ∃ (hB : B.Nonempty),
        y ∈ B ∧
        IsStrongSetModel T y B hB
          (hereditaryStrongTransportStrength c epsilon strength) ∧
        plainSetComplexity V B hB ≤
          plainSetComplexity V S hS + (2 * epsilon + c : ENat) ∧
        finiteSetLogCard B ≤ finiteSetLogCard S := by
  obtain ⟨cPlain, hPlain⟩ :=
    plainK_canonicalImageCode_le T V hT.1 hV
  obtain ⟨cImage, hImage⟩ :=
    hT.2 (totalProgramImageCodeFromSetCode T)
      (totalProgramImageCodeFromSetCode_partrec T hT.1)
  obtain ⟨cTrans, hTrans⟩ :=
    TotalReducesWithin.trans_logSlack T hT
  let c := cPlain + cImage + cTrans
  refine ⟨c, ?_⟩
  intro x y epsilon strength S hS hxS hequiv hStrong
  obtain ⟨hxy, hyx⟩ :=
    (totalEquivalentWithin_iff T x y epsilon).mp hequiv
  obtain ⟨p, hpTotal, hpLength, hpXY⟩ :=
    (totalReducesWithin_iff T x y epsilon).mp hxy
  obtain ⟨ys, hB, hCode, hForward, _hBackward, hCard⟩ :=
    exists_totalProgramCanonicalImage_from_code hpTotal S hS
  let B := ys.toFinset
  have hyB : y ∈ B := by
    obtain ⟨y', hy', hpXY'⟩ := hForward x hxS
    have hyy' : y = y' := Part.mem_unique hpXY hpXY'
    simpa [B, hyy'] using hy'
  have hBPlain : plainSetComplexity V B hB ≤
      plainSetComplexity V S hS + (2 * epsilon + c : ENat) := by
    have hSne : plainK V (codedUniformOn S hS).code ≠ ⊤ :=
      condK_ne_top_of_optimal V hV (codedUniformOn S hS).code []
    obtain ⟨a, haS⟩ := ENat.ne_top_iff_exists.mp hSne
    unfold plainSetComplexity
    rw [← haS]
    refine (hPlain hCode (le_of_eq haS.symm)).trans ?_
    exact_mod_cast (show a + 2 * programLength p + cPlain ≤ a + (2 * epsilon + c) by
      dsimp [c]; omega)
  have hSB : TotalReducesWithin T (codedUniformOn S hS).code
      (codedUniformOn B hB).code (epsilon + c) := by
    unfold TotalReducesWithin
    calc
      totalCondK T (codedUniformOn B hB).code
          (codedUniformOn S hS).code
          ≤ totalCondK (totalProgramImageCodeFromSetCode T)
              (codedUniformOn B hB).code
              (codedUniformOn S hS).code + (cImage : ENat) :=
            hImage _ _
      _ ≤ (programLength p : ENat) + (cImage : ENat) := by
            gcongr
            exact totalCondK_le_programLength hpTotal.imageSetCode hCode
      _ ≤ ((epsilon + c : Nat) : ENat) := by
            exact_mod_cast (show programLength p + cImage ≤ epsilon + c by
              dsimp [c]
              omega)
  let first := epsilon + strength + logSlack c (epsilon + strength)
  have hFirst : TotalReducesWithin T y (codedUniformOn S hS).code first := by
    refine (hTrans hyx hStrong).mono ?_
    dsimp [first, c]
    gcongr
    exact logSlack_mono_left (by omega) (epsilon + strength)
  have hBStrong : IsStrongSetModel T y B hB
      (hereditaryStrongTransportStrength c epsilon strength) := by
    have hComposed := hTrans hFirst hSB
    refine hComposed.mono ?_
    unfold hereditaryStrongTransportStrength
    dsimp only
    gcongr
    have hcTrans : cTrans ≤ c := by
      dsimp [c]
      omega
    simpa [first, Nat.add_assoc] using
      logSlack_mono_left hcTrans (first + (epsilon + c))
  exact ⟨B, hB, hyB, hBStrong, hBPlain, finiteSetLogCard_mono hCard⟩


lemma inStrongDescriptionProfile_of_totalEquivalentWithin
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ x y epsilon strength i j,
      TotalEquivalentWithin T x y epsilon →
      InStrongDescriptionProfile V T x strength i j →
      InStrongDescriptionProfile V T y
        (hereditaryStrongTransportStrength c epsilon strength)
        (i + 2 * epsilon + c) j := by
  obtain ⟨cPlain, hPlain⟩ :=
    plainK_canonicalImageCode_le T V hT.1 hV
  obtain ⟨cImage, hImage⟩ :=
    hT.2 (totalProgramImageCodeFromSetCode T)
      (totalProgramImageCodeFromSetCode_partrec T hT.1)
  obtain ⟨cTrans, hTrans⟩ :=
    TotalReducesWithin.trans_logSlack T hT
  let c := cPlain + cImage + cTrans
  refine ⟨c, ?_⟩
  intro x y epsilon strength i j hequiv hProfile
  obtain ⟨hxy, hyx⟩ :=
    (totalEquivalentWithin_iff T x y epsilon).mp hequiv
  obtain ⟨p, hpTotal, hpLength, hpXY⟩ :=
    (totalReducesWithin_iff T x y epsilon).mp hxy
  obtain ⟨S, hS, hDesc⟩ := hProfile
  obtain ⟨ys, hB, hCode, hForward, _hBackward, hCard⟩ :=
    exists_totalProgramCanonicalImage_from_code hpTotal S hS
  let B := ys.toFinset
  have hyB : y ∈ B := by
    obtain ⟨y', hy', hpXY'⟩ := hForward x hDesc.1.1
    have hyy' : y = y' := Part.mem_unique hpXY hpXY'
    simpa [B, hyy'] using hy'
  have hBPlain : plainSetComplexity V B hB ≤
      ((i + 2 * epsilon + c : Nat) : ENat) := by
    unfold plainSetComplexity
    refine (hPlain hCode hDesc.1.2.1).trans ?_
    exact_mod_cast (show
      i + 2 * programLength p + cPlain ≤
        i + 2 * epsilon + c by
      dsimp [c]
      omega)
  have hSB : TotalReducesWithin T (codedUniformOn S hS).code
      (codedUniformOn B hB).code (epsilon + c) := by
    unfold TotalReducesWithin
    calc
      totalCondK T (codedUniformOn B hB).code
          (codedUniformOn S hS).code
          ≤ totalCondK (totalProgramImageCodeFromSetCode T)
              (codedUniformOn B hB).code
              (codedUniformOn S hS).code + (cImage : ENat) :=
            hImage _ _
      _ ≤ (programLength p : ENat) + (cImage : ENat) := by
            gcongr
            exact totalCondK_le_programLength hpTotal.imageSetCode hCode
      _ ≤ ((epsilon + c : Nat) : ENat) := by
            exact_mod_cast (show programLength p + cImage ≤ epsilon + c by
              dsimp [c]
              omega)
  let first := epsilon + strength + logSlack c (epsilon + strength)
  have hFirst : TotalReducesWithin T y (codedUniformOn S hS).code first := by
    refine (hTrans hyx hDesc.2).mono ?_
    dsimp [first, c]
    gcongr
    exact logSlack_mono_left (by omega) (epsilon + strength)
  have hBStrong : IsStrongSetModel T y B hB
      (hereditaryStrongTransportStrength c epsilon strength) := by
    have hComposed := hTrans hFirst hSB
    refine hComposed.mono ?_
    unfold hereditaryStrongTransportStrength
    dsimp only
    gcongr
    have hcTrans : cTrans ≤ c := by
      dsimp [c]
      omega
    simpa [first, Nat.add_assoc] using
      logSlack_mono_left hcTrans (first + (epsilon + c))
  exact ⟨B, hB, ⟨⟨hyB, hBPlain, hCard.trans hDesc.1.2.2⟩,
    hBStrong⟩⟩

/-- Normality is stable under separately controlled changes of the ordinary
and strong profiles.  This is the metric triangle step needed after replacing
`A` by its total-equivalent partition member `A₁`. -/
lemma normality_transport_of_profile_neighborhoods
    {V T : Map} {x y : BitString} {epsilon epsilon' delta dPlain dStrong : Nat}
    (hPlain : ProfileSetsWithinNeighborhood
      (plainDescriptionProfileSet V y)
      (plainDescriptionProfileSet V x) dPlain)
    (hStrong : ProfileSetsWithinNeighborhood
      (strongDescriptionProfileSet V T x epsilon)
      (strongDescriptionProfileSet V T y epsilon') dStrong)
    (hNormal : IsNormalString V T x epsilon delta) :
    IsNormalString V T y epsilon' (dPlain + delta + dStrong) := by
  unfold IsNormalString at hNormal ⊢
  simpa [Nat.add_assoc] using hPlain.trans (hNormal.trans hStrong)

/-- To prove normality it is enough to approximate every ordinary profile
point by a strong one; the reverse approximation is automatic because the
strong profile is a subset of the ordinary profile. -/
lemma normality_of_plain_to_strong_nearby
    {V T : Map} {x : BitString} {strength delta : Nat}
    (h : ∀ i j, InPlainDescriptionProfile V x i j →
      ∃ i' j', InStrongDescriptionProfile V T x strength i' j' ∧
        natPairLInfDistance (i, j) (i', j') ≤ delta) :
    IsNormalString V T x strength delta := by
  constructor
  · rintro ⟨i, j⟩ hij
    obtain ⟨i', j', hStrong, hdist⟩ := h i j hij
    exact ⟨(i', j'), hStrong, hdist⟩
  · intro q hq
    exact ⟨q, strongDescriptionProfileSet_subset_plain V T x _ hq,
      by simp [natPairLInfDistance]⟩

/-- Normality transported along total equivalence, with no assumed
strong-profile neighborhood.  The nontrivial direction sends a nearby strong
description of `x` through the canonical-image construction above.  The other
direction is immediate from `P_y(strength) ⊆ P_y`. -/
lemma normality_of_totalEquivalentWithin
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ cPlain cStrong : Nat, ∀ x y epsilon strength delta,
      TotalEquivalentWithin T x y epsilon →
      IsNormalString V T x strength delta →
      IsNormalString V T y
        (hereditaryStrongTransportStrength cStrong epsilon strength)
        ((2 * epsilon + cPlain) + delta +
          (2 * epsilon + cStrong)) := by
  obtain ⟨cPlain, hPlain⟩ :=
    totalEquivalentWithin_plainProfiles V T hV hT
  obtain ⟨cStrong, hStrong⟩ :=
    inStrongDescriptionProfile_of_totalEquivalentWithin V T hV hT
  refine ⟨cPlain, cStrong, ?_⟩
  intro x y epsilon strength delta hequiv hNormal
  unfold IsNormalString at hNormal ⊢
  have hPlainXY := hPlain x y epsilon hequiv
  constructor
  · intro q hq
    obtain ⟨r, hrPlain, hqr⟩ := hPlainXY.2 q hq
    obtain ⟨s, hsStrong, hrs⟩ := hNormal.1 r hrPlain
    let s' : Nat × Nat :=
      (s.1 + 2 * epsilon + cStrong, s.2)
    have hs'Strong : s' ∈ strongDescriptionProfileSet V T y
        (hereditaryStrongTransportStrength cStrong epsilon strength) := by
      exact hStrong x y epsilon strength s.1 s.2 hequiv hsStrong
    have hss' : natPairLInfDistance s s' ≤
        2 * epsilon + cStrong := by
      dsimp [s']
      unfold natPairLInfDistance
      omega
    refine ⟨s', hs'Strong, ?_⟩
    calc
      natPairLInfDistance q s'
          ≤ natPairLInfDistance q r + natPairLInfDistance r s' :=
            natPairLInfDistance_triangle q r s'
      _ ≤ natPairLInfDistance q r +
          (natPairLInfDistance r s + natPairLInfDistance s s') := by
            gcongr
            exact natPairLInfDistance_triangle r s s'
      _ ≤ (2 * epsilon + cPlain) +
          (delta + (2 * epsilon + cStrong)) := by omega
      _ = (2 * epsilon + cPlain) + delta +
          (2 * epsilon + cStrong) := by omega
  · intro q hq
    exact ⟨q, strongDescriptionProfileSet_subset_plain V T y _ hq,
      by simp [natPairLInfDistance]⟩

/-- Canonical code of the intersection of the finite sets decoded from two
canonical model codes. -/
noncomputable def hereditaryIntersectionCode
    (input : BitString × BitString) : BitString :=
  canonicalImageCodeOfList
    (partitionIntersectionPointList input.1 input.2)

theorem hereditaryIntersectionCode_computable :
    Computable hereditaryIntersectionCode := by
  exact (canonicalImageCodeOfList_primrec.comp
    partitionIntersectionPointList_primrec).to_comp

theorem hereditaryIntersectionCode_eq
    (A M : Finset BitString) (hA : A.Nonempty) (hM : M.Nonempty)
    (hI : (A ∩ M).Nonempty) :
    hereditaryIntersectionCode
      ((codedUniformOn A hA).code, (codedUniformOn M hM).code) =
        (codedUniformOn (A ∩ M) hI).code := by
  unfold hereditaryIntersectionCode
  have hset := partitionIntersectionPointList_toFinset A M hA hM
  simpa [hset] using canonicalImageCodeOfList_eq_codedUniformOn
    (partitionIntersectionPointList
      (codedUniformOn A hA).code
      (codedUniformOn M hM).code)
    (hset.symm ▸ hI)

/-- Run a conditional program for `M` from `A`, then canonically intersect its
output with the decoded condition `A`. -/
noncomputable def hereditaryIntersectionDecompressor (V : Map) : Map :=
  fun input => (V input).map fun Mcode =>
    hereditaryIntersectionCode (input.2, Mcode)

theorem hereditaryIntersectionDecompressor_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (hereditaryIntersectionDecompressor V) := by
  unfold hereditaryIntersectionDecompressor
  exact Partrec.map hV
    (hereditaryIntersectionCode_computable.comp
      ((Computable.snd.comp Computable.fst).pair Computable.snd))

theorem hereditaryIntersectionDecompressor_produces
    (V : Map) (p Acode Mcode : BitString)
    (h : produces V p Acode Mcode) :
    produces (hereditaryIntersectionDecompressor V) p Acode
      (hereditaryIntersectionCode (Acode, Mcode)) := by
  unfold produces hereditaryIntersectionDecompressor
  exact (Part.mem_map_iff _).2 ⟨Mcode, h, rfl⟩

/-- The ordinary conditional chain used in the hereditary intersection step.
The first and last links are total programs for `T`; optimality of `V` first
forgets totality and changes machines, after which ordinary two-stage
transitivity composes `A₁ → A → M → M₁`. -/
lemma hereditary_partition_condK_chain
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ (A1code Acode Mcode M1code : BitString) (p d : Nat),
      totalCondK T Acode A1code ≤ (p : ENat) →
      condK V Mcode Acode ≤ (d : ENat) →
      totalCondK T M1code Mcode ≤ (p : ENat) →
      condK V M1code A1code ≤ (c * (p + d) + c : ENat) := by
  obtain ⟨cSim, hSim⟩ := hV.2 T hT.1
  obtain ⟨cTrans, hTrans⟩ := condK_trans_nat V hV
  let c := 5 * (cSim + cTrans + 1)
  refine ⟨c, ?_⟩
  intro A1code Acode Mcode M1code p d hA hM hM1
  have hAPlain :
      condK V Acode A1code ≤ ((p + cSim : Nat) : ENat) := by
    calc
      condK V Acode A1code
          ≤ condK T Acode A1code + (cSim : ENat) := hSim _ _
      _ ≤ totalCondK T Acode A1code + (cSim : ENat) := by
        gcongr
        exact condK_le_totalCondK T Acode A1code
      _ ≤ (p : ENat) + (cSim : ENat) := by gcongr
      _ = ((p + cSim : Nat) : ENat) := by norm_cast
  have hM1Plain :
      condK V M1code Mcode ≤ ((p + cSim : Nat) : ENat) := by
    calc
      condK V M1code Mcode
          ≤ condK T M1code Mcode + (cSim : ENat) := hSim _ _
      _ ≤ totalCondK T M1code Mcode + (cSim : ENat) := by
        gcongr
        exact condK_le_totalCondK T M1code Mcode
      _ ≤ (p : ENat) + (cSim : ENat) := by gcongr
      _ = ((p + cSim : Nat) : ENat) := by norm_cast
  have hFirst :=
    hTrans A1code Acode Mcode (p + cSim) d hAPlain hM
  have hFinal :=
    hTrans A1code Mcode M1code
      (2 * (p + cSim) + d + cTrans) (p + cSim) hFirst hM1Plain
  refine hFinal.trans ?_
  exact_mod_cast (show
    2 * (2 * (p + cSim) + d + cTrans) + (p + cSim) + cTrans ≤
      c * (p + d) + c by
    dsimp [c]
    nlinarith [Nat.zero_le p, Nat.zero_le d])

/-- A conditional description of `M` from `A` yields a plain description of
`A ∩ M`; the only nonconstant framing cost is the self-delimiting header for
the first-stage program describing `A`. -/
lemma plainSetComplexity_inter_le_of_condK
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ A (hA : A.Nonempty) M (hM : M.Nonempty)
        (hI : (A ∩ M).Nonempty) (a d : Nat),
      plainSetComplexity V A hA = (a : ENat) →
      condK V (codedUniformOn M hM).code
        (codedUniformOn A hA).code ≤ (d : ENat) →
      plainSetComplexity V (A ∩ M) hI ≤
        (a + d + 2 * (Nat.bits a).length + c : Nat) := by
  obtain ⟨cSim, hSim⟩ := hV.2 (hereditaryIntersectionDecompressor V)
    (hereditaryIntersectionDecompressor_partrec V hV.1)
  obtain ⟨cTwo, hTwo⟩ := plainK_two_stage V hV
  refine ⟨cSim + cTwo, ?_⟩
  intro A hA M hM hI a d hAValue hMA
  have hRaw :
      condK (hereditaryIntersectionDecompressor V)
        (hereditaryIntersectionCode
          ((codedUniformOn A hA).code, (codedUniformOn M hM).code))
        (codedUniformOn A hA).code ≤
          condK V (codedUniformOn M hM).code
            (codedUniformOn A hA).code := by
    apply sInf_le_sInf
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, hereditaryIntersectionDecompressor_produces V p
      (codedUniformOn A hA).code (codedUniformOn M hM).code hp, rfl⟩
  have hConditional :
      condK V
        (hereditaryIntersectionCode
          ((codedUniformOn A hA).code, (codedUniformOn M hM).code))
        (codedUniformOn A hA).code ≤ ((d + cSim : Nat) : ENat) := by
    calc
      condK V
          (hereditaryIntersectionCode
            ((codedUniformOn A hA).code, (codedUniformOn M hM).code))
          (codedUniformOn A hA).code
          ≤ condK (hereditaryIntersectionDecompressor V)
              (hereditaryIntersectionCode
                ((codedUniformOn A hA).code, (codedUniformOn M hM).code))
              (codedUniformOn A hA).code + (cSim : ENat) := hSim _ _
      _ ≤ (d : ENat) + (cSim : ENat) :=
        add_le_add (hRaw.trans hMA) le_rfl
      _ = ((d + cSim : Nat) : ENat) := by norm_cast
  have hPlain := hTwo
    (hereditaryIntersectionCode
      ((codedUniformOn A hA).code, (codedUniformOn M hM).code))
    (codedUniformOn A hA).code a (d + cSim) (le_of_eq hAValue) hConditional
  rw [hereditaryIntersectionCode_eq A M hA hM hI] at hPlain
  exact hPlain.trans (by
    exact_mod_cast (show
      a + (d + cSim) + 2 * (Nat.bits a).length + cTwo ≤
        a + d + 2 * (Nat.bits a).length + (cSim + cTwo) by omega))

/-- Sufficiency lower bound for an arbitrary competing model containing `x`.
If `I` costs at most `delta` more than `A`, its log-cardinality cannot be much
smaller.  This general form is needed because the hereditary proof compares
`A` with `A₁ ∩ M₁`, which need not be presented syntactically as `A ∩ M`. -/
lemma hereditary_sufficiency_model_lower_bound
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x A (hA : A.Nonempty) I (hI : I.Nonempty)
        (epsilon delta N aA aI : Nat),
      IsSufficientStatistic V x A hA epsilon →
      x ∈ I →
      plainSetComplexity V A hA = (aA : ENat) →
      plainSetComplexity V I hI = (aI : ENat) →
      aI ≤ aA + delta →
      aA + delta ≤ N →
      finiteSetLogCard A ≤
        finiteSetLogCard I + epsilon + delta + logSlack c N := by
  obtain ⟨cMem, hMem⟩ := plainK_mem_le_of_plainSetComplexity_le V hV
  refine ⟨cMem + 2, ?_⟩
  intro x A hA I hI epsilon delta N aA aI hSufficient hxI hAValue hIValue
    hIA hBudget
  have hxBound := hMem I hI x aI hxI (le_of_eq hIValue)
  have hTwoPart :
      aA + finiteSetLogCard A ≤
        aI + finiteSetLogCard I +
          2 * (Nat.bits aI).length + cMem + epsilon := by
    have hENat :
        ((aA + finiteSetLogCard A : Nat) : ENat) ≤
          ((aI + finiteSetLogCard I +
            2 * (Nat.bits aI).length + cMem + epsilon : Nat) : ENat) := by
      calc
        ((aA + finiteSetLogCard A : Nat) : ENat)
            = plainSetComplexity V A hA +
                (finiteSetLogCard A : ENat) := by
              rw [hAValue]
              norm_cast
        _ ≤ plainK V x + (epsilon : ENat) := hSufficient.2
        _ ≤ ((aI + finiteSetLogCard I +
              2 * (Nat.bits aI).length + cMem : Nat) : ENat) +
              (epsilon : ENat) := by
            gcongr
        _ = ((aI + finiteSetLogCard I +
              2 * (Nat.bits aI).length + cMem + epsilon : Nat) : ENat) := by
            norm_cast
    exact_mod_cast hENat
  have haIN : aI ≤ N := hIA.trans hBudget
  have hBits : (Nat.bits aI).length ≤ (Nat.bits N).length :=
    length_natBits_mono haIN
  have hLog : 2 * (Nat.bits aI).length + cMem ≤
      logSlack (cMem + 2) N := by
    unfold logSlack
    nlinarith [Nat.zero_le (cMem * (Nat.bits N).length)]
  omega

/-- Quantitative intersection-shaped corollary of
`hereditary_sufficiency_model_lower_bound`. -/
lemma hereditary_sufficiency_intersection_lower_bound
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x A (hA : A.Nonempty) M
        (hI : (A ∩ M).Nonempty) (epsilon delta N aA aI : Nat),
      IsSufficientStatistic V x A hA epsilon →
      x ∈ A ∩ M →
      plainSetComplexity V A hA = (aA : ENat) →
      plainSetComplexity V (A ∩ M) hI = (aI : ENat) →
      aI ≤ aA + delta →
      aA + delta ≤ N →
      finiteSetLogCard A ≤
        finiteSetLogCard (A ∩ M) + epsilon + delta + logSlack c N := by
  obtain ⟨cMem, hMem⟩ := plainK_mem_le_of_plainSetComplexity_le V hV
  refine ⟨cMem + 2, ?_⟩
  intro x A hA M hI epsilon delta N aA aI hSufficient hxI hAValue hIValue
    hIA hBudget
  have hxBound := hMem (A ∩ M) hI x aI hxI (le_of_eq hIValue)
  have hTwoPart :
      aA + finiteSetLogCard A ≤
        aI + finiteSetLogCard (A ∩ M) +
          2 * (Nat.bits aI).length + cMem + epsilon := by
    have hENat :
        ((aA + finiteSetLogCard A : Nat) : ENat) ≤
          ((aI + finiteSetLogCard (A ∩ M) +
            2 * (Nat.bits aI).length + cMem + epsilon : Nat) : ENat) := by
      calc
        ((aA + finiteSetLogCard A : Nat) : ENat)
            = plainSetComplexity V A hA +
                (finiteSetLogCard A : ENat) := by
              rw [hAValue]
              norm_cast
        _ ≤ plainK V x + (epsilon : ENat) := hSufficient.2
        _ ≤ ((aI + finiteSetLogCard (A ∩ M) +
              2 * (Nat.bits aI).length + cMem : Nat) : ENat) +
              (epsilon : ENat) := by
            gcongr
        _ = ((aI + finiteSetLogCard (A ∩ M) +
              2 * (Nat.bits aI).length + cMem + epsilon : Nat) : ENat) := by
            norm_cast
    exact_mod_cast hENat
  have haIN : aI ≤ N := hIA.trans hBudget
  have hBits : (Nat.bits aI).length ≤ (Nat.bits N).length :=
    length_natBits_mono haIN
  have hLog : 2 * (Nat.bits aI).length + cMem ≤
      logSlack (cMem + 2) N := by
    unfold logSlack
    nlinarith [Nat.zero_le (cMem * (Nat.bits N).length)]
  omega

/-- The partition selector in `HereditaryFamily` is usually consumed after a
separate argument has bounded the logarithmic loss in the intersection.  This
corollary exposes that exact form and discharges only the truncated-subtraction
arithmetic. -/
lemma partition_member_totalCondK_of_logCard_gap
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ P M (hM : M.Nonempty) A (hA : A.Nonempty)
        (p N gap : Nat),
      IsPartition P →
      M ∈ P →
      (A ∩ M).Nonempty →
      partitionComplexity V P ≤ (p : ENat) →
      finiteSetLogCard A ≤ N →
      finiteSetLogCard A ≤ finiteSetLogCard (A ∩ M) + gap →
      totalCondK T (codedUniformOn M hM).code
          (codedUniformOn A hA).code ≤
        (c * p + gap + logSlack c N : ENat) := by
  obtain ⟨c, hc⟩ :=
    partition_member_totalCondK_of_intersection V T hV hT
  refine ⟨c, ?_⟩
  intro P M hM A hA p N gap hPart hMP hInter hP hN hGap
  refine (hc P M hM A hA p N hPart hMP hInter hP hN).trans ?_
  exact_mod_cast (show
    c * p + (finiteSetLogCard A - finiteSetLogCard (A ∩ M)) +
        logSlack c N ≤
      c * p + gap + logSlack c N by omega)

/-- Final assembly step of `thm:hereditary` (the source's `M₁ → F → (i,j)`
closure via Proposition `prop:description-shift-1`).

If `F` is a `strength`-strong model for the datum `y` whose ordinary plain
complexity is at most `i` and whose complexity-plus-log-cardinality is at most
`i + j`, then the strong description profile of `y` contains a point within
`logSlack c (log #F)` of `(i, j)`, at strength `strength + logSlack c (log #F)`.
The proof shrinks `F` to log-cardinality `j` with `strong_description_shift`,
which raises the plain complexity back to `i` by exactly the freed bits; the
`log #F` slack is the description-shift address cost, absorbed downstream into
`O(log n)` because the consumed strong family has `log #F ≤ O(n)`.

This is exactly the step the source invokes as "From Proposition
`prop:description-shift-1` it follows that the strong profile of `A₁` includes
the point `(K(𝒢), log #𝒢)`"; it is the honest final closure consumed by
`lemma_hereditary_strong_approximation` once the strong family model
`F` (with complexity `≤ i + O(...)` and complexity-plus-log-cardinality
`≤ i + j + O(...)`) has been constructed through the `G → L → M → M₁ → F`
chain. -/
lemma inStrongDescriptionProfile_of_strong_model_params
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ (y : BitString) (F : Finset BitString) (hyF : y ∈ F)
        (strength i j : Nat),
      IsStrongSetModel T y F ⟨y, hyF⟩ strength →
      plainSetComplexity V F ⟨y, hyF⟩ ≤ (i : ENat) →
      plainSetComplexity V F ⟨y, hyF⟩ + (finiteSetLogCard F : ENat) ≤
        ((i + j : Nat) : ENat) →
      ∃ i' j',
        InStrongDescriptionProfile V T y
        (strength + logSlack c (min i (finiteSetLogCard F))) i' j' ∧
        natPairLInfDistance (i, j) (i', j') ≤
          logSlack c (min i (finiteSetLogCard F)) := by
  obtain ⟨cShift, hShift⟩ := strong_description_shift V hV T hT
  refine ⟨cShift + 1, ?_⟩
  intro y F hyF strength i j hStrong hComp hSum
  set L := finiteSetLogCard F with hL
  have hFne : plainSetComplexity V F ⟨y, hyF⟩ ≠ ⊤ :=
    condK_ne_top_of_optimal V hV (codedUniformOn F ⟨y, hyF⟩).code []
  set a := (plainSetComplexity V F ⟨y, hyF⟩).toNat with ha
  have haF : plainSetComplexity V F ⟨y, hyF⟩ = (a : ENat) :=
    (ENat.coe_toNat hFne).symm
  set slack := logSlack (cShift + 1) (min i L) with hslackdef
  have hslack_ge : cShift + 1 ≤ slack := by
    rw [hslackdef]; unfold logSlack; omega
  by_cases hLj : L ≤ j
  · -- Case A: `F` already has size budget `j`; distance `0`.
    refine ⟨i, j, ⟨F, ⟨y, hyF⟩,
      ⟨⟨hyF, hComp, (finiteSetLogCard_le_iff F j).mp (by rw [← hL]; exact hLj)⟩,
        hStrong.mono (Nat.le_add_right strength slack)⟩⟩, ?_⟩
    simp [natPairLInfDistance]
  · -- Case B: `j < L`, so `#F ≥ 2` and the shift precondition holds.
    have hjL : j < L := Nat.lt_of_not_le hLj
    have hLpos : 1 ≤ L := by omega
    have hcard2 : 1 < F.card := by
      rcases Nat.lt_or_ge 1 F.card with h | h
      · exact h
      · have h1 : F.card ≤ 2 ^ 0 := by simpa using h
        have hz : finiteSetLogCard F ≤ 0 := (finiteSetLogCard_le_iff F 0).mpr h1
        rw [← hL] at hz; omega
    have hpred : 2 ^ (L - 1) < F.card := by
      rw [hL]; exact finiteSetLogCard_pred_lt F hcard2
    set m := max j 1 with hm
    have hjm : j ≤ m := by rw [hm]; exact le_max_left j 1
    have h1m : 1 ≤ m := by rw [hm]; exact le_max_right j 1
    have hmL : m ≤ L := by rw [hm]; exact max_le hjL.le hLpos
    have hm_le : m ≤ j + 1 := by
      rw [hm]; exact max_le (Nat.le_succ j) (Nat.le_add_left 1 j)
    set s := L - m with hs
    have hsL : s ≤ L := by rw [hs]; exact Nat.sub_le L m
    have hsL1 : s ≤ L - 1 := by omega
    have haSum : a + L ≤ i + j := by
      have hcast : ((a + L : Nat) : ENat) ≤ ((i + j : Nat) : ENat) := by
        rw [Nat.cast_add, ← haF]; exact hSum
      exact_mod_cast hcast
    have h1 : a + s ≤ i := by omega
    have h2s : 2 ^ s ≤ F.card :=
      le_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hsL1) hpred)
    obtain ⟨S', hyS', hS'strong, hS'card, hS'comp⟩ :=
      hShift y F hyF strength hStrong s h2s
    have hFcard : F.card ≤ 2 ^ L := by rw [hL]; exact finiteSetLogCard_spec F
    have hcardLe : S'.card ≤ 2 ^ m := by
      have hchain : S'.card * 2 ^ s ≤ 2 ^ m * 2 ^ s := by
        calc S'.card * 2 ^ s ≤ F.card := hS'card
          _ ≤ 2 ^ L := hFcard
          _ = 2 ^ (m + s) := by congr 1; omega
          _ = 2 ^ m * 2 ^ s := by rw [pow_add]
      exact Nat.le_of_mul_le_mul_right hchain (Nat.two_pow_pos s)
    have hlogs : logSlack cShift s ≤ slack := by
      rw [hslackdef]
      have hsmin : s ≤ min i L := by omega
      exact (logSlack_mono_right cShift hsmin).trans
        (logSlack_mono_left (Nat.le_succ cShift) (min i L))
    refine ⟨i + slack, j + slack,
      ⟨S', ⟨y, hyS'⟩, ⟨⟨hyS', ?_, ?_⟩, ?_⟩⟩, ?_⟩
    · -- plain complexity of `S'` is at most `i + slack`.
      refine hS'comp.trans ?_
      rw [haF]
      have hnat : a + s + logSlack cShift s ≤ i + slack := by omega
      exact_mod_cast hnat
    · -- size budget `j + slack`.
      exact hcardLe.trans (Nat.pow_le_pow_right (by decide) (by omega))
    · -- strength budget `strength + slack`.
      exact hS'strong.mono (Nat.add_le_add_left hlogs strength)
    · -- distance.
      simp only [natPairLInfDistance]
      omega

private lemma hereditary_shift_slack_absorb (cOut cShift : Nat) :
    ∃ cNormal : Nat, ∀ delta epsilon n r : Nat,
      r ≤ n + delta + 2 * hereditarySlack cOut delta epsilon n →
      hereditarySlack cOut delta epsilon n + logSlack cShift r ≤
        hereditarySlack cNormal delta epsilon n := by
  -- `hereditarySlack c` is LINEAR in `c`, and `logSlack cShift r` is LOGARITHMIC
  -- in `r`.  Bounding `|bits r|` by the *sizes* of the summands of `r` keeps the
  -- whole shift cost inside the √n-scale slack (unlike the linear bound
  -- `|bits r| ≤ r`, which would introduce an unabsorbable `cShift * n` term).
  -- The `2 *` on the shift-cost budget `r` covers the `O(log n)` gap between the
  -- interesting condition `i + S < C(A)` and `C(A) ≤ n + delta + O(log n)`.
  refine ⟨(2 * cShift + 1) * cOut + 4 * cShift + 4, ?_⟩
  intro delta epsilon n r hr
  have hbr : (Nat.bits r).length ≤
      (Nat.bits n).length + delta + 2 * hereditarySlack cOut delta epsilon n + 2 := by
    have h1 : (Nat.bits r).length
        ≤ (Nat.bits (n + delta + 2 * hereditarySlack cOut delta epsilon n)).length :=
      length_natBits_mono hr
    have h2 : (Nat.bits (n + delta + 2 * hereditarySlack cOut delta epsilon n)).length ≤
        (Nat.bits (n + delta)).length
          + (Nat.bits (2 * hereditarySlack cOut delta epsilon n)).length + 1 :=
      length_natBits_add_le (n + delta) (2 * hereditarySlack cOut delta epsilon n)
    have h3 : (Nat.bits (n + delta)).length ≤
        (Nat.bits n).length + (Nat.bits delta).length + 1 :=
      length_natBits_add_le n delta
    have h4 : (Nat.bits delta).length ≤ delta := length_natBits_le_self delta
    have h5 : (Nat.bits (2 * hereditarySlack cOut delta epsilon n)).length
        ≤ 2 * hereditarySlack cOut delta epsilon n := length_natBits_le_self _
    omega
  have hlog : logSlack cShift r ≤
      cShift * ((Nat.bits n).length + delta + 2 * hereditarySlack cOut delta epsilon n + 2)
        + cShift := by
    unfold logSlack
    have := Nat.mul_le_mul_left cShift hbr
    omega
  have hbnP : (Nat.bits n).length ≤ (epsilon + (Nat.bits n).length) * Nat.sqrt n := by
    by_cases hn0 : n = 0
    · subst hn0; simp
    · have hsq : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr (Nat.zero_lt_of_ne_zero hn0)
      calc (Nat.bits n).length ≤ epsilon + (Nat.bits n).length := Nat.le_add_left _ _
        _ = (epsilon + (Nat.bits n).length) * 1 := (Nat.mul_one _).symm
        _ ≤ (epsilon + (Nat.bits n).length) * Nat.sqrt n := Nat.mul_le_mul_left _ hsq
  unfold hereditarySlack at hlog ⊢
  set bn := (Nat.bits n).length with hbndef
  set P := (epsilon + bn) * Nat.sqrt n with hPdef
  have hassoc : ∀ c : Nat, c * (epsilon + bn) * Nat.sqrt n = c * P := by
    intro c; rw [hPdef]; ring
  rw [hassoc cOut, hassoc ((2 * cShift + 1) * cOut + 4 * cShift + 4)] at *
  nlinarith [hbnP, hlog, Nat.zero_le delta, Nat.zero_le P, Nat.zero_le bn,
    Nat.zero_le cShift, Nat.zero_le cOut,
    Nat.mul_le_mul_left cShift hbnP, Nat.mul_le_mul_left (2 * cShift) hbnP]

private lemma hereditary_omega_chain
    (V T : Map) (hV : isOptimalConditional V) (_hT : IsOptimalTotalConditional T)
    (cLch : Nat) :
    ∃ cKappa cOut : Nat,
      ∀ x n A (hA : A.Nonempty) M (hM : M.Nonempty) delta
        (q : Nat.Partrec.Code) (_hq : IsCodeFor q V),
        x.length = n →
        IsMinimalModel V x A hA delta (logSlack cKappa n) →
        plainSetComplexity V M hM ≤ plainSetComplexity V A hA + (delta : ENat) →
        condK V (codedUniformOn M hM).code
          (omegaFixedCode q (plainK V (codedUniformOn M hM).code).toNat) ≤
            (cLch * Nat.sqrt n + logSlack cLch n : ENat) →
        condK V (codedUniformOn M hM).code (codedUniformOn A hA).code ≤
          (cOut * delta + cOut * Nat.sqrt n + logSlack cOut n : ENat) := by
  obtain ⟨cKappaMin, cMin, hMin⟩ := prop_min_hereditary V hV
  obtain ⟨cKappaBound, cBound, hBound⟩ :=
    minimalModel_plainSetComplexity_le V hV
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨cBridge, hBridge⟩ :=
    omegaFixedCode_bridge_linear V hV c hc 0
  obtain ⟨cBridgeLin, hBridgeLin⟩ :=
    logSlack_linear_bound cBridge (cBound + 3) cBound
  obtain ⟨cTrans, hTrans⟩ := condK_trans_nat V hV
  obtain ⟨cDrop, hDrop⟩ := condKLePlainK V hV
  let cKappa := cKappaMin + cKappaBound
  let cOut :=
    4 * cMin + 2 * cBridgeLin + cLch +
      3 * cTrans + 2 * cBound + cDrop + 10
  refine ⟨cKappa, cOut, ?_⟩
  intro x n A hA M hM delta q hq hn hMinimal hMA hLch
  have hMinForMin :
      IsMinimalModel V x A hA delta (logSlack cKappaMin n) :=
    IsMinimalModel.mono le_rfl
      (logSlack_mono_left (by dsimp [cKappa]; omega) n) hMinimal
  have hMinForBound :
      IsMinimalModel V x A hA delta (logSlack cKappaBound n) :=
    IsMinimalModel.mono le_rfl
      (logSlack_mono_left (by dsimp [cKappa]; omega) n) hMinimal
  have hABound := hBound x n A hA delta hn hMinForBound
  let codeA := (codedUniformOn A hA).code
  let codeM := (codedUniformOn M hM).code
  have hAFinite : plainK V codeA ≠ ⊤ := by
    change plainSetComplexity V A hA ≠ ⊤
    exact ne_top_of_le_ne_top
      (ENat.coe_ne_top (n + delta + logSlack cBound n)) hABound
  let a := (plainK V codeA).toNat
  have haValue : plainK V codeA = (a : ENat) :=
    (ENat.coe_toNat hAFinite).symm
  have haBound : a ≤ n + delta + logSlack cBound n := by
    have h : (a : ENat) ≤
        ((n + delta + logSlack cBound n : Nat) : ENat) := by
      rw [← haValue]
      exact hABound
    exact_mod_cast h
  have hMBound : plainK V codeM ≤
      ((n + 2 * delta + logSlack cBound n : Nat) : ENat) := by
    change plainSetComplexity V M hM ≤
      ((n + 2 * delta + logSlack cBound n : Nat) : ENat)
    calc
      plainSetComplexity V M hM
          ≤ plainSetComplexity V A hA + (delta : ENat) := hMA
      _ ≤ ((n + delta + logSlack cBound n : Nat) : ENat) +
            (delta : ENat) := by
              push_cast
              exact add_le_add hABound le_rfl
      _ = ((n + 2 * delta + logSlack cBound n : Nat) : ENat) := by
            push_cast
            ring
  have hMFinite : plainK V codeM ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENat.coe_ne_top (n + 2 * delta + logSlack cBound n)) hMBound
  let m := (plainK V codeM).toNat
  have hmValue : plainK V codeM = (m : ENat) :=
    (ENat.coe_toNat hMFinite).symm
  have hmGap : m ≤ a + delta := by
    have h : (m : ENat) ≤ (a : ENat) + (delta : ENat) := by
      rw [← hmValue, ← haValue]
      exact hMA
    exact_mod_cast h
  have hmBound : m ≤ n + 2 * delta + logSlack cBound n := by
    have h : (m : ENat) ≤
        ((n + 2 * delta + logSlack cBound n : Nat) : ENat) := by
      rw [← hmValue]
      exact hMBound
    exact_mod_cast h
  by_cases hDelta : delta < n
  · let visible := n + 2 * delta + logSlack cBound n
    have hVisibleLinear : visible ≤ (cBound + 3) * n + cBound := by
      dsimp [visible]
      unfold logSlack
      have hBits : (Nat.bits n).length ≤ n := length_natBits_le_self n
      nlinarith
    have hBridgeSlack : logSlack cBridge visible ≤
        logSlack cBridgeLin n :=
      (logSlack_mono_right cBridge hVisibleLinear).trans (hBridgeLin n)
    have haVisible : a ≤ visible := by
      dsimp [visible]
      omega
    have hmVisible : m ≤ visible := by
      simpa [visible] using hmBound
    have hOmegaRaw := hBridge visible m a
      (by simpa [logSlack] using hmVisible)
      (by simpa [logSlack] using haVisible)
    have hOmega :
        condK V (omegaFixedCode c m) (omegaFixedCode c a) ≤
          ((delta + logSlack cBridgeLin n : Nat) : ENat) := by
      calc
        condK V (omegaFixedCode c m) (omegaFixedCode c a)
            ≤ (((m - a) + logSlack cBridge visible : Nat) : ENat) := hOmegaRaw
        _ ≤ ((delta + logSlack cBridgeLin n : Nat) : ENat) := by
              exact_mod_cast (show m - a + logSlack cBridge visible ≤
                delta + logSlack cBridgeLin n by omega)
    have hMinCond :
        condK V (omegaFixedCode c a) codeA ≤
          ((cMin * delta + logSlack cMin n : Nat) : ENat) := by
      simpa [codeA, a] using
        hMin x n A hA delta c hc hn hMinForMin
    have hCodeSwap : omegaFixedCode q m = omegaFixedCode c m :=
      omegaFixedCode_eq_of_isCodeFor hq hc m
    have hLchFixed : condK V codeM (omegaFixedCode c m) ≤
        ((cLch * Nat.sqrt n + logSlack cLch n : Nat) : ENat) := by
      change condK V codeM (omegaFixedCode q m) ≤
        ((cLch * Nat.sqrt n + logSlack cLch n : Nat) : ENat) at hLch
      rw [hCodeSwap] at hLch
      exact hLch
    have hFirst := hTrans codeA (omegaFixedCode c a)
      (omegaFixedCode c m)
      (cMin * delta + logSlack cMin n)
      (delta + logSlack cBridgeLin n) hMinCond hOmega
    have hFinal := hTrans codeA (omegaFixedCode c m) codeM
      (2 * (cMin * delta + logSlack cMin n) +
        (delta + logSlack cBridgeLin n) + cTrans)
      (cLch * Nat.sqrt n + logSlack cLch n) hFirst hLchFixed
    calc
      condK V codeM codeA
          ≤ ((2 * (2 * (cMin * delta + logSlack cMin n) +
                (delta + logSlack cBridgeLin n) + cTrans) +
              (cLch * Nat.sqrt n + logSlack cLch n) + cTrans : Nat) : ENat) :=
            hFinal
      _ ≤ ((cOut * delta + cOut * Nat.sqrt n + logSlack cOut n : Nat) : ENat) := by
            apply Nat.cast_le.mpr
            dsimp [cOut]
            unfold logSlack
            nlinarith [Nat.zero_le (Nat.bits n).length, Nat.zero_le (Nat.sqrt n)]
  · have hLarge : n ≤ delta := Nat.le_of_not_gt hDelta
    calc
      condK V codeM codeA ≤ plainK V codeM + (cDrop : ENat) := hDrop _ _
      _ ≤ ((n + 2 * delta + logSlack cBound n : Nat) : ENat) +
            (cDrop : ENat) := by gcongr
      _ = ((n + 2 * delta + logSlack cBound n + cDrop : Nat) : ENat) := by
            push_cast
            ring
      _ ≤ ((cOut * delta + cOut * Nat.sqrt n + logSlack cOut n : Nat) : ENat) := by
            apply Nat.cast_le.mpr
            dsimp [cOut]
            unfold logSlack
            have hBits : (Nat.bits n).length ≤ n := length_natBits_le_self n
            nlinarith [Nat.zero_le (Nat.sqrt n)]

/-! ### A small calculus of polynomial slack budgets

The final assembly has to absorb a bounded number of nested constants into the
single uniform budget `hereditarySlack cOut delta epsilon n = cOut * U`, where
`U = delta + (epsilon + log n) * sqrt n + 1`.  Every intermediate quantity is
bounded by `cBase ^ k * U` for an explicit `k`, and the following four lemmas
are the only combination steps needed. -/

private lemma budget_mono_pow {b U a k m : Nat} (hb : 1 ≤ b) (hk : k ≤ m)
    (h : a ≤ b ^ k * U) : a ≤ b ^ m * U :=
  h.trans (Nat.mul_le_mul_right U (Nat.pow_le_pow_right hb hk))

private lemma budget_add_pow {b U a1 a2 k : Nat} (hb : 2 ≤ b)
    (h1 : a1 ≤ b ^ k * U) (h2 : a2 ≤ b ^ k * U) : a1 + a2 ≤ b ^ (k + 1) * U := by
  have h : b ^ k * U + b ^ k * U ≤ b ^ (k + 1) * U := by
    calc b ^ k * U + b ^ k * U = 2 * (b ^ k * U) := by ring
      _ ≤ b * (b ^ k * U) := Nat.mul_le_mul_right _ hb
      _ = b ^ (k + 1) * U := by ring
  omega

private lemma budget_add3_pow {b U a1 a2 a3 k : Nat} (hb : 3 ≤ b)
    (h1 : a1 ≤ b ^ k * U) (h2 : a2 ≤ b ^ k * U) (h3 : a3 ≤ b ^ k * U) :
    a1 + a2 + a3 ≤ b ^ (k + 1) * U := by
  have h : 3 * (b ^ k * U) ≤ b ^ (k + 1) * U := by
    calc 3 * (b ^ k * U) ≤ b * (b ^ k * U) := Nat.mul_le_mul_right _ hb
      _ = b ^ (k + 1) * U := by ring
  omega

private lemma budget_mul_pow {b U a c k : Nat} (hc : c ≤ b)
    (h : a ≤ b ^ k * U) : c * a ≤ b ^ (k + 1) * U := by
  calc c * a ≤ b * (b ^ k * U) := Nat.mul_le_mul hc h
    _ = b ^ (k + 1) * U := by ring

private lemma budget_const_pow {b U c : Nat} (hU : 1 ≤ U) (hc : c ≤ b) :
    c ≤ b ^ 1 * U := by
  calc c ≤ b := hc
    _ = b ^ 1 * 1 := by ring
    _ ≤ b ^ 1 * U := Nat.mul_le_mul_left _ hU

private lemma budget_logSlack_pow {b U c k a : Nat} (hb : 2 ≤ b) (hU : 1 ≤ U)
    (hc : c ≤ b) (h : (Nat.bits a).length ≤ b ^ k * U) :
    logSlack c a ≤ b ^ (k + 2) * U := by
  have h1 : c * (Nat.bits a).length ≤ b ^ (k + 1) * U := budget_mul_pow hc h
  have h2 : c ≤ b ^ (k + 1) * U :=
    budget_mono_pow (by omega) (by omega) (budget_const_pow hU hc)
  unfold logSlack
  exact budget_add_pow hb h1 h2

/-- Binary length of a quantity that is polynomial in `n`: it is logarithmic in
`n`, hence absorbed by two factors of the base constant. -/
private lemma budget_bits_of_le_two_mul {b U n m : Nat} (hb : 3 ≤ b) (hU : 1 ≤ U)
    (hLbU : (Nat.bits n).length ≤ U) (hm : m ≤ 2 * n + b) :
    (Nat.bits m).length ≤ b ^ 2 * U := by
  have h1 : (Nat.bits m).length ≤ (Nat.bits (2 * n + b)).length :=
    length_natBits_mono hm
  have h2 : (Nat.bits (2 * n + b)).length ≤
      (Nat.bits (2 * n)).length + (Nat.bits b).length + 1 :=
    length_natBits_add_le _ _
  have h3 : (Nat.bits (2 * n)).length ≤
      (Nat.bits n).length + (Nat.bits n).length + 1 := by
    simpa [two_mul] using length_natBits_add_le n n
  have h4 : (Nat.bits b).length ≤ b := length_natBits_le_self b
  have e1 : 2 * (Nat.bits n).length ≤ 2 * U := Nat.mul_le_mul_left 2 hLbU
  have e2 : b ≤ b * U := Nat.le_mul_of_pos_right _ hU
  have e3 : 2 ≤ 2 * U := Nat.le_mul_of_pos_right _ hU
  have e4 : (b + 4) * U = b * U + 2 * U + 2 * U := by ring
  have e5 : (b + 4) * U ≤ b ^ 2 * U := by
    have hle : b + 4 ≤ b ^ 2 := by nlinarith [hb]
    exact Nat.mul_le_mul_right _ hle
  omega

/-- Binary length of a quantity that is the sum of something polynomial in `n`
and something already inside the slack budget. -/
private lemma budget_bits_mix {b U n m k : Nat} (hb : 3 ≤ b) (hU : 1 ≤ U)
    (hLbU : (Nat.bits n).length ≤ U) (hm : m ≤ 2 * n + b + b ^ k * U) :
    (Nat.bits m).length ≤ b ^ (k + 3) * U := by
  have hb1 : 1 ≤ b := by omega
  have h1 : (Nat.bits m).length ≤ (Nat.bits (2 * n + b + b ^ k * U)).length :=
    length_natBits_mono hm
  have h2 : (Nat.bits (2 * n + b + b ^ k * U)).length ≤
      (Nat.bits (2 * n + b)).length + (Nat.bits (b ^ k * U)).length + 1 :=
    length_natBits_add_le _ _
  have h3 : (Nat.bits (2 * n + b)).length ≤ b ^ 2 * U :=
    budget_bits_of_le_two_mul hb hU hLbU le_rfl
  have h4 : (Nat.bits (b ^ k * U)).length ≤ b ^ k * U :=
    length_natBits_le_self _
  have h5 : b ^ 2 * U ≤ b ^ (k + 2) * U :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hb1 (by omega))
  have h6 : b ^ k * U ≤ b ^ (k + 2) * U :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hb1 (by omega))
  have h7 : 1 ≤ b ^ (k + 2) * U :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h8 : 3 * (b ^ (k + 2) * U) ≤ b ^ (k + 3) * U := by
    calc 3 * (b ^ (k + 2) * U) ≤ b * (b ^ (k + 2) * U) :=
          Nat.mul_le_mul_right _ hb
      _ = b ^ (k + 3) * U := by ring
  omega

private lemma budget_transport_pow {b U c e s k : Nat} (hb : 3 ≤ b) (hU : 1 ≤ U)
    (hc : c ≤ b) (he : e ≤ b ^ k * U) (hs : s ≤ b ^ k * U) :
    hereditaryStrongTransportStrength c e s ≤ b ^ (k + 9) * U := by
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hes : e + s ≤ b ^ (k + 1) * U := budget_add_pow hb2 he hs
  have hesbits : (Nat.bits (e + s)).length ≤ b ^ (k + 1) * U :=
    (length_natBits_le_self _).trans hes
  have hlog1 : logSlack c (e + s) ≤ b ^ (k + 3) * U :=
    budget_logSlack_pow hb2 hU hc hesbits
  have hfirst : e + s + logSlack c (e + s) ≤ b ^ (k + 4) * U :=
    budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hes) hlog1
  have hec : e + c ≤ b ^ (k + 2) * U :=
    budget_add_pow hb2 (budget_mono_pow hb1 (by omega) he)
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU hc))
  have hinner : e + s + logSlack c (e + s) + e + c ≤ b ^ (k + 6) * U := by
    have h1 : e + s + logSlack c (e + s) + e ≤ b ^ (k + 5) * U :=
      budget_add_pow hb2 hfirst (budget_mono_pow hb1 (by omega) he)
    exact budget_add_pow hb2 h1
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU hc))
  have hlog2 : logSlack c (e + s + logSlack c (e + s) + e + c) ≤ b ^ (k + 8) * U :=
    budget_logSlack_pow hb2 hU hc ((length_natBits_le_self _).trans hinner)
  have hsum : e + s + logSlack c (e + s) + (e + c) ≤ b ^ (k + 8) * U :=
    budget_mono_pow hb1 (by omega)
      (budget_add_pow hb2 hfirst (budget_mono_pow hb1 (by omega) hec))
  change e + s + logSlack c (e + s) + (e + c) +
      logSlack c (e + s + logSlack c (e + s) + e + c) ≤ b ^ (k + 9) * U
  exact budget_add_pow hb2 hsum hlog2

/-- The LCH two-part overhead `cLch * (epsilon + log n) * sqrt n` is linear in
the visible budget `U`. -/
private lemma budget_lch_pow {b U W n eps c : Nat} (hb : 3 ≤ b)
    (hW : W = (eps + (Nat.bits n).length) * Nat.sqrt n) (hWU : W ≤ U)
    (hLb1 : 1 ≤ (Nat.bits n).length) (hc : c ≤ b) :
    c * (eps + logSlack c n) * Nat.sqrt n ≤ b ^ 3 * U := by
  have hb2 : 2 ≤ b := by omega
  have h1 : eps + logSlack c n ≤ 2 * b * (eps + (Nat.bits n).length) := by
    unfold logSlack
    nlinarith [hLb1, hc, hb]
  have h2 : c * (eps + logSlack c n) * Nat.sqrt n ≤ 2 * b ^ 2 * W := by
    rw [hW]
    calc c * (eps + logSlack c n) * Nat.sqrt n
        ≤ (b * (2 * b * (eps + (Nat.bits n).length))) * Nat.sqrt n :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul hc h1)
      _ = 2 * b ^ 2 * ((eps + (Nat.bits n).length) * Nat.sqrt n) := by ring
  have h3 : 2 * b ^ 2 * W ≤ b ^ 3 * U := by
    calc 2 * b ^ 2 * W ≤ b * b ^ 2 * W :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb2)
      _ = b ^ 3 * W := by ring
      _ ≤ b ^ 3 * U := Nat.mul_le_mul_left _ hWU
  omega

/-- The intersection branch of the assembly — the ordinary chain `A₁ → A → M →
M₁`, the two-stage transfer to `A₁`, and the intersection estimate — stays
inside the visible budget. -/
private lemma budget_deltaOrig_pow
    {b U n eps delta aComp a1Comp pF1 pPlain dOmega dChain a1Over deltaInter
      deltaOrig NOrig cPart cSimT cTwo cInter cChain cOmegaOut cSuff : Nat}
    (hb : 3 ≤ b) (hU1 : 1 ≤ U)
    (hepsU : eps ≤ U) (hdeltaU : delta ≤ U) (hsqrtU : Nat.sqrt n ≤ U)
    (hLbU : (Nat.bits n).length ≤ U)
    (hcPart : cPart ≤ b) (hcSimT : cSimT ≤ b) (hcTwo : cTwo ≤ b)
    (hcInter : cInter ≤ b) (hcChain : cChain ≤ b) (hcOmegaOut : cOmegaOut ≤ b)
    (hcSuff : cSuff ≤ b)
    (haComp : aComp ≤ 2 * n + b)
    (hpF1 : pF1 = eps + logSlack cPart n)
    (hpPlain : pPlain = pF1 + cSimT)
    (hdOmega : dOmega =
      cOmegaOut * delta + cOmegaOut * Nat.sqrt n + logSlack cOmegaOut n)
    (hdChain : dChain = cChain * (pF1 + dOmega) + cChain)
    (ha1Over : a1Over = pPlain + 2 * (Nat.bits aComp).length + cTwo)
    (hdeltaInter : deltaInter = dChain + 2 * (Nat.bits a1Comp).length + cInter)
    (hdeltaOrig : deltaOrig = a1Over + deltaInter)
    (hNOrig : NOrig = aComp + deltaOrig)
    (ha1CompLe : a1Comp ≤ aComp + a1Over) :
    pF1 ≤ b ^ 3 * U ∧ pPlain ≤ b ^ 4 * U ∧ deltaOrig ≤ b ^ 13 * U ∧
      logSlack cSuff NOrig ≤ b ^ 18 * U ∧
      eps + deltaOrig + logSlack cSuff NOrig ≤ b ^ 20 * U := by
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hepsP : eps ≤ b ^ 0 * U := by simpa using hepsU
  have hdeltaP : delta ≤ b ^ 0 * U := by simpa using hdeltaU
  have hsqrtP : Nat.sqrt n ≤ b ^ 0 * U := by simpa using hsqrtU
  have hbitsnP : (Nat.bits n).length ≤ b ^ 0 * U := by simpa using hLbU
  have hbitsA : (Nat.bits aComp).length ≤ b ^ 2 * U :=
    budget_bits_of_le_two_mul hb hU1 hLbU haComp
  have hpF1U : pF1 ≤ b ^ 3 * U := by
    rw [hpF1]
    exact budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hepsP)
      (budget_logSlack_pow hb2 hU1 hcPart hbitsnP)
  have hpPlainU : pPlain ≤ b ^ 4 * U := by
    rw [hpPlain]
    exact budget_add_pow hb2 hpF1U
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hcSimT))
  have hdOmegaU : dOmega ≤ b ^ 4 * U := by
    rw [hdOmega]
    exact budget_add_pow hb2
      (budget_add_pow hb2
        (budget_mono_pow hb1 (by omega) (budget_mul_pow hcOmegaOut hdeltaP))
        (budget_mono_pow hb1 (by omega) (budget_mul_pow hcOmegaOut hsqrtP)))
      (budget_mono_pow hb1 (by omega)
        (budget_logSlack_pow hb2 hU1 hcOmegaOut hbitsnP))
  have hdChainU : dChain ≤ b ^ 7 * U := by
    rw [hdChain]
    have h1 : pF1 + dOmega ≤ b ^ 5 * U :=
      budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hpF1U) hdOmegaU
    exact budget_add_pow hb2 (budget_mul_pow hcChain h1)
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hcChain))
  have ha1OverU : a1Over ≤ b ^ 6 * U := by
    rw [ha1Over]
    exact budget_add_pow hb2
      (budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hpPlainU)
        (budget_mono_pow hb1 (by omega)
          (budget_mul_pow (by omega : 2 ≤ b) hbitsA)))
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hcTwo))
  have hbitsA1 : (Nat.bits a1Comp).length ≤ b ^ 9 * U :=
    budget_bits_mix hb hU1 hLbU
      (ha1CompLe.trans (Nat.add_le_add haComp ha1OverU))
  have hdeltaInterU : deltaInter ≤ b ^ 12 * U := by
    rw [hdeltaInter]
    exact budget_add_pow hb2
      (budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hdChainU)
        (budget_mul_pow (by omega : 2 ≤ b) hbitsA1))
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hcInter))
  have hdeltaOrigU : deltaOrig ≤ b ^ 13 * U := by
    rw [hdeltaOrig]
    exact budget_add_pow hb2 (budget_mono_pow hb1 (by omega) ha1OverU)
      hdeltaInterU
  have hlogNU : logSlack cSuff NOrig ≤ b ^ 18 * U :=
    budget_logSlack_pow hb2 hU1 hcSuff
      (budget_bits_mix hb hU1 hLbU
        (by rw [hNOrig]; exact Nat.add_le_add haComp hdeltaOrigU))
  refine ⟨hpF1U, hpPlainU, hdeltaOrigU, hlogNU, ?_⟩
  exact budget_add_pow hb2
    (budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hepsP)
      (budget_mono_pow hb1 (by omega) hdeltaOrigU))
    (budget_mono_pow hb1 (by omega) hlogNU)

/-- The ordinary-complexity constants of the assembly stay inside the visible
budget. -/
private lemma hereditary_core_budget_sum
    {b U n eps i mComp cardA cardA1 pF1 pPlain deltaOrig logN c5
      cLift cPart cFam cTrans cTwo : Nat}
    (hb : 3 ≤ b) (hU1 : 1 ≤ U) (hepsU : eps ≤ U)
    (hLbU : (Nat.bits n).length ≤ U)
    (hcLift : cLift ≤ b) (hcFam : cFam ≤ b)
    (hcTrans : cTrans ≤ b) (hcTwo : cTwo ≤ b)
    (hcardA : cardA ≤ 2 * n + b) (hcardA1 : cardA1 ≤ 2 * n + b)
    (hi : i ≤ 2 * n + b)
    (hpF1 : pF1 = eps + logSlack cPart n)
    (hpF1U : pF1 ≤ b ^ 3 * U) (hpPlainU : pPlain ≤ b ^ 4 * U)
    (hc6U : eps + deltaOrig + logN ≤ b ^ 20 * U)
    (hc5U : c5 ≤ b ^ 3 * U)
    (hmCompLe : mComp ≤ i + (logSlack cLift cardA + eps)) :
    (2 * (eps + logSlack cPart n) + cTrans) +
        (cFam * pF1 + logSlack cFam cardA1) +
        (pPlain + 2 * (Nat.bits mComp).length + cTwo) +
        logSlack cLift cardA + c5 +
        (eps + deltaOrig + logN) + eps + 2 ≤ b ^ 27 * U := by
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hepsP : eps ≤ b ^ 0 * U := by simpa using hepsU
  have hlogcardA : ∀ c : Nat, c ≤ b → logSlack c cardA ≤ b ^ 4 * U := fun c hc =>
    budget_logSlack_pow hb2 hU1 hc (budget_bits_of_le_two_mul hb hU1 hLbU hcardA)
  have hc1U : 2 * (eps + logSlack cPart n) + cTrans ≤ b ^ 5 * U := by
    have h1 : eps + logSlack cPart n ≤ b ^ 3 * U := by rw [← hpF1]; exact hpF1U
    exact budget_add_pow hb2 (budget_mul_pow (by omega : 2 ≤ b) h1)
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hcTrans))
  have hc2U : cFam * pF1 + logSlack cFam cardA1 ≤ b ^ 5 * U :=
    budget_add_pow hb2 (budget_mul_pow hcFam hpF1U)
      (budget_logSlack_pow hb2 hU1 hcFam
        (budget_bits_of_le_two_mul hb hU1 hLbU hcardA1))
  have hc4U : logSlack cLift cardA ≤ b ^ 4 * U := hlogcardA cLift hcLift
  have hbitsM : (Nat.bits mComp).length ≤ b ^ 8 * U := by
    refine budget_bits_mix hb hU1 hLbU ?_
    refine hmCompLe.trans (Nat.add_le_add hi ?_)
    exact budget_add_pow hb2 hc4U (budget_mono_pow hb1 (by omega) hepsP)
  have hc3U : pPlain + 2 * (Nat.bits mComp).length + cTwo ≤ b ^ 11 * U := by
    have h2 : 2 * (Nat.bits mComp).length ≤ b ^ 9 * U :=
      budget_mul_pow (by omega : 2 ≤ b) hbitsM
    exact budget_add_pow hb2
      (budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hpPlainU) h2)
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hcTwo))
  have t1 := budget_add_pow (a1 := 2 * (eps + logSlack cPart n) + cTrans)
    (a2 := cFam * pF1 + logSlack cFam cardA1) (k := 20) hb2
    (budget_mono_pow hb1 (by omega) hc1U) (budget_mono_pow hb1 (by omega) hc2U)
  have t2 := budget_add_pow (a2 := pPlain + 2 * (Nat.bits mComp).length + cTwo)
    (k := 21) hb2 (budget_mono_pow hb1 (by omega) t1)
    (budget_mono_pow hb1 (by omega) hc3U)
  have t3 := budget_add_pow (a2 := logSlack cLift cardA) (k := 22) hb2
    (budget_mono_pow hb1 (by omega) t2) (budget_mono_pow hb1 (by omega) hc4U)
  have t4 := budget_add_pow (a2 := c5) (k := 23) hb2
    (budget_mono_pow hb1 (by omega) t3) (budget_mono_pow hb1 (by omega) hc5U)
  have t5 := budget_add_pow (a2 := eps + deltaOrig + logN) (k := 24) hb2
    (budget_mono_pow hb1 (by omega) t4) (budget_mono_pow hb1 (by omega) hc6U)
  have t6 := budget_add_pow (a2 := eps) (k := 25) hb2
    (budget_mono_pow hb1 (by omega) t5) (budget_mono_pow hb1 (by omega) hepsP)
  exact budget_add_pow (a2 := 2) (k := 26) hb2
    (budget_mono_pow hb1 (by omega) t6)
    (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 (by omega : 2 ≤ b)))

/-- The transported strength of the assembly stays inside the visible budget. -/
private lemma hereditary_core_budget_strength
    {b U n cardA gap pF1 sF1 cGap cFam cTrans : Nat}
    (hb : 3 ≤ b) (hU1 : 1 ≤ U) (hLbU : (Nat.bits n).length ≤ U)
    (hcGap : cGap ≤ b) (hcFam : cFam ≤ b) (hcTrans : cTrans ≤ b)
    (hcardA : cardA ≤ 2 * n + b)
    (hpF1U : pF1 ≤ b ^ 3 * U) (hgapU : gap ≤ b ^ 20 * U)
    (hsF1 : sF1 = cGap * pF1 + gap + logSlack cGap cardA) :
    hereditaryStrongTransportStrength cTrans pF1
      (cFam * (pF1 + sF1) + cFam) ≤ b ^ 34 * U := by
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hsF1U : sF1 ≤ b ^ 22 * U := by
    rw [hsF1]
    exact budget_add_pow hb2
      (budget_add_pow hb2
        (budget_mono_pow hb1 (by omega) (budget_mul_pow hcGap hpF1U)) hgapU)
      (budget_mono_pow hb1 (by omega)
        (budget_logSlack_pow hb2 hU1 hcGap
          (budget_bits_of_le_two_mul hb hU1 hLbU hcardA)))
  have hstrengthU : cFam * (pF1 + sF1) + cFam ≤ b ^ 25 * U := by
    have h1 : pF1 + sF1 ≤ b ^ 23 * U :=
      budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hpF1U) hsF1U
    exact budget_add_pow hb2 (budget_mul_pow hcFam h1)
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hcFam))
  exact budget_transport_pow hb hU1 hcTrans
    (budget_mono_pow hb1 (by omega) hpF1U) hstrengthU

/-- Final linear bookkeeping of the hereditary assembly: the ordinary
complexity bound and the two-part bound for the transported family, given the
numeric form of every step of the `G → L → M → M₁ → F₁ → F` construction. -/
private lemma hereditary_core_arith
    {fComp f1Comp m1Comp mComp lComp gComp c1 c2 c3 c4 c5 c6 eps i j S
      cardF cardF1 cardM cardM1 cardL cardG cardA r : Nat}
    (n1 : fComp ≤ f1Comp + c1) (n2 : f1Comp ≤ m1Comp + c2)
    (n3 : m1Comp ≤ mComp + c3) (n4 : mComp + cardM ≤ lComp + cardL + c5)
    (n5 : lComp ≤ gComp + c4) (n6 : gComp ≤ i)
    (n7 : cardL ≤ cardG + cardA) (n8 : cardG ≤ j)
    (n9 : cardF ≤ cardF1) (n10 : cardF1 + r ≤ cardM1 + 2)
    (n11 : cardM1 ≤ cardM) (n12 : cardA ≤ r + c6)
    (n13 : mComp ≤ lComp + eps)
    (hbud : c1 + c2 + c3 + c4 + c5 + c6 + eps + 2 ≤ S) :
    fComp ≤ i + S ∧ fComp + cardF ≤ i + j + S := by
  omega

/-- The genuinely nontrivial branch of the hereditary construction.  The two
displayed inequalities are exactly the hypotheses needed to invoke `lemma_lch`;
the final strict inequality excludes the singleton fallback.  Its proof is the
remaining concrete `G → L → M → M₁ → F` assembly, using
`hereditary_omega_chain` between the LCH and partition steps. -/
private lemma hereditary_family_core
    (V T : Map) (hV : isOptimalConditional V) (hT : IsOptimalTotalConditional T) :
    ∃ cKappa cOut : Nat,
      ∀ x n A (hA : A.Nonempty) epsilon delta,
        x.length = n →
        IsMinimalModel V x A hA delta (logSlack cKappa n) →
        IsSufficientStatistic V x A hA epsilon →
        IsStrongSetModel T x A hA epsilon →
        IsNormalString V T x epsilon epsilon →
        ∀ i j,
        epsilon ≤ n →
        epsilon * 2 < Nat.sqrt n →
        ((i + hereditarySlack cOut delta epsilon n : Nat) : ENat) <
          plainSetComplexity V A hA →
        InPlainDescriptionProfile V (codedUniformOn A hA).code i j →
        ∃ F, ∃ hF : F.Nonempty,
          (codedUniformOn A hA).code ∈ F ∧
          IsStrongSetModel T (codedUniformOn A hA).code F hF
            (hereditarySlack cOut delta epsilon n) ∧
          plainSetComplexity V F hF ≤ (i + hereditarySlack cOut delta epsilon n : ENat) ∧
          plainSetComplexity V F hF + (finiteSetLogCard F : ENat) ≤
            ((i + j + hereditarySlack cOut delta epsilon n : Nat) : ENat) := by
  -- The genuine `G → L → M → M₁ → F` assembly of VS40 `thm:hereditary`.
  -- This is a multi-iteration obligation; the reusable component lemmas that feed
  -- it are already proved above and in `HereditaryLift`/`HereditaryFamily`/
  -- `LchLemma`:
  --   * G → L : `hereditary_lift_model` (lift the plain-profile model `G` of
  --     `code A` to a model `L ∋ x`).
  --   * L → M : `lemma_lch_with_mem` — MUST be invoked with `alpha = epsilon` (not
  --     `cOut*delta+…`), because `LemmaLchStatement` requires `alpha*2 < n.sqrt`,
  --     supplied here exactly by `hEpsSqrt : epsilon*2 < n.sqrt`; the normality
  --     input is `hNormal : IsNormalString V T x epsilon epsilon`.
  --   * M → M₁ : `IsStrongSetModel.exists_partition`.  This needs `x ∈ M`.
  --     The frozen `LemmaLchStatement` predates that field, so the worker
  --     theorem `lemma_lch_with_mem` exposes the membership already carried by
  --     `LchIterates`; the public `lemma_lch` remains unchanged.
  --   * M₁ → F : `hereditary_family_model` (+ `partition_member_totalCondK_of_logCard_gap`,
  --     `hereditary_omega_chain`, `hereditary_sufficiency_intersection_lower_bound`),
  --     then `strong_model_of_totalEquivalentWithin` transports the strong family
  --     for `code A₁` back to `code A` along the total equivalence `A₁ ↔ A` from the
  --     partition step.
  -- The remaining work is substantive parameter flow: compose the ordinary
  -- conditional chain `A₁ → A → M → M₁`, use it to bound the complexity of
  -- `A₁ ∩ M₁`, apply sufficiency to control `gap`, and only then absorb the
  -- resulting `p`, `s`, and `N` budgets into the single hereditary slack.
  obtain ⟨cLift, hLift⟩ := hereditary_lift_model V hV
  obtain ⟨cLch, hLch⟩ := lemma_lch_with_mem V T hV hT
  obtain ⟨cPart, hPart⟩ := IsStrongSetModel.exists_partition V hV T hT
  obtain ⟨cFam, hFam⟩ := hereditary_family_model_sharp V T hV hT
  obtain ⟨cGap, hGap⟩ := partition_member_totalCondK_of_logCard_gap V T hV hT
  obtain ⟨cOmegaKappa, cOmegaOut, hOmega⟩ := hereditary_omega_chain V T hV hT cLch
  obtain ⟨cSuff, hSuff⟩ := hereditary_sufficiency_model_lower_bound V hV
  obtain ⟨cTrans, hTrans⟩ := strong_model_of_totalEquivalentWithin V T hV hT
  obtain ⟨cChain, hChain⟩ := hereditary_partition_condK_chain V T hV hT
  obtain ⟨cInter, hInter⟩ := plainSetComplexity_inter_le_of_condK V hV
  obtain ⟨cTwo, hTwo⟩ := plainK_two_stage V hV
  obtain ⟨cSimT, hSimT⟩ := hV.2 T hT.1
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  obtain ⟨cLiftLin, hLiftLin⟩ :=
    logSlack_linear_bound cLift 2 cLen
  obtain ⟨q, hq⟩ := Nat.Partrec.Code.exists_code.mp hV.1
  let cBase :=
    cLift + cLch + cPart + cFam + cGap + cOmegaOut + cSuff + cTrans +
      cChain + cInter + cTwo + cSimT + cLen + cLiftLin + 10
  let cOut := cBase ^ 40
  refine ⟨cOmegaKappa, cOut, ?_⟩
  intro x n A hA epsilon delta hn hMin hSuffA hStrong hNorm i j
    heps_le heps_sqrt h_i_lt h_prof
  -- Step 1: G -> L Lift
  obtain ⟨G, hG_nonempty, hx_G, hG_i, hG_j⟩ := h_prof
  have hA_mem_x : x ∈ A := hMin.1
  have hAcode_G : (codedUniformOn A hA).code ∈ G := hx_G
  obtain ⟨L, hL, hx_L, hLcomp, hLcard⟩ :=
    hLift x A hA G hG_nonempty hA_mem_x hAcode_G
  -- Step 2: L -> M LCH
  have hL_mem_x : x ∈ L := hx_L
  obtain ⟨M, hM, hx_M, hM_strong, hM_bound, hM_omega, hM_plain⟩ :=
    hLch x n L hL epsilon epsilon q hq hn hL_mem_x heps_le
      heps_sqrt hNorm
  -- Step 3: Partition Equivalence
  obtain ⟨Q, M1, hM1_x, hQ_part, hM1_Q, hM1_card, hQ_comp,
      hM_M1, hM1_M⟩ :=
    hPart x n hn M hx_M epsilon hM_strong
  have hStrong_cast : IsStrongSetModel T x A ⟨x, hA_mem_x⟩ epsilon := by
    -- Cast hStrong which uses hA to use ⟨x, hA_mem_x⟩
    exact hStrong
  obtain ⟨P, A1, hA1_x, hP_part, hA1_P, hA1_card, hP_comp,
      hA_A1, hA1_A⟩ :=
    hPart x n hn A hA_mem_x epsilon hStrong_cast
  -- Step 4: Omega Chain
  have hM_plain_bound :
      plainSetComplexity V M hM ≤
        plainSetComplexity V A hA + (delta : ENat) := by
    have hxPlain : plainK V x ≤ ((n + cLen : Nat) : ENat) := by
      simpa [hn] using hLen x
    have hcardA_ENat :
        (finiteSetLogCard A : ENat) ≤ ((2 * n + cLen : Nat) : ENat) := by
      calc
        (finiteSetLogCard A : ENat)
            ≤ plainSetComplexity V A hA +
                (finiteSetLogCard A : ENat) := le_add_left le_rfl
        _ ≤ plainK V x + (epsilon : ENat) := hSuffA.2
        _ ≤ ((n + cLen : Nat) : ENat) + (epsilon : ENat) := by
          gcongr
        _ ≤ ((2 * n + cLen : Nat) : ENat) := by
          exact_mod_cast (show n + cLen + epsilon ≤ 2 * n + cLen by omega)
    have hcardA : finiteSetLogCard A ≤ 2 * n + cLen := by
      exact_mod_cast hcardA_ENat
    have hLiftSlack :
        logSlack cLift (finiteSetLogCard A) ≤ logSlack cLiftLin n :=
      (logSlack_mono_right cLift hcardA).trans (hLiftLin n)
    have hcBaseTen : 10 ≤ cBase := by
      dsimp [cBase]
      omega
    have hcBasePos : 0 < cBase := (by omega)
    have hcBaseOut : cBase ≤ cOut := by
      dsimp [cOut]
      exact Nat.le_self_pow (by norm_num) cBase
    have hcLiftLinOut : cLiftLin ≤ cOut := by
      apply le_trans (b := cBase)
      · dsimp [cBase]
        omega
      · exact hcBaseOut
    have hOneBase : 1 ≤ cBase := Nat.succ_le_iff.mpr hcBasePos
    have hcOutPos : 1 ≤ cOut := hOneBase.trans hcBaseOut
    have hsqrtPos : 1 ≤ n.sqrt :=
      Nat.succ_le_iff.mpr ((Nat.zero_le (epsilon * 2)).trans_lt heps_sqrt)
    have hbitsMul :
        cLiftLin * (Nat.bits n).length ≤
          cOut * (Nat.bits n).length :=
      Nat.mul_le_mul_right _ hcLiftLinOut
    have hepsMul : epsilon ≤ cOut * epsilon :=
      Nat.le_mul_of_pos_left epsilon hcOutPos
    have hscale :
        cOut * (epsilon + (Nat.bits n).length) ≤
          cOut * (epsilon + (Nat.bits n).length) * n.sqrt :=
      Nat.le_mul_of_pos_right _ hsqrtPos
    have hOverhead :
        logSlack cLift (finiteSetLogCard A) + epsilon ≤
          hereditarySlack cOut delta epsilon n := by
      calc
        logSlack cLift (finiteSetLogCard A) + epsilon
            ≤ logSlack cLiftLin n + epsilon :=
              Nat.add_le_add_right hLiftSlack epsilon
        _ ≤ cOut * (epsilon + (Nat.bits n).length) + cOut := by
          unfold logSlack
          nlinarith
        _ ≤ cOut * (epsilon + (Nat.bits n).length) * n.sqrt + cOut := by
          exact Nat.add_le_add_right hscale cOut
        _ ≤ hereditarySlack cOut delta epsilon n := by
          unfold hereditarySlack
          omega
    calc
      plainSetComplexity V M hM
          ≤ plainSetComplexity V L hL + (epsilon : ENat) := hM_plain
      _ ≤ (plainSetComplexity V G hG_nonempty +
            (logSlack cLift (finiteSetLogCard A) : ENat)) +
            (epsilon : ENat) := by
          gcongr
      _ ≤ (i : ENat) +
            (logSlack cLift (finiteSetLogCard A) : ENat) +
            (epsilon : ENat) := by
          gcongr
      _ ≤ ((i + hereditarySlack cOut delta epsilon n : Nat) : ENat) := by
          exact_mod_cast (show
            i + logSlack cLift (finiteSetLogCard A) + epsilon ≤
              i + hereditarySlack cOut delta epsilon n by omega)
      _ ≤ plainSetComplexity V A hA := h_i_lt.le
      _ ≤ plainSetComplexity V A hA + (delta : ENat) :=
        le_add_right le_rfl
  let dOmega :=
    cOmegaOut * delta + cOmegaOut * n.sqrt + logSlack cOmegaOut n
  have hM_omega_bound :
      condK V (codedUniformOn M hM).code
          (codedUniformOn A hA).code ≤ (dOmega : ENat) := by
    simpa [dOmega] using
      hOmega x n A hA M hM delta q hq hn hMin hM_plain_bound hM_omega
  -- Step 5: LogCard Gap
  have hA1M1_nonempty : (A1 ∩ M1).Nonempty := ⟨x, by simp [hM1_x, hA1_x]⟩
  set p_F1 := epsilon + logSlack cPart n
  let dChain := cChain * (p_F1 + dOmega) + cChain
  have hM1_A1_plain :
      condK V (codedUniformOn M1 ⟨x, hM1_x⟩).code
          (codedUniformOn A1 ⟨x, hA1_x⟩).code ≤ (dChain : ENat) := by
    apply hChain (codedUniformOn A1 ⟨x, hA1_x⟩).code
      (codedUniformOn A ⟨x, hA_mem_x⟩).code
      (codedUniformOn M hM).code
      (codedUniformOn M1 ⟨x, hM1_x⟩).code p_F1 dOmega
    · simpa [p_F1] using hA_A1
    · exact hM_omega_bound
    · simpa [p_F1] using hM1_M
  have hA1_finite : plainSetComplexity V A1 ⟨x, hA1_x⟩ ≠ ⊤ :=
    condK_ne_top_of_optimal V hV
      (codedUniformOn A1 ⟨x, hA1_x⟩).code []
  let a1Comp := (plainSetComplexity V A1 ⟨x, hA1_x⟩).toNat
  have hA1_value :
      plainSetComplexity V A1 ⟨x, hA1_x⟩ = (a1Comp : ENat) :=
    (ENat.coe_toNat hA1_finite).symm
  have hInter_plain :
      plainSetComplexity V (A1 ∩ M1) hA1M1_nonempty ≤
        (a1Comp + dChain + 2 * (Nat.bits a1Comp).length + cInter : Nat) :=
    hInter A1 ⟨x, hA1_x⟩ M1 ⟨x, hM1_x⟩ hA1M1_nonempty
      a1Comp dChain hA1_value hM1_A1_plain
  have hA_finite : plainSetComplexity V A hA ≠ ⊤ :=
    condK_ne_top_of_optimal V hV (codedUniformOn A hA).code []
  let aComp := (plainSetComplexity V A hA).toNat
  have hA_value : plainSetComplexity V A hA = (aComp : ENat) :=
    (ENat.coe_toNat hA_finite).symm
  let pPlain := p_F1 + cSimT
  have hA1_A_plain :
      condK V (codedUniformOn A1 ⟨x, hA1_x⟩).code
          (codedUniformOn A hA).code ≤ (pPlain : ENat) := by
    calc
      condK V (codedUniformOn A1 ⟨x, hA1_x⟩).code
          (codedUniformOn A hA).code
          ≤ condK T (codedUniformOn A1 ⟨x, hA1_x⟩).code
              (codedUniformOn A hA).code + (cSimT : ENat) := hSimT _ _
      _ ≤ totalCondK T (codedUniformOn A1 ⟨x, hA1_x⟩).code
              (codedUniformOn A hA).code + (cSimT : ENat) := by
            gcongr
            exact condK_le_totalCondK T _ _
      _ ≤ (p_F1 : ENat) + (cSimT : ENat) := by
            gcongr
            simpa [p_F1] using hA1_A
      _ = (pPlain : ENat) := by
            dsimp [pPlain]
            norm_cast
  let a1Over := pPlain + 2 * (Nat.bits aComp).length + cTwo
  have hA1_plain_from_A :
      plainSetComplexity V A1 ⟨x, hA1_x⟩ ≤
        ((aComp + a1Over : Nat) : ENat) := by
    have hRaw :=
      hTwo (codedUniformOn A1 ⟨x, hA1_x⟩).code
        (codedUniformOn A hA).code aComp pPlain
        (le_of_eq hA_value) hA1_A_plain
    calc
      plainSetComplexity V A1 ⟨x, hA1_x⟩
          ≤ ((aComp + pPlain + 2 * (Nat.bits aComp).length + cTwo : Nat) :
              ENat) := hRaw
      _ = ((aComp + a1Over : Nat) : ENat) := by
            dsimp [a1Over]
            congr 1
            omega
  have ha1Bound : a1Comp ≤ aComp + a1Over := by
    have h := hA1_plain_from_A
    rw [hA1_value] at h
    exact_mod_cast h
  have hI_finite :
      plainSetComplexity V (A1 ∩ M1) hA1M1_nonempty ≠ ⊤ :=
    condK_ne_top_of_optimal V hV
      (codedUniformOn (A1 ∩ M1) hA1M1_nonempty).code []
  let iComp :=
    (plainSetComplexity V (A1 ∩ M1) hA1M1_nonempty).toNat
  have hI_value :
      plainSetComplexity V (A1 ∩ M1) hA1M1_nonempty = (iComp : ENat) :=
    (ENat.coe_toNat hI_finite).symm
  let deltaInter := dChain + 2 * (Nat.bits a1Comp).length + cInter
  have hiComp : iComp ≤ a1Comp + deltaInter := by
    have h := hInter_plain
    rw [hI_value] at h
    have hNat :
        iComp ≤ a1Comp + dChain + 2 * (Nat.bits a1Comp).length + cInter := by
      exact_mod_cast h
    dsimp [deltaInter]
    omega
  let deltaOrig := a1Over + deltaInter
  have hiOrig : iComp ≤ aComp + deltaOrig := by
    dsimp [deltaOrig]
    omega
  let NOrig := aComp + deltaOrig
  have hLogGap :=
    hSuff x A hA (A1 ∩ M1) hA1M1_nonempty epsilon deltaOrig
      NOrig aComp iComp hSuffA (by simp [hA1_x, hM1_x])
      hA_value hI_value hiOrig le_rfl
  let gapBudget := epsilon + deltaOrig + logSlack cSuff NOrig
  set gap := finiteSetLogCard A1 - finiteSetLogCard (A1 ∩ M1)
  have hgap_budget : gap ≤ gapBudget := by
    dsimp [gap, gapBudget]
    have hA1Log : finiteSetLogCard A1 ≤ finiteSetLogCard A :=
      finiteSetLogCard_mono hA1_card
    omega
  have hgap_le : finiteSetLogCard A1 ≤ finiteSetLogCard (A1 ∩ M1) + gap := by omega
  have hM1_A1_gap :
      totalCondK T (codedUniformOn M1 ⟨x, hM1_x⟩).code
          (codedUniformOn A1 ⟨x, hA1_x⟩).code ≤
        (cGap * (epsilon + logSlack cPart n) + gap +
          logSlack cGap (finiteSetLogCard A) : ENat) := by
    have h_part_comp_Q :
        partitionComplexity V Q ≤
          (epsilon + logSlack cPart n : ENat) := hQ_comp
    have h_gap_apply :=
      hGap Q M1 ⟨x, hM1_x⟩ A1 ⟨x, hA1_x⟩
        (epsilon + logSlack cPart n) (finiteSetLogCard A) gap
        hQ_part hM1_Q hA1M1_nonempty h_part_comp_Q
        (finiteSetLogCard_mono hA1_card) hgap_le
    exact h_gap_apply
  -- Step 6: M1 -> F1 Hereditary Family
  have hp_bound :
      partitionComplexity V P ≤
        (epsilon + logSlack cPart n : ENat) := hP_comp
  set s_F1 := cGap * p_F1 + gap + logSlack cGap (finiteSetLogCard A)
  obtain ⟨F1, hF1, hA1_F1, hF1_strong, hF1_comp, hF1_card⟩ :=
    hFam P A1 ⟨x, hA1_x⟩ M1 ⟨x, hM1_x⟩ p_F1 s_F1
      hP_part hA1_P hA1M1_nonempty hp_bound hM1_A1_gap
  -- Step 7: F1 -> F Transport
  have hA1_eq_A :
      TotalEquivalentWithin T (codedUniformOn A1 ⟨x, hA1_x⟩).code
        (codedUniformOn A hA).code (epsilon + logSlack cPart n) := by
    exact ⟨hA1_A, hA_A1⟩
  obtain ⟨F, hF, hA_F, hF_strong, hF_comp, hF_card⟩ :=
    hTrans (codedUniformOn A1 ⟨x, hA1_x⟩).code
      (codedUniformOn A hA).code (epsilon + logSlack cPart n)
      (cFam * (p_F1 + s_F1) + cFam)
      F1 hF1 hA1_F1 hA1_eq_A hF1_strong
  -- Step 8: numeric form of every complexity occurring in the final bounds.
  have hFinite : ∀ (S : Finset BitString) (hS : S.Nonempty),
      ∃ k : Nat, plainSetComplexity V S hS = (k : ENat) := by
    intro S hS
    exact ⟨_, (ENat.coe_toNat
      (condK_ne_top_of_optimal V hV (codedUniformOn S hS).code [])).symm⟩
  obtain ⟨fComp, hfVal⟩ := hFinite F hF
  obtain ⟨f1Comp, hf1Val⟩ := hFinite F1 hF1
  obtain ⟨mComp, hmVal⟩ := hFinite M hM
  obtain ⟨m1Comp, hm1Val⟩ := hFinite M1 ⟨x, hM1_x⟩
  obtain ⟨lComp, hlVal⟩ := hFinite L hL
  obtain ⟨gComp, hgVal⟩ := hFinite G hG_nonempty
  obtain ⟨c1, hc1⟩ : ∃ t : Nat, t = 2 * (epsilon + logSlack cPart n) + cTrans :=
    ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ t : Nat,
      t = cFam * p_F1 + logSlack cFam (finiteSetLogCard A1) := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ t : Nat,
      t = pPlain + 2 * (Nat.bits mComp).length + cTwo := ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ t : Nat, t = logSlack cLift (finiteSetLogCard A) := ⟨_, rfl⟩
  obtain ⟨c5, hc5⟩ : ∃ t : Nat,
      t = cLch * (epsilon + logSlack cLch n) * Nat.sqrt n := ⟨_, rfl⟩
  obtain ⟨c6, hc6⟩ : ∃ t : Nat,
      t = epsilon + deltaOrig + logSlack cSuff NOrig := ⟨_, rfl⟩
  have n1 : fComp ≤ f1Comp + c1 := by
    have h := hF_comp
    rw [hfVal, hf1Val] at h
    rw [hc1]
    exact_mod_cast h
  have n2 : f1Comp ≤ m1Comp + c2 := by
    have h := hF1_comp
    rw [hf1Val, hm1Val] at h
    rw [hc2]
    exact_mod_cast h
  have hM1_M_plain :
      condK V (codedUniformOn M1 ⟨x, hM1_x⟩).code (codedUniformOn M hM).code ≤
        (pPlain : ENat) := by
    calc
      condK V (codedUniformOn M1 ⟨x, hM1_x⟩).code (codedUniformOn M hM).code
          ≤ condK T (codedUniformOn M1 ⟨x, hM1_x⟩).code
              (codedUniformOn M hM).code + (cSimT : ENat) := hSimT _ _
      _ ≤ totalCondK T (codedUniformOn M1 ⟨x, hM1_x⟩).code
              (codedUniformOn M hM).code + (cSimT : ENat) := by
            gcongr
            exact condK_le_totalCondK T _ _
      _ ≤ (p_F1 : ENat) + (cSimT : ENat) := by
            gcongr
            simpa [p_F1] using hM1_M
      _ = (pPlain : ENat) := by
            dsimp [pPlain]
            norm_cast
  have n3 : m1Comp ≤ mComp + c3 := by
    have h :=
      hTwo (codedUniformOn M1 ⟨x, hM1_x⟩).code (codedUniformOn M hM).code
        mComp pPlain (le_of_eq hmVal) hM1_M_plain
    have h' : (m1Comp : ENat) ≤
        ((mComp + pPlain + 2 * (Nat.bits mComp).length + cTwo : Nat) : ENat) := by
      rw [← hm1Val]
      exact h
    have hnat : m1Comp ≤ mComp + pPlain + 2 * (Nat.bits mComp).length + cTwo := by
      exact_mod_cast h'
    rw [hc3]
    omega
  have n4 : mComp + finiteSetLogCard M ≤ lComp + finiteSetLogCard L + c5 := by
    have h := hM_bound
    rw [hmVal, hlVal] at h
    rw [hc5]
    exact_mod_cast h
  have n5 : lComp ≤ gComp + c4 := by
    have h := hLcomp
    rw [hlVal, hgVal] at h
    rw [hc4]
    exact_mod_cast h
  have n6 : gComp ≤ i := by
    have h := hG_i
    rw [hgVal] at h
    exact_mod_cast h
  have n7 : finiteSetLogCard L ≤ finiteSetLogCard G + finiteSetLogCard A := hLcard
  have n8 : finiteSetLogCard G ≤ j := (finiteSetLogCard_le_iff G j).mpr hG_j
  have n9 : finiteSetLogCard F ≤ finiteSetLogCard F1 := hF_card
  have n10 : finiteSetLogCard F1 + finiteSetLogCard (A1 ∩ M1) ≤
      finiteSetLogCard M1 + 2 := hF1_card
  have n11 : finiteSetLogCard M1 ≤ finiteSetLogCard M :=
    finiteSetLogCard_mono hM1_card
  have n12 : finiteSetLogCard A ≤ finiteSetLogCard (A1 ∩ M1) + c6 := by
    rw [hc6, ← Nat.add_assoc, ← Nat.add_assoc]
    exact hLogGap
  have n13 : mComp ≤ lComp + epsilon := by
    have h := hM_plain
    rw [hmVal, hlVal] at h
    exact_mod_cast h
  -- Step 9: absorb every accumulated constant into the single hereditary
  -- slack budget `hereditarySlack cOut delta epsilon n = cOut * U`.
  obtain ⟨W, hW⟩ : ∃ W : Nat, W = (epsilon + (Nat.bits n).length) * Nat.sqrt n :=
    ⟨_, rfl⟩
  obtain ⟨Ubud, hUbud⟩ : ∃ U : Nat, U = delta + W + 1 := ⟨_, rfl⟩
  have hU1 : 1 ≤ Ubud := by omega
  have hb3 : 3 ≤ cBase := by dsimp [cBase]; omega
  have hb1 : 1 ≤ cBase := by omega
  have hcOutEq : cOut = cBase ^ 40 := rfl
  have hcLiftB : cLift ≤ cBase := by dsimp [cBase]; omega
  have hcLchB : cLch ≤ cBase := by dsimp [cBase]; omega
  have hcPartB : cPart ≤ cBase := by dsimp [cBase]; omega
  have hcFamB : cFam ≤ cBase := by dsimp [cBase]; omega
  have hcGapB : cGap ≤ cBase := by dsimp [cBase]; omega
  have hcOmegaOutB : cOmegaOut ≤ cBase := by dsimp [cBase]; omega
  have hcSuffB : cSuff ≤ cBase := by dsimp [cBase]; omega
  have hcTransB : cTrans ≤ cBase := by dsimp [cBase]; omega
  have hcChainB : cChain ≤ cBase := by dsimp [cBase]; omega
  have hcInterB : cInter ≤ cBase := by dsimp [cBase]; omega
  have hcTwoB : cTwo ≤ cBase := by dsimp [cBase]; omega
  have hcSimTB : cSimT ≤ cBase := by dsimp [cBase]; omega
  have hcLenB : cLen ≤ cBase := by dsimp [cBase]; omega
  -- From here on the two outer constants are used only through the bounds
  -- just recorded, so we may forget how they were built.
  clear_value cOut
  clear_value cBase
  have hslackU : hereditarySlack cOut delta epsilon n = cOut * Ubud := by
    unfold hereditarySlack
    rw [hUbud, hW]
    ring
  have hsqrt1 : 1 ≤ Nat.sqrt n :=
    Nat.succ_le_iff.mpr ((Nat.zero_le (epsilon * 2)).trans_lt heps_sqrt)
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hsqrt1; simp at hsqrt1
    · exact h
  have hLb1 : 1 ≤ (Nat.bits n).length := by
    have h_pos := Nat.size_pos.mpr hn1
    have h_len := Nat.size_eq_bits_len n
    omega
  have hepsW : epsilon ≤ W := by
    rw [hW]
    calc epsilon ≤ epsilon * Nat.sqrt n := Nat.le_mul_of_pos_right _ hsqrt1
      _ ≤ (epsilon + (Nat.bits n).length) * Nat.sqrt n :=
          Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hLbW : (Nat.bits n).length ≤ W := by
    rw [hW]
    calc (Nat.bits n).length ≤ (Nat.bits n).length * Nat.sqrt n :=
          Nat.le_mul_of_pos_right _ hsqrt1
      _ ≤ (epsilon + (Nat.bits n).length) * Nat.sqrt n :=
          Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  have hsqrtW : Nat.sqrt n ≤ W := by
    rw [hW]
    calc Nat.sqrt n ≤ (Nat.bits n).length * Nat.sqrt n :=
          Nat.le_mul_of_pos_left _ hLb1
      _ ≤ (epsilon + (Nat.bits n).length) * Nat.sqrt n :=
          Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  -- The visible complexities are polynomial in `n`.
  have hxPlain : plainK V x ≤ ((n + cLen : Nat) : ENat) := by
    simpa [hn] using hLen x
  have hAsuffNat : aComp + finiteSetLogCard A ≤ n + cLen + epsilon := by
    have h : ((aComp : Nat) : ENat) + ((finiteSetLogCard A : Nat) : ENat) ≤
        ((n + cLen + epsilon : Nat) : ENat) := by
      calc ((aComp : Nat) : ENat) + ((finiteSetLogCard A : Nat) : ENat)
          = plainSetComplexity V A hA + (finiteSetLogCard A : ENat) := by
            rw [hA_value]
        _ ≤ plainK V x + (epsilon : ENat) := hSuffA.2
        _ ≤ ((n + cLen : Nat) : ENat) + (epsilon : ENat) := by gcongr
        _ = ((n + cLen + epsilon : Nat) : ENat) := by push_cast; ring
    exact_mod_cast h
  have hcardA : finiteSetLogCard A ≤ 2 * n + cBase := by omega
  have haCompBig : aComp ≤ 2 * n + cBase := by omega
  have hilt : i + hereditarySlack cOut delta epsilon n < aComp := by
    have h := h_i_lt
    rw [hA_value] at h
    exact_mod_cast h
  have hiBig : i ≤ 2 * n + cBase := by omega
  have hmCompLe :
      mComp ≤ i + (logSlack cLift (finiteSetLogCard A) + epsilon) := by
    rw [← hc4]
    calc mComp ≤ lComp + epsilon := n13
      _ ≤ (gComp + c4) + epsilon := Nat.add_le_add_right n5 _
      _ ≤ (i + c4) + epsilon := Nat.add_le_add_right (Nat.add_le_add_right n6 _) _
      _ = i + (c4 + epsilon) := by ring
  have hcardA1 : finiteSetLogCard A1 ≤ 2 * n + cBase :=
    le_trans (finiteSetLogCard_mono hA1_card) hcardA
  obtain ⟨hpF1U, hpPlainU, -, -, hc6U⟩ :=
    budget_deltaOrig_pow (b := cBase) (U := Ubud) (n := n) (eps := epsilon)
      (delta := delta) (aComp := aComp) (a1Comp := a1Comp) (pF1 := p_F1)
      (pPlain := pPlain) (dOmega := dOmega) (dChain := dChain)
      (a1Over := a1Over) (deltaInter := deltaInter) (deltaOrig := deltaOrig)
      (NOrig := NOrig)
      hb3 hU1 (by omega) (by omega) (by omega) (by omega)
      hcPartB hcSimTB hcTwoB hcInterB hcChainB hcOmegaOutB hcSuffB
      haCompBig rfl rfl rfl rfl rfl rfl rfl rfl ha1Bound
  have hc5U : cLch * (epsilon + logSlack cLch n) * Nat.sqrt n ≤ cBase ^ 3 * Ubud :=
    budget_lch_pow hb3 hW (by omega) hLb1 hcLchB
  have hsumU :=
    hereditary_core_budget_sum (b := cBase) (U := Ubud) (n := n)
      (eps := epsilon) (i := i) (mComp := mComp)
      (cardA := finiteSetLogCard A) (cardA1 := finiteSetLogCard A1)
      (pF1 := p_F1) (pPlain := pPlain) (deltaOrig := deltaOrig)
      (logN := logSlack cSuff NOrig)
      (c5 := cLch * (epsilon + logSlack cLch n) * Nat.sqrt n)
      hb3 hU1 (by omega) (by omega)
      hcLiftB hcFamB hcTransB hcTwoB
      hcardA hcardA1 hiBig rfl hpF1U hpPlainU hc6U hc5U
      hmCompLe
  have htransU :=
    hereditary_core_budget_strength (b := cBase) (U := Ubud) (n := n)
      (cardA := finiteSetLogCard A) (gap := gap) (pF1 := p_F1) (sF1 := s_F1)
      hb3 hU1 (by omega) hcGapB hcFamB hcTransB hcardA hpF1U
      (hgap_budget.trans hc6U) rfl
  have hbud : c1 + c2 + c3 + c4 + c5 + c6 + epsilon + 2 ≤
      hereditarySlack cOut delta epsilon n := by
    rw [hc1, hc2, hc3, hc4, hc5, hc6, hslackU, hcOutEq]
    exact hsumU.trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hb1 (by norm_num)))
  obtain ⟨hgoal_comp, hgoal_sum⟩ :=
    hereditary_core_arith n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 hbud
  -- Final cleanup
  refine ⟨F, hF, hA_F, ?_, ?_, ?_⟩
  · -- the transported family is a strong model of `code A`
    refine hF_strong.mono ?_
    rw [hslackU, hcOutEq]
    exact htransU.trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hb1 (by norm_num)))
  · -- ordinary complexity of the transported family
    rw [hfVal]
    exact_mod_cast hgoal_comp
  · -- two-part complexity of the transported family
    rw [hfVal]
    exact_mod_cast hgoal_sum

private lemma hereditary_min_shift_bound
    (i n delta epsilon cBound cCore : Nat)
    (S : Nat) (F : Finset BitString)
    (hInteresting : ((i + hereditarySlack cCore delta epsilon n : Nat) : ENat)
      < (n + delta + logSlack cBound n : Nat))
    (hBoundSlack : logSlack cBound n + hereditarySlack cCore delta epsilon n ≤ S) :
    min (i + S) (finiteSetLogCard F) ≤ n + delta + 2 * S := by
  -- `hInteresting` + `hABound` give `i + hereditarySlack cCore ≤ n + delta + logSlack cBound n`,
  -- and `logSlack cBound n ≤ S` (from `hBoundSlack`), so `i ≤ n + delta + S`; hence
  -- `min (i+S) (log #F) ≤ i + S ≤ n + delta + 2*S`.  (The `i+S ≤ n+delta+S` bound is
  -- FALSE in general: `i < C(A)` only up to the `O(log n)` slack `logSlack cBound n`.)
  have h1 : i + hereditarySlack cCore delta epsilon n ≤ n + delta + logSlack cBound n := by
    exact_mod_cast (le_of_lt (ENat.coe_lt_coe.mp hInteresting))
  have h2 : min (i + S) (finiteSetLogCard F) ≤ i + S := Nat.min_le_left _ _
  omega


private lemma hereditary_family_from_plain_point
    (V T : Map) (hV : isOptimalConditional V) (hT : IsOptimalTotalConditional T) :
    ∃ cKappa cOut : Nat,
      ∀ x n A (hA : A.Nonempty) epsilon delta,
        x.length = n →
        IsMinimalModel V x A hA delta (logSlack cKappa n) →
        IsSufficientStatistic V x A hA epsilon →
        IsStrongSetModel T x A hA epsilon →
        IsNormalString V T x epsilon epsilon →
        ∀ i j, InPlainDescriptionProfile V (codedUniformOn A hA).code i j →
        ∃ F, ∃ hF : F.Nonempty,
          (codedUniformOn A hA).code ∈ F ∧
          IsStrongSetModel T (codedUniformOn A hA).code F hF
            (hereditarySlack cOut delta epsilon n) ∧
          plainSetComplexity V F hF ≤ (i + hereditarySlack cOut delta epsilon n : ENat) ∧
          plainSetComplexity V F hF + (finiteSetLogCard F : ENat) ≤
            ((i + j + hereditarySlack cOut delta epsilon n : Nat) : ENat) ∧
          min (i + hereditarySlack cOut delta epsilon n) (finiteSetLogCard F) ≤
            n + delta + 2 * hereditarySlack cOut delta epsilon n := by
  obtain ⟨cKappaCore, cCore, hCore⟩ := hereditary_family_core V T hV hT
  obtain ⟨cKappaBound, cBound, hBound⟩ :=
    minimalModel_plainSetComplexity_le V hV
  obtain ⟨cSingletonPlain, hSingletonPlain⟩ :=
    plainSetComplexity_singleton_le_plainK V hV
  obtain ⟨cSingletonStrong, hSingletonStrong⟩ :=
    singleton_isStrongSetModel T hT
  let cKappa := cKappaCore + cKappaBound
  let cOut :=
    cCore + 4 * cBound + 2 * cSingletonPlain + cSingletonStrong + 20
  refine ⟨cKappa, cOut, ?_⟩
  intro x n A hA epsilon delta hn hMinimal hSufficient hStrong hNormal i j hPlain
  have hMinCore :
      IsMinimalModel V x A hA delta (logSlack cKappaCore n) :=
    IsMinimalModel.mono le_rfl
      (logSlack_mono_left (by dsimp [cKappa]; omega) n) hMinimal
  have hMinBound :
      IsMinimalModel V x A hA delta (logSlack cKappaBound n) :=
    IsMinimalModel.mono le_rfl
      (logSlack_mono_left (by dsimp [cKappa]; omega) n) hMinimal
  have hABound := hBound x n A hA delta hn hMinBound
  have hCoreSlack : hereditarySlack cCore delta epsilon n ≤
      hereditarySlack cOut delta epsilon n :=
    hereditarySlack_mono_c (by dsimp [cOut]; omega)
  have hCoreSlackPlain :
      hereditarySlack cCore delta epsilon n + cSingletonPlain ≤
        hereditarySlack cOut delta epsilon n := by
    unfold hereditarySlack
    dsimp [cOut]
    nlinarith [Nat.zero_le delta,
      Nat.zero_le ((epsilon + (Nat.bits n).length) * Nat.sqrt n)]
  have hSingletonBudget : cSingletonStrong ≤
      hereditarySlack cOut delta epsilon n := by
    unfold hereditarySlack
    dsimp [cOut]
    omega
  by_cases hLchConditions : epsilon ≤ n ∧ epsilon * 2 < Nat.sqrt n
  · by_cases hInteresting :
        ((i + hereditarySlack cCore delta epsilon n : Nat) : ENat) <
          plainSetComplexity V A hA
    · obtain ⟨F, hF, hMem, hStrongF, hComp, hSum⟩ :=
        hCore x n A hA epsilon delta hn hMinCore hSufficient hStrong hNormal
          i j hLchConditions.1 hLchConditions.2 hInteresting hPlain
      have hBoundSlack :
          logSlack cBound n + hereditarySlack cCore delta epsilon n
            ≤ hereditarySlack cOut delta epsilon n := by
        have hbnP : (Nat.bits n).length ≤ (epsilon + (Nat.bits n).length) * Nat.sqrt n := by
          by_cases hn0 : n = 0
          · subst hn0; simp
          · have hsq : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr (Nat.zero_lt_of_ne_zero hn0)
            calc (Nat.bits n).length ≤ epsilon + (Nat.bits n).length := Nat.le_add_left _ _
              _ = (epsilon + (Nat.bits n).length) * 1 := (Nat.mul_one _).symm
              _ ≤ (epsilon + (Nat.bits n).length) * Nat.sqrt n := Nat.mul_le_mul_left _ hsq
        unfold hereditarySlack logSlack
        dsimp [cOut]
        nlinarith [Nat.zero_le delta, hbnP,
          Nat.zero_le ((epsilon + (Nat.bits n).length) * Nat.sqrt n),
          Nat.mul_le_mul_left cBound hbnP]
      have hIntTrans : ((i + hereditarySlack cCore delta epsilon n : Nat) : ENat)
          < (n + delta + logSlack cBound n : Nat) :=
        hInteresting.trans_le hABound
      refine ⟨F, hF, hMem, hStrongF.mono hCoreSlack, ?_, ?_,
        hereditary_min_shift_bound i n delta epsilon cBound cCore
          (hereditarySlack cOut delta epsilon n) F hIntTrans hBoundSlack⟩
      · exact hComp.trans (by exact_mod_cast
          (Nat.add_le_add_left hCoreSlack i))
      · exact hSum.trans (by exact_mod_cast
          (Nat.add_le_add_left hCoreSlack (i + j)))
    · push Not at hInteresting
      let y := (codedUniformOn A hA).code
      let F : Finset BitString := {y}
      let hF : F.Nonempty := Finset.singleton_nonempty y
      have hComp : plainSetComplexity V F hF ≤
          ((i + hereditarySlack cOut delta epsilon n : Nat) : ENat) := by
        calc
          plainSetComplexity V F hF
              ≤ plainK V y + (cSingletonPlain : ENat) := hSingletonPlain y
          _ = plainSetComplexity V A hA + (cSingletonPlain : ENat) := rfl
          _ ≤ ((i + hereditarySlack cCore delta epsilon n : Nat) : ENat) +
                (cSingletonPlain : ENat) := by gcongr
          _ ≤ ((i + hereditarySlack cOut delta epsilon n : Nat) : ENat) := by
                exact_mod_cast (show
                  i + hereditarySlack cCore delta epsilon n + cSingletonPlain ≤
                    i + hereditarySlack cOut delta epsilon n by omega)
      refine ⟨F, hF, by simp [F, y],
        (hSingletonStrong y).mono hSingletonBudget, hComp, ?_, ?_⟩
      · simpa [F] using hComp.trans (by exact_mod_cast
          (show i + hereditarySlack cOut delta epsilon n ≤
            i + j + hereditarySlack cOut delta epsilon n by omega))
      · have hFCardZero : finiteSetLogCard F = 0 := finiteSetLogCard_singleton y
        rw [hFCardZero]
        omega
  · push Not at hLchConditions
    let y := (codedUniformOn A hA).code
    let F : Finset BitString := {y}
    let hF : F.Nonempty := Finset.singleton_nonempty y
    have hFallbackNat :
        n + delta + logSlack cBound n + cSingletonPlain ≤
          i + hereditarySlack cOut delta epsilon n := by
      have hBits : (Nat.bits n).length ≤ n := length_natBits_le_self n
      have hcOne : 1 ≤ cOut := by dsimp [cOut]; omega
      have hcTwo : 2 ≤ cOut := by dsimp [cOut]; omega
      have hcBound : cBound + 2 ≤ cOut := by dsimp [cOut]; omega
      have hcConst : cBound + cSingletonPlain ≤ cOut := by
        dsimp [cOut]
        omega
      have hDeltaMul : delta ≤ cOut * delta :=
        Nat.le_mul_of_pos_left delta hcOne
      have hVariable :
          n + cBound * (Nat.bits n).length ≤
            cOut * (epsilon + (Nat.bits n).length) * Nat.sqrt n := by
        by_cases hn0 : n = 0
        · rw [hn0] at hBits ⊢
          have hBitsZero : (Nat.bits 0).length = 0 := by omega
          rw [hBitsZero]
          simp
        · have hsqrt : 1 ≤ Nat.sqrt n :=
            (Nat.sqrt_pos.2 (Nat.zero_lt_of_ne_zero hn0))
          have hBitsSqrt : (Nat.bits n).length ≤
              (Nat.bits n).length * Nat.sqrt n :=
            Nat.le_mul_of_pos_right _ hsqrt
          by_cases hEpsLe : epsilon ≤ n
          · have hSqrtLe : Nat.sqrt n ≤ 2 * epsilon :=
              by simpa [Nat.mul_comm] using hLchConditions hEpsLe
            have hnSqrt : n ≤ Nat.sqrt n * Nat.sqrt n + 2 * Nat.sqrt n := by
              have h := Nat.lt_succ_sqrt n
              nlinarith
            have hSquare : Nat.sqrt n * Nat.sqrt n ≤
                2 * epsilon * Nat.sqrt n :=
              Nat.mul_le_mul_right (Nat.sqrt n) hSqrtLe
            have hBitsPos : 1 ≤ (Nat.bits n).length := by
              have h_pos := Nat.size_pos.mpr (Nat.zero_lt_of_ne_zero hn0)
              have h_len := Nat.size_eq_bits_len n
              omega
            have hSqrtBits : Nat.sqrt n ≤
                (Nat.bits n).length * Nat.sqrt n :=
              Nat.le_mul_of_pos_left _ hBitsPos
            calc
              n + cBound * (Nat.bits n).length
                  ≤ (Nat.sqrt n * Nat.sqrt n + 2 * Nat.sqrt n) +
                    cBound * (Nat.bits n).length :=
                      Nat.add_le_add_right hnSqrt _
              _ ≤ (2 * epsilon * Nat.sqrt n + 2 * Nat.sqrt n) +
                    cBound * (Nat.bits n).length := by
                      exact Nat.add_le_add
                        (Nat.add_le_add hSquare le_rfl) le_rfl
              _ ≤ (2 * epsilon * Nat.sqrt n +
                    2 * ((Nat.bits n).length * Nat.sqrt n)) +
                    cBound * ((Nat.bits n).length * Nat.sqrt n) := by
                      exact Nat.add_le_add
                        (Nat.add_le_add le_rfl
                          (Nat.mul_le_mul_left 2 hSqrtBits))
                        (Nat.mul_le_mul_left cBound hBitsSqrt)
              _ = 2 * (epsilon * Nat.sqrt n) +
                    (cBound + 2) * ((Nat.bits n).length * Nat.sqrt n) := by
                      ring
              _ ≤ cOut * (epsilon * Nat.sqrt n) +
                    cOut * ((Nat.bits n).length * Nat.sqrt n) := by
                      exact Nat.add_le_add
                        (Nat.mul_le_mul_right _ hcTwo)
                        (Nat.mul_le_mul_right _ hcBound)
              _ = cOut * (epsilon + (Nat.bits n).length) * Nat.sqrt n := by
                    ring
          · have hneps : n < epsilon := Nat.lt_of_not_ge hEpsLe
            have hEpsSqrt : epsilon ≤ epsilon * Nat.sqrt n :=
              Nat.le_mul_of_pos_right _ hsqrt
            calc
              n + cBound * (Nat.bits n).length
                  ≤ epsilon + cBound * (Nat.bits n).length := by omega
              _ ≤ epsilon * Nat.sqrt n +
                    cBound * ((Nat.bits n).length * Nat.sqrt n) := by
                      gcongr
              _ ≤ cOut * (epsilon * Nat.sqrt n) +
                    cOut * ((Nat.bits n).length * Nat.sqrt n) := by
                      exact Nat.add_le_add
                        (Nat.le_mul_of_pos_left _ hcOne)
                        (Nat.mul_le_mul_right _ (by omega : cBound ≤ cOut))
              _ = cOut * (epsilon + (Nat.bits n).length) * Nat.sqrt n := by
                    ring
      unfold hereditarySlack logSlack
      calc
        n + delta + (cBound * (Nat.bits n).length + cBound) + cSingletonPlain
            = delta + (n + cBound * (Nat.bits n).length) +
                (cBound + cSingletonPlain) := by ring
        _ ≤ cOut * delta +
              cOut * (epsilon + (Nat.bits n).length) * Nat.sqrt n + cOut := by
              gcongr
        _ ≤ i + (cOut * delta +
              cOut * (epsilon + (Nat.bits n).length) * Nat.sqrt n + cOut) := by
              omega
    have hComp : plainSetComplexity V F hF ≤
        ((i + hereditarySlack cOut delta epsilon n : Nat) : ENat) := by
      calc
        plainSetComplexity V F hF
            ≤ plainK V y + (cSingletonPlain : ENat) := hSingletonPlain y
        _ = plainSetComplexity V A hA + (cSingletonPlain : ENat) := rfl
        _ ≤ ((n + delta + logSlack cBound n : Nat) : ENat) +
              (cSingletonPlain : ENat) := by
              push_cast
              exact add_le_add hABound le_rfl
        _ = ((n + delta + logSlack cBound n + cSingletonPlain : Nat) : ENat) := by
              norm_cast
        _ ≤ ((i + hereditarySlack cOut delta epsilon n : Nat) : ENat) := by
              exact_mod_cast hFallbackNat
    refine ⟨F, hF, by simp [F, y],
      (hSingletonStrong y).mono hSingletonBudget, hComp, ?_, ?_⟩
    · simpa [F] using hComp.trans (by exact_mod_cast
        (show i + hereditarySlack cOut delta epsilon n ≤
          i + j + hereditarySlack cOut delta epsilon n by omega))
    · have hFCardZero : finiteSetLogCard F = 0 := finiteSetLogCard_singleton y
      rw [hFCardZero]
      omega

lemma lemma_hereditary_strong_approximation
    (V T : Map) (hV : isOptimalConditional V) (hT : IsOptimalTotalConditional T) :
    ∃ cKappa cNormal : Nat,
      ∀ x n A (hA : A.Nonempty) epsilon delta,
        x.length = n →
        IsStrongSetModel T x A hA epsilon →
        IsSufficientStatistic V x A hA epsilon →
        IsNormalString V T x epsilon epsilon →
        IsMinimalModel V x A hA delta (logSlack cKappa n) →
        ∀ i j, InPlainDescriptionProfile V (codedUniformOn A hA).code i j →
        ∃ i' j', InStrongDescriptionProfile V T (codedUniformOn A hA).code
            (hereditarySlack cNormal delta epsilon n) i' j' ∧
          natPairLInfDistance (i, j) (i', j') ≤ hereditarySlack cNormal delta epsilon n := by
  obtain ⟨cKappa, cOut, hFamily⟩ := hereditary_family_from_plain_point V T hV hT
  obtain ⟨cShift, hShift⟩ := inStrongDescriptionProfile_of_strong_model_params V T hV hT
  obtain ⟨cNormal, hAbsorb⟩ := hereditary_shift_slack_absorb cOut cShift
  refine ⟨cKappa, cNormal, ?_⟩
  intro x n A hA epsilon delta hn hStrong hSuff hNormal hMin i j hPlain
  obtain ⟨F, hF, hMem, hStrongF, hComp, hSum, hCard⟩ :=
    hFamily x n A hA epsilon delta hn hMin hSuff hStrong hNormal i j hPlain
  -- The strong-description shift is charged against `min (i+S) (log #F)`, and the
  -- honest hereditary bound `hCard : min (i+S) (log #F) ≤ n + delta + 2*S` lets us
  -- absorb it into a single slack via `hereditary_shift_slack_absorb`.
  have hAbsorbF := hAbsorb delta epsilon n
    (min (i + hereditarySlack cOut delta epsilon n) (finiteSetLogCard F)) hCard
  obtain ⟨i', j', hProf, hDist⟩ :=
    hShift (codedUniformOn A hA).code F hMem
      (hereditarySlack cOut delta epsilon n) (i + hereditarySlack cOut delta epsilon n) j hStrongF
      hComp (by exact_mod_cast
        (show (i + hereditarySlack cOut delta epsilon n : Nat) + j
          = i + j + hereditarySlack cOut delta epsilon n by omega) ▸ hSum)
  refine ⟨i', j', hProf.mono_epsilon hAbsorbF, ?_⟩
  unfold natPairLInfDistance at hDist ⊢
  omega

theorem thm_hereditary
    (V T : Map)
    (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ThmHereditaryStatement V T := by
  obtain ⟨cKappa, cNormal, hApprox⟩ := lemma_hereditary_strong_approximation V T hV hT
  refine ⟨cKappa, cNormal, ?_⟩
  intro x n A hA epsilon delta hn hStrong hSuff hNormal hMin
  apply normality_of_plain_to_strong_nearby
  intro i j hPlain
  exact hApprox x n A hA epsilon delta hn hStrong hSuff hNormal hMin i j hPlain

end Kolmogorov
