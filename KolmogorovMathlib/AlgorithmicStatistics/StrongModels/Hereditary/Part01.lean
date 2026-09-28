import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.HereditaryLift
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FamilyStep.Filtered
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FamilyStep.PlainTotal
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Lemma4Support
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.OrdinalPlainRandomness
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FamilyStep
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LchLemma
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PropMinHereditary

/-!
# Transport and intersection lemmas for the hereditary theorem

The two mechanisms the proof of `thm_hereditary` runs on.

*Transport along a total equivalence.*  `strong_model_of_totalEquivalentWithin` and
`inStrongDescriptionProfile_of_totalEquivalentWithin` move a strong model, respectively a
strong profile point, from a string to a total-equivalent one, at the strength budget
`hereditaryStrongTransportStrength`; `normality_transport_of_profile_neighborhoods`,
`normality_of_plain_to_strong_nearby` and `normality_of_totalEquivalentWithin` do the same for
normality, the last two being the forms the main theorem calls.

*Intersecting a model with a partition member.*  `hereditaryIntersectionCode` is the canonical
code of an intersection, computable (`hereditaryIntersectionCode_computable`) and correct on
uniform codes (`hereditaryIntersectionCode_eq`); `hereditaryIntersectionDecompressor`
post-composes a decompressor with it, so a program for `M` given `A` also describes `A ∩ M`.
`hereditary_sufficiency_intersection_lower_bound`,
`partition_member_totalCondK_of_logCard_gap` and
`inStrongDescriptionProfile_of_strong_model_params` are the quantitative consequences, and
`budget_add3_pow` and its neighbours the calculus of polynomial slack budgets they use.
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


/-- Strong description profiles transport along total equivalence: if `y` is `epsilon`-equivalent
to `x` for the total machine `T`, a strong profile point `(i, j)` of `x` is a profile point
`(i + 2 * epsilon + c, j)` of `y`, at a strength weakened by `epsilon`. -/
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

/-- The code transformer taking two set codes to the code of the intersection is computable. -/
theorem hereditaryIntersectionCode_computable :
    Computable hereditaryIntersectionCode := by
  exact (canonicalImageCodeOfList_primrec.comp
    partitionIntersectionPointList_primrec).to_comp

/-- On codes of uniform distributions on `A` and `M`, the intersection transformer returns the
code of the uniform distribution on `A ∩ M`. -/
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

/-- Post-composing a decompressor with the intersection transformer yields a decompressor. -/
theorem hereditaryIntersectionDecompressor_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (hereditaryIntersectionDecompressor V) := by
  unfold hereditaryIntersectionDecompressor
  exact Partrec.map hV
    (hereditaryIntersectionCode_computable.comp
      ((Computable.snd.comp Computable.fst).pair Computable.snd))

/-- If `p` describes the code of `M` given the code of `A` under `V`, the same program describes
the code of `A ∩ M` given `A` under the intersection decompressor. -/
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

/-- The partition selector in `FamilyStep` is usually consumed after a
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

/-- If `F` is a `strength`-strong model for `y` whose plain set complexity is at most `i` and
whose complexity plus log-cardinality is at most `i + j`, then the strong description profile of
`y` contains a point within `logSlack c (log #F)` of `(i, j)`, at strength
`strength + logSlack c (log #F)`.  The slack is the address cost of shrinking `F` to
log-cardinality `j` (SUV `thm:hereditary`, via `prop:description-shift-1`). -/
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

/-! ### A small calculus of polynomial slack budgets

The final assembly has to absorb a bounded number of nested constants into the
single uniform budget `hereditarySlack cOut delta epsilon n = cOut * U`, where
`U = delta + (epsilon + log n) * sqrt n + 1`.  Every intermediate quantity is
bounded by `cBase ^ k * U` for an explicit `k`, and the following four lemmas
are the only combination steps needed. -/

private lemma budget_add3_pow {b U a1 a2 a3 k : Nat} (hb : 3 ≤ b)
    (h1 : a1 ≤ b ^ k * U) (h2 : a2 ≤ b ^ k * U) (h3 : a3 ≤ b ^ k * U) :
    a1 + a2 + a3 ≤ b ^ (k + 1) * U := by
  have h : 3 * (b ^ k * U) ≤ b ^ (k + 1) * U := by
    calc 3 * (b ^ k * U) ≤ b * (b ^ k * U) := Nat.mul_le_mul_right _ hb
      _ = b ^ (k + 1) * U := by ring
  omega

end Kolmogorov
