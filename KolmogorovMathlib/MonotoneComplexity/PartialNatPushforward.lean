import KolmogorovMathlib.MonotoneComplexity.PartialNatMap
import KolmogorovMathlib.MonotoneComplexity.ProbabilisticGenerator
import KolmogorovMathlib.MonotoneComplexity.SemimeasureRealization
import KolmogorovMathlib.MonotoneComplexity.EffectiveOpen
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.MonotoneComplexity.REClosure
import Mathlib.Computability.Primrec.List
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Pushing a probabilistic generator forward along a partial map

Composing a generator on streams with a computable partial map to `ℕ` produces a discrete
semimeasure on the outputs: `partialNatPushGraph` is the lower graph of the composite and
`partialNatPushforwardMass` the mass of an output. The composite graph is again recursively
enumerable (`partialNatPushGraph_isRE`), continuity makes the open sets at distinct outputs
disjoint (`partialNatPushGraph_cantorOpen_pairwise_disjoint`) and hence the masses summable
(`tsum_partialNatPushforwardMass_le_one`). Applying this to a generator realising the a priori
probability gives `exists_const_KPPlain_natBits_le_KA`: the prefix complexity of the value of a
computable partial map is at most the a priori complexity of its argument, up to a constant.
-/

open scoped ENNReal
open MeasureTheory

namespace Kolmogorov

/-- The lower graph of the composite that runs the generator and then applies the partial map `f`,
relating a program to the binary digits of the number `f` outputs. -/
def partialNatPushGraph (G_lowerGraph : BitString → BitString → Prop)
    (f : BitStream → Option ℕ) (p : BitString) (z : BitString) : Prop :=
  ∃ (x : BitString) (n : ℕ), G_lowerGraph p x ∧ f (.finite x) = some n ∧ z = Nat.bits n

/-- The mass that the generator, pushed forward along the partial map `f`, assigns to the string
`z`. -/
noncomputable def partialNatPushforwardMass (G_lowerGraph : BitString → BitString → Prop)
    (f : BitStream → Option ℕ) (z : BitString) : ℝ≥0∞ :=
  cantorOpenMass (partialNatPushGraph G_lowerGraph f) z

/-- Pushing a recursively enumerable lower graph forward along a computable partial map gives a
recursively enumerable graph. -/
lemma partialNatPushGraph_isRE {G_lowerGraph : BitString → BitString → Prop}
    (hG : IsRE fun q : BitString × BitString => G_lowerGraph q.1 q.2)
    {f : BitStream → Option ℕ} (hf : IsComputablePartialNatMap f) :
    IsRE fun q : BitString × BitString => partialNatPushGraph G_lowerGraph f q.1 q.2 := by
  let P := fun (p : (BitString × BitString) × (BitString × ℕ)) =>
      G_lowerGraph p.1.1 p.2.1 ∧ partialNatLowerGraph f p.2.1 p.2.2 ∧ p.1.2 = Nat.bits p.2.2
  have h_base : IsRE P := by
    dsimp [P]
    refine IsRE.and ?_ ?_
    · exact hG.comp_computable
        (Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.fst.comp Computable.snd))
    · refine IsRE.and ?_ ?_
      · exact hf.2.comp_computable Computable.snd
      · have h_pred : PrimrecPred
            (fun (p : (BitString × BitString) × BitString × ℕ) =>
              p.1.2 = Nat.bits p.2.2) := by
          have h1 : Primrec
              (fun (p : (BitString × BitString) × BitString × ℕ) =>
                p.1.2) :=
            Primrec.snd.comp Primrec.fst
          have h2 : Primrec
              (fun (p : (BitString × BitString) × BitString × ℕ) =>
                Nat.bits p.2.2) :=
            primrec_natBits.comp (Primrec.snd.comp Primrec.snd)
          exact PrimrecRel.comp Primrec.eq h1 h2
        obtain ⟨inst, h_prim⟩ := h_pred
        exact isRE_of_computable_bool _
          (fun p => @decide _ (inst p))
          (fun p => decide_eq_true_iff) h_prim.to_comp
  have h_ex : IsRE (fun (q : BitString × BitString) => ∃ (xn : BitString × ℕ), P (q, xn)) :=
    IsRE.exists_encodable h_base
  apply IsRE.of_iff h_ex
  intro q
  simp only [partialNatPushGraph, P]
  constructor
  · rintro ⟨xn, h1, h2, h3⟩
    exact ⟨xn.1, xn.2, h1, h2, h3⟩
  · rintro ⟨x, n, h1, h2, h3⟩
    exact ⟨(x, n), h1, h2, h3⟩

/-- Inputs producing `x` produce, after applying `f`, the digits of `f x`, so their open set sits
inside the pushed-forward one. -/
lemma cantorOpen_generator_subset_partialNatPushGraph
    {G : ProbabilisticGenerator} {f : BitStream → Option ℕ}
    {x : BitString} {n : ℕ} (hfx : f (.finite x) = some n) :
    cantorOpen G.lowerGraph x ⊆ cantorOpen (partialNatPushGraph G.lowerGraph f) (Nat.bits n) := by
  intro w hw
  simp only [cantorOpen, Set.mem_iUnion] at hw ⊢
  rcases hw with ⟨p, hp, hw⟩
  exact ⟨p, ⟨x, n, hp, hfx, rfl⟩, hw⟩

/-- For a continuous partial map the open sets of the pushforward at distinct outputs are disjoint.
-/
lemma partialNatPushGraph_cantorOpen_pairwise_disjoint
    {G : ProbabilisticGenerator} {f : BitStream → Option ℕ} (hf : IsContinuousPartialNatMap f) :
    Pairwise (fun z1 z2 =>
      Disjoint (cantorOpen (partialNatPushGraph G.lowerGraph f) z1)
        (cantorOpen (partialNatPushGraph G.lowerGraph f) z2)) := by
  intro z1 z2 hz
  rw [Set.disjoint_iff_forall_ne]
  intro s h1 t h2 hst
  subst hst
  simp only [cantorOpen, Set.mem_iUnion] at h1 h2
  rcases h1 with ⟨p1, hp1_graph, hs1⟩
  rcases h2 with ⟨p2, hp2_graph, hs2⟩
  simp only [partialNatPushGraph] at hp1_graph hp2_graph
  rcases hp1_graph with ⟨x1, n1, h1_G, h1_f, h1_eq⟩
  rcases hp2_graph with ⟨x2, n2, h2_G, h2_f, h2_eq⟩
  have H1 : G.output s ∈ bitStreamCylinder x1 := G.lowerGraph_sound h1_G hs1
  have H2 : G.output s ∈ bitStreamCylinder x2 := G.lowerGraph_sound h2_G hs2
  have h_comp : x1 <+: x2 ∨ x2 <+: x1 := by
    by_contra h_not
    rw [not_or] at h_not
    have h_disj := bitStreamCylinder_disjoint_of_incompatible h_not.1 h_not.2
    exact Set.disjoint_iff.mp h_disj ⟨H1, H2⟩
  rcases h_comp with h_comp | h_comp
  · have h_eq := hf.value_unique_of_compatible h_comp (List.prefix_refl x2) h1_f h2_f
    subst h_eq
    rw [h1_eq, h2_eq] at hz
    exact hz rfl
  · have h_eq := hf.value_unique_of_compatible (List.prefix_refl x1) h_comp h1_f h2_f
    subst h_eq
    rw [h1_eq, h2_eq] at hz
    exact hz rfl

/-- The pushforward masses over all outputs sum to at most `1`, so they form a discrete semimeasure.
-/
lemma tsum_partialNatPushforwardMass_le_one
    {G : ProbabilisticGenerator} {f : BitStream → Option ℕ} (hf : IsContinuousPartialNatMap f) :
    ∑' z, partialNatPushforwardMass G.lowerGraph f z ≤ 1 := by
  have h_meas : ∀ z, MeasurableSet (cantorOpen (partialNatPushGraph G.lowerGraph f) z) := fun z =>
    IsOpen.measurableSet (isOpen_cantorOpen (partialNatPushGraph G.lowerGraph f) z)
  have h_disj := partialNatPushGraph_cantorOpen_pairwise_disjoint (G := G) hf
  have h_sum : ∑' z, partialNatPushforwardMass G.lowerGraph f z =
      uniformMeasure
        (⋃ z, cantorOpen (partialNatPushGraph G.lowerGraph f) z) := by
    exact (measure_iUnion h_disj h_meas).symm
  rw [h_sum]
  exact prob_le_one

/-- If the generator realises the universal continuous semimeasure then the pushforward mass of the
digits of `f x` is at least the a priori mass of `x`. -/
lemma universalContinuousSemimeasure_le_partialNatPushforwardMass
    {G : ProbabilisticGenerator} (hG : generatedTreeSemimeasure G = universalContinuousSemimeasure)
    {f : BitStream → Option ℕ}
    {x : BitString} {n : ℕ} (hfx : f (.finite x) = some n) :
    universalContinuousSemimeasure x ≤ partialNatPushforwardMass G.lowerGraph f (Nat.bits n) := by
  have h_meas_eq : universalContinuousSemimeasure x = generatedTreeSemimeasure G x := by
    rw [← hG]
  rw [h_meas_eq]
  have h_gen : generatedTreeSemimeasure G x = uniformMeasure (cantorOpen G.lowerGraph x) := by
    change generatedTreeSemimeasure G x = _
    rw [generatedTreeSemimeasure, preimage_bitStreamCylinder_eq_cantorOpen]
  rw [h_gen]
  change uniformMeasure (cantorOpen G.lowerGraph x) ≤
    uniformMeasure (cantorOpen (partialNatPushGraph G.lowerGraph f) (Nat.bits n))
  apply measure_mono
  exact cantorOpen_generator_subset_partialNatPushGraph hfx

/-- For a computable partial map from streams to naturals, the prefix complexity of the output is at
most the a priori complexity of the input plus a constant. -/
theorem exists_const_KPPlain_natBits_le_KA
    (U : Map) (hU : IsOptimalPrefixConditional U)
    {f : BitStream → Option ℕ} (hf : IsComputablePartialNatMap f) :
    ∃ c : ℝ, ∀ (x : BitString) (n : ℕ), f (.finite x) = some n →
      ((KPPlain U (Nat.bits n)).toNat : ℝ) ≤ KA x + c := by
  -- Step 1: Realize the universal continuous semimeasure by a probabilistic generator
  obtain ⟨G, hG⟩ :=
    exists_probabilisticGenerator_generatedTreeSemimeasure_eq
      universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure
  have hG_eq : generatedTreeSemimeasure G = universalContinuousSemimeasure :=
    funext hG
  -- Step 2: The pushforward mass is lower semicomputable (IsLSC) and sums to ≤ 1
  have h_isRE := partialNatPushGraph_isRE G.lowerGraph_re hf
  have h_lsc : IsLSC fun z _ => partialNatPushforwardMass G.lowerGraph f z :=
    cantorOpenMass_isLSC h_isRE
  have h_sum : ∀ ctx : BitString,
      ∑' z, (fun z _ => partialNatPushforwardMass G.lowerGraph f z) z ctx ≤ 1 :=
    fun _ => tsum_partialNatPushforwardMass_le_one hf.1
  -- Step 3: Kraft-Chaitin realization
  obtain ⟨M', hM', c₀, hc₀⟩ := kraftChaitin_realization_bound_unit h_lsc h_sum
  -- Step 4: Optimality/invariance of U
  obtain ⟨cI, hI⟩ := hU.invariance hM'
  -- Step 5: Assemble the additive bound
  refine ⟨((c₀ + cI : ℕ) : ℝ), fun x n hfx => ?_⟩
  -- The realization gives:
  -- 2⁻¹^c₀ * pushMass(Nat.bits n) ≤ complexityWeight(KP M' (Nat.bits n) [])
  have h1 := hc₀ (Nat.bits n) []
  -- Domination: universalContinuousSemimeasure x ≤ pushMass(Nat.bits n)
  have h_dom := universalContinuousSemimeasure_le_partialNatPushforwardMass hG_eq hfx
  -- Invariance: KP U (Nat.bits n) [] ≤ KP M' (Nat.bits n) [] + cI
  have h2 : complexityWeight (KP M' (Nat.bits n) [] + (cI : ENat)) ≤
      complexityWeight (KP U (Nat.bits n) []) :=
    complexityWeight_le_of_le (hI (Nat.bits n) [])
  rw [complexityWeight_add_nat] at h2
  -- Chain: 2⁻¹^(c₀+cI) * a(x) ≤ complexityWeight(KPPlain U (Nat.bits n))
  have hkey : (2 : ℝ≥0∞)⁻¹ ^ (c₀ + cI) * universalContinuousSemimeasure x ≤
      complexityWeight (KPPlain U (Nat.bits n)) := by
    change _ ≤ complexityWeight (KP U (Nat.bits n) [])
    calc
      (2 : ℝ≥0∞)⁻¹ ^ (c₀ + cI) * universalContinuousSemimeasure x
          = ((2 : ℝ≥0∞)⁻¹ ^ c₀ * universalContinuousSemimeasure x)
              * (2 : ℝ≥0∞)⁻¹ ^ cI := by
            rw [pow_add]; ring
      _ ≤ ((2 : ℝ≥0∞)⁻¹ ^ c₀ * partialNatPushforwardMass G.lowerGraph f (Nat.bits n)) *
            (2 : ℝ≥0∞)⁻¹ ^ cI := by gcongr
      _ ≤ complexityWeight (KP M' (Nat.bits n) []) * (2 : ℝ≥0∞)⁻¹ ^ cI := by gcongr
      _ ≤ complexityWeight (KP U (Nat.bits n) []) := h2
  exact toNat_le_KA_add_of_complexityWeight_ge x _ _ hkey

end Kolmogorov
