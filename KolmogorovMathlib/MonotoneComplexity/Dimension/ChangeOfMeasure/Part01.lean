



/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.Basic
import KolmogorovMathlib.MonotoneComplexity.Dimension.AbsolutelyNonRandom
import KolmogorovMathlib.MonotoneComplexity.Dimension.ImageMeasure
import KolmogorovMathlib.MonotoneComplexity.Dimension.EffectiveNullDiff
import KolmogorovMathlib.MonotoneComplexity.Dimension.DeficiencySemimeasure
import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint
import KolmogorovMathlib.MonotoneComplexity.Dimension.ArithMeasurePreserving
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Infra
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria
import KolmogorovMathlib.MonotoneComplexity.GeneratorComposition
import KolmogorovMathlib.MonotoneComplexity.SemimeasureRealization
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.MonotoneComplexity.ContinuousStreamMap
import KolmogorovMathlib.AlgorithmicRandomness.ExpectationBounded
import KolmogorovMathlib.MonotoneComplexity.ExpectationBoundedDeficiency
import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations

/-!
# Randomness with respect to different measures (SUV §5.9, pp. 176-185)

This module renders §5.9.1 (changing the measure, Theorem 121), §5.9.2
("absolutely non-random sequences", Theorem 122 and the a priori randomness
deficiency of finite strings) and §5.9.3 (image randomness, Lemma 1,
Theorem 123, Lemma 2, Theorem 124).

## Source definitions rendered here

* (p. 176) *atomless measure*: every individual sequence has measure `0`.
* (p. 177) *a priori randomness deficiency of a finite string* with respect to a
  computable measure `P`:  `d_P(x) = -log₂ P(Ω_x) - KA(x)`, with the source
  convention `d_P(x) = +∞` when `P(Ω_x) = 0` (p. 178).
* (p. 181) the *image measure* `ν(U) = μ(f⁻¹(U))` of a computable measure `μ`
  under a computable continuous map `f : Σ → Σ`, under the source's standing
  assumption that `ν` is a measure on `Ω` (not merely a semimeasure).
* (§3.5, named here) *maximal expectation-bounded randomness test*, the
  conclusion of Theorem 42, whose binary logarithm is the expectation-bounded
  deficiency of an infinite sequence used by Problem 185.

## Rendering decisions (do not change without re-reading the source)

* `deficiency` is `EReal`-valued, so that the source's `+∞` convention for
  `P(Ω_x) = 0` is expressed rather than replaced by a junk real value.  The
  finite-valued statements (Theorem 124, Problem 187) therefore quantify over
  the real value `d` with `deficiency P x = (d : EReal)`; the infinite case of
  Theorem 124 is the separate, proved `deficiency_eq_top_of_prefix`.
* `log` is the *binary* logarithm `Real.logb 2` throughout, as in the source.
* **Convention for `log d` on a deficiency `d` (Theorem 124 and Problem 187).**
  Both statements are quantified over `1 ≤ d`.  `Real.logb 2 d = 0` for `d ≤ 0`
  in Mathlib, and for `0 < d < 1` the term `-2 log d` is *positive*, so an
  unrestricted `d` would silently assert something strictly stronger than the
  source's asymptotic `d_P(y) ≥ d_P(x) - 2 log d_P(x) - c`.  The source's own
  proof (p. 184) runs over integers `k ≥ 1` ("for each `k` consider … deficiency
  greater than `k`", `S = ∑_k (1/(2k²)) P_k`, `-log S(x) ≤ -log P(x) - k +
  2 log k + O(1)`), i.e. it only ever applies the bound at `d ≥ 1`; the small-`d`
  range is absorbed by the constant `c`, which is the meaning of the `O(1)`.
  Theorem 124 and Problem 187 use the *same* convention -- the book's hint to
  Problem 187 calls it "a generalization of Theorem 124" (p. 185).
* Theorem 121 is stated for *computable* atomless measures.  The displayed
  statement on p. 176 says only "two atomless measures", but the paragraph
  introducing it ("If `μ₁` and `μ₂` are two computable atomless measures") and
  the proof both use computability, and the conclusion is false without it.
* `Σ → Σ` maps of the source are `BitStream → BitStream`; `Σ_u` is the set of
  finite-or-infinite extensions of `u`, whereas `Ω_u` is `cantorCylinder u`.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ## §5.9.1 Changing the measure -/

/-- **SUV §5.9.1, p. 176.** A measure is *atomless* if each individual sequence
has measure zero. -/
def IsAtomlessMeasure (μ : Measure CantorSeq) : Prop :=
  ∀ w : CantorSeq, μ {w} = 0

/-! ### Stream maps compose -/

/-- A finite lower bound of `g S` is already a lower bound of `g` at a finite
approximation of `S`. -/
lemma exists_finite_le_of_finite_le_apply {g : BitStream → BitStream}
    (hg : IsContinuousStreamMap g) (S : BitStream) (z : BitString)
    (hz : BitStream.finite z ≤ g S) :
    ∃ a : BitString, BitStream.finite a ≤ S ∧ BitStream.finite z ≤ g (BitStream.finite a) := by
  cases S with
  | finite s => exact ⟨s, le_refl _, hz⟩
  | infinite v =>
      obtain ⟨m, hm⟩ := (continuousStreamMap_finite_le_infinite_iff g hg v z).1 hz
      exact ⟨cantorPrefix v m, BitStream.finite_cantorPrefix_le_infinite v m, hm⟩

/-- The lower graph of a composition. -/
lemma streamLowerGraph_comp {f g : BitStream → BitStream} (hg : IsContinuousStreamMap g)
    (x z : BitString) :
    streamLowerGraph (fun s => g (f s)) x z ↔
      ∃ a : BitString, streamLowerGraph f x a ∧ streamLowerGraph g a z := by
  constructor
  · intro h
    obtain ⟨a, ha, hza⟩ := exists_finite_le_of_finite_le_apply hg (f (BitStream.finite x)) z h
    exact ⟨a, ha, hza⟩
  · rintro ⟨a, ha, hza⟩
    exact le_trans hza (hg.1 ha)

/-- Continuous stream maps compose. -/
lemma IsContinuousStreamMap.comp {f g : BitStream → BitStream}
    (hg : IsContinuousStreamMap g) (hf : IsContinuousStreamMap f) :
    IsContinuousStreamMap (fun s => g (f s)) := by
  refine ⟨fun s t hst => hg.1 (hf.1 hst), ?_⟩
  intro w y hy
  rw [BitStream.le_iff_forall_finite_le]
  intro z hz
  obtain ⟨a, ha, hza⟩ := exists_finite_le_of_finite_le_apply hg (f (BitStream.infinite w)) z hz
  obtain ⟨n, hn⟩ := (continuousStreamMap_finite_le_infinite_iff f hf w a).1 ha
  exact le_trans (le_trans hza (hg.1 hn)) (hy n)

/-- Computable stream maps compose. -/
lemma IsComputableStreamMap.comp {f g : BitStream → BitStream}
    (hg : IsComputableStreamMap g) (hf : IsComputableStreamMap f) :
    IsComputableStreamMap (fun s => g (f s)) := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  have hfst : Computable fun q : (BitString × BitString) × BitString => (q.1.1, q.2) :=
    Computable.pair (Computable.fst.comp Computable.fst) Computable.snd
  have hsnd : Computable fun q : (BitString × BitString) × BitString => (q.2, q.1.2) :=
    Computable.pair Computable.snd (Computable.snd.comp Computable.fst)
  have h1 : IsRE fun q : (BitString × BitString) × BitString =>
      streamLowerGraph f q.1.1 q.2 := hf.2.comp_computable hfst
  have h2 : IsRE fun q : (BitString × BitString) × BitString =>
      streamLowerGraph g q.2 q.1.2 := hg.2.comp_computable hsnd
  have hand : IsRE fun q : (BitString × BitString) × BitString =>
      streamLowerGraph f q.1.1 q.2 ∧ streamLowerGraph g q.2 q.1.2 := h1.and h2
  exact (IsRE.exists_encodable hand).of_iff fun p => (streamLowerGraph_comp hg.1 p.1 p.2).symm

/-! ### Theorem 121

Stated and proved at the end of this module, under `§5.9.1 concluded`, after
Theorem 123(a) of §5.9.3, which its proof uses.  There is no circularity: §5.9.3
nowhere uses Theorem 121. -/

/-! ## §5.9.2 A priori randomness deficiency of finite strings -/

/-- **SUV §5.9.2, pp. 177-178.** The a priori randomness deficiency of a finite
string `x` with respect to a measure `P`:

`d_P(x) = -log₂ P(Ω_x) - KA(x)`,

with the source's convention `d_P(x) = +∞` when `P(Ω_x) = 0`. -/
noncomputable def deficiency (P : Measure CantorSeq) (x : BitString) : EReal :=
  if cantorMass P x = 0 then ⊤
  else ((-Real.logb 2 (cantorMass P x).toReal - KA x : ℝ) : EReal)

/-- The deficiency is infinite exactly on the null cylinders (SUV p. 178). -/
@[simp] lemma deficiency_eq_top_iff (P : Measure CantorSeq) (x : BitString) :
    deficiency P x = ⊤ ↔ cantorMass P x = 0 := by
  unfold deficiency
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun hc => absurd hc (EReal.coe_ne_top _), fun hc => absurd hc h⟩

/-- The finite value of the deficiency on a cylinder of positive measure. -/
lemma deficiency_of_ne_zero {P : Measure CantorSeq} {x : BitString}
    (h : cantorMass P x ≠ 0) :
    deficiency P x = ((-Real.logb 2 (cantorMass P x).toReal - KA x : ℝ) : EReal) := by
  unfold deficiency
  exact ite_eq_right h

/-- **SUV §5.9.2, p. 184** (the infinite case of Theorem 124): "if `P(Ω_x) = 0`,
then `P(Ω_y) = 0` for any `y` that has prefix `x`, and the deficiency of `y` is
also infinite". -/
lemma deficiency_eq_top_of_prefix (P : Measure CantorSeq) {x y : BitString} (hxy : x <+: y)
    (hx : deficiency P x = ⊤) : deficiency P y = ⊤ := by
  rw [deficiency_eq_top_iff] at hx ⊢
  have hle : cantorMass P y ≤ cantorMass P x := by
    simp only [cantorMass]
    exact measure_mono (cantorCylinder_subset_of_prefix hxy)
  rw [hx] at hle
  exact le_antisymm hle (zero_le)

/-! ## §5.9.3 Image randomness -/

/-- **SUV §5.9.3, p. 181.** `ν` is the image of `μ` under the computable
continuous map `f : Σ → Σ`, i.e. `ν(U) = μ(f⁻¹(U))`, expressed on the
generating intervals: for every string `u`,

`ν(Ω_u) = μ {ω | u ⪯ f(ω)}`,

the right-hand side being the `μ`-measure of `f⁻¹(Σ_u)` (`Σ_u` is the set of
finite-or-infinite extensions of `u`).  Requiring `ν` to be a genuine
(probability) measure on `Ω` with these interval masses is exactly the source's
standing assumption that the image is a measure and not merely a lower
semicomputable semimeasure.

*Relation to `MeasureTheory.Measure.map`* (freeze audit remark).  On the domain
where `f` maps into infinite sequences -- which is a set of full `μ`-measure
under the source's standing assumption, since otherwise the image is only a
semimeasure -- this condition is equivalent to `ν = Measure.map f̂ μ` for the
induced map `f̂ : CantorSeq → CantorSeq`, because the cylinders generate the
Borel σ-algebra and the interval masses determine a measure on `Ω` uniquely
(`cantorMeasure_unique`).  That equivalence is **not** needed by any statement
in this file: every theorem below uses only the interval masses, and the
`Measure.map` form would additionally require the measurability bookkeeping for
`f̂` and a name for the full-measure domain. -/
def IsImageMeasure (μ : Measure CantorSeq) (f : BitStream → BitStream)
    (ν : Measure CantorSeq) : Prop :=
  ∀ u : BitString,
    cantorMass ν u = μ {w : CantorSeq | BitStream.finite u ≤ f (BitStream.infinite w)}

/-- **SUV §5.9.3, p. 181.** "It is easy to see that in this case `ν` is a
computable measure."

The proof is the reduction recorded by the previous round: the interval masses of
`ν` are the `μ`-masses of the effectively open preimages `f^{-1}(Σ_u)`
(`setOf_le_comp_eq_cantorOpen`), hence lower semicomputable
(`cantorOpenMass_isLSC_of_isComputableMeasure`); they are exact
(`cantorMass_add`) and normalized (`cantorMass_nil`), so SUV Theorem 77(b)
(`exists_isComputableMeasure_of_isLowerSemicomputableContinuousSemimeasure`)
produces a computable measure with those interval masses, which is `ν` itself by
`cantorMeasure_unique`. -/
theorem isComputableMeasure_of_isImageMeasure {μ ν : Measure CantorSeq}
    {f : BitStream → BitStream} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsComputableMeasure μ) (hf : IsComputableStreamMap f)
    (hν : IsImageMeasure μ f ν) : IsComputableMeasure ν := by
  have hmass : ∀ u : BitString, cantorMass ν u = μ (cantorOpen (streamLowerGraph f) u) := by
    intro u
    rw [hν u, setOf_le_comp_eq_cantorOpen hf.1 u]
  have hfun : (fun (u : BitString) (_ : BitString) => cantorMass ν u)
      = fun (u : BitString) (_ : BitString) => μ (cantorOpen (streamLowerGraph f) u) := by
    funext u _
    exact hmass u
  have hlsc : IsLSC (fun (u : BitString) (_ : BitString) => cantorMass ν u) := by
    rw [hfun]
    exact cantorOpenMass_isLSC_of_isComputableMeasure hμ hf.2
  have hcont : IsContinuousTreeSemimeasure (cantorMass ν) :=
    ⟨cantorMass_nil ν, fun x => le_of_eq (cantorMass_add ν x).symm⟩
  obtain ⟨ρ, hρcomp, hρmass⟩ :=
    exists_isComputableMeasure_of_isLowerSemicomputableContinuousSemimeasure
      ⟨hcont, hlsc⟩ (fun x => cantorMass_add ν x)
  have : IsProbabilityMeasure ρ := by
    constructor
    have h0 := hρmass ([] : BitString)
    rw [cantorMass_nil ν] at h0
    rw [← cantorCylinder_nil]
    exact h0
  have hEq : ρ = ν := cantorMeasure_unique ρ ν hρmass
  rwa [hEq] at hρcomp

/-- **SUV Lemma 1 of §5.9.3 (p. 182).** Let `μ` be a computable measure on `Ω`
and let `U ⊆ V` be two effectively open sets with `μ(V \ U) = 0`.  Then `V \ U`
is an effectively null set (so it contains no random sequences).

The source remarks that effective openness of `V` is not used; only the stated
form is asserted here.

The proof is the source's, with the machinery in `Dimension/EffectiveNullDiff.lean`:
`V` is a countable union of intervals `Ω_v`, so it suffices to cover each
`Ω_v \ U` uniformly (`IsUniformlyEffectivelyNull.isEffectivelyNull_iUnion`), and
`diffCover` is that cover: the union of the *certified* stages `diffStage`, the
source's "remaining part of the interval `I`" after finitely many steps of the
enumeration of `U`. -/
theorem isEffectivelyNull_diff_of_measure_eq_zero {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {U V : Set CantorSeq}
    (hU : IsEffectiveOpen U) (hV : IsEffectiveOpen V) (_hUV : U ⊆ V)
    (hzero : μ (V \ U) = 0) : IsEffectivelyNull μ (V \ U) := by
  classical
  obtain ⟨a, ha_comp, ha⟩ := hμ
  obtain ⟨g, hg, hVg⟩ := hV
  obtain ⟨e, he, hUe⟩ := hU
  have hUe' : U = ⋃ j, coverSet e j := hUe
  have hunion : (⋃ i, (coverSet g i \ U)) = V \ U := by
    rw [hVg, Set.iUnion_sdiff]
    rfl
  have hsubV : ∀ i, coverSet g i ⊆ V := by
    intro i
    rw [hVg]
    exact Set.subset_iUnion (fun j => (g j).elim ∅ cantorCylinder) i
  have hzero' : ∀ v : BitString, cantorCylinder v ⊆ V →
      μ (cantorCylinder v \ ⋃ j, coverSet e j) = 0 := by
    intro v hv
    refine le_antisymm ?_ (zero_le)
    rw [← hzero, ← hUe']
    exact measure_mono (Set.sdiff_subset_sdiff_left hv)
  have hkey : IsUniformlyEffectivelyNull μ (fun i => coverSet g i \ U) := by
    refine ⟨fun m => diffCover a e ((g (Nat.unpair m).1).getD []) (Nat.unpair m).2, ?_, ?_, ?_⟩
    · refine ⟨fun m i =>
        diffCoverEnum a e ((g (Nat.unpair m).1).getD []) (Nat.unpair m).2 i, ?_, ?_⟩
      · have hdec : Computable fun q : ℕ × ℕ =>
            ((((g (Nat.unpair q.1).1).getD ([] : BitString)), (Nat.unpair q.1).2), q.2) := by
          have hu1 : Computable fun q : ℕ × ℕ => (Nat.unpair q.1).1 :=
            (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)).to_comp
          have hu2 : Computable fun q : ℕ × ℕ => (Nat.unpair q.1).2 :=
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)).to_comp
          have hv : Computable fun q : ℕ × ℕ => (g (Nat.unpair q.1).1).getD ([] : BitString) :=
            Computable.option_getD (hg.comp hu1) (Computable.const [])
          exact Computable.pair (Computable.pair hv hu2) Computable.snd
        refine ((computable_diffCoverEnum ha_comp he).comp hdec).of_eq fun q => ?_
        rfl
      · intro m
        exact diffCover_eq_iUnion a e _ _
    · intro k
      refine Set.subset_iInter fun n => ?_
      simp only [Nat.unpair_pair]
      cases hgk : g k with
      | none =>
          intro x hx
          rw [coverSet, hgk] at hx
          exact absurd hx.1 (by simp)
      | some v =>
          have hcv : cantorCylinder v ⊆ V := by
            simpa [coverSet, hgk] using hsubV k
          have hcert : ∃ L t, diffCert a e v n L t = true :=
            exists_diffCert_of_measure_eq_zero ha e v (hzero' v hcv) n
          have hsub := sdiff_subset_diffCover (a := a) (h := e) (v := v) (n := n) hcert
          intro x hx
          have hx' : x ∈ cantorCylinder v \ ⋃ j, coverSet e j := by
            refine ⟨?_, ?_⟩
            · have := hx.1
              rwa [coverSet, hgk] at this
            · rw [← hUe']
              exact hx.2
          have := hsub hx'
          simpa [hgk] using this
    · intro k n
      simp only [Nat.unpair_pair]
      exact measure_diffCover_le ha e _ n
  rw [← hunion]
  exact hkey.isEffectivelyNull_iUnion

/-- The preimage `f^{-1}(Σ_u)` is effectively open (SUV §5.9.3, p. 181: "the
preimage of `Σ_z` is an effectively open set, the union of an enumerable set of
intervals"). -/
lemma isEffectiveOpen_setOf_le_comp {f : BitStream → BitStream}
    (hf : IsComputableStreamMap f) (u : BitString) :
    IsEffectiveOpen {x : CantorSeq | BitStream.finite u ≤ f (BitStream.infinite x)} := by
  rw [setOf_le_comp_eq_cantorOpen hf.1 u]
  exact isEffectiveOpen_cantorOpen_of_isRE hf.2 u

/-- **SUV Theorem 123(a), first half (§5.9.3, p. 181).** The image of a
`μ`-random sequence is infinite:

> "If this is not the case and `f(ω)` is a finite string `z`, consider all
> infinite sequences `w` such that `f(w) = z` … The preimage of `Σ_z` is an
> effectively open set …, and the preimage of `Σ_{z0} ∪ Σ_{z1}` is another
> effectively open set that is a subset of the first one.  To get the
> contradiction, we have to prove that the preimage of the difference … does not
> contain random sequences.  This is a special case of [Lemma 1]."  (p. 181)

The difference is null because the two preimages have `ν`-masses `ν(Ω_z)` and
`ν(Ω_{z0}) + ν(Ω_{z1})`, which agree by `cantorMass_add` — this is exactly where
the standing assumption that `ν` is a *measure* (not a semimeasure) enters. -/
theorem exists_infinite_comp_of_isMartinLofRandom {μ ν : Measure CantorSeq}
    {f : BitStream → BitStream} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsComputableMeasure μ) (hf : IsComputableStreamMap f)
    (hν : IsImageMeasure μ f ν) {w : CantorSeq} (hw : IsMartinLofRandom μ w) :
    ∃ v : CantorSeq, f (BitStream.infinite w) = BitStream.infinite v := by
  cases hfw : f (BitStream.infinite w) with
  | infinite v => exact ⟨v, rfl⟩
  | finite z =>
      exfalso
      set Pre : BitString → Set CantorSeq :=
        fun u => {x : CantorSeq | BitStream.finite u ≤ f (BitStream.infinite x)} with hPre
      have hmono : ∀ u u' : BitString, u <+: u' → Pre u' ⊆ Pre u := by
        intro u u' huu' x hx
        have hle : BitStream.finite u ≤ BitStream.finite u' := huu'
        exact le_trans hle hx
      have hUV : Pre (z ++ [false]) ∪ Pre (z ++ [true]) ⊆ Pre z :=
        Set.union_subset (hmono z (z ++ [false]) ⟨[false], rfl⟩)
          (hmono z (z ++ [true]) ⟨[true], rfl⟩)
      have hdisj : Disjoint (Pre (z ++ [false])) (Pre (z ++ [true])) := by
        rw [Set.disjoint_left]
        intro x hx0 hx1
        have h0 : BitStream.finite (z ++ [false]) ≤ f (BitStream.infinite x) := hx0
        have h1 : BitStream.finite (z ++ [true]) ≤ f (BitStream.infinite x) := hx1
        cases hfx : f (BitStream.infinite x) with
        | finite y =>
            rw [hfx] at h0 h1
            have hpre := List.prefix_of_prefix_length_le h0 h1 (by simp)
            have heq : z ++ [false] = z ++ [true] :=
              List.IsPrefix.eq_of_length hpre (by simp)
            simp at heq
        | infinite y =>
            rw [hfx] at h0 h1
            have hp0 : IsCantorPrefix (z ++ [false]) y := h0
            have hp1 : IsCantorPrefix (z ++ [true]) y := h1
            have e0 := hp0 z.length (by simp)
            have e1 := hp1 z.length (by simp)
            rw [List.getElem_append_right (le_refl _)] at e0 e1
            simp at e0 e1
            simp [e0] at e1
      have hmassV : μ (Pre z) = cantorMass ν z := (hν z).symm
      have hmassU : μ (Pre (z ++ [false]) ∪ Pre (z ++ [true])) = cantorMass ν z := by
        rw [measure_union hdisj ((isEffectiveOpen_setOf_le_comp hf (z ++ [true])).measurableSet),
          ← hν (z ++ [false]), ← hν (z ++ [true])]
        exact (cantorMass_add ν z).symm
      have hzero : μ (Pre z \ (Pre (z ++ [false]) ∪ Pre (z ++ [true]))) = 0 := by
        rw [measure_sdiff hUV
          (((isEffectiveOpen_setOf_le_comp hf (z ++ [false])).measurableSet.union
            (isEffectiveOpen_setOf_le_comp hf (z ++ [true])).measurableSet).nullMeasurableSet)
          (by rw [hmassU]; exact measure_ne_top ν _), hmassU, hmassV, tsub_self]
      have hnull := isEffectivelyNull_diff_of_measure_eq_zero hμ
        (isEffectiveOpen_union (isEffectiveOpen_setOf_le_comp hf (z ++ [false]))
          (isEffectiveOpen_setOf_le_comp hf (z ++ [true])))
        (isEffectiveOpen_setOf_le_comp hf z) hUV hzero
      have hmem : w ∈ Pre z \ (Pre (z ++ [false]) ∪ Pre (z ++ [true])) := by
        refine ⟨?_, ?_⟩
        · change BitStream.finite z ≤ f (BitStream.infinite w)
          rw [hfw]
        · rintro (h0 | h1)
          · have h0' : BitStream.finite (z ++ [false]) ≤ f (BitStream.infinite w) := h0
            rw [hfw] at h0'
            have hpre : z ++ [false] <+: z := h0'
            have hlen := hpre.length_le
            simp at hlen
          · have h1' : BitStream.finite (z ++ [true]) ≤ f (BitStream.infinite w) := h1
            rw [hfw] at h1'
            have hpre : z ++ [true] <+: z := h1'
            have hlen := hpre.length_le
            simp at hlen
      exact ((isEffectivelyNull_iff_forall_not_random hμ _).1 hnull w hmem) hw

/-- **SUV Theorem 123(a) (§5.9.3, p. 181).** For any sequence `ω ∈ Ω` that is
ML-random with respect to `μ`, its image `f(ω)` is an infinite sequence that is
ML-random with respect to the image measure `ν`.

The second half is the source's

> "assume that `f(ω)` is infinite but does not [pass a test].  The preimages of
> the intervals that cover `f(ω)` cover `ω`, and we get an effectively open set
> that contains `ω` and has small measure (recall that the `μ`-measure of the
> preimage of an effectively open set is equal to the `ν`-measure of the set
> itself)."  (p. 181)

The test is disjointified first (`disjEnum`), so that the sum of the `ν`-masses
of its intervals is exactly `ν(U_n)` and the countable subadditivity of `μ` on
the preimages gives the bound. -/
theorem image_isMartinLofRandom_of_isMartinLofRandom {μ ν : Measure CantorSeq}
    {f : BitStream → BitStream} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsComputableMeasure μ) (hf : IsComputableStreamMap f)
    (hν : IsImageMeasure μ f ν) {w : CantorSeq} (hw : IsMartinLofRandom μ w) :
    ∃ v : CantorSeq, f (BitStream.infinite w) = BitStream.infinite v ∧
      IsMartinLofRandom ν v := by
  classical
  obtain ⟨v, hfw⟩ := exists_infinite_comp_of_isMartinLofRandom hμ hf hν hw
  refine ⟨v, hfw, ?_⟩
  -- the code of the lower graph of `f`, and its interval enumeration
  obtain ⟨p, hp, hpR⟩ := hf.2
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hp
  have hc' : ∀ q y, (c.eval (Encodable.encode (q, y))).Dom ↔ streamLowerGraph f q y := by
    intro q y
    have h_eq : c.eval (Encodable.encode (q, y)) = (p (q, y)).map Encodable.encode := by
      have hc_app : c.eval (Encodable.encode (q, y)) =
          (fun n => Part.bind (Encodable.decode n : Option (BitString × BitString))
            fun b => (p b).map Encodable.encode) (Encodable.encode (q, y)) := by
        rw [hc]
      rw [hc_app]
      simp
    rw [h_eq]
    simp [hpR]
  have hRel : (fun q y => (c.eval (Encodable.encode (q, y))).Dom) = streamLowerGraph f := by
    funext q y
    exact propext (hc' q y)
  have hEunion : ∀ u : BitString, (⋃ j, coverSet (cantorOpenREEnumerator c u) j)
      = {x : CantorSeq | BitStream.finite u ≤ f (BitStream.infinite x)} := by
    intro u
    rw [setOf_le_comp_eq_cantorOpen hf.1 u]
    simp only [coverSet]
    rw [range_cantorOpenREEnumerator c u, hRel]
  -- an arbitrary test for `ν`, disjointified
  intro T hT hvT
  obtain ⟨⟨F, hF, hTF⟩, hTmass⟩ := hT
  set D : ℕ → ℕ → Option BitString := fun n => disjEnum (F n) with hD
  set G : ℕ → ℕ → Option BitString := fun n k =>
    (D n (Nat.unpair k).1).bind fun u => cantorOpenREEnumerator c u (Nat.unpair k).2 with hG
  have hGcomp : Computable₂ G := by
    have hDcomp : Computable₂ D := computable_disjEnum hF
    have h1 : Computable fun q : ℕ × ℕ => D q.1 (Nat.unpair q.2).1 :=
      hDcomp.comp Computable.fst
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have h2 : Computable₂ fun (q : ℕ × ℕ) (u : BitString) =>
        cantorOpenREEnumerator c u (Nat.unpair q.2).2 :=
      (computable_cantorOpenREEnumerator c).comp Computable.snd
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))).to_comp
    exact Computable.option_bind h1 h2
  have hPre : ∀ n, (⋃ k, coverSet (G n) k)
      = ⋃ i, (D n i).elim ∅
        (fun u => {x : CantorSeq | BitStream.finite u ≤ f (BitStream.infinite x)}) := by
    intro n
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨(Nat.unpair k).1, ?_⟩
      cases hDk : D n (Nat.unpair k).1 with
      | none =>
          rw [coverSet, hG] at hk
          simp [hDk] at hk
      | some u =>
          simp only [Option.elim_some]
          rw [← hEunion u]
          refine Set.mem_iUnion.2 ⟨(Nat.unpair k).2, ?_⟩
          rw [coverSet, hG] at hk
          simpa [hDk, coverSet] using hk
    · rintro ⟨i, hi⟩
      cases hDi : D n i with
      | none => rw [hDi] at hi; simp at hi
      | some u =>
          rw [hDi] at hi
          simp only [Option.elim_some] at hi
          rw [← hEunion u] at hi
          obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hi
          exact ⟨Nat.pair i j, by simpa [hG, hDi, coverSet, Nat.unpair_pair] using hj⟩
  have hPmass : ∀ n, μ (⋃ k, coverSet (G n) k) ≤ dyadicValue 1 n := by
    intro n
    rw [hPre n]
    calc μ (⋃ i, (D n i).elim ∅
            (fun u => {x : CantorSeq | BitStream.finite u ≤ f (BitStream.infinite x)}))
        ≤ ∑' i, μ ((D n i).elim ∅
            (fun u => {x : CantorSeq | BitStream.finite u ≤ f (BitStream.infinite x)})) :=
          measure_iUnion_le _
      _ = ∑' i, (D n i).elim 0 (cantorMass ν) := by
          refine tsum_congr fun i => ?_
          cases hDi : D n i with
          | none => simp
          | some u => simpa using (hν u).symm
      _ = ν (⋃ j, coverSet (F n) j) := tsum_measure_disjEnum ν (F n)
      _ = ν (T n) := by rw [hTF n]; rfl
      _ ≤ dyadicValue 1 n := hTmass n
  have hmem : w ∈ ⋂ n, (⋃ k, coverSet (G n) k) := by
    refine Set.mem_iInter.2 fun n => ?_
    rw [hPre n]
    have hvTn : v ∈ T n := Set.mem_iInter.1 hvT n
    have hvD : v ∈ ⋃ i, coverSet (D n) i := by
      have hu : (⋃ i, coverSet (D n) i) = ⋃ j, coverSet (F n) j :=
        coverSet_disjEnum_iUnion (F n)
      rw [hu]
      have hvTn' := hvTn
      rw [hTF n] at hvTn'
      exact hvTn'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hvD
    cases hDi : D n i with
    | none => rw [coverSet, hDi] at hi; simp at hi
    | some u =>
        rw [coverSet, hDi] at hi
        simp only [Option.elim_some] at hi
        refine Set.mem_iUnion.2 ⟨i, ?_⟩
        rw [hDi]
        simp only [Option.elim_some, Set.mem_ofPred_eq]
        rw [hfw]
        exact hi
  exact hw (fun n => ⋃ k, coverSet (G n) k) ⟨⟨G, hGcomp, fun n => rfl⟩, hPmass⟩ hmem

/-- Two finite streams below a common stream are comparable. -/
lemma prefix_of_finite_le_finite_le {a b : BitString} {s : BitStream}
    (ha : BitStream.finite a ≤ s) (hb : BitStream.finite b ≤ s) (hab : a.length ≤ b.length) :
    a <+: b := by
  cases s with
  | finite z => exact List.prefix_of_prefix_length_le ha hb hab
  | infinite x => exact prefix_of_isCantorPrefix ha hb hab

/-- **SUV §5.9.3, pp. 182-183, the machine comparison of Lemma 2:**

> "Now consider the continuous a priori probability of the set `F_u`, i.e. the
> probability of the event 'the output of a universal probabilistic machine `M`
> belongs to `F_u`'.  This event can be rephrased as follows: the output of the
> machine `f ∘ M` (that applies `f` to the output of `M`) starts with `u`.
> Comparing the machine `f ∘ M` and the universal one, we conclude that the
> (continuous) a priori probability of the set `F_u` can be only a constant times
> bigger than the (continuous) a priori probability of `Σ_u`."  (SUV p. 182)

`F_u` is the preimage of `Σ_u`, i.e. the union of the intervals `Ω_w` with
`u ⪯ f(w)`, and its a priori probability is the supremum of `∑ a(w)` over the
*finite prefix-free* families of such `w` — which is the form stated here, and
the only one Lemma 2 uses (through `ENNReal.tsum_eq_iSup_sum`). -/
theorem exists_const_finsetSum_apriori_le {f : BitStream → BitStream}
    (hf : IsComputableStreamMap f) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (u : BitString) (W : Finset BitString),
      (∀ w ∈ W, BitStream.finite u ≤ f (BitStream.finite w)) →
      (∀ w ∈ W, ∀ w' ∈ W, w <+: w' → w = w') →
      ∑ w ∈ W, universalContinuousSemimeasure w
        ≤ C * universalContinuousSemimeasure u := by
  classical
  -- the universal semimeasure is the output distribution of a machine `G`
  obtain ⟨G, hG⟩ := exists_probabilisticGenerator_generatedTreeSemimeasure_eq
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure
  -- and `f ∘ G` is again such a machine, so its output distribution is dominated
  obtain ⟨C, hCtop, hC⟩ := universalContinuousSemimeasure_isMaximal
    (fun x => uniformMeasure (G.output ⁻¹' (f ⁻¹' bitStreamCylinder x)))
    (generatorComposition_isLowerSemicomputableContinuousSemimeasure G hf)
  refine ⟨C, hCtop, fun u W hWf hWanti => ?_⟩
  have hmeas : ∀ w : BitString, MeasurableSet (G.output ⁻¹' bitStreamCylinder w) := by
    intro w
    rw [preimage_bitStreamCylinder_eq_cantorOpen]
    exact measurableSet_cantorOpen _ _
  have hdisj : (W : Set BitString).Pairwise
      (Function.onFun Disjoint (fun w => G.output ⁻¹' bitStreamCylinder w)) := by
    intro w hw w' hw' hne
    change Disjoint (G.output ⁻¹' bitStreamCylinder w) (G.output ⁻¹' bitStreamCylinder w')
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : BitStream.finite w ≤ G.output x := hx
    have h2 : BitStream.finite w' ≤ G.output x := hx'
    rcases le_total w.length w'.length with hlen | hlen
    · exact hne (hWanti w (Finset.mem_coe.1 hw) w' (Finset.mem_coe.1 hw')
        (prefix_of_finite_le_finite_le h1 h2 hlen))
    · exact hne (hWanti w' (Finset.mem_coe.1 hw') w (Finset.mem_coe.1 hw)
        (prefix_of_finite_le_finite_le h2 h1 hlen)).symm
  have hsub : (⋃ w ∈ W, G.output ⁻¹' bitStreamCylinder w)
      ⊆ G.output ⁻¹' (f ⁻¹' bitStreamCylinder u) := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.1 hx
    have h1 : BitStream.finite w ≤ G.output x := hxw
    have h2 : f (BitStream.finite w) ≤ f (G.output x) := hf.1.1 h1
    exact le_trans (hWf w (Finset.mem_coe.1 hw)) h2
  calc ∑ w ∈ W, universalContinuousSemimeasure w
      = ∑ w ∈ W, uniformMeasure (G.output ⁻¹' bitStreamCylinder w) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        exact (hG w).symm
    _ = uniformMeasure (⋃ w ∈ W, G.output ⁻¹' bitStreamCylinder w) :=
        (measure_biUnion_finset hdisj (fun w _ => hmeas w)).symm
    _ ≤ uniformMeasure (G.output ⁻¹' (f ⁻¹' bitStreamCylinder u)) := measure_mono hsub
    _ ≤ C * universalContinuousSemimeasure u := hC u

/-- **SUV Lemma 2 of §5.9.3 (p. 182).** Let `u` be a string with `ν(Ω_u) > 0`.
Then there exists a string `w` with `u ⪯ f(w)` and `d_μ(w) ≤ d_ν(u) + O(1)`.

"The constant hidden in `O(1)` may depend on `f`, `μ` and `ν` but not on `u`":
the constant is therefore chosen before `u` is quantified. -/
theorem exists_const_forall_exists_deficiency_le {μ ν : Measure CantorSeq}
    {f : BitStream → BitStream} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (_hμ : IsComputableMeasure μ) (hf : IsComputableStreamMap f)
    (hν : IsImageMeasure μ f ν) :
    ∃ c : ℝ, ∀ u : BitString, cantorMass ν u ≠ 0 →
      ∃ w : BitString, BitStream.finite u ≤ f (BitStream.finite w) ∧
        deficiency μ w ≤ deficiency ν u + (c : EReal) := by
  classical
  obtain ⟨C, hCtop, hC⟩ := exists_const_finsetSum_apriori_le hf
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hCtop
  have hCn : C < (2 : ℝ≥0∞) ^ n := by
    refine lt_of_lt_of_le hn ?_
    have hnat : (n : ℕ) ≤ 2 ^ n := le_of_lt Nat.lt_two_pow_self
    calc (n : ℝ≥0∞) ≤ ((2 ^ n : ℕ) : ℝ≥0∞) := by exact_mod_cast hnat
      _ = (2 : ℝ≥0∞) ^ n := by push_cast; ring
  refine ⟨(n : ℝ), fun u hu => ?_⟩
  have hAu : universalContinuousSemimeasure u ≠ 0 := (universalContinuousSemimeasure_pos u).ne'
  have hAutop : universalContinuousSemimeasure u ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top u
  have hutop : cantorMass ν u ≠ ⊤ := measure_ne_top ν _
  -- the multiplicative form of the conclusion, by the source's averaging over the
  -- disjoint intervals of the preimage
  have key : ∃ w : BitString, BitStream.finite u ≤ f (BitStream.finite w) ∧
      cantorMass ν u * universalContinuousSemimeasure w
        ≤ (2 : ℝ≥0∞) ^ n * universalContinuousSemimeasure u * cantorMass μ w := by
    by_contra hcon
    push Not at hcon
    set S : Set BitString := {w : BitString | BitStream.finite u ≤ f (BitStream.finite w)}
      with hS
    have hPre : prefixHitSet S
        = {x : CantorSeq | BitStream.finite u ≤ f (BitStream.infinite x)} := by
      rw [prefixHitSet_eq_iUnion_cantorCylinder, setOf_le_comp_eq_cantorOpen hf.1 u]
      rfl
    have hmass : cantorMass ν u
        ≤ ∑' w : minimalPrefixElements S, cantorMass μ (w : BitString) := by
      rw [hν u, ← hPre]
      exact measure_prefixHitSet_le_tsum_minimalPrefixElements μ S
    have hsum : ∑' w : minimalPrefixElements S, universalContinuousSemimeasure (w : BitString)
        ≤ C * universalContinuousSemimeasure u := by
      rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun s => ?_
      have himg : ∑ x ∈ s, universalContinuousSemimeasure (x : BitString)
          = ∑ w ∈ s.image Subtype.val, universalContinuousSemimeasure w :=
        (Finset.sum_image (fun x _ y _ h => Subtype.ext h)).symm
      rw [himg]
      refine hC u _ ?_ ?_
      · intro w hw
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hw
        exact x.2.1
      · intro w hw w' hw' hpre
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hw
        obtain ⟨x', -, rfl⟩ := Finset.mem_image.1 hw'
        exact minimalPrefixElements_antichain S _ x.2 _ x'.2 hpre
    have hstep : ∀ w : minimalPrefixElements S,
        (2 : ℝ≥0∞) ^ n * universalContinuousSemimeasure u * cantorMass μ (w : BitString)
          ≤ cantorMass ν u * universalContinuousSemimeasure (w : BitString) := by
      intro w
      exact le_of_lt (hcon (w : BitString) w.2.1)
    have hchain : (2 : ℝ≥0∞) ^ n * universalContinuousSemimeasure u * cantorMass ν u
        < cantorMass ν u * ((2 : ℝ≥0∞) ^ n * universalContinuousSemimeasure u) := by
      calc (2 : ℝ≥0∞) ^ n * universalContinuousSemimeasure u * cantorMass ν u
          ≤ ((2 : ℝ≥0∞) ^ n * universalContinuousSemimeasure u)
            * ∑' w : minimalPrefixElements S, cantorMass μ (w : BitString) := by gcongr
        _ = ∑' w : minimalPrefixElements S,
              ((2 : ℝ≥0∞) ^ n * universalContinuousSemimeasure u) * cantorMass μ (w : BitString) :=
            ENNReal.tsum_mul_left.symm
        _ ≤ ∑' w : minimalPrefixElements S,
              cantorMass ν u * universalContinuousSemimeasure (w : BitString) :=
            ENNReal.tsum_le_tsum hstep
        _ = cantorMass ν u
              * ∑' w : minimalPrefixElements S, universalContinuousSemimeasure (w : BitString) :=
            ENNReal.tsum_mul_left
        _ ≤ cantorMass ν u * (C * universalContinuousSemimeasure u) := by gcongr
        _ < cantorMass ν u * ((2 : ℝ≥0∞) ^ n * universalContinuousSemimeasure u) :=
            ENNReal.mul_lt_mul_right hu hutop
              (ENNReal.mul_lt_mul_left hAu hAutop hCn)
    have hcomm : (2 : ℝ≥0∞) ^ n * universalContinuousSemimeasure u * cantorMass ν u
        = cantorMass ν u * ((2 : ℝ≥0∞) ^ n * universalContinuousSemimeasure u) := mul_comm _ _
    rw [hcomm] at hchain
    exact lt_irrefl _ hchain
  -- the logarithmic form
  obtain ⟨w, hwf, hmul⟩ := key
  refine ⟨w, hwf, ?_⟩
  have hAw : universalContinuousSemimeasure w ≠ 0 := (universalContinuousSemimeasure_pos w).ne'
  have hAwtop : universalContinuousSemimeasure w ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top w
  have hwmass : cantorMass μ w ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact (mul_ne_zero hu hAw) (le_antisymm hmul (zero_le))
  have hwtop : cantorMass μ w ≠ ⊤ := measure_ne_top μ _
  rw [deficiency_of_ne_zero hwmass, deficiency_of_ne_zero hu, ← EReal.coe_add,
    EReal.coe_le_coe_iff, KA, KA]
  -- transport the inequality to the reals and take binary logarithms
  set Au : ℝ := (universalContinuousSemimeasure u).toReal with hAudef
  set Aw : ℝ := (universalContinuousSemimeasure w).toReal with hAwdef
  set Nu : ℝ := (cantorMass ν u).toReal with hNudef
  set Mw : ℝ := (cantorMass μ w).toReal with hMwdef
  have hAupos : 0 < Au := ENNReal.toReal_pos hAu hAutop
  have hAwpos : 0 < Aw := ENNReal.toReal_pos hAw hAwtop
  have hNupos : 0 < Nu := ENNReal.toReal_pos hu hutop
  have hMwpos : 0 < Mw := ENNReal.toReal_pos hwmass hwtop
  have hreal : Nu * Aw ≤ (2 : ℝ) ^ n * Au * Mw := by
    have hle := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hAutop) hwtop) hmul
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul] at hle
    simpa [hAudef, hAwdef, hNudef, hMwdef] using hle
  have hlog : Real.logb 2 (Nu * Aw) ≤ Real.logb 2 ((2 : ℝ) ^ n * Au * Mw) :=
    (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).mpr hreal
  rw [Real.logb_mul hNupos.ne' hAwpos.ne',
    Real.logb_mul (by positivity) hMwpos.ne', Real.logb_mul (by positivity) hAupos.ne',
    Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlog
  linarith

/-! ### Bridges between the `EReal` deficiency and the multiplicative form -/

/-- The `EReal` deficiency of `x` is below `c` exactly when the a priori
probability of `x` is below `2^c` times its `P`-mass.  (`deficiency` is
`-log P(Ω_x) - KA(x)` and `KA = -log a`.) -/
lemma deficiency_le_of_apriori_le {P : Measure CantorSeq} [IsProbabilityMeasure P]
    {x : BitString} {c : ℕ}
    (h : universalContinuousSemimeasure x ≤ (2 : ℝ≥0∞) ^ c * cantorMass P x) :
    deficiency P x ≤ (((c : ℝ)) : EReal) := by
  have hA : universalContinuousSemimeasure x ≠ 0 := (universalContinuousSemimeasure_pos x).ne'
  have hAtop : universalContinuousSemimeasure x ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  have hPtop : cantorMass P x ≠ ⊤ := measure_ne_top P _
  have hP0 : cantorMass P x ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact hA (le_antisymm h (zero_le))
  rw [deficiency_of_ne_zero hP0, EReal.coe_le_coe_iff, KA]
  have hApos : 0 < (universalContinuousSemimeasure x).toReal := ENNReal.toReal_pos hA hAtop
  have hPpos : 0 < (cantorMass P x).toReal := ENNReal.toReal_pos hP0 hPtop
  have hreal : (universalContinuousSemimeasure x).toReal
      ≤ (2 : ℝ) ^ c * (cantorMass P x).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hPtop) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at this
  have hlog := (Real.logb_le_logb (b := 2) (by norm_num) hApos (by positivity)).mpr hreal
  rw [Real.logb_mul (by positivity) hPpos.ne', Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)] at hlog
  linarith

/-- The converse bridge. -/
lemma apriori_le_of_deficiency_le {P : Measure CantorSeq} [IsProbabilityMeasure P]
    {x : BitString} {c : ℕ}
    (hP0 : cantorMass P x ≠ 0) (h : deficiency P x ≤ (((c : ℝ)) : EReal)) :
    universalContinuousSemimeasure x ≤ (2 : ℝ≥0∞) ^ c * cantorMass P x := by
  have hA : universalContinuousSemimeasure x ≠ 0 := (universalContinuousSemimeasure_pos x).ne'
  have hAtop : universalContinuousSemimeasure x ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  have hPtop : cantorMass P x ≠ ⊤ := measure_ne_top P _
  have hApos : 0 < (universalContinuousSemimeasure x).toReal := ENNReal.toReal_pos hA hAtop
  have hPpos : 0 < (cantorMass P x).toReal := ENNReal.toReal_pos hP0 hPtop
  rw [deficiency_of_ne_zero hP0, EReal.coe_le_coe_iff, KA] at h
  have hlog : Real.logb 2 (universalContinuousSemimeasure x).toReal
      ≤ Real.logb 2 ((2 : ℝ) ^ c * (cantorMass P x).toReal) := by
    rw [Real.logb_mul (by positivity) hPpos.ne', Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    linarith
  have hreal : (universalContinuousSemimeasure x).toReal
      ≤ (2 : ℝ) ^ c * (cantorMass P x).toReal :=
    (Real.logb_le_logb (b := 2) (by norm_num) hApos (by positivity)).mp hlog
  have hmul : ((2 : ℝ≥0∞) ^ c * cantorMass P x).toReal = (2 : ℝ) ^ c * (cantorMass P x).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  refine (ENNReal.toReal_le_toReal hAtop (ENNReal.mul_ne_top (by simp) hPtop)).mp ?_
  rw [hmul]
  exact hreal

/-- A cylinder of positive `μ`-mass contains a `μ`-random sequence: the union of
a universal Martin-Löf test is null, so it cannot swallow the cylinder.  This is
the source's "we let `ω` be any `μ`-random continuation of the string `w` (we know
that it exists, since the `μ`-deficiency of `w` is finite and `μ(Ω_w) > 0`)"
(SUV §5.9.3, p. 183). -/
lemma exists_isMartinLofRandom_mem_cantorCylinder {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {w : BitString}
    (hw : cantorMass μ w ≠ 0) :
    ∃ x : CantorSeq, x ∈ cantorCylinder w ∧ IsMartinLofRandom μ x := by
  classical
  obtain ⟨U, hU⟩ := exists_universal_martinLof_test hμ
  have hzero : μ (⋂ n, U n) = 0 := by
    refine le_antisymm ?_ (zero_le)
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨u, hu⟩ := exists_inv_two_pow_lt (ε := (ε : ℝ≥0∞)) (by exact_mod_cast hε.ne')
    calc μ (⋂ n, U n) ≤ μ (U u) := measure_mono (Set.iInter_subset _ u)
      _ ≤ dyadicValue 1 u := hU.1.2 u
      _ = ((2 : ℝ≥0∞)⁻¹) ^ u := dyadicValue_one_eq_inv_two_pow' u
      _ ≤ (ε : ℝ≥0∞) := hu.le
      _ = 0 + (ε : ℝ≥0∞) := (zero_add _).symm
  have hnsub : ¬ cantorCylinder w ⊆ ⋂ n, U n := by
    intro hsub
    exact hw (le_antisymm (by rw [cantorMass, ← hzero]; exact measure_mono hsub) (zero_le))
  obtain ⟨x, hxw, hxU⟩ := Set.not_subset.1 hnsub
  refine ⟨x, hxw, ?_⟩
  intro T hT hmem
  exact hxU (hU.2 (⋂ n, T n) ⟨T, hT.1, subset_rfl, hT.2⟩ hmem)

/-- `x - 2 log₂ x` tends to infinity, in the explicit form Theorem 123(b) needs:
a bound on `x - 2 log₂ x` bounds `x`. -/
lemma le_of_sub_two_logb_le {x M : ℝ} (hx : 1 ≤ x) (h : x - 2 * Real.logb 2 x ≤ M) :
    x ≤ max 64 (2 * M) := by
  by_cases hle : x ≤ 64
  · exact le_trans hle (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    have hlt : (64 : ℝ) < x := not_le.1 hle
    have hxpos : (0 : ℝ) < x := by linarith
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hlogpos : (0 : ℝ) < Real.log 2 := by linarith
    have hstep : Real.log (x / 64) ≤ x / 64 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hlog64 : Real.log (x / 64) = Real.log x - 6 * Real.log 2 := by
      rw [Real.log_div hxpos.ne' (by norm_num), show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num,
        Real.log_pow]
      push_cast
      ring
    have hlogx : Real.log x ≤ x / 64 - 1 + 6 * Real.log 2 := by
      rw [hlog64] at hstep
      linarith
    have hkey : 4 * Real.log x ≤ x * Real.log 2 := by nlinarith [hlogx, hlog2, hlog2', hlt]
    have hlogb : 2 * Real.logb 2 x ≤ x / 2 := by
      have hdef : Real.logb 2 x = Real.log x / Real.log 2 := rfl
      rw [hdef, mul_div_assoc', div_le_iff₀ hlogpos]
      have h2 : x / 2 * Real.log 2 = x * Real.log 2 / 2 := by ring
      rw [h2, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
    linarith

end Kolmogorov
