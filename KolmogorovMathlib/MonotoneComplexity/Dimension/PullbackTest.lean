/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.ChangeOfMeasure.Part01
import KolmogorovMathlib.MonotoneComplexity.Dimension.ChangeOfMeasure

/-!
# The pullback of a randomness test along a computable stream map (SUV §5.9.3)

SUV Problem 185 (p. 182) compares the expectation-bounded deficiency of `f(ω)`
with respect to the image measure `ν` with that of `ω` with respect to `μ`.  The
comparison needs the pullback of a test for `ν` to a test for `μ`, and the naive
pullback does not work: with the convention that the value is `0` where `f(ω)`
is a finite string, the superlevel set of `v ∘ f` is the intersection of an
effectively open set with `{ω | f(ω) is infinite}`, a `Π₂` set, so `v ∘ f` is
*not* lower semicomputable.

`pullbackTest` is the correct object: the supremum of the rationals `q` for
which one of the intervals enumerated at level `q` by the lower semicomputability
of `v` is a prefix of `f(ω)`.  It is lower semicomputable
(`isLowerSemicomputableFun_pullbackTest`), because the preimages
`{ω | u ⪯ f(ω)}` are effectively open *uniformly in `u`*
(`exists_uniform_enumerator_setOf_le_comp`, the uniform form of
`isEffectiveOpen_setOf_le_comp`), and it dominates `v ∘ f` wherever `f(ω)` is
infinite (`le_pullbackTest`).  Its integral is still at most one
(`lintegral_pullbackTest_le`), so it is an expectation-bounded test for `μ`, and
Problem 185 follows from the maximality of the test for `μ`.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-- The uniform form of `isEffectiveOpen_cantorOpen_of_isRE`: one computable
enumerator serves all the parameters at once. -/
theorem exists_uniform_cantorOpen_enumerator_of_isRE {R : BitString → BitString → Prop}
    (hR : IsRE fun q : BitString × BitString => R q.1 q.2) :
    ∃ E : BitString → ℕ → Option BitString, Computable₂ E ∧
      ∀ x : BitString, cantorOpen R x = ⋃ i, (E x i).elim ∅ cantorCylinder := by
  rcases hR with ⟨g, hg, hgR⟩
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg
  have hc' : ∀ p y, (c.eval (Encodable.encode (p, y))).Dom ↔ R p y := by
    intro p y
    have h_eq : c.eval (Encodable.encode (p, y)) = (g (p, y)).map Encodable.encode := by
      have hc_app : c.eval (Encodable.encode (p, y)) =
          (fun n => Part.bind (Encodable.decode n : Option (BitString × BitString))
            fun a => (g a).map Encodable.encode) (Encodable.encode (p, y)) := by
        rw [hc]
      rw [hc_app]
      simp
    rw [h_eq]
    simp [hgR]
  refine ⟨cantorOpenREEnumerator c, computable_cantorOpenREEnumerator c, fun x => ?_⟩
  rw [range_cantorOpenREEnumerator c x]
  have hRR : (fun p y => (c.eval (Encodable.encode (p, y))).Dom) = R := by
    ext p y
    exact hc' p y
  rw [hRR]

/-- A computable stream map has a single computable enumerator for all the
preimages of the generating intervals. -/
theorem exists_uniform_enumerator_setOf_le_comp {f : BitStream → BitStream}
    (hf : IsComputableStreamMap f) :
    ∃ E : BitString → ℕ → Option BitString, Computable₂ E ∧
      ∀ u : BitString, {x : CantorSeq | BitStream.finite u ≤ f (BitStream.infinite x)}
        = ⋃ i, (E u i).elim ∅ cantorCylinder := by
  obtain ⟨E, hE, hEspec⟩ := exists_uniform_cantorOpen_enumerator_of_isRE hf.2
  refine ⟨E, hE, fun u => ?_⟩
  rw [setOf_le_comp_eq_cantorOpen hf.1 u]
  exact hEspec u



/-! ### The pullback test -/

/-- The pullback of a lower semicomputable function along a computable stream
map, described by an enumerator `enum` of its superlevel sets: the supremum of
the rationals `q` such that one of the intervals enumerated at level `q` is a
prefix of the image of `w`. -/
noncomputable def pullbackTest (enum : ℚ → ℕ → Option BitString) (f : BitStream → BitStream)
    (w : CantorSeq) : ℝ≥0∞ :=
  ⨆ (p : ℚ × ℕ) (_ : 0 ≤ p.1 ∧ ∃ u : BitString, enum p.1 p.2 = some u ∧
      BitStream.finite u ≤ f (BitStream.infinite w)), ENNReal.ofReal (p.1 : ℝ)

/-- The pullback test at `w` exceeds `q₀` exactly when some enumerated string above threshold `q₀`
already approximates the image of `w`. -/
lemma lt_pullbackTest_iff {enum : ℚ → ℕ → Option BitString} {f : BitStream → BitStream}
    {w : CantorSeq} {q₀ : ℚ} (hq₀ : 0 ≤ q₀) :
    ENNReal.ofReal (q₀ : ℝ) < pullbackTest enum f w ↔
      ∃ p : ℚ × ℕ, (q₀ < p.1 ∧ ∃ u : BitString, enum p.1 p.2 = some u ∧
        BitStream.finite u ≤ f (BitStream.infinite w)) := by
  simp only [pullbackTest]
  rw [lt_iSup_iff]
  constructor
  · rintro ⟨p, hp⟩
    rw [lt_iSup_iff] at hp
    obtain ⟨hP, hlt⟩ := hp
    refine ⟨p, ?_, hP.2⟩
    by_contra hcon
    push Not at hcon
    exact absurd hlt (not_lt.2 (ENNReal.ofReal_le_ofReal (by exact_mod_cast hcon)))
  · rintro ⟨p, hlt, hu⟩
    have hp0 : 0 ≤ p.1 := le_of_lt (lt_of_le_of_lt hq₀ hlt)
    refine ⟨p, ?_⟩
    rw [lt_iSup_iff]
    refine ⟨⟨hp0, hu⟩, ?_⟩
    have hpos : (0 : ℝ) < (p.1 : ℝ) := by
      have : (q₀ : ℝ) < (p.1 : ℝ) := by exact_mod_cast hlt
      exact lt_of_le_of_lt (by exact_mod_cast hq₀) this
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 (by exact_mod_cast hlt)

/-- The enumerator of the superlevel sets of `pullbackTest`. -/
def pullbackEnum (E : BitString → ℕ → Option BitString) (enum : ℚ → ℕ → Option BitString)
    (q₀ : ℚ) (j : ℕ) : Option BitString :=
  if q₀ < 0 then some [] else
    if q₀ < (Denumerable.ofNat (ℚ × ℕ) (Nat.unpair j).1).1 then
      (enum (Denumerable.ofNat (ℚ × ℕ) (Nat.unpair j).1).1
        (Denumerable.ofNat (ℚ × ℕ) (Nat.unpair j).1).2).bind
        fun u => E u (Nat.unpair j).2
    else none


/-- For computable preimage and test enumerations the pullback enumeration is computable. -/
lemma computable₂_pullbackEnum {E : BitString → ℕ → Option BitString} (hE : Computable₂ E)
    {enum : ℚ → ℕ → Option BitString} (henum : Computable₂ enum) :
    Computable₂ (pullbackEnum E enum) := by
  have hp : Computable fun r : ℚ × ℕ => Denumerable.ofNat (ℚ × ℕ) (Nat.unpair r.2).1 :=
    (Primrec.ofNat (ℚ × ℕ)).to_comp.comp
      ((Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd)
  have hq : Computable fun r : ℚ × ℕ => (Denumerable.ofNat (ℚ × ℕ) (Nat.unpair r.2).1).1 :=
    Computable.fst.comp hp
  have hi : Computable fun r : ℚ × ℕ => (Denumerable.ofNat (ℚ × ℕ) (Nat.unpair r.2).1).2 :=
    Computable.snd.comp hp
  have hk : Computable fun r : ℚ × ℕ => (Nat.unpair r.2).2 :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.snd
  have hneg : Computable fun r : ℚ × ℕ => decide (r.1 < 0) :=
    computable₂_ratLt.comp Computable.fst (Computable.const 0)
  have hlt : Computable fun r : ℚ × ℕ => decide (r.1 < (Denumerable.ofNat (ℚ × ℕ)
      (Nat.unpair r.2).1).1) := computable₂_ratLt.comp Computable.fst hq
  have hbody : Computable fun r : ℚ × ℕ =>
      (enum (Denumerable.ofNat (ℚ × ℕ) (Nat.unpair r.2).1).1
        (Denumerable.ofNat (ℚ × ℕ) (Nat.unpair r.2).1).2).bind
        fun u => E u (Nat.unpair r.2).2 := by
    have hopt : Computable fun r : ℚ × ℕ =>
        enum (Denumerable.ofNat (ℚ × ℕ) (Nat.unpair r.2).1).1
          (Denumerable.ofNat (ℚ × ℕ) (Nat.unpair r.2).1).2 := henum.comp hq hi
    exact Computable.option_bind hopt (hE.comp Computable.snd (hk.comp Computable.fst))
  have hinner : Computable fun r : ℚ × ℕ =>
      if r.1 < (Denumerable.ofNat (ℚ × ℕ) (Nat.unpair r.2).1).1 then
        (enum (Denumerable.ofNat (ℚ × ℕ) (Nat.unpair r.2).1).1
          (Denumerable.ofNat (ℚ × ℕ) (Nat.unpair r.2).1).2).bind
          fun u => E u (Nat.unpair r.2).2
      else none := by
    refine (Computable.cond hlt hbody (Computable.const none)).of_eq fun r => ?_
    by_cases h : r.1 < (Denumerable.ofNat (ℚ × ℕ) (Nat.unpair r.2).1).1 <;> simp
  refine (Computable.cond hneg (Computable.const (some [])) hinner).of_eq fun r => ?_
  unfold pullbackEnum
  by_cases h : r.1 < 0 <;> simp


/-- The pullback enumeration generates exactly the open set on which the pullback test exceeds `q₀`.
-/
lemma iUnion_pullbackEnum {E : BitString → ℕ → Option BitString} {f : BitStream → BitStream}
    (hEspec : ∀ u : BitString, {x : CantorSeq | BitStream.finite u ≤ f (BitStream.infinite x)}
      = ⋃ i, (E u i).elim ∅ cantorCylinder)
    (enum : ℚ → ℕ → Option BitString) (q₀ : ℚ) :
    {w : CantorSeq | (q₀ : ℝ) < 0 ∨ ENNReal.ofReal (q₀ : ℝ) < pullbackTest enum f w}
      = ⋃ j, (pullbackEnum E enum q₀ j).elim ∅ cantorCylinder := by
  by_cases hneg : q₀ < 0
  · have hnegR : ((q₀ : ℝ) < 0) := by exact_mod_cast hneg
    refine Set.eq_of_subset_of_subset (fun w _ => ?_) (fun w _ => Or.inl hnegR)
    refine Set.mem_iUnion.2 ⟨0, ?_⟩
    have hval : pullbackEnum E enum q₀ 0 = some [] := by
      unfold pullbackEnum
      rw [if_pos hneg]
    rw [hval]
    change w ∈ cantorCylinder ([] : BitString)
    intro i hi
    simp at hi
  · have hq₀ : 0 ≤ q₀ := not_lt.1 hneg
    have hnegR : ¬ ((q₀ : ℝ) < 0) := by
      push Not
      exact_mod_cast hq₀
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro (h | h)
      · exact absurd h hnegR
      obtain ⟨p, hlt, u, heq, hu⟩ := (lt_pullbackTest_iff hq₀).1 h
      have hmem : w ∈ ⋃ i, (E u i).elim ∅ cantorCylinder := by
        rw [← hEspec u]
        exact hu
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hmem
      obtain ⟨n, hn⟩ : ∃ n : ℕ, Denumerable.ofNat (ℚ × ℕ) n = p :=
        ⟨_, Denumerable.ofNat_encode p⟩
      refine ⟨Nat.pair n k, ?_⟩
      have e1 : (Nat.unpair (Nat.pair n k)).1 = n := by rw [Nat.unpair_pair]
      have e2 : (Nat.unpair (Nat.pair n k)).2 = k := by rw [Nat.unpair_pair]
      have hval : pullbackEnum E enum q₀ (Nat.pair n k) = E u k := by
        unfold pullbackEnum
        rw [if_neg hneg, e1, e2, hn, if_pos hlt, heq]
        rfl
      rw [hval]
      exact hk
    · rintro ⟨j, hj⟩
      refine Or.inr ?_
      rw [lt_pullbackTest_iff hq₀]
      set p : ℚ × ℕ := Denumerable.ofNat (ℚ × ℕ) (Nat.unpair j).1 with hp
      by_cases hlt : q₀ < p.1
      · have hval : pullbackEnum E enum q₀ j = (enum p.1 p.2).bind
            fun u => E u (Nat.unpair j).2 := by
          unfold pullbackEnum
          rw [if_neg hneg, ← hp, if_pos hlt]
        rw [hval] at hj
        cases heq : enum p.1 p.2 with
        | none =>
            rw [heq] at hj
            simp at hj
        | some u =>
            rw [heq] at hj
            refine ⟨p, hlt, u, heq, ?_⟩
            have : w ∈ ⋃ i, (E u i).elim ∅ cantorCylinder :=
              Set.mem_iUnion.2 ⟨(Nat.unpair j).2, hj⟩
            rw [← hEspec u] at this
            exact this
      · have hval : pullbackEnum E enum q₀ j = none := by
          unfold pullbackEnum
          rw [if_neg hneg, ← hp, if_neg hlt]
        rw [hval] at hj
        simp at hj

/-- **The pullback dominates the composition** wherever the image is infinite. -/
lemma le_pullbackTest {f : BitStream → BitStream} {v : CantorSeq → ℝ≥0∞}
    {enum : ℚ → ℕ → Option BitString}
    (hspec : ∀ q : ℚ, {w : CantorSeq | (q : ℝ) < 0 ∨ ENNReal.ofReal (q : ℝ) < v w}
      = ⋃ i, (enum q i).elim ∅ cantorCylinder)
    (w t : CantorSeq) (hft : f (BitStream.infinite w) = BitStream.infinite t) :
    v t ≤ pullbackTest enum f w := by
  refine le_of_forall_lt fun a ha => ?_
  obtain ⟨q, hq0, haq, hqv⟩ := ENNReal.lt_iff_exists_rat_btwn.1 ha
  have hmem : t ∈ {x : CantorSeq | (q : ℝ) < 0 ∨ ENNReal.ofReal (q : ℝ) < v x} := Or.inr hqv
  rw [hspec q] at hmem
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmem
  cases heq : enum q i with
  | none =>
      rw [heq] at hi
      simp at hi
  | some u =>
      rw [heq] at hi
      have hut : BitStream.finite u ≤ f (BitStream.infinite w) := by
        rw [hft]
        exact BitStream.finite_le_infinite_iff.2 hi
      have hle : ENNReal.ofReal ((q : ℝ)) ≤ pullbackTest enum f w := by
        simp only [pullbackTest]
        refine le_iSup_of_le (q, i) ?_
        exact le_iSup_of_le ⟨hq0, u, heq, hut⟩ le_rfl
      exact lt_of_lt_of_le haq hle

/-- **The pullback of a lower semicomputable function along a computable stream
map is lower semicomputable.** -/
theorem isLowerSemicomputableFun_pullbackTest {f : BitStream → BitStream}
    (hf : IsComputableStreamMap f) {enum : ℚ → ℕ → Option BitString}
    (henum : Computable₂ enum) : IsLowerSemicomputableFun (pullbackTest enum f) := by
  obtain ⟨E, hE, hEspec⟩ := exists_uniform_enumerator_setOf_le_comp hf
  exact ⟨pullbackEnum E enum, computable₂_pullbackEnum hE henum,
    fun q => iUnion_pullbackEnum hEspec enum q⟩

/-! ## Almost every image is infinite, and there the pullback is exact -/

/-- **The image of almost every sequence is infinite.** -/
lemma measure_compl_setOf_infinite_comp_eq_zero {μ ν : Measure CantorSeq}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : BitStream → BitStream}
    (hμ : IsComputableMeasure μ) (hf : IsComputableStreamMap f) (hν : IsImageMeasure μ f ν) :
    μ {w : CantorSeq | ¬ ∃ t : CantorSeq, f (BitStream.infinite w) = BitStream.infinite t}
      = 0 := by
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
  refine measure_mono_null (fun w hw => ?_) hzero
  by_contra hcon
  have hrand : IsMartinLofRandom μ w := by
    intro T hT hmem
    exact hcon (hU.2 (⋂ n, T n) ⟨T, hT.1, subset_rfl, hT.2⟩ hmem)
  exact hw (exists_infinite_comp_of_isMartinLofRandom hμ hf hν hrand)

/-- **On the sequences with infinite image the pullback is the composition.** -/
lemma pullbackTest_eq_of_infinite {f : BitStream → BitStream} {v : CantorSeq → ℝ≥0∞}
    {enum : ℚ → ℕ → Option BitString}
    (hspec : ∀ q : ℚ, {w : CantorSeq | (q : ℝ) < 0 ∨ ENNReal.ofReal (q : ℝ) < v w}
      = ⋃ i, (enum q i).elim ∅ cantorCylinder)
    (w t : CantorSeq) (hft : f (BitStream.infinite w) = BitStream.infinite t) :
    pullbackTest enum f w = v t := by
  refine le_antisymm ?_ (le_pullbackTest hspec w t hft)
  simp only [pullbackTest]
  refine iSup_le fun p => iSup_le fun hp => ?_
  obtain ⟨hp0, u, heq, hu⟩ := hp
  have hmem : t ∈ ⋃ i, (enum p.1 i).elim ∅ cantorCylinder := by
    refine Set.mem_iUnion.2 ⟨p.2, ?_⟩
    rw [heq]
    rw [hft] at hu
    exact BitStream.finite_le_infinite_iff.1 hu
  rw [← hspec p.1] at hmem
  rcases hmem with h | h
  · exact absurd h (by push Not; exact_mod_cast hp0)
  · exact le_of_lt h

/-! ## The remaining leaf: the change of variables -/

/-- **The change of variables** (SUV Problem 185, §5.9.3, p. 182): the pullback
of a test still integrates to at most one.

Write `A = {ω | f(ω) is infinite}`; `A` has full `μ`-measure
(`measure_compl_setOf_infinite_comp_eq_zero`) and on it the pullback is exactly
`v ∘ f` (`pullbackTest_eq_of_infinite`).  Write `v` as the monotone limit of the
basic functions `g_s(τ) = 2^{-s}·approx(s, τ↾s)`
(`lowerSemicomputableFun_characterizations`).  The function

`h_s(ω) = ∑_{l(y)=s} 2^{-s}·approx(s,y)·1_{ω | y ⪯ f(ω)}`

is measurable, equals `g_s(f(ω))` on `A` -- the intervals `{ω | y ⪯ f(ω)}` of a
fixed length are disjoint and `ω` lies in the one indexed by `f(ω)↾s` -- and its
integral is `∑_{l(y)=s} 2^{-s}·approx(s,y)·μ {ω | y ⪯ f(ω)} = ∫ g_s dν` by the
image relation and `lintegral_stageFun`.  Monotone convergence (a.e. monotone,
`lintegral_iSup'`) and `g_s ≤ v` finish the computation. -/
theorem lintegral_pullbackTest_le {μ ν : Measure CantorSeq} {f : BitStream → BitStream}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμ : IsComputableMeasure μ)
    (hf : IsComputableStreamMap f) (hν : IsImageMeasure μ f ν) {v : CantorSeq → ℝ≥0∞}
    (hv : IsExpectationBoundedRandomnessTest ν v) {enum : ℚ → ℕ → Option BitString}
    (hspec : ∀ q : ℚ, {w : CantorSeq | (q : ℝ) < 0 ∨ ENNReal.ofReal (q : ℝ) < v w}
      = ⋃ i, (enum q i).elim ∅ cantorCylinder) :
    ∫⁻ w, pullbackTest enum f w ∂μ ≤ 1 := by
  classical
  obtain ⟨E, hE, hEspec⟩ := exists_uniform_enumerator_setOf_le_comp hf
  obtain ⟨approx, hacomp, hamono, hasup⟩ :=
    (lowerSemicomputableFun_characterizations v).2.1.mp hv.1
  set Pre : BitString → Set CantorSeq :=
    fun y => {x : CantorSeq | BitStream.finite y ≤ f (BitStream.infinite x)} with hPre
  have hPremeas : ∀ y, MeasurableSet (Pre y) := by
    intro y
    have : Pre y = ⋃ i, (E y i).elim ∅ cantorCylinder := hEspec y
    rw [this]
    refine MeasurableSet.iUnion fun i => ?_
    cases hEi : E y i with
    | none => simp
    | some z => simpa using measurableSet_cantorCylinder z
  set h : ℕ → CantorSeq → ℝ≥0∞ :=
    fun s w => ∑ y ∈ levelFinset s, dyadicValue (approx s y) s * (Pre y).indicator 1 w with hh
  have hmeas : ∀ s, Measurable (h s) := by
    intro s
    refine Finset.measurable_sum _ fun y _ => ?_
    exact measurable_const.mul (measurable_one.indicator (hPremeas y))
  have hval : ∀ (s : ℕ) (w t : CantorSeq), f (BitStream.infinite w) = BitStream.infinite t →
      h s w = dyadicValue (approx s (cantorPrefix t s)) s := by
    intro s w t hft
    rw [hh]
    simp only
    rw [Finset.sum_eq_single (cantorPrefix t s)]
    · have hmem2 : w ∈ Pre (cantorPrefix t s) := by
        change BitStream.finite (cantorPrefix t s) ≤ f (BitStream.infinite w)
        rw [hft]
        exact BitStream.finite_cantorPrefix_le_infinite t s
      rw [Set.indicator_of_mem hmem2]
      simp
    · intro y hy hne
      have hnot : w ∉ Pre y := by
        intro hmem
        have h1 : BitStream.finite y ≤ BitStream.infinite t := by
          rw [← hft]
          exact hmem
        have h2 : IsCantorPrefix y t := BitStream.finite_le_infinite_iff.1 h1
        have h3 : cantorPrefix t y.length = y := (isCantorPrefix_iff_cantorPrefix_eq y t).1 h2
        rw [mem_levelFinset.1 hy] at h3
        exact hne h3.symm
      first
        | rw [Set.indicator_of_not_mem hnot, mul_zero]
        | rw [Set.indicator_of_notMem hnot, mul_zero]
    · intro hnot
      exact absurd (mem_levelFinset.2 (cantorPrefix_length t s)) hnot
  have hint : ∀ s, ∫⁻ w, h s w ∂μ = ∫⁻ x, stageFun (approx s) s x ∂ν := by
    intro s
    rw [lintegral_stageFun ν (approx s) s, hh]
    simp only
    rw [lintegral_finsetSum]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [lintegral_const_mul _ (measurable_one.indicator (hPremeas y)),
        lintegral_indicator_one (hPremeas y), ← hν y]
    · exact fun y _ => measurable_const.mul (measurable_one.indicator (hPremeas y))
  have hstage_le : ∀ s, ∫⁻ x, stageFun (approx s) s x ∂ν ≤ 1 := by
    intro s
    refine le_trans (lintegral_mono fun x => ?_) hv.2
    rw [hasup x]
    exact le_iSup (fun s => dyadicValue (approx s (cantorPrefix x s)) s) s
  have hAae : {w : CantorSeq | ∃ t : CantorSeq,
      f (BitStream.infinite w) = BitStream.infinite t} ∈ ae μ := by
    rw [mem_ae_iff]
    exact measure_compl_setOf_infinite_comp_eq_zero hμ hf hν
  have hae : (fun w => pullbackTest enum f w) =ᵐ[μ] (fun w => ⨆ s, h s w) := by
    refine Filter.eventuallyEq_of_mem hAae ?_
    rintro w ⟨t, hft⟩
    change pullbackTest enum f w = ⨆ s, h s w
    rw [pullbackTest_eq_of_infinite hspec w t hft, hasup t]
    exact iSup_congr fun s => (hval s w t hft).symm
  calc ∫⁻ w, pullbackTest enum f w ∂μ = ∫⁻ w, ⨆ s, h s w ∂μ := lintegral_congr_ae hae
    _ = ⨆ s, ∫⁻ w, h s w ∂μ := by
        refine lintegral_iSup' (fun s => (hmeas s).aemeasurable) ?_
        filter_upwards [hAae] with w hw
        obtain ⟨t, hft⟩ := hw
        refine monotone_nat_of_le_succ fun s => ?_
        rw [hval s w t hft, hval (s + 1) w t hft]
        exact hamono s t
    _ = ⨆ s, ∫⁻ x, stageFun (approx s) s x ∂ν := by simp only [hint]
    _ ≤ 1 := iSup_le hstage_le

/-- **The pullback of a test for the image measure is a test for the source
measure** (SUV Problem 185, §5.9.3, p. 182). -/
theorem exists_expectationBoundedTest_comp {μ ν : Measure CantorSeq}
    {f : BitStream → BitStream} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsComputableMeasure μ) (hf : IsComputableStreamMap f)
    (hν : IsImageMeasure μ f ν) {v : CantorSeq → ℝ≥0∞}
    (hv : IsExpectationBoundedRandomnessTest ν v) :
    ∃ V : CantorSeq → ℝ≥0∞, IsExpectationBoundedRandomnessTest μ V ∧
      ∀ w t : CantorSeq, f (BitStream.infinite w) = BitStream.infinite t → v t ≤ V w := by
  obtain ⟨enum, henum, hspec⟩ := hv.1
  exact ⟨pullbackTest enum f,
    ⟨isLowerSemicomputableFun_pullbackTest hf henum,
      lintegral_pullbackTest_le hμ hf hν hv hspec⟩,
    fun w t hft => le_pullbackTest hspec w t hft⟩

end Kolmogorov
