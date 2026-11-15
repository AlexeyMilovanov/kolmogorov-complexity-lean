/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Analysis.Asymptotics.Defs
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveLaws
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveSLLN
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.Selection
import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.Complexity.Incompressibility
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Mises-Church randomness

A sequence is Mises-Church random (at frequency `p`) if every selection rule given by a decidable
set of prefixes selects either a finite subsequence or an infinite one with limit frequency `p`.

Main declarations:
* `IsMisesChurchRandomAt`, `IsMisesChurchRandom`: the definition of Mises-Church randomness.
* `isEffectivelyNull_selectPreimage`: the preimage of an effectively null set under the selection
  map of a decidable rule is effectively null.
* `isMisesChurchRandom_of_isMartinLofRandom`: Martin-Löf random sequences are Mises-Church random
  (Theorem 167 of Shen, Uspensky and Vereshchagin).
* `not_computable_of_isMisesChurchRandom`: Mises-Church random sequences are not computable.
-/

namespace Kolmogorov.FrequencyGames

open MeasureTheory Filter Topology

/-! ### The definition -/

/-- **SUV p. 264**, with the frequency as a parameter (Section 9.12 needs other `p`).  Every
Church-admissible rule selects a finite sequence or one with limit frequency `p`. -/
def IsMisesChurchRandomAt (p : ℝ) (w : CantorSeq) : Prop :=
  ∀ R : Set BitString, IsDecidableSet R → FiniteOrFreq p (selectStream R w)

/-- **SUV p. 264.**  *Mises-Church random* (Church stochastic) sequences: the frequency is `1/2`. -/
abbrev IsMisesChurchRandom (w : CantorSeq) : Prop := IsMisesChurchRandomAt (1 / 2) w

open Classical in
/-- Auxiliary for `isEffectivelyNull_selectPreimage_meas` (copy of the private
`measure_selectPreimage_le_aux_cover` of `Selection.lean`). -/
private lemma isEffectivelyNull_selectPreimage_aux_cover (R : Set BitString) (x' : BitString)
    (b : Bool) (w : CantorSeq) :
    ∀ t, x' ++ [b] <+: selectedBits R (cantorPrefix w t) →
      ∃ z, (z ∈ R ∧ selectedBits R z = x') ∧ w ∈ cantorCylinder (z ++ [b]) := by
  intro t
  induction t with
  | zero =>
    intro h
    exfalso
    have h0 : selectedBits R (cantorPrefix w 0) = [] := by
      simp [cantorPrefix, selectedBits, selectedAux]
    rw [h0] at h
    have := h.length_le
    simp at this
  | succ t ih =>
    intro h
    rw [cantorPrefix_succ, selectedBits_append_singleton] at h
    by_cases hz : cantorPrefix w t ∈ R
    · rw [ite_eq_left hz] at h
      rcases List.prefix_concat_iff.mp h with h1 | h1
      · obtain ⟨h2, h3⟩ := List.append_inj' h1.symm rfl
        have hb : b = w t := by simpa using h3.symm
        refine ⟨cantorPrefix w t, ⟨hz, h2⟩, ?_⟩
        change IsCantorPrefix (cantorPrefix w t ++ [b]) w
        rw [isCantorPrefix_iff_cantorPrefix_eq]
        simp only [List.length_append, cantorPrefix_length, List.length_singleton]
        rw [cantorPrefix_succ, hb]
      · exact ih h1
    · rw [ite_eq_right hz, List.append_nil] at h
      exact ih h

open Classical in
/-- Auxiliary for `isEffectivelyNull_selectPreimage_meas` (copy of the private
`measure_selectPreimage_le_aux_antichain` of `Selection.lean`). -/
private lemma isEffectivelyNull_selectPreimage_aux_antichain (R : Set BitString)
    (x' : BitString) {z z' : BitString} (hz : z ∈ R ∧ selectedBits R z = x')
    (hz' : z' ∈ R ∧ selectedBits R z' = x') (hpre : z <+: z') : z = z' := by
  by_contra hne
  obtain ⟨t, rfl⟩ := hpre
  cases t with
  | nil => simp at hne
  | cons c t' =>
    have h1 : z ++ [c] <+: z ++ c :: t' := ⟨t', by simp⟩
    have h2 := selectedBits_prefix R h1
    rw [selectedBits_append_singleton, ite_eq_left hz.1, hz.2, hz'.2] at h2
    have := h2.length_le
    simp at this

/-- Auxiliary for `isEffectivelyNull_selectPreimage_meas` (copy of the private
`measure_selectPreimage_le_aux_preimage_le` of `Selection.lean`). -/
private lemma isEffectivelyNull_selectPreimage_aux_preimage_le (R : Set BitString)
    (x : BitString) :
    uniformMeasure {w : CantorSeq | x ∈ chainPrefixSet (selectChain R w)} ≤
      (1/2:ENNReal)^x.length := by
  induction x using List.reverseRecOn with
  | nil => simp [prob_le_one]
  | append_singleton x' b ih =>
    set W : Set BitString := {z | z ∈ R ∧ selectedBits R z = x'} with hW
    have hsub : {w : CantorSeq | x' ++ [b] ∈ chainPrefixSet (selectChain R w)} ⊆
        ⋃ z : W, cantorCylinder (z.1 ++ [b]) := by
      intro w hw
      obtain ⟨t, ht⟩ := hw
      obtain ⟨z, hz, hwz⟩ := isEffectivelyNull_selectPreimage_aux_cover R x' b w t ht
      exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hwz⟩
    have hsub2 : (⋃ z : W, cantorCylinder z.1) ⊆
        {w : CantorSeq | x' ∈ chainPrefixSet (selectChain R w)} := by
      intro w hw
      obtain ⟨⟨z, hz1, hz2⟩, hwz⟩ := Set.mem_iUnion.mp hw
      refine ⟨z.length, ?_⟩
      have : cantorPrefix w z.length = z := (isCantorPrefix_iff_cantorPrefix_eq z w).mp hwz
      change x' <+: selectedBits R (cantorPrefix w z.length)
      rw [this, hz2]
    have hdisj : Pairwise (Function.onFun Disjoint (fun z : W => cantorCylinder z.1)) := by
      intro z z' hne
      apply cantorCylinder_disjoint_of_incompatible
      · intro hpre
        exact hne (Subtype.ext
          (isEffectivelyNull_selectPreimage_aux_antichain R x' z.2 z'.2 hpre))
      · intro hpre
        exact hne (Subtype.ext
          (isEffectivelyNull_selectPreimage_aux_antichain R x' z'.2 z.2 hpre).symm)
    have hmass : ∀ z : W, uniformMeasure (cantorCylinder (z.1 ++ [b])) =
        2⁻¹ * uniformMeasure (cantorCylinder z.1) := by
      intro z
      have h1 := cantorMass_uniformMeasure (z.1 ++ [b])
      have h2 := cantorMass_uniformMeasure z.1
      unfold cantorMass at h1 h2
      rw [h1, h2, List.length_append, List.length_singleton, pow_succ, mul_comm]
    have hone : (1/2 : ENNReal) = 2⁻¹ := one_div 2
    calc uniformMeasure {w : CantorSeq | x' ++ [b] ∈ chainPrefixSet (selectChain R w)}
        ≤ uniformMeasure (⋃ z : W, cantorCylinder (z.1 ++ [b])) := measure_mono hsub
      _ ≤ ∑' z : W, uniformMeasure (cantorCylinder (z.1 ++ [b])) := measure_iUnion_le _
      _ = ∑' z : W, 2⁻¹ * uniformMeasure (cantorCylinder z.1) := by
          exact tsum_congr hmass
      _ = 2⁻¹ * ∑' z : W, uniformMeasure (cantorCylinder z.1) := ENNReal.tsum_mul_left
      _ = 2⁻¹ * uniformMeasure (⋃ z : W, cantorCylinder z.1) := by
          rw [measure_iUnion hdisj (fun z => measurableSet_cantorCylinder _)]
      _ ≤ 2⁻¹ * uniformMeasure {w : CantorSeq | x' ∈ chainPrefixSet (selectChain R w)} := by
          gcongr
      _ ≤ 2⁻¹ * (1/2:ENNReal)^x'.length := by gcongr
      _ = (1/2:ENNReal)^(x' ++ [b]).length := by
          rw [List.length_append, List.length_singleton, pow_succ, hone, mul_comm]

/-- Step 1 of the proof of `isEffectivelyNull_selectPreimage`: for arbitrary `R` and every
string `x`, `uniformMeasure {w | ∃ t, x <+: selectChain R w t} ≤ 2^{-|x|}`. -/
private lemma isEffectivelyNull_selectPreimage_meas (R : Set BitString) (x : BitString) :
    uniformMeasure {w | ∃ t, x <+: selectChain R w t} ≤ (2 : ENNReal)⁻¹ ^ x.length := by
  have h := isEffectivelyNull_selectPreimage_aux_preimage_le R x
  rw [one_div] at h
  exact h

/-- Auxiliary for step 2: `selectedAux` as a left fold with a Boolean test for `R`. -/
private lemma isEffectivelyNull_selectPreimage_foldl_eq (R : Set BitString)
    (f : BitString → Bool) (hf : ∀ a, f a = true ↔ a ∈ R) (y : BitString) :
    ∀ pre out : BitString,
      y.foldl (fun (s : BitString × BitString) (b : Bool) =>
          (s.1 ++ [b], cond (f s.1) (s.2 ++ [b]) s.2)) (pre, out)
        = (pre ++ y, out ++ selectedAux R pre y) := by
  induction y with
  | nil => intro pre out; simp [selectedAux]
  | cons b rest ih =>
    intro pre out
    simp only [List.foldl_cons]
    rw [ih]
    by_cases h : pre ∈ R
    · have hfp : f pre = true := (hf pre).2 h
      simp [selectedAux, h, hfp]
    · have hfp : f pre = false := by
        cases hfp' : f pre
        · rfl
        · exact absurd ((hf pre).1 hfp') h
      simp [selectedAux, h, hfp]

/-- Auxiliary for step 2: for decidable `R` the selected bits of a string are computable. -/
lemma isEffectivelyNull_selectPreimage_computable_selectedBits {R : Set BitString}
    (hR : IsDecidableSet R) : Computable (fun y : BitString => selectedBits R y) := by
  obtain ⟨f, hf, hfR⟩ := hR
  have hs : Computable (fun q : BitString × ((BitString × BitString) × Bool) => q.2.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have ho : Computable (fun q : BitString × ((BitString × BitString) × Bool) => q.2.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.snd)
  have hb : Computable (fun q : BitString × ((BitString × BitString) × Bool) => q.2.2) :=
    Computable.snd.comp Computable.snd
  have h1 : Computable (fun q : BitString × ((BitString × BitString) × Bool) =>
      q.2.1.1 ++ [q.2.2]) := Computable.list_concat.comp hs hb
  have h2 : Computable (fun q : BitString × ((BitString × BitString) × Bool) =>
      q.2.1.2 ++ [q.2.2]) := Computable.list_concat.comp ho hb
  have h3 : Computable (fun q : BitString × ((BitString × BitString) × Bool) => f q.2.1.1) :=
    hf.comp hs
  have hstep : Computable₂ (fun (_ : BitString) (p : (BitString × BitString) × Bool) =>
      ((p.1.1 ++ [p.2], cond (f p.1.1) (p.1.2 ++ [p.2]) p.1.2) : BitString × BitString)) :=
    Computable.pair h1 (Computable.cond h3 h2 ho)
  have hfold := Computable.list_foldl (l := fun y : BitString => y)
    (g := fun _ : BitString => (([] : BitString), ([] : BitString)))
    (h := fun (_ : BitString) (p : (BitString × BitString) × Bool) =>
      ((p.1.1 ++ [p.2], cond (f p.1.1) (p.1.2 ++ [p.2]) p.1.2) : BitString × BitString))
    Computable.id (Computable.const _) hstep
  refine (Computable.snd.comp hfold).of_eq fun y => ?_
  simp only
  rw [isEffectivelyNull_selectPreimage_foldl_eq R f hfR y [] []]
  simp [selectedBits]

/-- Step 2 of the proof of `isEffectivelyNull_selectPreimage`: for decidable `R`, `x ↦ {w
| ∃ t, x <+: selectChain R w t}` is effectively open uniformly in `x`. -/
private lemma isEffectivelyNull_selectPreimage_open {R : Set BitString} (hR : IsDecidableSet
    R) :
    ∃ g : BitString → ℕ → Option BitString, Computable₂ g ∧
      ∀ x, {w | ∃ t, x <+: selectChain R w t} = ⋃ i, (g x i).elim ∅ cantorCylinder := by
  have hsel := isEffectivelyNull_selectPreimage_computable_selectedBits hR
  refine ⟨fun x i => (Encodable.decode₂ BitString i).bind fun y =>
    cond (decide (x = (selectedBits R y).take x.length)) (some y) none, ?_, ?_⟩
  · have hdec : Computable (fun p : BitString × ℕ => Encodable.decode₂ BitString p.2) :=
      (Primrec.decode₂.comp Primrec.snd).to_comp
    have hx : Computable (fun q : (BitString × ℕ) × BitString => q.1.1) :=
      Computable.fst.comp Computable.fst
    have hy : Computable (fun q : (BitString × ℕ) × BitString => q.2) := Computable.snd
    have hlen : Computable (fun q : (BitString × ℕ) × BitString => q.1.1.length) :=
      Computable.list_length.comp hx
    have htake : Computable (fun q : (BitString × ℕ) × BitString =>
        (selectedBits R q.2).take q.1.1.length) :=
      (Primrec.list_take.to_comp).comp hlen (hsel.comp hy)
    have heq : Computable (fun q : (BitString × ℕ) × BitString =>
        decide (q.1.1 = (selectedBits R q.2).take q.1.1.length)) :=
      (Primrec.eq.decide.to_comp).comp hx htake
    have hbody : Computable₂ (fun (p : BitString × ℕ) (y : BitString) =>
        cond (decide (p.1 = (selectedBits R y).take p.1.length)) (some y) none) :=
      Computable.cond heq (Computable.option_some.comp hy) (Computable.const none)
    exact Computable.option_bind hdec hbody
  · intro x
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨Encodable.encode (cantorPrefix w t), ?_⟩
      have hp : x = (selectedBits R (cantorPrefix w t)).take x.length :=
        List.prefix_iff_eq_take.mp ht
      have hd : decide (x = (selectedBits R (cantorPrefix w t)).take x.length) = true :=
        decide_eq_true hp
      simp only [Encodable.encodek₂, Option.bind_some, hd, Bool.cond_true, Option.elim_some]
      exact mem_cantorCylinder_cantorPrefix w t
    · rintro ⟨i, hi⟩
      cases hdi : Encodable.decode₂ BitString i with
      | none => simp [hdi] at hi
      | some y =>
        simp only [hdi, Option.bind_some] at hi
        by_cases hp : x = (selectedBits R y).take x.length
        · have hd : decide (x = (selectedBits R y).take x.length) = true := decide_eq_true hp
          simp only [hd, Bool.cond_true, Option.elim_some] at hi
          refine ⟨y.length, ?_⟩
          have hpy : cantorPrefix w y.length = y := (isCantorPrefix_iff_cantorPrefix_eq y w).mp hi
          change x <+: selectedBits R (cantorPrefix w y.length)
          rw [hpy]
          exact List.prefix_iff_eq_take.mpr hp
        · have hd : decide (x = (selectedBits R y).take x.length) = false := decide_eq_false hp
          simp [hd] at hi

/-- Step 3 of the proof of `isEffectivelyNull_selectPreimage`: there is a uniformly
effectively open family `W` that covers the `S_R`-preimage of any uniformly effectively open family
`V`, provided `R` is decidable, and `W n` has measure at most the measure of `V n`. -/
private lemma isEffectivelyNull_selectPreimage_cover {R : Set BitString}
    (hR : IsDecidableSet R) {V : ℕ → Set CantorSeq} (hV : IsUniformlyEffectiveOpen V) :
    ∃ W : ℕ → Set CantorSeq, IsUniformlyEffectiveOpen W ∧
      (∀ n, selectPreimage R (V n) ⊆ W n) ∧
      (∀ n, uniformMeasure (W n) ≤ uniformMeasure (V n)) := by
  obtain ⟨f, hf, hVf⟩ := hV
  obtain ⟨gg, hgg, hggeq⟩ := isEffectivelyNull_selectPreimage_open hR
  have hd : Computable₂ (fun n i => disjEnum (f n) i) := computable_disjEnum hf
  -- enumerator of the cover
  let F : ℕ → ℕ → Option BitString := fun n k =>
    (disjEnum (f n) (Nat.unpair k).1).bind fun x => gg x (Nat.unpair k).2
  have hF : Computable₂ F := by
    have h1 : Computable (fun p : ℕ × ℕ => disjEnum (f p.1) (Nat.unpair p.2).1) :=
      hd.comp Computable.fst
        ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp)
    have h2 : Computable₂ (fun (p : ℕ × ℕ) (x : BitString) => gg x (Nat.unpair p.2).2) :=
      hgg.comp Computable.snd
        ((Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))).to_comp)
    exact Computable.option_bind h1 h2
  -- the cover is the union over the disjoint pieces of `V n` of the sets `P_x`
  let S : ℕ → ℕ → Set CantorSeq := fun n i =>
    (disjEnum (f n) i).elim ∅ fun x => {w | ∃ t, x <+: selectChain R w t}
  have hW : ∀ n, (⋃ k, (F n k).elim ∅ cantorCylinder) = ⋃ i, S n i := by
    intro n
    ext w
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      cases hx : disjEnum (f n) (Nat.unpair k).1 with
      | none => simp [F, hx] at hk
      | some x =>
        refine ⟨(Nat.unpair k).1, ?_⟩
        simp only [S, hx, Option.elim_some]
        rw [hggeq x]
        simp only [Set.mem_iUnion]
        exact ⟨(Nat.unpair k).2, by simpa [F, hx] using hk⟩
    · rintro ⟨i, hi⟩
      cases hx : disjEnum (f n) i with
      | none => simp [S, hx] at hi
      | some x =>
        simp only [S, hx, Option.elim_some] at hi
        rw [hggeq x] at hi
        simp only [Set.mem_iUnion] at hi
        obtain ⟨j, hj⟩ := hi
        exact ⟨Nat.pair i j, by simpa [F, hx, Nat.unpair_pair] using hj⟩
  refine ⟨fun n => ⋃ k, (F n k).elim ∅ cantorCylinder, ⟨F, hF, fun n => rfl⟩, ?_, ?_⟩
  · intro n w hw
    rcases hw with ⟨u, hu, hsw⟩
    change w ∈ ⋃ k, (F n k).elim ∅ cantorCylinder
    rw [hW n]
    rw [hVf n] at hu
    have hu' : u ∈ ⋃ i, coverSet (disjEnum (f n)) i := by
      rw [coverSet_disjEnum_iUnion]
      exact hu
    simp only [Set.mem_iUnion] at hu' ⊢
    obtain ⟨i, hi⟩ := hu'
    refine ⟨i, ?_⟩
    cases hx : disjEnum (f n) i with
    | none => simp [coverSet, hx] at hi
    | some x =>
      simp only [coverSet, hx, Option.elim_some] at hi
      simp only [S, hx, Option.elim_some]
      have h := BitStream.finite_le_ofPrefixSet_iff
        (isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)) x
      have hsw' : BitStream.ofPrefixSet (chainPrefixSet (selectChain R w))
          (isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)) = .infinite u := hsw
      rw [hsw'] at h
      exact h.mp hi
  · intro n
    change uniformMeasure (⋃ k, (F n k).elim ∅ cantorCylinder) ≤ uniformMeasure (V n)
    rw [hW n]
    calc uniformMeasure (⋃ i, S n i) ≤ ∑' i, uniformMeasure (S n i) := measure_iUnion_le _
      _ ≤ ∑' i, (disjEnum (f n) i).elim 0 (cantorMass uniformMeasure) := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          cases hx : disjEnum (f n) i with
          | none => simp [S, hx]
          | some x =>
            simp only [S, hx, Option.elim_some]
            rw [cantorMass_uniformMeasure]
            exact isEffectivelyNull_selectPreimage_meas R x
      _ = uniformMeasure (⋃ j, coverSet (f n) j) := tsum_measure_disjEnum uniformMeasure (f n)
      _ = uniformMeasure (V n) := by rw [hVf n]; rfl

/-- **Proof of Theorem 167, SUV p. 264.**  For decidable `R` the `S_R`-preimage of a uniform
effectively null set is effectively null. -/
theorem isEffectivelyNull_selectPreimage {R : Set BitString} (hR : IsDecidableSet R)
    {U : Set CantorSeq} (hU : IsEffectivelyNull uniformMeasure U) :
    IsEffectivelyNull uniformMeasure (selectPreimage R U) := by
  rcases hU with ⟨V, hV, hUV, hVbound⟩
  rcases isEffectivelyNull_selectPreimage_cover hR hV with ⟨W, hW, hWcover, hWbound⟩
  use W
  refine ⟨hW, ?_, ?_⟩
  · intro w hw
    simp only [Set.mem_iInter, selectPreimage] at hw ⊢
    intro n
    rcases hw with ⟨u, hu, hinf⟩
    have huv : u ∈ V n := Set.mem_iInter.mp (hUV hu) n
    have hwv : ∃ u ∈ V n, selectStream R w = .infinite u := ⟨u, huv, hinf⟩
    exact hWcover n hwv
  · intro n
    exact (hWbound n).trans (hVbound n)

/-- **SUV Theorem 167, p. 264.**  Every Martin-Löf random sequence with respect to the uniform
measure is Mises-Church random. -/
theorem isMisesChurchRandom_of_isMartinLofRandom {w : CantorSeq}
    (hw : IsMartinLofRandom uniformMeasure w) : IsMisesChurchRandom w := by
  intro R hR
  have hU := isEffectivelyNull_notTendsto_freqOne
  have hpre := isEffectivelyNull_selectPreimage hR hU
  have hrand := isEffectivelyNull_iff_forall_not_random isComputableMeasure_uniform
      (selectPreimage R {x | ¬Tendsto (fun n => freqOne x n) atTop (𝓝 (1 / 2))})
  have hw_not_in : w ∉ selectPreimage R {x | ¬Tendsto (fun n => freqOne x n) atTop (𝓝 (1 / 2))} :=
      mt (hrand.1 hpre w) (by simpa using hw)
  rcases hsw : selectStream R w with u | u
  · exact trivial
  · dsimp [FiniteOrFreq]
    dsimp [HasLimitFreq]
    have h1 : u ∉ {x | ¬Tendsto (fun n => freqOne x n) atTop (𝓝 (1 / 2))} := by
      intro hu
      apply hw_not_in
      dsimp [selectPreimage]
      exact ⟨u, hu, hsw⟩
    dsimp at h1
    push Not at h1
    have h2 : Tendsto (fun n => ((freqOne u n : ℚ) : ℝ)) atTop (𝓝 ((1/2 : ℚ) : ℝ)) := by
      exact Tendsto.comp (continuous_algebraMap ℚ ℝ).continuousAt h1
    simpa using h2

/-- The rule `{x | w |x| = b}` is decidable when `w` is computable. -/
private theorem not_computable_of_isMisesChurchRandom_decidable
    {w : CantorSeq} (hw : Computable w) (b : Bool) :
    IsDecidableSet {x : BitString | w x.length = b} := by
  have hlen : Computable (fun x : BitString => w x.length) :=
    hw.comp Primrec.list_length.to_comp
  refine ⟨fun x => if b then w x.length else !(w x.length), ?_, ?_⟩
  · cases b
    · exact (Primrec.not.to_comp).comp hlen
    · exact hlen
  · intro x
    cases b <;> cases h : w x.length <;> simp [h]

/-- If `w` has infinitely many `b`'s, the rule `{x | w |x| = b}` selects an infinite sequence all of
whose terms are `b`, so the selection is not finite and not balanced. -/
private theorem not_computable_of_isMisesChurchRandom_not_finiteOrFreq
    {w : CantorSeq} (b : Bool) (hinf : ∀ N, ∃ n, N ≤ n ∧ w n = b) :
    ¬ FiniteOrFreq (1 / 2) (selectStream {x : BitString | w x.length = b} w) := by
  classical
  set R : Set BitString := {x : BitString | w x.length = b} with hR
  have hall : ∀ t, ∀ a ∈ selectedBits R (cantorPrefix w t), a = b := by
    intro t
    induction t with
    | zero => simp [cantorPrefix, selectedBits, selectedAux]
    | succ t ih =>
      intro a ha
      rw [cantorPrefix_succ, selectedBits_append_singleton] at ha
      by_cases hz : cantorPrefix w t ∈ R
      · rw [ite_eq_left hz] at ha
        rcases List.mem_append.mp ha with h | h
        · exact ih a h
        · have : w t = b := by simpa [hR] using hz
          simp only [List.mem_singleton] at h
          rw [h, this]
      · rw [ite_eq_right hz] at ha
        simp only [List.append_nil] at ha
        exact ih a ha
  have hunb : ∀ M, ∃ t, M ≤ (selectedBits R (cantorPrefix w t)).length := by
    intro M
    induction M with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ M ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨n, hn, hwn⟩ := hinf t
      refine ⟨n + 1, ?_⟩
      have hmono := selectedBits_prefix R (cantorPrefix_mono w hn)
      have hlen := hmono.length_le
      rw [cantorPrefix_succ, selectedBits_append_singleton]
      have hz : cantorPrefix w n ∈ R := by simpa [hR] using hwn
      rw [ite_eq_left hz]
      simp
      omega
  have key : ∀ x, BitStream.finite x ≤ selectStream R w ↔ x ∈ chainPrefixSet (selectChain R w) :=
    fun x => BitStream.finite_le_ofPrefixSet_iff
      (isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)) x
  rcases hs : selectStream R w with y | u
  · exfalso
    obtain ⟨t, ht⟩ := hunb (y.length + 1)
    have h1 : selectChain R w t ∈ chainPrefixSet (selectChain R w) := ⟨t, List.prefix_rfl⟩
    rw [← key, hs] at h1
    have := h1.length_le
    simp only [selectChain] at this
    omega
  · intro hfreq
    have hu : ∀ i, u i = b := by
      intro i
      have hmem : cantorPrefix u (i + 1) ∈ chainPrefixSet (selectChain R w) := by
        rw [← key, hs]
        change IsCantorPrefix _ u
        rw [isCantorPrefix_iff_cantorPrefix_eq]
        simp
      obtain ⟨s, hs'⟩ := hmem
      have hi : i < (cantorPrefix u (i + 1)).length := by simp
      have hmem2 : (cantorPrefix u (i + 1))[i] ∈ selectedBits R (cantorPrefix w s) :=
        hs'.subset (List.getElem_mem hi)
      have := hall s _ hmem2
      simpa using this
    have hfun : u = fun _ => b := funext hu
    change HasLimitFreq (1 / 2) u at hfreq
    unfold HasLimitFreq at hfreq
    have hfreq1 : ∀ n, 0 < n → (freqOne u n : ℝ) = if b then 1 else 0 := by
      intro n hn
      subst hfun
      simp only [freqOne, cantorPrefix]
      have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
      cases b <;> simp [List.count_replicate, hn']
    have hlim : Tendsto (fun n => (freqOne u n : ℝ)) atTop (nhds (if b then 1 else 0)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact (hfreq1 n hn).symm
    have := tendsto_nhds_unique hfreq hlim
    cases b <;> norm_num at this

/-- **SUV p. 266.**  A Mises-Church random sequence is not computable: a computable sequence has a
computable rule selecting only zeros or only ones. -/
theorem not_computable_of_isMisesChurchRandom {w : CantorSeq} (hw : IsMisesChurchRandom w) :
    ¬ Computable w := by
  intro hc
  by_cases h : ∀ N, ∃ n, N ≤ n ∧ w n = false
  · exact not_computable_of_isMisesChurchRandom_not_finiteOrFreq false h
      (hw _ (not_computable_of_isMisesChurchRandom_decidable hc false))
  · push Not at h
    obtain ⟨N, hN⟩ := h
    refine not_computable_of_isMisesChurchRandom_not_finiteOrFreq true (fun M => ?_)
      (hw _ (not_computable_of_isMisesChurchRandom_decidable hc true))
    refine ⟨max M N, le_max_left _ _, ?_⟩
    have := hN (max M N) (le_max_right _ _)
    simpa using this

end Kolmogorov.FrequencyGames
