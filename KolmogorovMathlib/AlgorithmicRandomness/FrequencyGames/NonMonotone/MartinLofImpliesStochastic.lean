/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.KLRules

/-!
# Martin Lof Implies Stochastic

A sequence that is Martin-Löf random for a Bernoulli measure `B_p` with computable parameter `p`
has limit frequency `p` along every admissible Kolmogorov-Loveland (non-monotone) selection rule
(SUV Theorem 192(b)).  The proof combines Hoeffding tail bounds for the first `n` bits, a
comparison of the selected sequence with `B_p`, effective openness of the resulting events, and
a union bound that yields a Martin-Löf test.

The main declaration is `isMisesKLRandomAt_of_isMartinLofRandom_bernoulli`.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-! ### Helpers for `isMisesKLRandomAt_of_isMartinLofRandom_bernoulli` (SUV Theorem 192(b))

Following the book: Hoeffding tails for the first `n` bits (step 1); the selected sequence is no
likelier than `B_p` itself to begin with `u`, for an arbitrary non-monotone rule (step 2); the
corresponding events are effectively open for admissible rules (step 3); union bound over the
strings of a given length (step 4); the Martin-Löf test and the limit frequency (step 5). -/

private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_tail_gt {p : NNReal}
    (hp : p ≤ 1) (a b : ℕ) (hb : 0 < b) (k n : ℕ)
    (hq : (p : ℝ) + 1 / ((k : ℝ) + 1) ≤ (a : ℝ) / b) :
    bernoulliMeasure p hp {w | a * n < b * (cantorPrefix w n).count true} ≤
      ENNReal.ofReal (Real.exp (-(2 * n) / ((k : ℝ) + 1) ^ 2)) := by
  have hsub : {w : CantorSeq | a * n < b * (cantorPrefix w n).count true} ⊆
      {w : CantorSeq | (n : ℝ) / ((k : ℝ) + 1)
        ≤ ∑ i ∈ Finset.range n, (bitVal (w i) - (p : ℝ))} := by
    intro w hw
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    set c := (cantorPrefix w n).count true with hc
    have h1 : (a : ℝ) * n < (b : ℝ) * c := by exact_mod_cast hw
    have h2 : (a : ℝ) / b * n < c := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hb']
      linarith
    have h3 : (n : ℝ) * ((p : ℝ) + 1 / ((k : ℝ) + 1)) ≤ (n : ℝ) * ((a : ℝ) / b) :=
      mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg n)
    have h3' : (n : ℝ) * (p : ℝ) + (n : ℝ) * (1 / ((k : ℝ) + 1)) ≤ (n : ℝ) * ((a : ℝ) / b) := by
      rw [← mul_add]; exact h3
    have hsum1 : ∑ i ∈ Finset.range n, (bitVal (w i) - (p : ℝ)) = (c : ℝ) - n * p := by
      rw [Finset.sum_sub_distrib, sum_bitVal_eq_count, ← hc, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
    have h4 : (n : ℝ) / ((k : ℝ) + 1) = (n : ℝ) * (1 / ((k : ℝ) + 1)) := by ring
    change (n : ℝ) / ((k : ℝ) + 1) ≤ _
    rw [hsum1, h4]
    linarith
  have hAle : bernoulliMeasure p hp {w : CantorSeq | (n : ℝ) / ((k : ℝ) + 1)
        ≤ ∑ i ∈ Finset.range n, (bitVal (w i) - (p : ℝ))}
      ≤ ENNReal.ofReal (Real.exp (-(2 * n) / ((k : ℝ) + 1) ^ 2)) := by
    have h := measureReal_sum_ge (bernoulliMeasure p hp) k n
      (fun i w => bitVal (w i) - (p : ℝ))
      (iIndepFun_bernoulli_centered p hp) (hasSubgaussian_bernoulli_centered p hp)
    have hfin : bernoulliMeasure p hp {w : CantorSeq | (n : ℝ) / ((k : ℝ) + 1)
        ≤ ∑ i ∈ Finset.range n, (bitVal (w i) - (p : ℝ))} ≠ ⊤ := measure_ne_top _ _
    calc bernoulliMeasure p hp {w : CantorSeq | (n : ℝ) / ((k : ℝ) + 1)
          ≤ ∑ i ∈ Finset.range n, (bitVal (w i) - (p : ℝ))}
        = ENNReal.ofReal ((bernoulliMeasure p hp).real {w : CantorSeq | (n : ℝ) / ((k : ℝ) + 1)
          ≤ ∑ i ∈ Finset.range n, (bitVal (w i) - (p : ℝ))}) :=
          (ENNReal.ofReal_toReal hfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h
  exact (measure_mono hsub).trans hAle

private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_tail_lt {p : NNReal}
    (hp : p ≤ 1) (a b : ℕ) (hb : 0 < b) (k n : ℕ)
    (hq : (a : ℝ) / b + 1 / ((k : ℝ) + 1) ≤ (p : ℝ)) :
    bernoulliMeasure p hp {w | b * (cantorPrefix w n).count true < a * n} ≤
      ENNReal.ofReal (Real.exp (-(2 * n) / ((k : ℝ) + 1) ^ 2)) := by
  have hsub : {w : CantorSeq | b * (cantorPrefix w n).count true < a * n} ⊆
      {w : CantorSeq | (n : ℝ) / ((k : ℝ) + 1)
        ≤ ∑ i ∈ Finset.range n, ((p : ℝ) - bitVal (w i))} := by
    intro w hw
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    set c := (cantorPrefix w n).count true with hc
    have h1 : (b : ℝ) * c < (a : ℝ) * n := by exact_mod_cast hw
    have h2 : (c : ℝ) < (a : ℝ) / b * n := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ hb']
      linarith
    have h3 : (n : ℝ) * ((a : ℝ) / b + 1 / ((k : ℝ) + 1)) ≤ (n : ℝ) * (p : ℝ) :=
      mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg n)
    have h3' : (n : ℝ) * ((a : ℝ) / b) + (n : ℝ) * (1 / ((k : ℝ) + 1)) ≤ (n : ℝ) * (p : ℝ) := by
      rw [← mul_add]; exact h3
    have hsum2 : ∑ i ∈ Finset.range n, ((p : ℝ) - bitVal (w i)) = (n : ℝ) * p - c := by
      rw [Finset.sum_sub_distrib, sum_bitVal_eq_count, ← hc, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
    have h4 : (n : ℝ) / ((k : ℝ) + 1) = (n : ℝ) * (1 / ((k : ℝ) + 1)) := by ring
    change (n : ℝ) / ((k : ℝ) + 1) ≤ _
    rw [hsum2, h4]
    linarith
  have hBle : bernoulliMeasure p hp {w : CantorSeq | (n : ℝ) / ((k : ℝ) + 1)
        ≤ ∑ i ∈ Finset.range n, ((p : ℝ) - bitVal (w i))}
      ≤ ENNReal.ofReal (Real.exp (-(2 * n) / ((k : ℝ) + 1) ^ 2)) := by
    have h := measureReal_sum_ge (bernoulliMeasure p hp) k n
      (fun i w => (p : ℝ) - bitVal (w i))
      (iIndepFun_bernoulli_centered_neg p hp) (hasSubgaussian_bernoulli_centered_neg p hp)
    have hfin : bernoulliMeasure p hp {w : CantorSeq | (n : ℝ) / ((k : ℝ) + 1)
        ≤ ∑ i ∈ Finset.range n, ((p : ℝ) - bitVal (w i))} ≠ ⊤ := measure_ne_top _ _
    calc bernoulliMeasure p hp {w : CantorSeq | (n : ℝ) / ((k : ℝ) + 1)
          ≤ ∑ i ∈ Finset.range n, ((p : ℝ) - bitVal (w i))}
        = ENNReal.ofReal ((bernoulliMeasure p hp).real {w : CantorSeq | (n : ℝ) / ((k : ℝ) + 1)
          ≤ ∑ i ∈ Finset.range n, ((p : ℝ) - bitVal (w i))}) :=
          (ENNReal.ofReal_toReal hfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h
  exact (measure_mono hsub).trans hBle
/-- The coordinates of a Cantor sequence are independent under a Bernoulli measure. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_iIndep (p : NNReal)
    (hp : p ≤ 1) :
    ProbabilityTheory.iIndepFun (fun (i : ℕ) (w : CantorSeq) => w i) (bernoulliMeasure p hp) :=
  ProbabilityTheory.iIndepFun_infinitePi (X := fun _ : ℕ => (id : Bool → Bool))
    (fun _ => measurable_id)

/-- The restriction of a Cantor sequence to the coordinates in a finite set `S`. -/
private def isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_restrict (S : Finset ℕ)
    (w : CantorSeq) : S → Bool := fun i => w i

private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_measurable_restrict
    (S : Finset ℕ) :
    Measurable (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_restrict S) :=
  measurable_pi_iff.2 (fun i => measurable_pi_apply (i : ℕ))

/-- An event depending only on the coordinates in `S` is the preimage of its image under the
restriction to `S`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_eq_preimage (S : Finset ℕ)
    (E : Set CantorSeq)
    (hE : ∀ w w' : CantorSeq, (∀ i ∈ S, w i = w' i) → (w ∈ E ↔ w' ∈ E)) :
    E = isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_restrict S ⁻¹'
        (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_restrict S '' E) := by
  ext w
  constructor
  · intro hw
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w', hw', hww'⟩
    have hcoord : ∀ i ∈ S, w' i = w i := by
      intro i hi
      have := congrFun hww' ⟨i, hi⟩
      simpa [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_restrict] using this
    exact (hE w' w hcoord).1 hw'

/-- The probability that the `n`-th coordinate is `b` is the mass of the cylinder `[b]`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_coord_mass {p : NNReal}
    (hp : p ≤ 1) (n : ℕ) (b : Bool) :
    bernoulliMeasure p hp {w : CantorSeq | w n = b} =
      cantorMass (bernoulliMeasure p hp) [b] := by
  have hmp := fun i : ℕ => measurePreserving_eval_infinitePi
        (fun _ : ℕ => ProbabilityTheory.bernoulliMeasure true false
          ⟨p, p.2, NNReal.coe_le_one.mpr hp⟩) i
  have h1 : {w : CantorSeq | w n = b} = (Function.eval n : CantorSeq → Bool) ⁻¹' {b} := by
    ext w
    simp [Function.eval]
  have h0 : cantorCylinder [b] = (Function.eval 0 : CantorSeq → Bool) ⁻¹' {b} := by
    ext w
    simp only [cantorCylinder, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
      Function.eval]
    constructor
    · intro hw
      have := hw 0 (by simp)
      simpa using this
    · intro hw i hi
      have : i = 0 := by simp only [List.length_singleton] at hi; omega
      subst this; simpa using hw
  unfold cantorMass bernoulliMeasure
  rw [h0, h1, (hmp n).measure_preimage (measurableSet_singleton b).nullMeasurableSet,
    (hmp 0).measure_preimage (measurableSet_singleton b).nullMeasurableSet]

/-- Step 2a: a coordinate `n ∉ S` is independent of an event that depends only on the
coordinates in the finite set `S`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_indep {p : NNReal}
    (hp : p ≤ 1) (S : Finset ℕ) (n : ℕ) (hn : n ∉ S)
    (E : Set CantorSeq)
    (hE : ∀ w w' : CantorSeq, (∀ i ∈ S, w i = w' i) → (w ∈ E ↔ w' ∈ E)) (b : Bool) :
    bernoulliMeasure p hp (E ∩ {w | w n = b}) =
      bernoulliMeasure p hp E * cantorMass (bernoulliMeasure p hp) [b] := by
  classical
  have hdisj : Disjoint S ({n} : Finset ℕ) := Finset.disjoint_singleton_right.2 hn
  have h := (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_iIndep p hp).indepFun_finset
      S {n} hdisj
    (fun i => measurable_pi_apply i)
  let E' : Set (S → Bool) := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_restrict S
      '' E
  let t : Set (({n} : Finset ℕ) → Bool) :=
    {x | x ⟨n, Finset.mem_singleton_self n⟩ = b}
  have hE' : MeasurableSet E' := (Set.toFinite E').measurableSet
  have ht : MeasurableSet t := (Set.toFinite t).measurableSet
  have hEeq : E = isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_restrict S ⁻¹' E' :=
      isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_eq_preimage S E hE
  have hteq : {w : CantorSeq | w n = b} =
      (fun (w : CantorSeq) (i : ({n} : Finset ℕ)) => w i) ⁻¹' t := by
    ext w
    simp [t]
  have key := h.measure_inter_preimage_eq_mul E' t hE' ht
  have key' : bernoulliMeasure p hp (E ∩ {w | w n = b}) =
      bernoulliMeasure p hp E * bernoulliMeasure p hp {w : CantorSeq | w n = b} := by
    rw [hteq, hEeq]
    exact key
  rw [key', isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_coord_mass hp n b]

/-- Step 2a': an event that depends only on finitely many coordinates is measurable. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_measurable (S : Finset ℕ)
    (E : Set CantorSeq)
    (hE : ∀ w w' : CantorSeq, (∀ i ∈ S, w i = w' i) → (w ∈ E ↔ w' ∈ E)) :
    MeasurableSet E := by
  rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_eq_preimage S E hE]
  exact (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_measurable_restrict S)
    (Set.toFinite (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_restrict S ''
        E)).measurableSet
/-- Auxiliary: the revealed string has length at most the time. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_length_le
    (ρ : KLRule) (w : CantorSeq) (t : ℕ) :
    (ρ.revealed w t).length ≤ t := by
  induction t with
  | zero => simp [KLRule.revealed]
  | succ t ih =>
    rw [KLRule.revealed]
    split_ifs
    · simp only [List.length_append, List.length_singleton]
      omega
    · omega

/-- Auxiliary: one step of `revealed` when `F` is defined. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_succ_dom
    (ρ : KLRule) (w : CantorSeq) (t : ℕ)
    (hd : (ρ.next (ρ.revealed w t)).Dom) :
    ρ.revealed w (t + 1) = ρ.revealed w t ++ [w ((ρ.next (ρ.revealed w t)).get hd)] := by
  rw [KLRule.revealed]
  exact dite_eq_left hd

/-- Auxiliary: one step of `revealed` when `F` is undefined. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_succ_not_dom
    (ρ : KLRule) (w : CantorSeq) (t : ℕ)
    (hd : ¬ (ρ.next (ρ.revealed w t)).Dom) :
    ρ.revealed w (t + 1) = ρ.revealed w t := by
  rw [KLRule.revealed]
  exact dite_eq_right hd

/-- Auxiliary: if `F` is defined on the string revealed at time `t`, its length is `t`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_length_eq
    (ρ : KLRule) (w : CantorSeq) (t : ℕ)
    (hd : (ρ.next (ρ.revealed w t)).Dom) : (ρ.revealed w t).length = t := by
  induction t with
  | zero => simp [KLRule.revealed]
  | succ t ih =>
    by_cases hdt : (ρ.next (ρ.revealed w t)).Dom
    · rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_succ_dom ρ w t hdt]
      simp [ih hdt]
    · exfalso
      rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_succ_not_dom ρ w t
          hdt] at hd
      exact hdt hd

/-- Auxiliary: a string `x` followed by a bit inside `h` is a proper prefix of `h`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_proper_prefix
    {x h : BitString} {c : Bool} (hxc : x ++ [c] <+: h) :
    x <+: h ∧ x ≠ h := by
  refine ⟨(List.prefix_append x [c]).trans hxc, ?_⟩
  rintro rfl
  have := hxc.length_le
  simp at this

/-- Auxiliary: path characterization of the scenario `{revealed w |h| = h}`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_path (ρ : KLRule)
    (w : CantorSeq) (h : BitString) :
    ρ.revealed w h.length = h ↔
      ∀ (x : BitString) (c : Bool), x ++ [c] <+: h → ∃ n ∈ ρ.next x, w n = c := by
  induction h using List.reverseRecOn with
  | nil =>
    simp only [List.length_nil]
    constructor
    · intro _ x c hx
      exfalso
      have := hx.length_le
      simp at this
    · intro _
      simp [KLRule.revealed]
  | append_singleton h' c0 ih =>
    have hlen : (h' ++ [c0]).length = h'.length + 1 := by simp
    rw [hlen]
    constructor
    · intro H
      by_cases hd : (ρ.next (ρ.revealed w h'.length)).Dom
      · rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_succ_dom ρ w _ hd]
          at H
        obtain ⟨hrev, hc⟩ := List.append_inj' H rfl
        have hP := ih.mp hrev
        obtain ⟨n, hn, hnc⟩ : ∃ n, n ∈ ρ.next (ρ.revealed w h'.length) ∧ w n = c0 :=
          ⟨_, Part.get_mem hd, by simpa using hc⟩
        rw [hrev] at hn
        intro x c hx
        rw [List.prefix_concat_iff] at hx
        rcases hx with hx | hx
        · obtain ⟨hx1, hx2⟩ := List.append_inj' hx rfl
          have hcc : c = c0 := by simpa using hx2
          rw [hx1, hcc]
          exact ⟨n, hn, hnc⟩
        · exact hP x c hx
      · exfalso
        rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_succ_not_dom ρ w _
            hd] at H
        have h1 := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_length_le ρ
            w h'.length
        rw [H] at h1
        simp at h1
    · intro P
      have hP' : ∀ (x : BitString) (c : Bool), x ++ [c] <+: h' → ∃ n ∈ ρ.next x, w n = c :=
        fun x c hx => P x c (hx.trans (List.prefix_append _ _))
      have hrev : ρ.revealed w h'.length = h' := ih.mpr hP'
      obtain ⟨n, hn, hnc⟩ := P h' c0 List.prefix_rfl
      have hn' : n ∈ ρ.next (ρ.revealed w h'.length) := by rw [hrev]; exact hn
      have hd : (ρ.next (ρ.revealed w h'.length)).Dom := Part.dom_iff_mem.mpr ⟨n, hn'⟩
      have hget : (ρ.next (ρ.revealed w h'.length)).get hd = n := Part.get_eq_of_mem hn' hd
      rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_succ_dom ρ w _ hd,
          hget, hnc, hrev]

/-- Step 2b (cover): if `u ++ [b]` is a prefix of the selected bits at some time, then at the
first such time the revealed string `h` selects exactly `u`, is itself selected (`h ∈ R`), `F h`
is defined, and the next revealed bit `w (F h)` equals `b`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_cover (ρ : KLRule)
    (u : BitString) (b : Bool) :
    {w : CantorSeq | ∃ t, u ++ [b] <+: ρ.outputChain w t} ⊆
      ⋃ h ∈ {h : BitString | (ρ.next h).Dom ∧ h ∈ partialRuleSet ρ.sel ∧
          selectedBits (partialRuleSet ρ.sel) h = u},
        ({w : CantorSeq | ρ.revealed w h.length = h} ∩ {w : CantorSeq | ∃ n ∈ ρ.next h, w n = b}) :=
            by
  intro w hw
  obtain ⟨t, ht⟩ := hw
  have key : ∀ t : ℕ, u ++ [b] <+: ρ.outputChain w t →
      ∃ h : BitString, ((ρ.next h).Dom ∧ h ∈ partialRuleSet ρ.sel ∧
          selectedBits (partialRuleSet ρ.sel) h = u) ∧ ρ.revealed w h.length = h ∧
          ∃ n ∈ ρ.next h, w n = b := by
    intro t
    induction t with
    | zero =>
      intro hpre
      exfalso
      have h0 : ρ.outputChain w 0 = [] := by
        simp [KLRule.outputChain, KLRule.revealed, selectedBits, selectedAux]
      rw [h0] at hpre
      have := hpre.length_le
      simp at this
    | succ t ih =>
      intro hpre
      have hpre' : u ++ [b] <+: selectedBits (partialRuleSet ρ.sel) (ρ.revealed w (t + 1)) :=
        hpre
      by_cases hd : (ρ.next (ρ.revealed w t)).Dom
      · rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_succ_dom ρ w t hd,
          selectedBits_append_singleton] at hpre'
        by_cases hxR : ρ.revealed w t ∈ partialRuleSet ρ.sel
        · rw [ite_eq_left hxR] at hpre'
          rw [List.prefix_concat_iff] at hpre'
          rcases hpre' with hpre' | hpre'
          · obtain ⟨hS, hc⟩ := List.append_inj' hpre' rfl
            have hn : (ρ.next (ρ.revealed w t)).get hd ∈ ρ.next (ρ.revealed w t) :=
              Part.get_mem hd
            refine ⟨ρ.revealed w t, ⟨hd, hxR, hS.symm⟩, ?_, _, hn, ?_⟩
            · rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_length_eq ρ w
                t hd]
            · simpa using hc.symm
          · exact ih hpre'
        · rw [ite_eq_right hxR, List.append_nil] at hpre'
          exact ih hpre'
      · rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_succ_not_dom ρ w t
          hd] at hpre'
        exact ih hpre'
  obtain ⟨h, hH, hrev, hn⟩ := key t ht
  exact Set.mem_iUnion₂.mpr ⟨h, hH, hrev, hn⟩

/-- Step 2b (disjointness): the scenarios `{revealed w |h| = h}` for different `h` selecting
exactly `u` and selecting the next bit are disjoint. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_disjoint (ρ : KLRule)
    (u : BitString) :
    Set.PairwiseDisjoint {h : BitString | (ρ.next h).Dom ∧ h ∈ partialRuleSet ρ.sel ∧
          selectedBits (partialRuleSet ρ.sel) h = u}
      (fun h => {w : CantorSeq | ρ.revealed w h.length = h}) := by
  have key : ∀ h h' : BitString,
      ((ρ.next h).Dom ∧ h ∈ partialRuleSet ρ.sel ∧ selectedBits (partialRuleSet ρ.sel) h = u) →
      ((ρ.next h').Dom ∧ h' ∈ partialRuleSet ρ.sel ∧ selectedBits (partialRuleSet ρ.sel) h' = u) →
      h.length < h'.length →
      Disjoint {w : CantorSeq | ρ.revealed w h.length = h}
        {w : CantorSeq | ρ.revealed w h'.length = h'} := by
    intro h h' hh hh' hlt
    rw [Set.disjoint_left]
    intro w hw hw'
    have hw1 : ρ.revealed w h.length = h := hw
    have hw2 : ρ.revealed w h'.length = h' := hw'
    have hpre : ρ.revealed w h.length <+: ρ.revealed w h'.length :=
      chain_prefix_of_le (ρ.revealed_prefix w) hlt.le
    rw [hw1, hw2] at hpre
    obtain ⟨z, hz⟩ := hpre
    have hz0 : z ≠ [] := by
      rintro rfl
      have hlen := congrArg List.length hz
      simp at hlen
      omega
    obtain ⟨c, z', rfl⟩ := List.exists_cons_of_ne_nil hz0
    have hpre2 : h ++ [c] <+: h' := ⟨z', by rw [← hz]; simp⟩
    have h3 := selectedBits_prefix (partialRuleSet ρ.sel) hpre2
    rw [selectedBits_append_singleton, ite_eq_left hh.2.1, hh.2.2, hh'.2.2] at h3
    have := h3.length_le
    simp at this
  intro h hh h' hh' hne
  change Disjoint {w : CantorSeq | ρ.revealed w h.length = h}
    {w : CantorSeq | ρ.revealed w h'.length = h'}
  rcases lt_trichotomy h.length h'.length with hlt | heq | hgt
  · exact key h h' hh hh' hlt
  · rw [Set.disjoint_left]
    intro w hw hw'
    have hw1 : ρ.revealed w h.length = h := hw
    have hw2 : ρ.revealed w h'.length = h' := hw'
    apply hne
    rw [← hw1, ← hw2, heq]
  · exact (key h' h hh' hh hgt).symm

/-- Step 2b (inclusion): on the scenario of `h`, the selected bits at time `|h|` are
`selectedBits R h`, so if this is `u` the sequence is in the event for `u`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_subset (ρ : KLRule)
    (u : BitString) (h : BitString)
    (hh : selectedBits (partialRuleSet ρ.sel) h = u) :
    {w : CantorSeq | ρ.revealed w h.length = h} ⊆ {w : CantorSeq | ∃ t, u <+: ρ.outputChain w t} :=
        by
  intro w hw
  have hw' : ρ.revealed w h.length = h := hw
  refine ⟨h.length, ?_⟩
  have : ρ.outputChain w h.length = u := by
    change selectedBits (partialRuleSet ρ.sel) (ρ.revealed w h.length) = u
    rw [hw']
    exact hh
  rw [this]

/-- Step 2b (dependence): the scenario `{revealed w |h| = h}` depends only on finitely many
coordinates, none of which is the coordinate `F h` revealed next. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_depends (ρ : KLRule)
    (h : BitString) :
    ∃ S : Finset ℕ, (∀ n ∈ ρ.next h, n ∉ S) ∧
      ∀ w w' : CantorSeq, (∀ i ∈ S, w i = w' i) →
        (ρ.revealed w h.length = h ↔ ρ.revealed w' h.length = h) := by
  classical
  have hfin : {n : ℕ | ∃ x : BitString, x <+: h ∧ x ≠ h ∧ n ∈ ρ.next x}.Finite := by
    have hsub : {n : ℕ | ∃ x : BitString, x <+: h ∧ x ≠ h ∧ n ∈ ρ.next x} ⊆
        ⋃ x ∈ (h.inits.toFinset : Set BitString), {n | n ∈ ρ.next x} := by
      rintro n ⟨x, hxh, hxne, hn⟩
      simp only [Set.mem_iUnion]
      refine ⟨x, ?_, hn⟩
      simpa [List.mem_inits] using hxh
    refine Set.Finite.subset ?_ hsub
    refine Set.Finite.biUnion (Finset.finite_toSet _) (fun x _ => ?_)
    exact (show ({n | n ∈ ρ.next x} : Set ℕ).Subsingleton from
      fun a ha b hb => Part.mem_unique ha hb).finite
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro n hn hnS
    rw [Set.Finite.mem_toFinset] at hnS
    obtain ⟨x, hxh, hxne, hnx⟩ := hnS
    exact ρ.noRepeat x h hxh hxne n hnx n hn rfl
  · have hdir : ∀ w w' : CantorSeq, (∀ i ∈ hfin.toFinset, w i = w' i) →
        ρ.revealed w h.length = h → ρ.revealed w' h.length = h := by
      intro w w' hww' hrev
      rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_path] at hrev ⊢
      intro x c hxc
      obtain ⟨n, hn, hwn⟩ := hrev x c hxc
      refine ⟨n, hn, ?_⟩
      have hmem : n ∈ hfin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact ⟨x, (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_proper_prefix hxc).1,
            (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_proper_prefix hxc).2, hn⟩
      rw [← hww' n hmem]
      exact hwn
    intro w w' hww'
    exact ⟨hdir w w' hww', hdir w' w (fun i hi => (hww' i hi).symm)⟩
/-- Step 2c: one step of the induction: appending the selected bit `b` multiplies the
probability by at most the mass of `[b]`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_step {p : NNReal} (hp : p ≤ 1)
    (ρ : KLRule) (u : BitString) (b : Bool) :
    bernoulliMeasure p hp {w : CantorSeq | ∃ t, u ++ [b] <+: ρ.outputChain w t} ≤
      cantorMass (bernoulliMeasure p hp) [b] *
        bernoulliMeasure p hp {w : CantorSeq | ∃ t, u <+: ρ.outputChain w t} := by
  classical
  have hcover := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_cover ρ u b
  have hdisj := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_disjoint ρ u
  set H : Set BitString := {h : BitString | (ρ.next h).Dom ∧ h ∈ partialRuleSet ρ.sel ∧
      selectedBits (partialRuleSet ρ.sel) h = u} with hH
  have hHc : H.Countable := Set.to_countable H
  have hmeas : ∀ h : BitString,
      MeasurableSet {w : CantorSeq | ρ.revealed w h.length = h} := by
    intro h
    obtain ⟨S, -, hS⟩ := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_depends ρ h
    exact isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_measurable S _ hS
  have hterm : ∀ h ∈ H,
      bernoulliMeasure p hp ({w : CantorSeq | ρ.revealed w h.length = h} ∩
          {w : CantorSeq | ∃ n ∈ ρ.next h, w n = b}) =
        bernoulliMeasure p hp {w : CantorSeq | ρ.revealed w h.length = h} *
          cantorMass (bernoulliMeasure p hp) [b] := by
    intro h hh
    have hh' : (ρ.next h).Dom ∧ h ∈ partialRuleSet ρ.sel ∧
        selectedBits (partialRuleSet ρ.sel) h = u := hh
    obtain ⟨S, hSn, hS⟩ := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_depends ρ h
    have hdom : (ρ.next h).Dom := hh'.1
    have hn : (ρ.next h).get hdom ∈ ρ.next h := Part.get_mem hdom
    have hset : {w : CantorSeq | ∃ n ∈ ρ.next h, w n = b} =
        {w : CantorSeq | w ((ρ.next h).get hdom) = b} := by
      ext w
      constructor
      · rintro ⟨n, hn', hw⟩
        have : n = (ρ.next h).get hdom := Part.mem_unique hn' hn
        rw [← this]
        exact hw
      · intro hw
        exact ⟨_, hn, hw⟩
    rw [hset]
    exact isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_indep hp S _ (hSn _ hn) _ hS b
  have hsub : (⋃ h ∈ H, {w : CantorSeq | ρ.revealed w h.length = h}) ⊆
      {w : CantorSeq | ∃ t, u <+: ρ.outputChain w t} := by
    refine Set.iUnion₂_subset (fun h hh => ?_)
    have hh' : (ρ.next h).Dom ∧ h ∈ partialRuleSet ρ.sel ∧
        selectedBits (partialRuleSet ρ.sel) h = u := hh
    exact isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_subset ρ u h hh'.2.2
  calc bernoulliMeasure p hp {w : CantorSeq | ∃ t, u ++ [b] <+: ρ.outputChain w t}
      ≤ bernoulliMeasure p hp (⋃ h ∈ H, ({w : CantorSeq | ρ.revealed w h.length = h} ∩
          {w : CantorSeq | ∃ n ∈ ρ.next h, w n = b})) := measure_mono hcover
    _ ≤ ∑' h : H, bernoulliMeasure p hp ({w : CantorSeq | ρ.revealed w (h : BitString).length = h} ∩
          {w : CantorSeq | ∃ n ∈ ρ.next h, w n = b}) :=
        measure_biUnion_le (bernoulliMeasure p hp) hHc _
    _ = ∑' h : H, bernoulliMeasure p hp {w : CantorSeq | ρ.revealed w (h : BitString).length = h} *
          cantorMass (bernoulliMeasure p hp) [b] := tsum_congr (fun h => hterm h h.2)
    _ = (∑' h : H, bernoulliMeasure p hp
          {w : CantorSeq | ρ.revealed w (h : BitString).length = h}) *
          cantorMass (bernoulliMeasure p hp) [b] := ENNReal.tsum_mul_right
    _ = bernoulliMeasure p hp (⋃ h ∈ H, {w : CantorSeq | ρ.revealed w h.length = h}) *
          cantorMass (bernoulliMeasure p hp) [b] := by
        rw [measure_biUnion hHc hdisj (fun h _ => hmeas h)]
    _ ≤ bernoulliMeasure p hp {w : CantorSeq | ∃ t, u <+: ρ.outputChain w t} *
          cantorMass (bernoulliMeasure p hp) [b] := by
        exact mul_le_mul_left (measure_mono hsub) _
    _ = _ := mul_comm _ _

/-- The mass of a cylinder under a Bernoulli measure multiplies when a bit is appended. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cantorMass_append
    {p : NNReal} (hp : p ≤ 1) (u : BitString) (b : Bool) :
    cantorMass (bernoulliMeasure p hp) (u ++ [b]) =
      cantorMass (bernoulliMeasure p hp) u * cantorMass (bernoulliMeasure p hp) [b] := by
  have hset : cantorCylinder (u ++ [b]) = cantorCylinder u ∩ {w : CantorSeq | w u.length = b} := by
    ext w
    simp only [cantorCylinder, Set.mem_ofPred_eq, Set.mem_inter_iff]
    exact isCantorPrefix_append_singleton u b w
  have hdep : ∀ w w' : CantorSeq, (∀ i ∈ Finset.range u.length, w i = w' i) →
      (w ∈ cantorCylinder u ↔ w' ∈ cantorCylinder u) := by
    intro w w' hww'
    simp only [cantorCylinder, Set.mem_ofPred_eq, IsCantorPrefix]
    constructor
    · intro h i hi
      rw [← hww' i (Finset.mem_range.2 hi)]
      exact h i hi
    · intro h i hi
      rw [hww' i (Finset.mem_range.2 hi)]
      exact h i hi
  unfold cantorMass
  rw [hset]
  exact isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_indep hp (Finset.range u.length)
      u.length (by simp) (cantorCylinder u) hdep b

/-- Step 2d: the selection bound for an arbitrary non-monotone rule. -/
lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_selection {p : NNReal}
    (hp : p ≤ 1) (ρ : KLRule) (u : BitString) :
    bernoulliMeasure p hp {w : CantorSeq | ∃ t, u <+: ρ.outputChain w t} ≤
      bernoulliMeasure p hp (cantorCylinder u) := by
  induction u using List.reverseRecOn with
  | nil =>
    have hunivcyl : cantorCylinder ([] : BitString) = Set.univ := by
      ext w
      simp [cantorCylinder, IsCantorPrefix]
    rw [hunivcyl]
    exact measure_mono (Set.subset_univ _)
  | append_singleton u b ih =>
    have h := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cantorMass_append hp u b
    calc bernoulliMeasure p hp {w : CantorSeq | ∃ t, u ++ [b] <+: ρ.outputChain w t}
        ≤ cantorMass (bernoulliMeasure p hp) [b] *
            bernoulliMeasure p hp {w : CantorSeq | ∃ t, u <+: ρ.outputChain w t} :=
          isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_step hp ρ u b
      _ ≤ cantorMass (bernoulliMeasure p hp) [b] *
            bernoulliMeasure p hp (cantorCylinder u) := by gcongr
      _ = cantorMass (bernoulliMeasure p hp) (u ++ [b]) := by
          rw [h]
          exact mul_comm _ _
      _ = bernoulliMeasure p hp (cantorCylinder (u ++ [b])) := rfl
/-- Step 3 aux: one position of the certificate check.  `acc` is the list of bits selected so far,
`r1 = EF (h.take i) s`, `r2 = EG (h.take i) s`, `r3 = h[i]?`.  The check passes when the
evaluators have converged, and the queried coordinate `n` of `x` is the bit `h[i]`. -/
private def isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_fin (x : BitString)
    (acc : Option BitString) (r1 : Option ℕ)
    (r2 r3 : Option Bool) : Option BitString :=
  cond (acc.isSome && r1.isSome && r2.isSome && r3.isSome && decide (x[r1.getD 0]? = r3))
    (some (cond (r2.getD false) (acc.getD [] ++ [r3.getD false]) (acc.getD []))) none

/-- Unfolding of the successful case of the check. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_fin_eq_some {x : BitString}
    {acc : Option BitString} {r1 : Option ℕ}
    {r2 r3 : Option Bool} {L' : BitString} :
    isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_fin x acc r1 r2 r3 = some L' ↔
      ∃ (L : BitString) (n : ℕ) (v b : Bool), acc = some L ∧ r1 = some n ∧ r2 = some v ∧
        r3 = some b ∧ x[n]? = some b ∧ L' = cond v (L ++ [b]) L := by
  rcases acc with _ | L <;> rcases r1 with _ | n <;> rcases r2 with _ | v <;>
    rcases r3 with _ | b <;> simp [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_fin]
  by_cases hxb : x[n]? = some b <;> simp [hxb, eq_comm]

/-- The certificate: runs the check along the positions `0, …, n-1` of `h`, accumulating the
selected bits (a position is selected when the evaluator of `G` answers `true`). -/
private def isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert (EF : BitString → ℕ →
    Option ℕ) (EG : BitString → ℕ → Option Bool)
    (s : ℕ) (x h : BitString) (n : ℕ) : Option BitString :=
  Nat.rec (motive := fun _ => Option BitString) (some [])
    (fun i acc => isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_fin x acc
                    (EF (h.take i) s) (EG (h.take i) s) h[i]?) n

private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_zero (EF : BitString →
    ℕ → Option ℕ)
    (EG : BitString → ℕ → Option Bool) (s : ℕ) (x h : BitString) :
    isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert EF EG s x h 0 = some [] := rfl

private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_succ (EF : BitString →
    ℕ → Option ℕ)
    (EG : BitString → ℕ → Option Bool) (s : ℕ) (x h : BitString) (i : ℕ) :
    isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert EF EG s x h (i + 1) =
      isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_fin x
        (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert EF EG s x h i)
        (EF (h.take i) s) (EG (h.take i) s) h[i]? := rfl

private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_fin_primrec :
    Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool =>
      isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_fin z.1 z.2.1 z.2.2.1 z.2.2.2.1
          z.2.2.2.2) := by
  have hx : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool =>
      z.1) := Primrec.fst
  have hacc : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      z.2.1) := Primrec.fst.comp Primrec.snd
  have hr1 : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool =>
      z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr2 : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool =>
      z.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hr3 : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool =>
      z.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hget : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      z.2.2.1.getD 0) := Primrec.option_getD.comp hr1 (Primrec.const 0)
  have hxn : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool =>
      z.1[z.2.2.1.getD 0]?) := Primrec.list_getElem?.comp hx hget
  have hdec : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      decide (z.1[z.2.2.1.getD 0]? = z.2.2.2.2)) :=
    (Primrec.dom_finite (fun p : Option Bool × Option Bool => decide (p.1 = p.2))).comp
      (Primrec.pair hxn hr3)
  have hc : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool =>
      (z.2.1.isSome && z.2.2.1.isSome && z.2.2.2.1.isSome && z.2.2.2.2.isSome &&
        decide (z.1[z.2.2.1.getD 0]? = z.2.2.2.2))) := by
    refine Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
      (Primrec.option_isSome.comp hacc) (Primrec.option_isSome.comp hr1))
      (Primrec.option_isSome.comp hr2)) (Primrec.option_isSome.comp hr3)) hdec
  have haccd : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      z.2.1.getD []) := Primrec.option_getD.comp hacc (Primrec.const [])
  have hr2d : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      z.2.2.2.1.getD false) := Primrec.option_getD.comp hr2 (Primrec.const false)
  have hr3d : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      z.2.2.2.2.getD false) := Primrec.option_getD.comp hr3 (Primrec.const false)
  have happ : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      z.2.1.getD [] ++ [z.2.2.2.2.getD false]) :=
    Primrec.list_append.comp haccd (Primrec.list_cons.comp hr3d (Primrec.const []))
  have hval : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      cond (z.2.2.2.1.getD false) (z.2.1.getD [] ++ [z.2.2.2.2.getD false]) (z.2.1.getD [])) :=
    Primrec.cond hr2d happ haccd
  exact Primrec.cond hc (Primrec.option_some.comp hval) (Primrec.const none)

private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_primrec_decide_eq
    {α β : Type} [Primcodable α] [Primcodable β]
    [DecidableEq β] {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => decide (f a = g a)) :=
  (Primrec.eq.comp hf hg).decide

private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_computable
    {EF : BitString → ℕ → Option ℕ}
    {EG : BitString → ℕ → Option Bool} (hEF : Computable₂ EF) (hEG : Computable₂ EG) :
    Computable (fun c : BitString × ℕ × BitString =>
      isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert EF EG c.2.1 c.2.2 c.1
          c.1.length) := by
  have hh : Computable (fun c : BitString × ℕ × BitString => c.1) := Computable.fst
  refine Computable.nat_rec (f := fun c : BitString × ℕ × BitString => c.1.length)
    (g := fun _ => some ([] : BitString))
    (h := fun (c : BitString × ℕ × BitString) (p : ℕ × Option BitString) =>
      isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_fin c.2.2 p.2
          (EF (c.1.take p.1) c.2.1) (EG (c.1.take p.1) c.2.1) c.1[p.1]?)
    (Computable.list_length.comp hh) (Computable.const _) ?_
  -- the step function, as a function of `q = (c, (i, acc))`
  have hq1 : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString => q.1.1) :=
    Computable.fst.comp Computable.fst
  have hqs : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString => q.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hqx : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString => q.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hqi : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString => q.2.1) :=
    Computable.fst.comp Computable.snd
  have hqa : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString => q.2.2) :=
    Computable.snd.comp Computable.snd
  have htake : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString =>
      q.1.1.take q.2.1) :=
    (Primrec.list_take.to_comp : Computable₂ (List.take : ℕ → BitString → BitString)).comp hqi hq1
  have hr1 : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString =>
      EF (q.1.1.take q.2.1) q.1.2.1) := hEF.comp htake hqs
  have hr2 : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString =>
      EG (q.1.1.take q.2.1) q.1.2.1) := hEG.comp htake hqs
  have hr3 : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString =>
      q.1.1[q.2.1]?) :=
    (Computable.list_getElem? : Computable₂ (fun (l : BitString) (n : ℕ) => l[n]?)).comp hq1 hqi
  have hfin := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_fin_primrec.to_comp.comp
    (Computable.pair hqx (Computable.pair hqa (Computable.pair hr1 (Computable.pair hr2 hr3))))
  exact hfin

/-- The check of one candidate `c = (h, s, x)` for the string `u`: output `x` when the certificate
passes and `u` is a prefix of the selected bits. -/
private def isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_ok (EF : BitString → ℕ →
    Option ℕ) (EG : BitString → ℕ → Option Bool)
    (a : BitString × BitString × ℕ × BitString) : Option BitString :=
  (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert EF EG a.2.2.1 a.2.2.2 a.2.1
      a.2.1.length).bind fun L =>
    cond (decide (a.1 = L.take a.1.length)) (some a.2.2.2) none

private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_ok_computable
    {EF : BitString → ℕ → Option ℕ}
    {EG : BitString → ℕ → Option Bool} (hEF : Computable₂ EF) (hEG : Computable₂ EG) :
    Computable (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_ok EF EG) := by
  have hcert := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_computable hEF hEG
  have hc : Computable (fun a : BitString × BitString × ℕ × BitString =>
      isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert EF EG a.2.2.1 a.2.2.2 a.2.1
          a.2.1.length) := hcert.comp Computable.snd
  refine Computable.option_bind hc ?_
  -- last step: a function of `r = (a, L)`
  have hu : Computable (fun r : (BitString × BitString × ℕ × BitString) × BitString => r.1.1) :=
    Computable.fst.comp Computable.fst
  have hL : Computable (fun r : (BitString × BitString × ℕ × BitString) × BitString => r.2) :=
    Computable.snd
  have hx : Computable (fun r : (BitString × BitString × ℕ × BitString) × BitString =>
      r.1.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hdecP : Primrec (fun p : BitString × BitString =>
      decide (p.1 = p.2.take p.1.length)) :=
    isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_primrec_decide_eq (f := fun p :
        BitString × BitString => p.1)
      (g := fun p : BitString × BitString => p.2.take p.1.length) Primrec.fst
      (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd)
  have hdec : Computable (fun r : (BitString × BitString × ℕ × BitString) × BitString =>
      decide (r.1.1 = r.2.take r.1.1.length)) :=
    Computable.comp (f := fun p : BitString × BitString => decide (p.1 = p.2.take p.1.length))
      (g := fun r : (BitString × BitString × ℕ × BitString) × BitString => (r.1.1, r.2))
      hdecP.to_comp (Computable.pair hu hL)
  exact Computable.cond (c := fun r : (BitString × BitString × ℕ × BitString) × BitString =>
      decide (r.1.1 = r.2.take r.1.1.length))
    (f := fun r : (BitString × BitString × ℕ × BitString) × BitString => some r.1.2.2.2)
    (g := fun _ => none) hdec (Computable.option_some.comp hx) (Computable.const none)

/-- The enumeration of cylinders: decode a candidate `(h, s, x)`, run the certificate, and output
`x` when `u` is a prefix of the selected bits. -/
private def isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_f (EF : BitString → ℕ →
    Option ℕ) (EG : BitString → ℕ → Option Bool)
    (u : BitString) (j : ℕ) : Option BitString :=
  (Encodable.decode j : Option (BitString × ℕ × BitString)).bind fun c =>
    (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert EF EG c.2.1 c.2.2 c.1
        c.1.length).bind fun L =>
      cond (decide (u = L.take u.length)) (some c.2.2) none

private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_f_computable
    {EF : BitString → ℕ → Option ℕ}
    {EG : BitString → ℕ → Option Bool} (hEF : Computable₂ EF) (hEG : Computable₂ EG) :
    Computable₂ (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_f EF EG) := by
  have hok := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_ok_computable hEF hEG
  have hdec : Computable (fun a : BitString × ℕ =>
      (Encodable.decode a.2 : Option (BitString × ℕ × BitString))) :=
    Computable.decode.comp Computable.snd
  have hg : Computable₂ (fun (a : BitString × ℕ) (c : BitString × ℕ × BitString) =>
      isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_ok EF EG (a.1, c)) :=
    Computable.comp (f := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_ok EF EG)
      (g := fun p : (BitString × ℕ) × (BitString × ℕ × BitString) => (p.1.1, p.2)) hok
      (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  exact Computable.option_bind (f := fun a : BitString × ℕ =>
      (Encodable.decode a.2 : Option (BitString × ℕ × BitString)))
    (g := fun (a : BitString × ℕ) (c : BitString × ℕ × BitString) =>
      isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_ok EF EG (a.1, c)) hdec hg

/-! ### Soundness of the certificate -/

/-- Unfolding of `cert (i+1) = some L'`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_succ_eq_some
    {EF : BitString → ℕ → Option ℕ}
    {EG : BitString → ℕ → Option Bool} {s : ℕ} {x h : BitString} {i : ℕ} {L' : BitString} :
    isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert EF EG s x h (i + 1) = some L' ↔
      ∃ (L : BitString) (n : ℕ) (v b : Bool),
          isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert EF EG s x h i = some L ∧
        EF (h.take i) s = some n ∧ EG (h.take i) s = some v ∧ h[i]? = some b ∧
        x[n]? = some b ∧ L' = cond v (L ++ [b]) L := by
  rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_succ,
    isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_fin_eq_some]

/-- If the certificate succeeds, each of the first `i` positions of `h` was checked: the evaluators
converged and the queried coordinate of `x` is the bit of `h`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_loc {EF : BitString →
    ℕ → Option ℕ}
    {EG : BitString → ℕ → Option Bool} {s : ℕ} {x h : BitString} :
    ∀ (i : ℕ) (L : BitString), isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert EF EG
        s x h i = some L →
      ∀ j, j < i → ∃ (n : ℕ) (v b : Bool), EF (h.take j) s = some n ∧ EG (h.take j) s = some v ∧
        h[j]? = some b ∧ x[n]? = some b := by
  intro i
  induction i with
  | zero => intro L _ j hj; omega
  | succ i ih =>
    intro L' hL' j hj
    obtain ⟨L, n, v, b, hL, hn, hv, hb, hxb, -⟩ :=
        isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_succ_eq_some.1 hL'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hji | hji
    · exact ih L hL j hji
    · subst hji
      exact ⟨n, v, b, hn, hv, hb, hxb⟩

/-- A prefix of a prefix. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_prefix_take
    {y h : BitString} {i : ℕ} (hy : y <+: h.take i) :
    y.length ≤ i ∧ y = h.take y.length := by
  have hle : y.length ≤ (h.take i).length := hy.length_le
  have hlen : y.length ≤ i := le_trans hle (List.length_take_le _ _)
  refine ⟨hlen, ?_⟩
  have hy' := List.prefix_iff_eq_take.1 hy
  rw [List.take_take, min_eq_left hlen] at hy'
  exact hy'

/-- The selected bits of a successful certificate are those of the rule `G`, and `G` is defined
on all the prefixes checked. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_selected (ρ : KLRule)
    {EF : BitString → ℕ → Option ℕ}
    {EG : BitString → ℕ → Option Bool}
    (hEGs : ∀ (a : BitString) (v : Bool), v ∈ ρ.sel a ↔ ∃ s, EG a s = some v)
    {s : ℕ} {x h : BitString} :
    ∀ (i : ℕ) (L : BitString), isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert EF EG
        s x h i = some L →
      (∀ j, j < i → (ρ.sel (h.take j)).Dom) ∧
        L = selectedBits (partialRuleSet ρ.sel) (h.take i) := by
  intro i
  induction i with
  | zero =>
    intro L hL
    refine ⟨fun j hj => by omega, ?_⟩
    have hL0 : L = [] := by
      have : isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert EF EG s x h 0 =
          some [] := rfl
      rw [this] at hL
      exact (Option.some.inj hL).symm
    simp [hL0, selectedBits, selectedAux]
  | succ i ih =>
    intro L' hL'
    obtain ⟨L, n, v, b, hL, hn, hv, hb, hxb, hL'eq⟩ :=
        isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_succ_eq_some.1 hL'
    obtain ⟨hdom, hLsel⟩ := ih L hL
    have hvmem : v ∈ ρ.sel (h.take i) := (hEGs _ _).2 ⟨s, hv⟩
    have hdomi : (ρ.sel (h.take i)).Dom := Part.dom_iff_mem.2 ⟨v, hvmem⟩
    refine ⟨?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hji | hji
      · exact hdom j hji
      · subst hji; exact hdomi
    · have htake : h.take (i + 1) = h.take i ++ [b] := by
        rw [List.take_add_one, hb]; rfl
      have hmem : h.take i ∈ partialRuleSet ρ.sel ↔ v = true := by
        constructor
        · rintro ⟨-, ht⟩
          exact Part.mem_unique hvmem ht
        · rintro rfl
          refine ⟨fun y hy => ?_, hvmem⟩
          obtain ⟨hyi, hyeq⟩ :=
              isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_prefix_take hy
          rw [hyeq]
          rcases Nat.lt_or_ge y.length i with hlt | hge
          · exact hdom _ hlt
          · have : y.length = i := le_antisymm hyi hge
            rw [this]; exact hdomi
      rw [htake, selectedBits_append_singleton, hL'eq, hLsel]
      cases v
      · have : ¬ (h.take i ∈ partialRuleSet ρ.sel) := fun hh => by simpa using hmem.1 hh
        simp [this]
      · have : h.take i ∈ partialRuleSet ρ.sel := hmem.2 rfl
        simp [this]

open Classical in
/-- If `w` follows the path `h` (each revealed coordinate holds the next bit of `h`), then the
revealed string of `w` after `i ≤ |h|` steps is the prefix of `h` of length `i`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_of_path
    (ρ : KLRule) (w : CantorSeq) (h : BitString)
    (hpath : ∀ (i : ℕ) (hi : i < h.length), ∃ n ∈ ρ.next (h.take i), w n = h[i]) :
    ∀ i, i ≤ h.length → ρ.revealed w i = h.take i := by
  intro i
  induction i with
  | zero => intro _; simp [KLRule.revealed]
  | succ i ih =>
    intro hi
    have hi' : i < h.length := hi
    have h1 : ρ.revealed w i = h.take i := ih (Nat.le_of_lt hi')
    obtain ⟨n, hn, hwn⟩ := hpath i hi'
    have hdom : (ρ.next (h.take i)).Dom := Part.dom_iff_mem.2 ⟨n, hn⟩
    have hget : (ρ.next (h.take i)).get hdom = n := Part.get_eq_of_mem hn hdom
    have key : ∀ x : BitString, x = h.take i →
        (if hd : (ρ.next x).Dom then x ++ [w ((ρ.next x).get hd)] else x) =
          h.take i ++ [w n] := by
      intro x hx
      subst hx
      rw [dite_eq_left hdom, hget]
    have hstep : ρ.revealed w (i + 1) = h.take i ++ [w n] := by
      rw [KLRule.revealed]
      exact key _ h1
    rw [hstep, hwn, List.take_add_one, List.getElem?_eq_getElem hi']
    rfl

/-- **Soundness.**  If candidate `j` passes the check for `u` and outputs `x`, every `w` in the
cylinder of `x` has `u` as a prefix of its selected bits at some time. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_sound (ρ : KLRule)
    {EF : BitString → ℕ → Option ℕ}
    {EG : BitString → ℕ → Option Bool}
    (hEFs : ∀ (a : BitString) (v : ℕ), v ∈ ρ.next a ↔ ∃ s, EF a s = some v)
    (hEGs : ∀ (a : BitString) (v : Bool), v ∈ ρ.sel a ↔ ∃ s, EG a s = some v)
    (u : BitString) (j : ℕ) (x : BitString)
        (hj : isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_f EF EG u j = some x)
    (w : CantorSeq) (hw : w ∈ cantorCylinder x) : ∃ t, u <+: ρ.outputChain w t := by
  unfold isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_f at hj
  rw [Option.bind_eq_some_iff] at hj
  obtain ⟨c, hc, hj⟩ := hj
  rw [Option.bind_eq_some_iff] at hj
  obtain ⟨L, hL, hj⟩ := hj
  obtain ⟨h, s, x'⟩ := c
  simp only at hL hj
  have hdec : decide (u = L.take u.length) = true ∧ x' = x := by
    cases hd : decide (u = L.take u.length)
    · rw [hd] at hj; simp at hj
    · rw [hd] at hj; exact ⟨rfl, by simpa using hj⟩
  obtain ⟨hdec, rfl⟩ := hdec
  have hu : u <+: L := List.prefix_iff_eq_take.2 (of_decide_eq_true hdec)
  have hloc := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_loc h.length L hL
  have hpath : ∀ (i : ℕ) (hi : i < h.length), ∃ n ∈ ρ.next (h.take i), w n = h[i] := by
    intro i hi
    obtain ⟨n, v, b, hn, -, hb, hxb⟩ := hloc i hi
    refine ⟨n, (hEFs _ _).2 ⟨s, hn⟩, ?_⟩
    have hb' : h[i] = b := by
      rw [List.getElem?_eq_getElem hi] at hb
      exact Option.some.inj hb
    have hnx : n < x'.length := by
      by_contra hcon
      rw [List.getElem?_eq_none (not_lt.1 hcon)] at hxb
      exact absurd hxb (by simp)
    rw [List.getElem?_eq_getElem hnx] at hxb
    have hxb' : x'[n] = b := Option.some.inj hxb
    rw [hb', ← hxb']
    exact hw n hnx
  have hrev := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_of_path ρ w h
      hpath h.length le_rfl
  rw [List.take_length] at hrev
  obtain ⟨-, hLsel⟩ := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_selected ρ
      hEGs h.length L hL
  rw [List.take_length] at hLsel
  refine ⟨h.length, ?_⟩
  have : ρ.outputChain w h.length = L := by
    unfold KLRule.outputChain
    rw [hrev, hLsel]
  rw [this]
  exact hu
/-- Step 3a: step-bounded evaluation of a partial computable function. -/
lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_stepEval {α σ : Type}
    [Primcodable α] [Primcodable σ] {f : α →. σ}
    (hf : Partrec f) :
    ∃ E : α → ℕ → Option σ, Computable₂ E ∧
      (∀ (a : α) (s t : ℕ) (v : σ), s ≤ t → E a s = some v → E a t = some v) ∧
      (∀ (a : α) (v : σ), v ∈ f a ↔ ∃ s, E a s = some v) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  have hevalr : ∀ a : α,
      Nat.Partrec.Code.eval c (Encodable.encode a) = Part.map Encodable.encode (f a) := by
    intro a
    simp only [hc]
    rw [Encodable.encodek]
    simp
  refine ⟨fun a s => (Nat.Partrec.Code.evaln s c (Encodable.encode a)).bind
    (fun m => Encodable.decode (α := σ) m), ?_, ?_, ?_⟩
  · have hsnd : Primrec (fun x : α × ℕ => x.2) := Primrec.snd
    have hfst : Primrec (fun x : α × ℕ => x.1) := Primrec.fst
    have h_prim := Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair hsnd (Primrec.const c)) (Primrec.encode.comp hfst))
    exact Computable.option_bind (Primrec.to_comp h_prim)
      (Computable.decode.comp Computable.snd)
  · intro a s t v hst h
    simp only at h ⊢
    rcases hev : Nat.Partrec.Code.evaln s c (Encodable.encode a) with _ | m
    · rw [hev] at h; simp at h
    · have hmono : Nat.Partrec.Code.evaln t c (Encodable.encode a) = some m :=
        Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hst (Option.mem_def.mpr hev))
      rw [hev] at h
      rw [hmono]
      exact h
  · intro a v
    simp only
    constructor
    · intro hv
      have hmem : (Encodable.encode v) ∈ Nat.Partrec.Code.eval c (Encodable.encode a) := by
        rw [hevalr a]
        exact Part.mem_map _ hv
      obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
      refine ⟨s, ?_⟩
      rw [Option.mem_def.mp hs]
      simp only [Option.bind]
      exact Encodable.encodek v
    · rintro ⟨s, hs⟩
      rcases hev : Nat.Partrec.Code.evaln s c (Encodable.encode a) with _ | m
      · rw [hev] at hs; simp at hs
      · rw [hev] at hs
        have hdec : (Encodable.decode (α := σ) m) = some v := hs
        have hmem : m ∈ Nat.Partrec.Code.eval c (Encodable.encode a) :=
          Nat.Partrec.Code.evaln_complete.mpr ⟨s, Option.mem_def.mpr hev⟩
        rw [hevalr a] at hmem
        obtain ⟨x, hx, hxm⟩ := (Part.mem_map_iff _).mp hmem
        have hxq : x = v := by
          have hd2 : (Encodable.decode (α := σ) (Encodable.encode x)) = some v := by
            rw [hxm]; exact hdec
          rw [Encodable.encodek] at hd2
          exact Option.some_injective _ hd2
        rwa [← hxq]

/-- Aux: at the time equal to the length of a revealed string, the revealed string is the same. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_fix (ρ : KLRule)
    (w : CantorSeq) (t : ℕ) :
    ρ.revealed w (ρ.revealed w t).length = ρ.revealed w t := by
  induction t with
  | zero => simp [KLRule.revealed]
  | succ t ih =>
    by_cases hd : (ρ.next (ρ.revealed w t)).Dom
    · have hlen := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_length_eq ρ
        w t hd
      rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_succ_dom ρ w t hd]
      simp only [List.length_append, List.length_singleton, hlen]
      exact isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_succ_dom ρ w t hd
    · rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_succ_not_dom ρ w t
        hd]
      exact ih

/-- Aux: membership in `partialRuleSet`, unfolded. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_mem_partialRuleSet
    {r : BitString →. Bool} {x : BitString} :
    x ∈ partialRuleSet r ↔ (∀ y, y <+: x → (r y).Dom) ∧ true ∈ r x := Iff.rfl

/-- Aux: a common stage for finitely many monotone requirements. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_common_stage (P : ℕ → ℕ →
    Prop)
    (hmono : ∀ k s t, s ≤ t → P k s → P k t) :
    ∀ m : ℕ, (∀ k, k < m → ∃ s, P k s) → ∃ s, ∀ k, k < m → P k s := by
  intro m
  induction m with
  | zero => intro _; exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro h
    obtain ⟨s1, hs1⟩ := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    obtain ⟨s2, hs2⟩ := h m (Nat.lt_succ_self m)
    refine ⟨max s1 s2, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact hmono _ _ _ (le_max_left _ _) (hs1 k hk)
    · exact hmono _ _ _ (le_max_right _ _) hs2

/-- Aux: the certificate computes the selected bits of the prefix. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_eq (ρ : KLRule)
    (EF : BitString → ℕ → Option ℕ) (EG : BitString → ℕ → Option Bool)
    (hGsound : ∀ (a : BitString) (s : ℕ) (v : Bool), EG a s = some v → v ∈ ρ.sel a)
    (s : ℕ) (x h : BitString)
    (hcond : ∀ k, (hk : k < h.length) → ∃ (n : ℕ) (v : Bool),
        EF (h.take k) s = some n ∧ x[n]? = some h[k] ∧ EG (h.take k) s = some v) :
    ∀ i, i ≤ h.length →
      isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert EF EG s x h i =
          some (selectedBits (partialRuleSet ρ.sel) (h.take i)) := by
  intro i
  induction i with
  | zero => intro _; simp [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_zero,
              selectedBits, selectedAux]
  | succ i ih =>
    intro hi
    have hi' : i < h.length := hi
    have ih' := ih (Nat.le_of_lt hi')
    obtain ⟨n, v, hn, hx, hv⟩ := hcond i hi'
    have hvmem : v ∈ ρ.sel (h.take i) := hGsound _ _ _ hv
    have hmem : h.take i ∈ partialRuleSet ρ.sel ↔ v = true := by
      constructor
      · intro hh
        exact Part.mem_unique hvmem
            ((isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_mem_partialRuleSet.mp hh).2)
      · intro hvt
        refine isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_mem_partialRuleSet.mpr ⟨?_,
            hvt ▸ hvmem⟩
        intro y hy
        have hy' : y = h.take (min y.length i) := by
          have h1 : y = (h.take i).take y.length := List.prefix_iff_eq_take.mp hy
          rw [List.take_take] at h1
          exact h1
        have hlt : min y.length i < h.length := lt_of_le_of_lt (min_le_right _ _) hi'
        obtain ⟨_, v', -, -, hv'⟩ := hcond _ hlt
        rw [hy']
        exact Part.dom_iff_mem.mpr ⟨v', hGsound _ _ _ hv'⟩
    have htk : h.take (i + 1) = h.take i ++ [h[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi']
      rfl
    rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_succ, ih', hn, hv,
        List.getElem?_eq_getElem hi',
      isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_fin_eq_some]
    refine ⟨selectedBits (partialRuleSet ρ.sel) (h.take i), n, v, h[i], rfl, rfl, rfl, rfl, hx, ?_⟩
    rw [htk, selectedBits_append_singleton]
    by_cases hvt : v = true
    · have hR : h.take i ∈ partialRuleSet ρ.sel := hmem.mpr hvt
      simp [hvt, hR]
    · have hR : h.take i ∉ partialRuleSet ρ.sel := fun hh => hvt (hmem.mp hh)
      have hvf : v = false := by simpa using hvt
      simp [hvf, hR]

/-- Step 3 aux (completeness): if `u` is a prefix of the selected bits of `w` after some time,
the enumeration `isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_f` produces a cylinder
containing `w`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_complete (ρ : KLRule)
    (EF : BitString → ℕ → Option ℕ) (EG : BitString → ℕ → Option Bool)
    (hFmono : ∀ (a : BitString) (s t : ℕ) (v : ℕ), s ≤ t → EF a s = some v → EF a t = some v)
    (hFspec : ∀ (a : BitString) (v : ℕ), v ∈ ρ.next a ↔ ∃ s, EF a s = some v)
    (hGmono : ∀ (a : BitString) (s t : ℕ) (v : Bool), s ≤ t → EG a s = some v → EG a t = some v)
    (hGspec : ∀ (a : BitString) (v : Bool), v ∈ ρ.sel a ↔ ∃ s, EG a s = some v)
    (u : BitString) (w : CantorSeq) (t : ℕ) (hu : u <+: ρ.outputChain w t) :
    ∃ (j : ℕ) (x : BitString), isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_f EF EG u
        j = some x ∧ w ∈ cantorCylinder x := by
  classical
  set R := partialRuleSet ρ.sel with hR
  set H := ρ.revealed w t with hH
  have hpath : ∀ (x : BitString) (c : Bool), x ++ [c] <+: H → ∃ n ∈ ρ.next x, w n = c :=
    (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_path ρ w H).mp
        (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_revealed_fix ρ w t)
  have hu' : u <+: selectedBits R H := hu
  have hex : ∃ m, u <+: selectedBits R (H.take m) :=
    ⟨H.length, by rwa [List.take_length]⟩
  set m := Nat.find hex with hm
  have hmspec : u <+: selectedBits R (H.take m) := Nat.find_spec hex
  have hmle : m ≤ H.length := Nat.find_min' hex (by rwa [List.take_length])
  have hmin : ∀ k, k < m → ¬ u <+: selectedBits R (H.take k) := fun k hk => Nat.find_min hex hk
  have hdomm : ∀ k, k < m → (ρ.sel (H.take k)).Dom := by
    intro k hk
    have hq : m - 1 < H.length := by omega
    have htm : H.take m = H.take (m - 1) ++ [H[m - 1]] := by
      have hm1 : m = (m - 1) + 1 := by omega
      conv_lhs => rw [hm1]
      rw [List.take_add_one, List.getElem?_eq_getElem hq]
      rfl
    have hRq : H.take (m - 1) ∈ R := by
      by_contra hnot
      apply hmin (m - 1) (by omega)
      rw [htm, selectedBits_append_singleton, ite_eq_right hnot, List.append_nil] at hmspec
      exact hmspec
    refine (isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_mem_partialRuleSet.mp hRq).1
        (H.take k) ?_
    have hk' : H.take k = (H.take (m - 1)).take k := by
      rw [List.take_take]
      congr 1
      omega
    rw [hk']
    exact List.take_prefix _ _
  have hQ : ∀ k, k < m → ∃ M, ∃ (n : ℕ) (v b : Bool), H[k]? = some b ∧
      EF (H.take k) M = some n ∧ n < M ∧ w n = b ∧ EG (H.take k) M = some v := by
    intro k hk
    have hkH : k < H.length := lt_of_lt_of_le hk hmle
    have hpre : H.take k ++ [H[k]] <+: H := by
      have htk : H.take (k + 1) = H.take k ++ [H[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hkH]
        rfl
      rw [← htk]
      exact List.take_prefix _ _
    obtain ⟨n, hn, hwn⟩ := hpath _ _ hpre
    obtain ⟨s1, hs1⟩ := (hFspec _ _).mp hn
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp (hdomm k hk)
    obtain ⟨s2, hs2⟩ := (hGspec _ _).mp hv
    refine ⟨max (max s1 s2) (n + 1), n, v, H[k], List.getElem?_eq_getElem hkH, ?_, ?_, hwn, ?_⟩
    · exact hFmono _ _ _ _ ((le_max_left _ _).trans (le_max_left _ _)) hs1
    · exact lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)
    · exact hGmono _ _ _ _ ((le_max_right _ _).trans (le_max_left _ _)) hs2
  obtain ⟨M, hM⟩ := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_common_stage
    (fun k M => ∃ (n : ℕ) (v b : Bool), H[k]? = some b ∧
      EF (H.take k) M = some n ∧ n < M ∧ w n = b ∧ EG (H.take k) M = some v)
    (fun k s t hst ⟨n, v, b, h1, h2, h3, h4, h5⟩ =>
      ⟨n, v, b, h1, hFmono _ _ _ _ hst h2, lt_of_lt_of_le h3 hst, h4, hGmono _ _ _ _ hst h5⟩)
    m hQ
  have hlen : (H.take m).length = m := by
    rw [List.length_take]
    exact min_eq_left hmle
  have htake : ∀ k, k ≤ m → (H.take m).take k = H.take k := fun k hk => by
    rw [List.take_take, min_eq_left hk]
  have hcert := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_cert_eq ρ EF EG
      (fun a s v hv => (hGspec a v).mpr ⟨s, hv⟩) M
    (cantorPrefix w M) (H.take m) ?_ (H.take m).length le_rfl
  · rw [List.take_length] at hcert
    refine ⟨Encodable.encode (H.take m, M, cantorPrefix w M), cantorPrefix w M, ?_,
      mem_cantorCylinder_cantorPrefix w M⟩
    unfold isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_f
    rw [Encodable.encodek]
    simp only [Option.bind_some]
    rw [hcert]
    simp only [Option.bind_some]
    have hu_eq : u = (selectedBits R (H.take m)).take u.length :=
      List.prefix_iff_eq_take.mp hmspec
    have hdec : decide (u = (selectedBits R (H.take m)).take u.length) = true :=
      decide_eq_true hu_eq
    rw [hdec]
    rfl
  · intro k hk
    have hkm : k < m := by rw [hlen] at hk; exact hk
    obtain ⟨n, v, b, hb, hn1, hn2, hn3, hv⟩ := hM k hkm
    have hkH : k < H.length := lt_of_lt_of_le hkm hmle
    have hget : (H.take m)[k] = b := by
      have h1 : (H.take m)[k] = H[k] := List.getElem_take ..
      have h2 : H[k]? = some H[k] := List.getElem?_eq_getElem hkH
      rw [h2] at hb
      rw [h1]
      exact Option.some.inj hb
    have hxn : (cantorPrefix w M)[n]? = some (w n) := by
      have hn' : n < (cantorPrefix w M).length := by
        rw [cantorPrefix_length]
        exact hn2
      rw [List.getElem?_eq_getElem hn', cantorPrefix_getElem]
    refine ⟨n, v, by rw [htake k hkm.le]; exact hn1, ?_, by rw [htake k hkm.le]; exact hv⟩
    rw [hxn, hget, hn3]

/-- Step 3b: the events `{w | ∃ t, u <+: outputChain w t}` are uniformly effectively open for an
admissible rule. -/
lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_effopen {ρ : KLRule}
    (hρ : ρ.IsAdmissible) :
    ∃ f : BitString → ℕ → Option BitString, Computable₂ f ∧
      ∀ u : BitString, {w : CantorSeq | ∃ t, u <+: ρ.outputChain w t} =
        ⋃ i, (f u i).elim ∅ cantorCylinder := by
  obtain ⟨hF, hG⟩ := hρ
  obtain ⟨EF, hEFc, hEFm, hEFs⟩ := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_stepEval
      hF
  obtain ⟨EG, hEGc, hEGm, hEGs⟩ := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_stepEval
      hG
  refine ⟨isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_f EF EG,
      isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_f_computable hEFc hEGc,
      fun u => ?_⟩
  ext w
  constructor
  · intro hw
    obtain ⟨t, hu⟩ := hw
    obtain ⟨j, x, hj, hwx⟩ := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_complete ρ
        EF EG hEFm hEFs hEGm hEGs u w t hu
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    rw [hj]
    exact hwx
  · intro hw
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hw
    cases hfj : isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_f EF EG u j with
    | none => rw [hfj] at hj; simp at hj
    | some x =>
      rw [hfj] at hj
      exact isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_sound ρ hEFs hEGs u j x hfj w
          hj
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_output_tail_gt {p : NNReal}
    (hp : p ≤ 1) (a b : ℕ) (hb : 0 < b) (k n : ℕ)
    (hq : (p : ℝ) + 1 / ((k : ℝ) + 1) ≤ (a : ℝ) / b) (ρ : KLRule) :
    bernoulliMeasure p hp {w : CantorSeq | ∃ t, ∃ v : BitString, v.length = n ∧
        a * n < b * v.count true ∧ v <+: ρ.outputChain w t} ≤
      ENNReal.ofReal (Real.exp (-(2 * n) / ((k : ℝ) + 1) ^ 2)) := by
  classical
  set D : Set BitString := {v | v.length = n ∧ a * n < b * v.count true} with hD
  have hDc : D.Countable := Set.to_countable D
  have hset : {w : CantorSeq | ∃ t, ∃ v : BitString, v.length = n ∧
        a * n < b * v.count true ∧ v <+: ρ.outputChain w t}
      = ⋃ v ∈ D, {w : CantorSeq | ∃ t, v <+: ρ.outputChain w t} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hD, exists_prop]
    constructor
    · rintro ⟨t, v, h1, h2, h3⟩
      exact ⟨v, ⟨h1, h2⟩, t, h3⟩
    · rintro ⟨v, ⟨h1, h2⟩, t, h3⟩
      exact ⟨t, v, h1, h2, h3⟩
  have hdisj : D.PairwiseDisjoint cantorCylinder := by
    intro x hx y hy hxy
    apply cantorCylinder_disjoint_of_incompatible
    · intro h
      exact hxy (h.eq_of_length (hx.1.trans hy.1.symm))
    · intro h
      exact hxy (h.eq_of_length (hy.1.trans hx.1.symm)).symm
  have hcyl : (⋃ v ∈ D, cantorCylinder v) =
      {w : CantorSeq | a * n < b * (cantorPrefix w n).count true} := by
    ext w
    simp only [Set.mem_iUnion, exists_prop, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, ⟨h1, h2⟩, hw⟩
      have : cantorPrefix w n = v := by
        have := (isCantorPrefix_iff_cantorPrefix_eq v w).1 hw
        rw [← h1]
        exact this
      rw [this]
      exact h2
    · intro h
      exact ⟨cantorPrefix w n, ⟨cantorPrefix_length w n, h⟩, mem_cantorCylinder_cantorPrefix w n⟩
  rw [hset]
  calc bernoulliMeasure p hp (⋃ v ∈ D, {w : CantorSeq | ∃ t, v <+: ρ.outputChain w t})
      ≤ ∑' v : D, bernoulliMeasure p hp
          {w : CantorSeq | ∃ t, (v : BitString) <+: ρ.outputChain w t} :=
        measure_biUnion_le _ hDc _
    _ ≤ ∑' v : D, bernoulliMeasure p hp (cantorCylinder (v : BitString)) :=
        ENNReal.tsum_le_tsum (fun v =>
          isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_selection hp ρ v)
    _ = bernoulliMeasure p hp (⋃ v ∈ D, cantorCylinder v) :=
        (measure_biUnion hDc hdisj (fun v _ => measurableSet_cantorCylinder v)).symm
    _ = bernoulliMeasure p hp {w : CantorSeq | a * n < b * (cantorPrefix w n).count true} := by
        rw [hcyl]
    _ ≤ _ := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_tail_gt hp a b hb k n hq

private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_output_tail_lt {p : NNReal}
    (hp : p ≤ 1) (a b : ℕ) (hb : 0 < b) (k n : ℕ)
    (hq : (a : ℝ) / b + 1 / ((k : ℝ) + 1) ≤ (p : ℝ)) (ρ : KLRule) :
    bernoulliMeasure p hp {w : CantorSeq | ∃ t, ∃ v : BitString, v.length = n ∧
        b * v.count true < a * n ∧ v <+: ρ.outputChain w t} ≤
      ENNReal.ofReal (Real.exp (-(2 * n) / ((k : ℝ) + 1) ^ 2)) := by
  classical
  set D : Set BitString := {v | v.length = n ∧ b * v.count true < a * n} with hD
  have hDc : D.Countable := Set.to_countable D
  have hset : {w : CantorSeq | ∃ t, ∃ v : BitString, v.length = n ∧
        b * v.count true < a * n ∧ v <+: ρ.outputChain w t}
      = ⋃ v ∈ D, {w : CantorSeq | ∃ t, v <+: ρ.outputChain w t} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hD, exists_prop]
    constructor
    · rintro ⟨t, v, h1, h2, h3⟩
      exact ⟨v, ⟨h1, h2⟩, t, h3⟩
    · rintro ⟨v, ⟨h1, h2⟩, t, h3⟩
      exact ⟨t, v, h1, h2, h3⟩
  have hdisj : D.PairwiseDisjoint cantorCylinder := by
    intro x hx y hy hxy
    apply cantorCylinder_disjoint_of_incompatible
    · intro h
      exact hxy (h.eq_of_length (hx.1.trans hy.1.symm))
    · intro h
      exact hxy (h.eq_of_length (hy.1.trans hx.1.symm)).symm
  have hcyl : (⋃ v ∈ D, cantorCylinder v) =
      {w : CantorSeq | b * (cantorPrefix w n).count true < a * n} := by
    ext w
    simp only [Set.mem_iUnion, exists_prop, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, ⟨h1, h2⟩, hw⟩
      have : cantorPrefix w n = v := by
        have := (isCantorPrefix_iff_cantorPrefix_eq v w).1 hw
        rw [← h1]
        exact this
      rw [this]
      exact h2
    · intro h
      exact ⟨cantorPrefix w n, ⟨cantorPrefix_length w n, h⟩, mem_cantorCylinder_cantorPrefix w n⟩
  rw [hset]
  calc bernoulliMeasure p hp (⋃ v ∈ D, {w : CantorSeq | ∃ t, v <+: ρ.outputChain w t})
      ≤ ∑' v : D, bernoulliMeasure p hp
          {w : CantorSeq | ∃ t, (v : BitString) <+: ρ.outputChain w t} :=
        measure_biUnion_le _ hDc _
    _ ≤ ∑' v : D, bernoulliMeasure p hp (cantorCylinder (v : BitString)) :=
        ENNReal.tsum_le_tsum (fun v =>
          isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_selection hp ρ v)
    _ = bernoulliMeasure p hp (⋃ v ∈ D, cantorCylinder v) :=
        (measure_biUnion hDc hdisj (fun v _ => measurableSet_cantorCylinder v)).symm
    _ = bernoulliMeasure p hp {w : CantorSeq | b * (cantorPrefix w n).count true < a * n} := by
        rw [hcyl]
    _ ≤ _ := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_tail_lt hp a b hb k n hq

/-! ## Step 5a: tail unions have measure at most `2^{-m}` -/

private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_union_gt {p : NNReal}
    (hp : p ≤ 1) (a b : ℕ) (hb : 0 < b) (k m : ℕ)
    (hq : (p : ℝ) + 1 / ((k : ℝ) + 1) ≤ (a : ℝ) / b) (ρ : KLRule) :
    bernoulliMeasure p hp {w : CantorSeq | ∃ t, ∃ v : BitString, devThresh k m ≤ v.length ∧
        a * v.length < b * v.count true ∧ v <+: ρ.outputChain w t} ≤ dyadicValue 1 m := by
  set T := devThresh k m with hTdef
  have hsub : {w : CantorSeq | ∃ t, ∃ v : BitString, T ≤ v.length ∧
        a * v.length < b * v.count true ∧ v <+: ρ.outputChain w t} ⊆
      ⋃ j : ℕ, {w : CantorSeq | ∃ t, ∃ v : BitString, v.length = T + j ∧
        a * (T + j) < b * v.count true ∧ v <+: ρ.outputChain w t} := by
    rintro w ⟨t, v, h1, h2, h3⟩
    refine Set.mem_iUnion.2 ⟨v.length - T, ?_⟩
    have hsum : T + (v.length - T) = v.length := by omega
    refine ⟨t, v, hsum.symm, ?_, h3⟩
    rw [hsum]
    exact h2
  have hle : bernoulliMeasure p hp {w : CantorSeq | ∃ t, ∃ v : BitString, T ≤ v.length ∧
        a * v.length < b * v.count true ∧ v <+: ρ.outputChain w t}
      ≤ ∑' j : ℕ, bernoulliMeasure p hp {w : CantorSeq | ∃ t, ∃ v : BitString,
        v.length = T + j ∧ a * (T + j) < b * v.count true ∧ v <+: ρ.outputChain w t} :=
    (measure_mono hsub).trans (measure_iUnion_le _)
  have hterm : ∀ j : ℕ, bernoulliMeasure p hp {w : CantorSeq | ∃ t, ∃ v : BitString,
        v.length = T + j ∧ a * (T + j) < b * v.count true ∧ v <+: ρ.outputChain w t}
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2)) := by
    intro j
    have h := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_output_tail_gt hp a b hb k
        (T + j) hq ρ
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    push_cast
    have := Real.exp_pos (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2)
    linarith
  refine hle.trans ((ENNReal.tsum_le_tsum hterm).trans ?_)
  have hnonneg : ∀ j : ℕ,
      (0 : ℝ) ≤ 2 * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2) := by
    intro j; positivity
  have hsum := (ENNReal.ofReal_tsum_of_nonneg hnonneg (expTail_summable k T)).symm
  rw [hsum]
  have hT : (T : ℝ) = ((k : ℝ) + 1) ^ 2 * ((m : ℝ) + 2 * k + 4) := by
    rw [hTdef, devThresh]; push_cast; ring
  have hb' := expTail_le k m T hT
  refine (ENNReal.ofReal_le_ofReal hb').trans ?_
  rw [dyadicValue_one_eq_inv_two_pow']
  rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_union_lt {p : NNReal}
    (hp : p ≤ 1) (a b : ℕ) (hb : 0 < b) (k m : ℕ)
    (hq : (a : ℝ) / b + 1 / ((k : ℝ) + 1) ≤ (p : ℝ)) (ρ : KLRule) :
    bernoulliMeasure p hp {w : CantorSeq | ∃ t, ∃ v : BitString, devThresh k m ≤ v.length ∧
        b * v.count true < a * v.length ∧ v <+: ρ.outputChain w t} ≤ dyadicValue 1 m := by
  set T := devThresh k m with hTdef
  have hsub : {w : CantorSeq | ∃ t, ∃ v : BitString, T ≤ v.length ∧
        b * v.count true < a * v.length ∧ v <+: ρ.outputChain w t} ⊆
      ⋃ j : ℕ, {w : CantorSeq | ∃ t, ∃ v : BitString, v.length = T + j ∧
        b * v.count true < a * (T + j) ∧ v <+: ρ.outputChain w t} := by
    rintro w ⟨t, v, h1, h2, h3⟩
    refine Set.mem_iUnion.2 ⟨v.length - T, ?_⟩
    have hsum : T + (v.length - T) = v.length := by omega
    refine ⟨t, v, hsum.symm, ?_, h3⟩
    rw [hsum]
    exact h2
  have hle : bernoulliMeasure p hp {w : CantorSeq | ∃ t, ∃ v : BitString, T ≤ v.length ∧
        b * v.count true < a * v.length ∧ v <+: ρ.outputChain w t}
      ≤ ∑' j : ℕ, bernoulliMeasure p hp {w : CantorSeq | ∃ t, ∃ v : BitString,
        v.length = T + j ∧ b * v.count true < a * (T + j) ∧ v <+: ρ.outputChain w t} :=
    (measure_mono hsub).trans (measure_iUnion_le _)
  have hterm : ∀ j : ℕ, bernoulliMeasure p hp {w : CantorSeq | ∃ t, ∃ v : BitString,
        v.length = T + j ∧ b * v.count true < a * (T + j) ∧ v <+: ρ.outputChain w t}
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2)) := by
    intro j
    have h := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_output_tail_lt hp a b hb k
        (T + j) hq ρ
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    push_cast
    have := Real.exp_pos (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2)
    linarith
  refine hle.trans ((ENNReal.tsum_le_tsum hterm).trans ?_)
  have hnonneg : ∀ j : ℕ,
      (0 : ℝ) ≤ 2 * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2) := by
    intro j; positivity
  have hsum := (ENNReal.ofReal_tsum_of_nonneg hnonneg (expTail_summable k T)).symm
  rw [hsum]
  have hT : (T : ℝ) = ((k : ℝ) + 1) ^ 2 * ((m : ℝ) + 2 * k + 4) := by
    rw [hTdef, devThresh]; push_cast; ring
  have hb' := expTail_le k m T hT
  refine (ENNReal.ofReal_le_ofReal hb').trans ?_
  rw [dyadicValue_one_eq_inv_two_pow']
  rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num
/-- Counting the `true` bits of a bitstring is primitive recursive (private copy of
`Kolmogorov.primrec_count_true`, which is not in the import closure of this file). -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_primrec_count_true :
    Primrec (fun s : BitString => s.count true) := by
  have hstep : Primrec₂ (fun (_ : BitString) (bn : Bool × ℕ) =>
      bif bn.1 then bn.2 + 1 else bn.2) :=
    (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have heq : (fun s : BitString => s.count true)
      = fun s => s.foldr (fun b n => bif b then n + 1 else n) 0 := by
    funext s; induction s with
    | nil => rfl
    | cons b s ih => cases b <;> simp [ih]
  rw [heq]
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) hstep

/-- Step 5b: a Martin-Löf random sequence for `B_p` is outside one of the tail unions of the
selection events, for any computable family of strings `d` and computable thresholds `N`
whose tail unions have measure at most `2^{-m}`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_mltest {p : NNReal}
    (hp : p ≤ 1) {ρ : KLRule} (hρ : ρ.IsAdmissible)
    (d : BitString → Bool) (hd : Computable d) (N : ℕ → ℕ) (hN : Computable N)
    (hbound : ∀ m : ℕ, bernoulliMeasure p hp {w : CantorSeq | ∃ t, ∃ v : BitString,
        N m ≤ v.length ∧ d v = true ∧ v <+: ρ.outputChain w t} ≤ dyadicValue 1 m)
    {w : CantorSeq} (hw : IsMartinLofRandom (bernoulliMeasure p hp) w) :
    ∃ m : ℕ, ∀ t : ℕ, ∀ v : BitString, N m ≤ v.length → d v = true → ¬ v <+: ρ.outputChain w t := by
  classical
  obtain ⟨f, hf, hfeq⟩ := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_effopen hρ
  set g : ℕ → ℕ → Option BitString := fun m j =>
    (Encodable.decode (α := BitString) j.unpair.1).bind
      (fun v => bif ((N m - v.length == 0) && d v) then f v j.unpair.2 else none) with hgdef
  have hg : Computable₂ g := by
    have h1 : Computable (fun q : ℕ × ℕ => Encodable.decode (α := BitString) q.2.unpair.1) :=
      Computable.decode.comp ((Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd)
    have hN1 : Computable (fun x : (ℕ × ℕ) × BitString => N x.1.1) :=
      hN.comp (Computable.fst.comp Computable.fst)
    have hlen : Computable (fun x : (ℕ × ℕ) × BitString => x.2.length) :=
      Primrec.list_length.to_comp.comp Computable.snd
    have hsub : Computable (fun x : (ℕ × ℕ) × BitString => N x.1.1 - x.2.length) :=
      Primrec.nat_sub.to_comp.comp hN1 hlen
    have hbeq : Computable (fun x : (ℕ × ℕ) × BitString => (N x.1.1 - x.2.length == 0)) :=
      Primrec.beq.to_comp.comp hsub (Computable.const 0)
    have hcond : Computable (fun x : (ℕ × ℕ) × BitString =>
        ((N x.1.1 - x.2.length == 0) && d x.2)) :=
      Primrec.and.to_comp.comp hbeq (hd.comp Computable.snd)
    have hj2 : Computable (fun x : (ℕ × ℕ) × BitString => x.1.2.unpair.2) :=
      (Primrec.snd.comp Primrec.unpair).to_comp.comp (Computable.snd.comp Computable.fst)
    have hfv : Computable (fun x : (ℕ × ℕ) × BitString => f x.2 x.1.2.unpair.2) :=
      Computable₂.comp (f := f) hf Computable.snd hj2
    exact Computable.option_bind h1 (Computable.cond hcond hfv (Computable.const none))
  have hU : ∀ m, {w : CantorSeq | ∃ t, ∃ v : BitString, N m ≤ v.length ∧ d v = true ∧
        v <+: ρ.outputChain w t} = ⋃ j, (g m j).elim ∅ cantorCylinder := by
    intro m
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨t, v, hNv, hdv, hpre⟩
      have hx : x ∈ {w : CantorSeq | ∃ t, v <+: ρ.outputChain w t} := ⟨t, hpre⟩
      rw [hfeq v] at hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      refine ⟨Nat.pair (Encodable.encode v) i, ?_⟩
      have hc : ((N m - v.length == 0) && d v) = true := by
        simp [hdv, Nat.sub_eq_zero_of_le hNv]
      simp only [hgdef, Nat.unpair_pair, Encodable.encodek, Option.bind_some, hc, Bool.cond_true]
      exact hi
    · rintro ⟨j, hj⟩
      simp only [hgdef] at hj
      cases hdec : Encodable.decode (α := BitString) j.unpair.1 with
      | none => simp [hdec] at hj
      | some v =>
        rw [hdec] at hj
        simp only [Option.bind_some] at hj
        by_cases hc : ((N m - v.length == 0) && d v) = true
        · rw [hc] at hj
          simp only [Bool.cond_true] at hj
          have hx : x ∈ {w : CantorSeq | ∃ t, v <+: ρ.outputChain w t} := by
            rw [hfeq v]
            exact Set.mem_iUnion.2 ⟨j.unpair.2, hj⟩
          obtain ⟨t, ht⟩ := hx
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          exact ⟨t, v, by omega, hc.2, ht⟩
        · have hc' : ((N m - v.length == 0) && d v) = false := by simpa using hc
          rw [hc'] at hj
          simp at hj
  have htest : IsMartinLofTest (bernoulliMeasure p hp)
      (fun m => {w : CantorSeq | ∃ t, ∃ v : BitString, N m ≤ v.length ∧ d v = true ∧
        v <+: ρ.outputChain w t}) :=
    ⟨⟨g, hg, hU⟩, hbound⟩
  have hnot := hw _ htest
  rw [Set.mem_iInter] at hnot
  push Not at hnot
  obtain ⟨m, hm⟩ := hnot
  exact ⟨m, fun t v hv hdv hpre => hm ⟨t, v, hv, hdv, hpre⟩⟩

/-! ## Step 5c: the limit frequency -/

/-- A nonnegative rational number is a quotient of natural numbers. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_rat_eq_nat_div (q : ℚ)
    (hq : 0 ≤ q) :
    ∃ a b : ℕ, 0 < b ∧ (q : ℝ) = (a : ℝ) / b := by
  refine ⟨q.num.toNat, q.den, q.pos, ?_⟩
  have hnum : (0 : ℤ) ≤ q.num := Rat.num_nonneg.2 hq
  have h1 : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg hnum
  have h2 : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by exact_mod_cast h1
  rw [h2]
  exact Rat.cast_def q

/-- The real frequency of ones in the prefix of length `n`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_freqOne_real
    (u : CantorSeq) (n : ℕ) :
    (freqOne u n : ℝ) = ((cantorPrefix u n).count true : ℝ) / n := by
  simp [freqOne]

/-- Step 5c: from the tail estimates to the limit frequency of the output. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_limit {p : ℝ} (hp0 : 0 ≤ p)
    {w u : CantorSeq} (ρ : KLRule)
    (hout : ∀ n : ℕ, ∃ t : ℕ, cantorPrefix u n <+: ρ.outputChain w t)
    (hgt : ∀ (a b k : ℕ), 0 < b → p + 1 / ((k : ℝ) + 1) ≤ (a : ℝ) / b →
      ∃ m : ℕ, ∀ t : ℕ, ∀ v : BitString, devThresh k m ≤ v.length → a * v.length < b * v.count true
          →
        ¬ v <+: ρ.outputChain w t)
    (hlt : ∀ (a b k : ℕ), 0 < b → (a : ℝ) / b + 1 / ((k : ℝ) + 1) ≤ p →
      ∃ m : ℕ, ∀ t : ℕ, ∀ v : BitString, devThresh k m ≤ v.length → b * v.count true < a * v.length
          →
        ¬ v <+: ρ.outputChain w t) :
    HasLimitFreq p u := by
  unfold HasLimitFreq
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
  set c : ℝ := 1 / ((k : ℝ) + 1) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcε : 2 * c < ε := by linarith
  have hupper : ∃ N1 : ℕ, ∀ n : ℕ, N1 ≤ n → 0 < n → (freqOne u n : ℝ) < p + ε := by
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show p + c < p + 2 * c by linarith)
    have hqpos : (0 : ℚ) ≤ q := by
      have : (0 : ℝ) ≤ (q : ℝ) := by linarith
      exact_mod_cast this
    obtain ⟨a, b, hb, hab⟩ :=
        isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_rat_eq_nat_div q hqpos
    obtain ⟨m, hm⟩ := hgt a b k hb (by rw [← hab]; exact hq1.le)
    refine ⟨devThresh k m, fun n hn hn0 => ?_⟩
    obtain ⟨t, ht⟩ := hout n
    have hle : b * (cantorPrefix u n).count true ≤ a * n := by
      by_contra hcon
      push Not at hcon
      exact hm t (cantorPrefix u n) (by rw [cantorPrefix_length]; exact hn)
        (by rwa [cantorPrefix_length]) ht
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have hle' : ((cantorPrefix u n).count true : ℝ) / n ≤ (a : ℝ) / b := by
      rw [div_le_div_iff₀ hn' hb']
      have : (((cantorPrefix u n).count true * b : ℕ) : ℝ) ≤ ((a * n : ℕ) : ℝ) := by
        exact_mod_cast (by rw [Nat.mul_comm]; exact hle)
      push_cast at this
      exact this
    rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_freqOne_real]
    have hq3 : (a : ℝ) / b = (q : ℝ) := hab.symm
    linarith
  have hlower : ∃ N2 : ℕ, ∀ n : ℕ, N2 ≤ n → 0 < n → p - ε < (freqOne u n : ℝ) := by
    by_cases hpe : p - ε < 0
    · refine ⟨0, fun n _ hn0 => ?_⟩
      have : (0 : ℝ) ≤ (freqOne u n : ℝ) := by
        rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_freqOne_real]; positivity
      linarith
    · push Not at hpe
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show p - 2 * c < p - c by linarith)
      have hqpos : (0 : ℚ) ≤ q := by
        have : (0 : ℝ) ≤ (q : ℝ) := by linarith
        exact_mod_cast this
      obtain ⟨a, b, hb, hab⟩ :=
          isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_rat_eq_nat_div q hqpos
      obtain ⟨m, hm⟩ := hlt a b k hb (by rw [← hab]; linarith)
      refine ⟨devThresh k m, fun n hn hn0 => ?_⟩
      obtain ⟨t, ht⟩ := hout n
      have hle : a * n ≤ b * (cantorPrefix u n).count true := by
        by_contra hcon
        push Not at hcon
        exact hm t (cantorPrefix u n) (by rw [cantorPrefix_length]; exact hn)
          (by rwa [cantorPrefix_length]) ht
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
      have hb' : (0 : ℝ) < b := by exact_mod_cast hb
      have hle' : (a : ℝ) / b ≤ ((cantorPrefix u n).count true : ℝ) / n := by
        rw [div_le_div_iff₀ hb' hn']
        have : ((a * n : ℕ) : ℝ) ≤ ((b * (cantorPrefix u n).count true : ℕ) : ℝ) := by
          exact_mod_cast hle
        push_cast at this
        linarith
      rw [isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_freqOne_real]
      have hq3 : (a : ℝ) / b = (q : ℝ) := hab.symm
      linarith
  obtain ⟨N1, h1⟩ := hupper
  obtain ⟨N2, h2⟩ := hlower
  refine ⟨max (max N1 N2) 1, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hn)
  have e1 := h1 n hn1 hn0
  have e2 := h2 n hn2 hn0
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **SUV Theorem 192(b), p. 292**, for a Bernoulli measure with computable parameter: a sequence
that is Martin-Löf random for `B_p` has limit frequency `p` under every Kolmogorov-Loveland
admissible rule.  Computability of `p` is explicit, as required by the book.  The degenerate
parameters `0` and `1` are also admitted: their only random sequences are the constant ones. -/
theorem isMisesKLRandomAt_of_isMartinLofRandom_bernoulli {p : NNReal} (hp : p ≤ 1)
    (_hpc : ComputableReals.IsComputableReal (p : ℝ)) {w : CantorSeq}
    (hw : IsMartinLofRandom (bernoulliMeasure p hp) w) : IsMisesKLRandomAt (p : ℝ) w := by
  intro ρ hρ
  rcases hs : ρ.output w with x | u
  · trivial
  · change HasLimitFreq (p : ℝ) u
    have hout : ∀ n : ℕ, ∃ t : ℕ, cantorPrefix u n <+: ρ.outputChain w t := by
      intro n
      have H2 : BitStream.finite (cantorPrefix u n) ≤ BitStream.infinite u := by
        apply BitStream.finite_le_infinite_iff.mpr
        rw [isCantorPrefix_iff_cantorPrefix_eq, cantorPrefix_length]
      have H := BitStream.finite_le_ofPrefixSet_iff
        (isStreamPrefixSet_chainPrefixSet (KLRule.outputChain_prefix ρ w)) (cantorPrefix u n)
      rw [← hs] at H2
      exact H.mp H2
    have hgt : ∀ (a b k : ℕ), 0 < b → (p : ℝ) + 1 / ((k : ℝ) + 1) ≤ (a : ℝ) / b →
        ∃ m : ℕ, ∀ t : ℕ, ∀ v : BitString, devThresh k m ≤ v.length →
          a * v.length < b * v.count true → ¬ v <+: ρ.outputChain w t := by
      intro a b k hb hq
      have hd : Computable (fun v : BitString => decide (a * v.length < b * v.count true)) := by
        have hl : Primrec (fun v : BitString => a * v.length) :=
          Primrec.nat_mul.comp (Primrec.const a) Primrec.list_length
        have hc : Primrec (fun v : BitString => b * v.count true) :=
          Primrec.nat_mul.comp (Primrec.const b)
              isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_primrec_count_true
        exact ((PrimrecRel.decide Primrec.nat_lt).comp hl hc).to_comp
      have hN : Computable (devThresh k) :=
        computable_devThresh (k := fun _ : ℕ => k) (m := fun m : ℕ => m)
          (Computable.const k) Computable.id
      obtain ⟨m, hm⟩ := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_mltest hp hρ
        (fun v : BitString => decide (a * v.length < b * v.count true)) hd (devThresh k) hN
        (fun m => by
          have h := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_union_gt hp a b hb k m
              hq ρ
          refine le_trans (le_of_eq ?_) h
          congr 1
          ext x
          simp only [Set.mem_ofPred_eq, decide_eq_true_eq]) hw
      exact ⟨m, fun t v hv hlt hpre => hm t v hv (by simpa using hlt) hpre⟩
    have hlt : ∀ (a b k : ℕ), 0 < b → (a : ℝ) / b + 1 / ((k : ℝ) + 1) ≤ (p : ℝ) →
        ∃ m : ℕ, ∀ t : ℕ, ∀ v : BitString, devThresh k m ≤ v.length →
          b * v.count true < a * v.length → ¬ v <+: ρ.outputChain w t := by
      intro a b k hb hq
      have hd : Computable (fun v : BitString => decide (b * v.count true < a * v.length)) := by
        have hl : Primrec (fun v : BitString => a * v.length) :=
          Primrec.nat_mul.comp (Primrec.const a) Primrec.list_length
        have hc : Primrec (fun v : BitString => b * v.count true) :=
          Primrec.nat_mul.comp (Primrec.const b)
              isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_aux_primrec_count_true
        exact ((PrimrecRel.decide Primrec.nat_lt).comp hc hl).to_comp
      have hN : Computable (devThresh k) :=
        computable_devThresh (k := fun _ : ℕ => k) (m := fun m : ℕ => m)
          (Computable.const k) Computable.id
      obtain ⟨m, hm⟩ := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_mltest hp hρ
        (fun v : BitString => decide (b * v.count true < a * v.length)) hd (devThresh k) hN
        (fun m => by
          have h := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_union_lt hp a b hb k m
              hq ρ
          refine le_trans (le_of_eq ?_) h
          congr 1
          ext x
          simp only [Set.mem_ofPred_eq, decide_eq_true_eq]) hw
      exact ⟨m, fun t v hv hlt hpre => hm t v hv (by simpa using hlt) hpre⟩
    exact isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_limit (NNReal.coe_nonneg p) ρ hout
        hgt hlt

/-- **SUV Theorem 192(b), p. 292**, for the uniform measure. -/
theorem isMisesKLRandom_of_isMartinLofRandom {w : CantorSeq}
    (hw : IsMartinLofRandom uniformMeasure w) : IsMisesKLRandom w := by
  have hcomp : ComputableReals.IsComputableReal (1 / 2 : ℝ) := by
    have h : (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by norm_num
    rw [h]
    exact ComputableReals.isComputableReal_ratCast (1 / 2 : ℚ)
  exact isMisesKLRandomAt_of_isMartinLofRandom_bernoulli (p := 1 / 2) (by norm_num) hcomp hw

end Kolmogorov.FrequencyGames
