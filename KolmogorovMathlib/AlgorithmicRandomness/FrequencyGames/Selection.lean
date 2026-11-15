/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.LibraryAPI
import KolmogorovMathlib.AlgorithmicRandomness.StrongLaw
import KolmogorovMathlib.AlgorithmicRandomness.BlockMap

/-!
# Selection rules given by sets of strings (SUV Sections 9.1-9.2, pp. 261-263)

The output of a selection rule is a finite or infinite sequence, which is the library's
`BitStream` (the book's `Σ`).  `selectedBits R x` lists the selected terms of a finite string,
`selectStream R ω` is the book's `S_R(ω)`, and `partialRuleSet r` is the set `R` of a partial rule
`r` (p. 287), so that hanging is modelled exactly as the book describes: after the first string on
which `r` is undefined nothing more is selected.

`FiniteOrFreq p s` says that `s` is finite or has limit frequency `p`; `IsBalanced` is the case
`p = 1/2` (p. 262).  A limit frequency is a statement about an infinite sequence only, so the
finite case is a separate branch and no ratio with denominator `0` is ever used to decide it.

The main statements are Theorem 166 and the preimage Lemma of p. 263.
-/

namespace Kolmogorov.FrequencyGames

open MeasureTheory Filter Topology ProbabilityTheory

/-! ### Frequencies -/

/-- The frequency of ones in the prefixes of `w` tends to `p`.  SUV p. 261. -/
def HasLimitFreq (p : ℝ) (w : CantorSeq) : Prop :=
  Tendsto (fun n => (freqOne w n : ℝ)) atTop (𝓝 p)

/-- A *balanced* sequence: the frequency of ones has limit `1/2`.  SUV p. 262. -/
abbrev IsBalanced (w : CantorSeq) : Prop := HasLimitFreq (1 / 2) w

/-- A finite or infinite sequence that is finite, or infinite with limit frequency `p`.  This is
the condition every admissible rule has to satisfy in the Mises-style definitions. -/
def FiniteOrFreq (p : ℝ) : BitStream → Prop
  | .finite _ => True
  | .infinite w => HasLimitFreq p w

/-! ### Chains of strings and the sequence they determine -/

/-- All prefixes of the members of a chain. -/
def chainPrefixSet (c : ℕ → BitString) : Set BitString := {y | ∃ t, y <+: c t}

/-- A chain of strings, each a prefix of the next, is monotone for the prefix relation. -/
lemma chain_prefix_of_le {c : ℕ → BitString} (hc : ∀ t, c t <+: c (t + 1)) {s t : ℕ}
    (h : s ≤ t) : c s <+: c t := by
  induction h with
  | refl => exact List.prefix_rfl
  | step _ ih => exact ih.trans (hc _)

/-- The prefixes of a chain form the approximation set of a single stream. -/
lemma isStreamPrefixSet_chainPrefixSet {c : ℕ → BitString} (hc : ∀ t, c t <+: c (t + 1)) :
    IsStreamPrefixSet (chainPrefixSet c) := by
  refine ⟨⟨0, List.nil_prefix⟩, ?_, ?_⟩
  · rintro x y hxy ⟨t, ht⟩
    exact ⟨t, hxy.trans ht⟩
  · rintro x y ⟨s, hs⟩ ⟨t, ht⟩
    have hle := chain_prefix_of_le hc (le_max_left s t)
    have hle' := chain_prefix_of_le hc (le_max_right s t)
    exact List.prefix_or_prefix_of_prefix (hs.trans hle) (ht.trans hle')

/-- The finite or infinite sequence determined by a chain of strings. -/
noncomputable def streamOfChain (c : ℕ → BitString) (hc : ∀ t, c t <+: c (t + 1)) : BitStream :=
  BitStream.ofPrefixSet (chainPrefixSet c) (isStreamPrefixSet_chainPrefixSet hc)

/-! ### Selecting from a string -/

open Classical in
/-- Auxiliary form of `selectedBits`: `pre` is the part of the string already read. -/
noncomputable def selectedAux (R : Set BitString) : BitString → BitString → BitString
  | _, [] => []
  | pre, b :: rest => (if pre ∈ R then [b] else []) ++ selectedAux R (pre ++ [b]) rest

/-- The terms of `x` selected by `R`: those `x_n` with `x_0 … x_{n-1} ∈ R`, in their order.  The
decision for a term depends only on the terms before it, not on its value.  SUV p. 262. -/
noncomputable def selectedBits (R : Set BitString) (x : BitString) : BitString :=
  selectedAux R [] x

/-- Reading `x ++ z` selects what `x` selects, followed by what `z` selects after `x`. -/
lemma selectedAux_append (R : Set BitString) (pre x z : BitString) :
    selectedAux R pre (x ++ z) = selectedAux R pre x ++ selectedAux R (pre ++ x) z := by
  induction x generalizing pre with
  | nil => simp [selectedAux]
  | cons b x ih =>
    simp only [List.cons_append, selectedAux, List.append_assoc, ih]
    congr 3

/-- Selection is monotone in the string read. -/
lemma selectedBits_prefix (R : Set BitString) {x y : BitString} (h : x <+: y) :
    selectedBits R x <+: selectedBits R y := by
  rcases h with ⟨z, rfl⟩
  exact ⟨_, (selectedAux_append R [] x z).symm⟩

open Classical in
/-- One more term: `x_n` is selected exactly when `x_0 … x_{n-1} ∈ R`. -/
lemma selectedBits_append_singleton (R : Set BitString) (x : BitString) (b : Bool) :
    selectedBits R (x ++ [b]) = selectedBits R x ++ (if x ∈ R then [b] else []) := by
  simp [selectedBits, selectedAux_append, selectedAux]

/-! ### The selection rule `S_R` -/

/-- The chain of selected prefixes of `ω`. -/
noncomputable def selectChain (R : Set BitString) (w : CantorSeq) (t : ℕ) : BitString :=
  selectedBits R (cantorPrefix w t)

/-- The chain of selected prefixes is a chain. -/
lemma selectChain_prefix (R : Set BitString) (w : CantorSeq) (t : ℕ) :
    selectChain R w t <+: selectChain R w (t + 1) :=
  selectedBits_prefix R (cantorPrefix_mono w (Nat.le_succ t))

/-- The selection rule `S_R : Ω → Σ`: the terms `ω_n` with `ω_0 … ω_{n-1} ∈ R`.  SUV p. 262. -/
noncomputable def selectStream (R : Set BitString) (w : CantorSeq) : BitStream :=
  streamOfChain (selectChain R w) (selectChain_prefix R w)

/-- The set of a partial rule `r`: the strings on all of whose prefixes `r` is defined and on which
it takes value `1`.  The rule `S_r` of SUV p. 287 is `S_R` for this set `R`. -/
def partialRuleSet (r : BitString →. Bool) : Set BitString :=
  {x | (∀ y, y <+: x → (r y).Dom) ∧ true ∈ r x}

/-! ### Theorem 166 -/

/-- The `S_R`-preimage of a set of infinite sequences. -/
def selectPreimage (R : Set BitString) (U : Set CantorSeq) : Set CantorSeq :=
  {w | ∃ u ∈ U, selectStream R w = .infinite u}

/-- Step 1 of the proof of measure_selectPreimage_eq_zero: Express the measure of U as the
infimum of sums of measures of its countable cylinder covers. -/
private lemma measure_selectPreimage_eq_zero_inf_sum (U : Set CantorSeq) :
    uniformMeasure U = ⨅ (s : ℕ → BitString) (_h : U ⊆ ⋃ i, cantorCylinder (s i)),
      ∑' i, (1/2:ENNReal)^(s i).length := by
  apply le_antisymm
  · apply le_iInf₂
    intro s hs
    apply le_trans (measure_mono hs)
    apply le_trans (measure_iUnion_le (fun i => cantorCylinder (s i)))
    have h_eq : (fun i => uniformMeasure (cantorCylinder (s i))) = fun i => (1/2:ENNReal)^(s
        i).length := by
      ext i
      have h_mass := cantorMass_uniformMeasure (s i)
      change uniformMeasure (cantorCylinder (s i)) = _ at h_mass
      rw [h_mass]
      simp [one_div]
    rw [h_eq]
  · classical
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hδ : ((ε : ENNReal) / 2) ≠ 0 := by
      simp [hε.ne']
    have hδ2 : ((ε : ENNReal) / 2 / 2) ≠ 0 := by
      simp [hε.ne']
    obtain ⟨V, hUV, hVo, hV⟩ := Set.exists_isOpen_lt_add U (measure_ne_top uniformMeasure U) hδ
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_two_pow_lt hδ2
    let h : ℕ → Option BitString := fun n =>
      match Encodable.decode (α := BitString) n with
      | some x => if cantorCylinder x ⊆ V then some x else none
      | none => none
    have hVeq : (⋃ j, coverSet h j) = V := by
      apply Set.Subset.antisymm
      · refine Set.iUnion_subset fun j => ?_
        unfold coverSet
        cases hj : h j with
        | none => simp
        | some x =>
          simp only [Option.elim_some]
          cases hd : Encodable.decode (α := BitString) j with
          | none => simp [h, hd] at hj
          | some y =>
            simp only [h, hd] at hj
            split_ifs at hj with hy
            cases hj
            exact hy
      · intro w hw
        obtain ⟨_, ⟨x, rfl⟩, hwx, hxV⟩ :=
          (isTopologicalBasis_cantorCylinders.isOpen_iff.mp hVo) w hw
        refine Set.mem_iUnion.mpr ⟨Encodable.encode x, ?_⟩
        unfold coverSet
        have : h (Encodable.encode x) = some x := by
          simp [h, hxV]
        rw [this]
        exact hwx
    let s : ℕ → BitString := fun i => (disjEnum h i).getD (List.replicate (i + k) false)
    have hcover : U ⊆ ⋃ i, cantorCylinder (s i) := by
      intro w hw
      have hwV : w ∈ ⋃ j, coverSet h j := by rw [hVeq]; exact hUV hw
      rw [← coverSet_disjEnum_iUnion h] at hwV
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hwV
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      unfold coverSet at hi
      cases hd : disjEnum h i with
      | none => rw [hd] at hi; simp at hi
      | some x =>
        rw [hd] at hi
        simp only [Option.elim_some] at hi
        simpa [s, hd] using hi
    have hgeom : ∑' i : ℕ, (2⁻¹ : ENNReal) ^ (i + k) = 2 * 2⁻¹ ^ k := by
      have : ∀ i : ℕ, (2⁻¹ : ENNReal) ^ (i + k) = 2⁻¹ ^ i * 2⁻¹ ^ k := fun i => pow_add _ _ _
      simp_rw [this]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    calc (⨅ (s : ℕ → BitString) (_h : U ⊆ ⋃ i, cantorCylinder (s i)),
            ∑' i, (1/2:ENNReal)^(s i).length)
        ≤ ∑' i, (1/2:ENNReal)^(s i).length := iInf₂_le s hcover
      _ ≤ ∑' i, ((disjEnum h i).elim 0 (cantorMass uniformMeasure) + 2⁻¹ ^ (i + k)) := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          cases hd : disjEnum h i with
          | none =>
            simp only [s, hd, Option.getD_none, Option.elim_none, zero_add, List.length_replicate,
              one_div]
            exact le_rfl
          | some x =>
            simp only [s, hd, Option.getD_some, Option.elim_some]
            rw [cantorMass_uniformMeasure, one_div]
            exact le_self_add
      _ = (∑' i, (disjEnum h i).elim 0 (cantorMass uniformMeasure)) + ∑' i, 2⁻¹ ^ (i + k) :=
          ENNReal.tsum_add
      _ = uniformMeasure V + 2 * 2⁻¹ ^ k := by
          rw [tsum_measure_disjEnum, hVeq, hgeom]
      _ ≤ (uniformMeasure U + (ε : ENNReal) / 2) + (ε : ENNReal) / 2 := by
          refine add_le_add hV.le ?_
          calc 2 * (2⁻¹ : ENNReal) ^ k ≤ 2 * ((ε : ENNReal) / 2 / 2) := by
                have := hk.le
                gcongr
            _ = (ε : ENNReal) / 2 := by
                rw [mul_comm]
                exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
      _ = uniformMeasure U + ε := by
          rw [add_assoc, ENNReal.add_halves]

open Classical in
private lemma measure_selectPreimage_eq_zero_preimage_le_aux_cover (R : Set BitString) (x' :
    BitString) (b : Bool)
    (w : CantorSeq) :
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
private lemma measure_selectPreimage_eq_zero_preimage_le_aux_antichain (R : Set BitString) (x'
    : BitString)
    {z z' : BitString} (hz : z ∈ R ∧ selectedBits R z = x') (hz' : z' ∈ R ∧ selectedBits R z' = x')
    (hpre : z <+: z') : z = z' := by
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

/-- Step 2 of the proof of measure_selectPreimage_eq_zero: The measure of the S_R preimage
of the cylinder of x is bounded by the measure of the cylinder of x. -/
private lemma measure_selectPreimage_eq_zero_preimage_le (R : Set BitString) (x : BitString) :
    uniformMeasure {w : CantorSeq | x ∈ chainPrefixSet (selectChain R w)} ≤ (1/2:ENNReal)^x.length
        := by
    induction x using List.reverseRecOn with
  | nil => simp [prob_le_one]
  | append_singleton x' b ih =>
    set W : Set BitString := {z | z ∈ R ∧ selectedBits R z = x'} with hW
    have hsub : {w : CantorSeq | x' ++ [b] ∈ chainPrefixSet (selectChain R w)} ⊆
        ⋃ z : W, cantorCylinder (z.1 ++ [b]) := by
      intro w hw
      obtain ⟨t, ht⟩ := hw
      obtain ⟨z, hz, hwz⟩ := measure_selectPreimage_eq_zero_preimage_le_aux_cover R x' b w t
          ht
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
        exact hne (Subtype.ext (measure_selectPreimage_eq_zero_preimage_le_aux_antichain R x'
            z.2 z'.2 hpre))
      · intro hpre
        exact hne (Subtype.ext (measure_selectPreimage_eq_zero_preimage_le_aux_antichain R x'
            z'.2 z.2 hpre).symm)
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


/-- Step 3 of the proof of measure_selectPreimage_eq_zero: If U is covered by a countable
union of cylinders, its S_R preimage is covered by the countable union of the preimages of those
cylinders. -/
private lemma measure_selectPreimage_eq_zero_subset (R : Set BitString) (U : Set CantorSeq) (s
    : ℕ → BitString)
    (h : U ⊆ ⋃ i, cantorCylinder (s i)) :
    selectPreimage R U ⊆ ⋃ i, {w : CantorSeq | s i ∈ chainPrefixSet (selectChain R w)} := by
  rintro w ⟨u, hu, hw⟩
  have hu_cov := h hu
  simp only [Set.mem_iUnion] at hu_cov ⊢
  rcases hu_cov with ⟨i, hi⟩
  use i
  have hs_le_u : BitStream.finite (s i) ≤ BitStream.infinite u := hi
  have hs_le_S : BitStream.finite (s i) ≤ selectStream R w := by
    rw [hw]
    exact hs_le_u
  have h_sel_eq : selectStream R w = BitStream.ofPrefixSet (chainPrefixSet (selectChain R w))
      (isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)) := by
    rfl
  rw [h_sel_eq] at hs_le_S
  exact (BitStream.finite_le_ofPrefixSet_iff (isStreamPrefixSet_chainPrefixSet (selectChain_prefix R
      w)) (s i)).mp hs_le_S


/-- **Lemma of SUV p. 263.**  The `S_R`-preimage of a uniform null set is a uniform null set, for an
arbitrary set `R`. -/
theorem measure_selectPreimage_eq_zero (R : Set BitString) {U : Set CantorSeq}
    (hU : uniformMeasure U = 0) : uniformMeasure (selectPreimage R U) = 0 := by
  apply eq_bot_iff.mpr
  rw [measure_selectPreimage_eq_zero_inf_sum U] at hU
  have h_le : uniformMeasure (selectPreimage R U) ≤ ⨅ (s : ℕ → BitString) (_h : U ⊆ ⋃ i,
      cantorCylinder (s i)), ∑' i, (1/2:ENNReal)^(s i).length := by
    apply le_iInf₂
    intro s hs
    apply le_trans (measure_mono (measure_selectPreimage_eq_zero_subset R U s hs))
    apply le_trans (measure_iUnion_le _)
    apply ENNReal.tsum_le_tsum
    intro i
    apply measure_selectPreimage_eq_zero_preimage_le
  rwa [hU] at h_le

/-- Auxiliary for `measure_selectPreimage_le`: the infimum of the sums `∑ 2^{-|s_i|}` over the
countable cylinder covers `U ⊆ ⋃ Ω_{s_i}` is at most the (outer) uniform measure of `U`.  An open
superset of small excess measure is split into disjoint cylinders (`disjEnum`), and the unused
indices are padded with long strings. -/
private lemma measure_selectPreimage_le_aux_inf_sum_le (U : Set CantorSeq) :
    (⨅ (s : ℕ → BitString) (_h : U ⊆ ⋃ i, cantorCylinder (s i)),
      ∑' i, (1/2:ENNReal)^(s i).length) ≤ uniformMeasure U := by
  classical
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hδ : ((ε : ENNReal) / 2) ≠ 0 := by
    simp [hε.ne']
  have hδ2 : ((ε : ENNReal) / 2 / 2) ≠ 0 := by
    simp [hε.ne']
  obtain ⟨V, hUV, hVo, hV⟩ := Set.exists_isOpen_lt_add U (measure_ne_top uniformMeasure U) hδ
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_two_pow_lt hδ2
  let h : ℕ → Option BitString := fun n =>
    match Encodable.decode (α := BitString) n with
    | some x => if cantorCylinder x ⊆ V then some x else none
    | none => none
  have hVeq : (⋃ j, coverSet h j) = V := by
    apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun j => ?_
      unfold coverSet
      cases hj : h j with
      | none => simp
      | some x =>
        simp only [Option.elim_some]
        cases hd : Encodable.decode (α := BitString) j with
        | none => simp [h, hd] at hj
        | some y =>
          simp only [h, hd] at hj
          split_ifs at hj with hy
          cases hj
          exact hy
    · intro w hw
      obtain ⟨_, ⟨x, rfl⟩, hwx, hxV⟩ :=
        (isTopologicalBasis_cantorCylinders.isOpen_iff.mp hVo) w hw
      refine Set.mem_iUnion.mpr ⟨Encodable.encode x, ?_⟩
      unfold coverSet
      have : h (Encodable.encode x) = some x := by
        simp [h, hxV]
      rw [this]
      exact hwx
  let s : ℕ → BitString := fun i => (disjEnum h i).getD (List.replicate (i + k) false)
  have hcover : U ⊆ ⋃ i, cantorCylinder (s i) := by
    intro w hw
    have hwV : w ∈ ⋃ j, coverSet h j := by rw [hVeq]; exact hUV hw
    rw [← coverSet_disjEnum_iUnion h] at hwV
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hwV
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    unfold coverSet at hi
    cases hd : disjEnum h i with
    | none => rw [hd] at hi; simp at hi
    | some x =>
      rw [hd] at hi
      simp only [Option.elim_some] at hi
      simpa [s, hd] using hi
  have hgeom : ∑' i : ℕ, (2⁻¹ : ENNReal) ^ (i + k) = 2 * 2⁻¹ ^ k := by
    have : ∀ i : ℕ, (2⁻¹ : ENNReal) ^ (i + k) = 2⁻¹ ^ i * 2⁻¹ ^ k := fun i => pow_add _ _ _
    simp_rw [this]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  calc (⨅ (s : ℕ → BitString) (_h : U ⊆ ⋃ i, cantorCylinder (s i)),
          ∑' i, (1/2:ENNReal)^(s i).length)
      ≤ ∑' i, (1/2:ENNReal)^(s i).length := iInf₂_le s hcover
    _ ≤ ∑' i, ((disjEnum h i).elim 0 (cantorMass uniformMeasure) + 2⁻¹ ^ (i + k)) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        cases hd : disjEnum h i with
        | none =>
          simp only [s, hd, Option.getD_none, Option.elim_none, zero_add, List.length_replicate,
            one_div]
          exact le_rfl
        | some x =>
          simp only [s, hd, Option.getD_some, Option.elim_some]
          rw [cantorMass_uniformMeasure, one_div]
          exact le_self_add
    _ = (∑' i, (disjEnum h i).elim 0 (cantorMass uniformMeasure)) + ∑' i, 2⁻¹ ^ (i + k) :=
        ENNReal.tsum_add
    _ = uniformMeasure V + 2 * 2⁻¹ ^ k := by
        rw [tsum_measure_disjEnum, hVeq, hgeom]
    _ ≤ (uniformMeasure U + (ε : ENNReal) / 2) + (ε : ENNReal) / 2 := by
        refine add_le_add hV.le ?_
        calc 2 * (2⁻¹ : ENNReal) ^ k ≤ 2 * ((ε : ENNReal) / 2 / 2) := by
              have := hk.le
              gcongr
          _ = (ε : ENNReal) / 2 := by
              rw [mul_comm]
              exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
    _ = uniformMeasure U + ε := by
        rw [add_assoc, ENNReal.add_halves]

open Classical in
/-- Auxiliary for `measure_selectPreimage_le`: if `x' ++ [b]` is a prefix of the selected prefix of
`w` of some length, then `w` lies in the cylinder of `z ++ [b]` for a string `z ∈ R` which selects
exactly `x'` (the first time the rule selects the `|x'|`-th term). -/
private lemma measure_selectPreimage_le_aux_cover (R : Set BitString) (x' : BitString) (b : Bool)
    (w : CantorSeq) :
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
/-- Auxiliary for `measure_selectPreimage_le`: the strings `z ∈ R` with `selectedBits R z = x'`
form an antichain for the prefix order (reading a longer string in `R` selects strictly more). -/
private lemma measure_selectPreimage_le_aux_antichain (R : Set BitString) (x' : BitString)
    {z z' : BitString} (hz : z ∈ R ∧ selectedBits R z = x') (hz' : z' ∈ R ∧ selectedBits R z' = x')
    (hpre : z <+: z') : z = z' := by
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

/-- Auxiliary for `measure_selectPreimage_le`: the set of `w` such that the selected stream
`S_R(w)` begins with `x` has uniform measure at most `2^{-|x|}`. -/
private lemma measure_selectPreimage_le_aux_preimage_le (R : Set BitString) (x : BitString) :
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
      obtain ⟨z, hz, hwz⟩ := measure_selectPreimage_le_aux_cover R x' b w t ht
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
        exact hne (Subtype.ext (measure_selectPreimage_le_aux_antichain R x' z.2 z'.2 hpre))
      · intro hpre
        exact hne (Subtype.ext (measure_selectPreimage_le_aux_antichain R x' z'.2 z.2 hpre).symm)
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

/-- Auxiliary for `measure_selectPreimage_le`: if `U` is covered by the cylinders of the `s i`, its
`S_R`-preimage is covered by the sets of `w` whose selected stream begins with `s i`. -/
private lemma measure_selectPreimage_le_aux_subset (R : Set BitString) (U : Set CantorSeq)
    (s : ℕ → BitString) (h : U ⊆ ⋃ i, cantorCylinder (s i)) :
    selectPreimage R U ⊆ ⋃ i, {w : CantorSeq | s i ∈ chainPrefixSet (selectChain R w)} := by
  rintro w ⟨u, hu, hw⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h hu)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  have hfin : BitStream.finite (s i) ≤ selectStream R w := by
    rw [hw]
    exact hi
  exact (BitStream.finite_le_ofPrefixSet_iff
    (isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)) (s i)).mp hfin

/-- **SUV p. 263, after Theorem 166.**  The preimage of a measurable set never has larger measure
than the set itself. -/
theorem measure_selectPreimage_le (R : Set BitString) {U : Set CantorSeq}
    (_hU : MeasurableSet U) : uniformMeasure (selectPreimage R U) ≤ uniformMeasure U := by
  refine le_trans ?_ (measure_selectPreimage_le_aux_inf_sum_le U)
  apply le_iInf₂
  intro s hs
  apply le_trans (measure_mono (measure_selectPreimage_le_aux_subset R U s hs))
  apply le_trans (measure_iUnion_le _)
  apply ENNReal.tsum_le_tsum
  intro i
  exact measure_selectPreimage_le_aux_preimage_le R (s i)

/-- Step 1 of the proof of measure_selectPreimage_eq: a helper for ENNReal arithmetic -/
private lemma measure_selectPreimage_eq_eq_of_add_eq_add {a b x y : ENNReal} (h1 : x + y = a +
    b) (h2 : x ≤ a) (h3 : y ≤ b) (h4 : a + b ≠ ⊤) : x = a := by
  have h5 : x + y ≤ x + b := add_le_add (le_refl x) h3
  have h6 : a + b ≤ x + b := by rw [← h1]; exact h5
  have hb : b ≠ ⊤ := by intro hb_eq; rw [hb_eq] at h4; simp at h4
  have h7 : a ≤ x := (ENNReal.add_le_add_iff_right hb).mp h6
  exact le_antisymm h2 h7

/-- **SUV p. 263, after Theorem 166.**  If `S_R(ω)` is infinite for almost every `ω`, it is
uniformly distributed. -/
theorem measure_selectPreimage_eq (R : Set BitString)
    (hinf : ∀ᵐ w ∂uniformMeasure, ∃ u, selectStream R w = .infinite u)
    {U : Set CantorSeq} (hU : MeasurableSet U) :
    uniformMeasure (selectPreimage R U) = uniformMeasure U := by
  have H1 : uniformMeasure (selectPreimage R U) ≤ uniformMeasure U := measure_selectPreimage_le R hU
  have H2 : uniformMeasure (selectPreimage R Uᶜ) ≤ uniformMeasure Uᶜ := measure_selectPreimage_le R
      hU.compl
  have H_disj : Disjoint (selectPreimage R U) (selectPreimage R Uᶜ) := by
    rw [Set.disjoint_iff]
    intro w hw
    rcases hw with ⟨⟨u1, hu1, h1⟩, ⟨u2, hu2, h2⟩⟩
    rw [h1] at h2
    injection h2 with h_eq
    rw [h_eq] at hu1
    exact hu2 hu1
  have H_union : selectPreimage R U ∪ selectPreimage R Uᶜ = {w | ∃ u, selectStream R w = .infinite
      u} := by
    ext w
    simp only [selectPreimage, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨u, hu, h⟩ | ⟨u, hu, h⟩)
      · exact ⟨u, h⟩
      · exact ⟨u, h⟩
    · rintro ⟨u, h⟩
      by_cases hU' : u ∈ U
      · left; exact ⟨u, hU', h⟩
      · right; exact ⟨u, hU', h⟩
  have H_meas_union : uniformMeasure (selectPreimage R U ∪ selectPreimage R Uᶜ) = 1 := by
    rw [H_union]
    rw [measure_congr (ae_eq_univ.mpr hinf)]
    exact measure_univ (μ := uniformMeasure)
  have H_subadd : uniformMeasure (selectPreimage R U ∪ selectPreimage R Uᶜ) ≤ uniformMeasure
      (selectPreimage R U) + uniformMeasure (selectPreimage R Uᶜ) := measure_union_le _ _
  have H_sum_le : uniformMeasure (selectPreimage R U) + uniformMeasure (selectPreimage R Uᶜ) ≤
      uniformMeasure U + uniformMeasure Uᶜ := add_le_add H1 H2
  have H_sum_eq : uniformMeasure U + uniformMeasure Uᶜ = 1 := by
    have h_meas : MeasurableSet Uᶜ := hU.compl
    have h_uni : U ∪ Uᶜ = Set.univ := Set.union_compl_self U
    rw [← measure_union disjoint_compl_right h_meas, h_uni]
    exact measure_univ (μ := uniformMeasure)
  have H_sum_eq_one : uniformMeasure (selectPreimage R U) + uniformMeasure (selectPreimage R Uᶜ) =
      uniformMeasure U + uniformMeasure Uᶜ := by
    apply le_antisymm
    · exact H_sum_le
    · rw [H_sum_eq, ← H_meas_union]
      exact H_subadd
  have H_top : uniformMeasure U + uniformMeasure Uᶜ ≠ ⊤ := by
    rw [H_sum_eq]
    exact ENNReal.one_ne_top
  exact measure_selectPreimage_eq_eq_of_add_eq_add H_sum_eq_one H1 H2 H_top


private lemma measure_infinite_unbalanced_eq_zero_unbalanced : uniformMeasure {w | ¬IsBalanced w} =
    0 := by
  have hae := strong_law_ae_real (μ := uniformMeasure)
    (fun (i : ℕ) (w : CantorSeq) => bitVal (w i))
    (bernoulli_integrable_coord (1/2) (by norm_num))
    (fun i j hij => (bernoulli_iIndepFun (1/2) (by norm_num)).indepFun hij)
    (bernoulli_identDistrib (1/2) (by norm_num))
  have hintergal : ∫ w, bitVal (w 0) ∂uniformMeasure = (1 / 2 : ℝ) := by
    exact bernoulli_integral_coord (1/2) (by norm_num)
  rw [hintergal] at hae
  have hae2 : uniformMeasure {w : CantorSeq | ¬Tendsto (fun n => (freqOne w n : ℝ)) atTop (𝓝 (1 /
      2))} = 0 := by
    rw [← ae_iff]
    filter_upwards [hae] with w hw
    have heq : (fun n => (freqOne w n : ℝ)) = fun n => (∑ i ∈ Finset.range n, bitVal (w i)) / ↑n :=
        by
      ext n
      rw [freqOne_eq]
    rw [heq]
    exact hw
  have h_eq : {w | ¬IsBalanced w} = {w | ¬Tendsto (fun n => (freqOne w n : ℝ)) atTop (𝓝 (1 / 2))} :=
      by
    ext w
    simp [IsBalanced, HasLimitFreq]
  rw [h_eq]
  exact hae2

/-- **SUV Theorem 166, p. 263.**  For an arbitrary set `R`, the sequences `ω` with `S_R(ω)` infinite
and unbalanced form a null set for the uniform measure.  The set is not assumed measurable: a
null set is one of outer measure `0`. -/
theorem measure_infinite_unbalanced_eq_zero (R : Set BitString) :
    uniformMeasure {w | ∃ u, selectStream R w = .infinite u ∧ ¬ IsBalanced u} = 0 := by
  have h1 : {w | ∃ u, selectStream R w = .infinite u ∧ ¬ IsBalanced u} = selectPreimage R {w | ¬
      IsBalanced w} := by
    ext w
    simp only [selectPreimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu1, hu2⟩
      exact ⟨u, hu2, hu1⟩
    · rintro ⟨u, hu2, hu1⟩
      exact ⟨u, hu1, hu2⟩
  rw [h1]
  apply measure_selectPreimage_eq_zero
  exact measure_infinite_unbalanced_eq_zero_unbalanced

/-- **Corollary of Theorem 166 (Wald, SUV p. 262).**  For a countable family of rules almost every
sequence is finite-or-balanced under all of them, so such a sequence exists. -/
theorem ae_finiteOrFreq_of_countable (R : ℕ → Set BitString) :
    ∀ᵐ w ∂uniformMeasure, ∀ i, FiniteOrFreq (1 / 2) (selectStream (R i) w) := by
  have h := fun i => measure_infinite_unbalanced_eq_zero (R i)
  rw [ae_all_iff]
  intro i
  have h_ae : ∀ᵐ w ∂uniformMeasure, w ∉ {w | ∃ u, selectStream (R i) w = .infinite u ∧ ¬ IsBalanced
      u} := by
    change uniformMeasure {w | ¬ w ∉ {w | ∃ u, selectStream (R i) w = .infinite u ∧ ¬ IsBalanced u}}
        = 0
    convert h i using 2
    ext w
    simp
  filter_upwards [h_ae] with w hw
  simp only [not_exists, not_and] at hw
  unfold FiniteOrFreq
  rcases h_sel_eq : selectStream (R i) w with _ | u
  · trivial
  · by_cases h_bal : IsBalanced u
    · exact h_bal
    · have := hw u h_sel_eq
      contradiction

/-- The rule selecting exactly the terms of `w` equal to `b`. -/
private def exists_rule_not_finiteOrFreq_rule (w : CantorSeq) (b : Bool) : Set BitString :=
  {x | cantorPrefix w x.length = x ∧ w x.length = b}

/-- Step 1 of the proof of `exists_rule_not_finiteOrFreq`: the rule selects from the
first `j` terms of `w` exactly the occurrences of `b`. -/
private lemma exists_rule_not_finiteOrFreq_sel (w : CantorSeq) (b : Bool) (j : ℕ) :
    selectedBits (exists_rule_not_finiteOrFreq_rule w b) (cantorPrefix w j) =
      List.replicate ((cantorPrefix w j).count b) b := by
  induction j with
  | zero => simp [cantorPrefix, selectedBits, selectedAux]
  | succ j ih =>
    rw [cantorPrefix_succ, selectedBits_append_singleton, ih]
    have hmem : (cantorPrefix w j ∈ exists_rule_not_finiteOrFreq_rule w b) ↔ w j = b := by
      simp [exists_rule_not_finiteOrFreq_rule]
    by_cases h : w j = b
    · rw [ite_eq_left (hmem.2 h), List.count_append, h]
      simp [List.replicate_succ']
    · rw [ite_eq_right (fun hh => h (hmem.1 hh))]
      have : [w j].count b = 0 := by simpa [List.count_cons] using h
      simp [List.count_append, this]

/-- Step 2 of the proof of `exists_rule_not_finiteOrFreq`: if a rule selects from the
first `j` terms of `w` exactly `z j` copies of `b`, with `z` unbounded, then the selected sequence
is infinite, constant `b`, and has no limit frequency `1/2`. -/
private lemma exists_rule_not_finiteOrFreq_not_freq (R : Set BitString)
    (w : CantorSeq) (b : Bool) (z : ℕ → ℕ)
    (hsel : ∀ j, selectedBits R (cantorPrefix w j) = List.replicate (z j) b)
    (hunb : ∀ i, ∃ j, i ≤ z j) : ¬ FiniteOrFreq (1 / 2) (selectStream R w) := by
  intro hfin
  have hmem : ∀ j, List.replicate (z j) b ∈ chainPrefixSet (selectChain R w) := fun j =>
    ⟨j, by rw [selectChain, hsel j]⟩
  have key : ∀ x, BitStream.finite x ≤ selectStream R w ↔ x ∈ chainPrefixSet (selectChain R w) :=
    fun x => BitStream.finite_le_ofPrefixSet_iff
      (isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)) x
  rcases hs : selectStream R w with u | u
  · obtain ⟨j, hj⟩ := hunb (u.length + 1)
    have h1 : BitStream.finite (List.replicate (z j) b) ≤ selectStream R w :=
      (key _).2 (hmem j)
    rw [hs] at h1
    have h2 : List.replicate (z j) b <+: u := h1
    have h3 := h2.length_le
    rw [List.length_replicate] at h3
    omega
  · have hu : ∀ k, u k = b := by
      intro k
      obtain ⟨j, hj⟩ := hunb (k + 1)
      have h1 : BitStream.finite (List.replicate (z j) b) ≤ selectStream R w :=
        (key _).2 (hmem j)
      rw [hs] at h1
      have h2 : IsCantorPrefix (List.replicate (z j) b) u := h1
      have h3 := h2 k (by rw [List.length_replicate]; omega)
      simpa using h3
    rw [hs] at hfin
    have hlim : HasLimitFreq (1 / 2) u := hfin
    have hconst : ∀ n, (freqOne u n : ℝ) = (∑ i ∈ Finset.range n, bitVal b) / n := by
      intro n
      rw [freqOne_eq]
      simp [hu]
    cases b
    · have hlim0 : Tendsto (fun n => (freqOne u n : ℝ)) atTop (𝓝 0) := by
        have hfun : (fun n => (freqOne u n : ℝ)) = fun _ => 0 := by
          funext n
          rw [hconst]
          simp [bitVal]
        rw [hfun]
        exact tendsto_const_nhds
      have h12 := tendsto_nhds_unique hlim hlim0
      norm_num at h12
    · have hlim1 : Tendsto (fun n => (freqOne u n : ℝ)) atTop (𝓝 1) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ne_atTop 0] with n hn
        rw [hconst]
        simp [bitVal, hn]
      have h12 := tendsto_nhds_unique hlim hlim1
      norm_num at h12

/-- Step 3 of the proof of `exists_rule_not_finiteOrFreq`: some bit occurs infinitely
often in `w`. -/
private lemma exists_rule_not_finiteOrFreq_infinitely_often (w : CantorSeq) :
    ∃ b : Bool, ∀ N, ∃ n, N ≤ n ∧ w n = b := by
  by_cases h : ∀ N, ∃ n, N ≤ n ∧ w n = false
  · exact ⟨false, h⟩
  · push Not at h
    obtain ⟨N, hN⟩ := h
    refine ⟨true, fun M => ⟨max N M, le_max_right _ _, ?_⟩⟩
    have := hN (max N M) (le_max_left _ _)
    simpa using this

/-- Step 4 of the proof of `exists_rule_not_finiteOrFreq`: if `b` occurs infinitely often
in `w`, its number of occurrences in the prefixes is unbounded. -/
private lemma exists_rule_not_finiteOrFreq_unbounded (w : CantorSeq) (b : Bool)
    (hb : ∀ N, ∃ n, N ≤ n ∧ w n = b) (i : ℕ) : ∃ j, i ≤ (cantorPrefix w j).count b := by
  induction i with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ i ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨n, hn, hwn⟩ := hb j
    refine ⟨n + 1, ?_⟩
    have hsub : (cantorPrefix w j).count b ≤ (cantorPrefix w n).count b :=
      (cantorPrefix_mono w hn).sublist.count_le b
    rw [cantorPrefix_succ, List.count_append, hwn]
    simp
    omega

/-- **SUV p. 262.**  No sequence is finite-or-balanced under *all* rules: after the game one can
choose `R` to select only zeros or only ones, infinitely often. -/
theorem exists_rule_not_finiteOrFreq (w : CantorSeq) :
    ∃ R : Set BitString, ¬ FiniteOrFreq (1 / 2) (selectStream R w) := by
  obtain ⟨b, hb⟩ := exists_rule_not_finiteOrFreq_infinitely_often w
  exact ⟨exists_rule_not_finiteOrFreq_rule w b,
    exists_rule_not_finiteOrFreq_not_freq _ w b (fun j => (cantorPrefix w j).count b)
      (exists_rule_not_finiteOrFreq_sel w b)
      (exists_rule_not_finiteOrFreq_unbounded w b hb)⟩

/-- Step 1A of the proof of `bernoulli_selectPreimage_eq`: bound by cantor mass. -/
private lemma bernoulli_selectPreimage_eq_step1a (p : NNReal) (hp : p ≤ 1) (R : Set BitString)
    (x : BitString) :
    bernoulliMeasure p hp {w | x ∈ chainPrefixSet (selectChain R w)} ≤
    cantorMass (bernoulliMeasure p hp) x := by
  have hmass : ∀ (z : BitString) (b : Bool), cantorMass (bernoulliMeasure p hp) (z ++ [b]) =
      (if b then (p : ENNReal) else 1 - p) * cantorMass (bernoulliMeasure p hp) z := by
    intro z b
    rw [cantorMass_bernoulliMeasure_prod, cantorMass_bernoulliMeasure_prod]
    simp [List.map_append, List.prod_append, mul_comm]
  induction x using List.reverseRecOn with
  | nil =>
    calc _ ≤ bernoulliMeasure p hp Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ = cantorMass (bernoulliMeasure p hp) [] := by
          unfold cantorMass
          have : cantorCylinder ([] : BitString) = Set.univ := by
            ext w
            simp [cantorCylinder, IsCantorPrefix]
          rw [this, measure_univ]
  | append_singleton x' b ih =>
    set W : Set BitString := {z | z ∈ R ∧ selectedBits R z = x'} with hW
    have hsub : {w : CantorSeq | x' ++ [b] ∈ chainPrefixSet (selectChain R w)} ⊆
        ⋃ z : W, cantorCylinder (z.1 ++ [b]) := by
      intro w hw
      obtain ⟨t, ht⟩ := hw
      obtain ⟨z, hz, hwz⟩ := measure_selectPreimage_le_aux_cover R x' b w t ht
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
        exact hne (Subtype.ext (measure_selectPreimage_le_aux_antichain R x' z.2 z'.2 hpre))
      · intro hpre
        exact hne (Subtype.ext (measure_selectPreimage_le_aux_antichain R x' z'.2 z.2 hpre).symm)
    calc bernoulliMeasure p hp {w : CantorSeq | x' ++ [b] ∈ chainPrefixSet (selectChain R w)}
        ≤ bernoulliMeasure p hp (⋃ z : W, cantorCylinder (z.1 ++ [b])) := measure_mono hsub
      _ ≤ ∑' z : W, bernoulliMeasure p hp (cantorCylinder (z.1 ++ [b])) := measure_iUnion_le _
      _ = ∑' z : W, (if b then (p : ENNReal) else 1 - p) *
            bernoulliMeasure p hp (cantorCylinder z.1) := tsum_congr fun z => hmass z.1 b
      _ = (if b then (p : ENNReal) else 1 - p) *
            ∑' z : W, bernoulliMeasure p hp (cantorCylinder z.1) := ENNReal.tsum_mul_left
      _ = (if b then (p : ENNReal) else 1 - p) *
            bernoulliMeasure p hp (⋃ z : W, cantorCylinder z.1) := by
          rw [measure_iUnion hdisj (fun z => measurableSet_cantorCylinder _)]
      _ ≤ (if b then (p : ENNReal) else 1 - p) *
            bernoulliMeasure p hp {w : CantorSeq | x' ∈ chainPrefixSet (selectChain R w)} := by
          gcongr
      _ ≤ (if b then (p : ENNReal) else 1 - p) * cantorMass (bernoulliMeasure p hp) x' := by
          gcongr
      _ = cantorMass (bernoulliMeasure p hp) (x' ++ [b]) := (hmass x' b).symm

/-- Step 1B of the proof of `bernoulli_selectPreimage_eq`: bound for open sets. -/
private lemma bernoulli_selectPreimage_eq_step1b (p : NNReal) (hp : p ≤ 1) (R : Set BitString)
    (V : Set CantorSeq) (hV : IsOpen V) :
    bernoulliMeasure p hp (selectPreimage R V) ≤ bernoulliMeasure p hp V := by
  classical
  let h : ℕ → Option BitString := fun n =>
    match Encodable.decode (α := BitString) n with
    | some x => if cantorCylinder x ⊆ V then some x else none
    | none => none
  have hVeq : (⋃ j, coverSet h j) = V := by
    apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun j => ?_
      unfold coverSet
      cases hj : h j with
      | none => simp
      | some x =>
        simp only [Option.elim_some]
        cases hd : Encodable.decode (α := BitString) j with
        | none => simp [h, hd] at hj
        | some y =>
          simp only [h, hd] at hj
          split_ifs at hj with hy
          cases hj
          exact hy
    · intro w hw
      obtain ⟨_, ⟨x, rfl⟩, hwx, hxV⟩ :=
        (isTopologicalBasis_cantorCylinders.isOpen_iff.mp hV) w hw
      refine Set.mem_iUnion.mpr ⟨Encodable.encode x, ?_⟩
      unfold coverSet
      have : h (Encodable.encode x) = some x := by
        simp [h, hxV]
      rw [this]
      exact hwx
  let A : ℕ → Set CantorSeq := fun i =>
    (disjEnum h i).elim ∅ (fun s => {w | s ∈ chainPrefixSet (selectChain R w)})
  have hsub : selectPreimage R V ⊆ ⋃ i, A i := by
    rintro w ⟨u, hu, hw⟩
    have hwV : u ∈ ⋃ j, coverSet h j := by rw [hVeq]; exact hu
    rw [← coverSet_disjEnum_iUnion h] at hwV
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hwV
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    unfold coverSet at hi
    cases hd : disjEnum h i with
    | none => rw [hd] at hi; simp at hi
    | some x =>
      rw [hd] at hi
      simp only [Option.elim_some] at hi
      simp only [A, hd, Option.elim_some]
      have hfin : BitStream.finite x ≤ selectStream R w := by
        rw [hw]
        exact hi
      exact (BitStream.finite_le_ofPrefixSet_iff
        (isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)) x).mp hfin
  calc bernoulliMeasure p hp (selectPreimage R V)
      ≤ bernoulliMeasure p hp (⋃ i, A i) := measure_mono hsub
    _ ≤ ∑' i, bernoulliMeasure p hp (A i) := measure_iUnion_le _
    _ ≤ ∑' i, (disjEnum h i).elim 0 (cantorMass (bernoulliMeasure p hp)) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        cases hd : disjEnum h i with
        | none => simp [A, hd]
        | some x =>
          simp only [A, hd, Option.elim_some]
          exact bernoulli_selectPreimage_eq_step1a p hp R x
    _ = bernoulliMeasure p hp V := by
        rw [tsum_measure_disjEnum, hVeq]

/-- Step 1 of the proof of `bernoulli_selectPreimage_eq`: the preimage never has larger
measure. -/
private lemma bernoulli_selectPreimage_eq_le (p : NNReal) (hp : p ≤ 1) (R : Set BitString)
    (U : Set CantorSeq) :
    bernoulliMeasure p hp (selectPreimage R U) ≤ bernoulliMeasure p hp U := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hδ : ((ε : ENNReal)) ≠ 0 := by
    simp [hε.ne']
  obtain ⟨V, hUV, hVo, hV⟩ :=
    Set.exists_isOpen_lt_add U (measure_ne_top (bernoulliMeasure p hp) U) hδ
  have hsub : selectPreimage R U ⊆ selectPreimage R V := by
    rintro w ⟨u, hu, h⟩
    exact ⟨u, hUV hu, h⟩
  calc bernoulliMeasure p hp (selectPreimage R U)
      ≤ bernoulliMeasure p hp (selectPreimage R V) := measure_mono hsub
    _ ≤ bernoulliMeasure p hp V := bernoulli_selectPreimage_eq_step1b p hp R V hVo
    _ ≤ _ := hV.le

/-- Step 2 of the proof of `bernoulli_selectPreimage_eq`: a helper for ENNReal arithmetic
-/
private lemma bernoulli_selectPreimage_eq_eq_of_add_eq_add {a b x y : ENNReal} (h1 : x + y = a
    + b) (h2 : x ≤ a) (h3 : y ≤ b) (h4 : a + b ≠ ⊤) : x = a := by
  have h5 : x + y ≤ x + b := add_le_add (le_refl x) h3
  have h6 : a + b ≤ x + b := by rw [← h1]; exact h5
  have hb : b ≠ ⊤ := by intro hb_eq; rw [hb_eq] at h4; simp at h4
  have h7 : a ≤ x := (ENNReal.add_le_add_iff_right hb).mp h6
  exact le_antisymm h2 h7

/-- **SUV Problem 253, p. 264.**  If `ω` has the Bernoulli distribution with parameter `p` and
`S_R(ω)` is almost surely infinite, then `S_R(ω)` has the same distribution. -/
theorem bernoulli_selectPreimage_eq (p : NNReal) (hp : p ≤ 1) (R : Set BitString)
    (hinf : ∀ᵐ w ∂(bernoulliMeasure p hp), ∃ u, selectStream R w = .infinite u)
    {U : Set CantorSeq} (hU : MeasurableSet U) :
    bernoulliMeasure p hp (selectPreimage R U) = bernoulliMeasure p hp U := by
  have H1 : bernoulliMeasure p hp (selectPreimage R U) ≤ bernoulliMeasure p hp U :=
      bernoulli_selectPreimage_eq_le p hp R U
  have H2 : bernoulliMeasure p hp (selectPreimage R Uᶜ) ≤ bernoulliMeasure p hp Uᶜ :=
      bernoulli_selectPreimage_eq_le p hp R Uᶜ
  have H_disj : Disjoint (selectPreimage R U) (selectPreimage R Uᶜ) := by
    rw [Set.disjoint_iff]
    intro w hw
    rcases hw with ⟨⟨u1, hu1, h1⟩, ⟨u2, hu2, h2⟩⟩
    rw [h1] at h2
    injection h2 with h_eq
    rw [h_eq] at hu1
    exact hu2 hu1
  have H_union : selectPreimage R U ∪ selectPreimage R Uᶜ = {w | ∃ u, selectStream R w = .infinite
      u} := by
    ext w
    simp only [selectPreimage, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨u, hu, h⟩ | ⟨u, hu, h⟩)
      · exact ⟨u, h⟩
      · exact ⟨u, h⟩
    · rintro ⟨u, h⟩
      by_cases hU' : u ∈ U
      · left; exact ⟨u, hU', h⟩
      · right; exact ⟨u, hU', h⟩
  have H_meas_union : bernoulliMeasure p hp (selectPreimage R U ∪ selectPreimage R Uᶜ) = 1 := by
    rw [H_union]
    rw [measure_congr (ae_eq_univ.mpr hinf)]
    exact measure_univ (μ := bernoulliMeasure p hp)
  have H_subadd : bernoulliMeasure p hp (selectPreimage R U ∪ selectPreimage R Uᶜ) ≤
      bernoulliMeasure p hp (selectPreimage R U) + bernoulliMeasure p hp (selectPreimage R Uᶜ) :=
      measure_union_le _ _
  have H_sum_le : bernoulliMeasure p hp (selectPreimage R U) + bernoulliMeasure p hp (selectPreimage
      R Uᶜ) ≤ bernoulliMeasure p hp U + bernoulliMeasure p hp Uᶜ := add_le_add H1 H2
  have H_sum_eq : bernoulliMeasure p hp U + bernoulliMeasure p hp Uᶜ = 1 := by
    have h_meas : MeasurableSet Uᶜ := hU.compl
    have h_uni : U ∪ Uᶜ = Set.univ := Set.union_compl_self U
    rw [← measure_union disjoint_compl_right h_meas, h_uni]
    exact measure_univ (μ := bernoulliMeasure p hp)
  have H_sum_eq_one : bernoulliMeasure p hp (selectPreimage R U) + bernoulliMeasure p hp
      (selectPreimage R Uᶜ) = bernoulliMeasure p hp U + bernoulliMeasure p hp Uᶜ := by
    apply le_antisymm
    · exact H_sum_le
    · rw [H_sum_eq, ← H_meas_union]
      exact H_subadd
  have H_top : bernoulliMeasure p hp U + bernoulliMeasure p hp Uᶜ ≠ ⊤ := by
    rw [H_sum_eq]
    exact ENNReal.one_ne_top
  exact bernoulli_selectPreimage_eq_eq_of_add_eq_add H_sum_eq_one H1 H2 H_top

end Kolmogorov.FrequencyGames
