import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint.GapCover

/-!
# Totality of the interval maps between a measure and the uniform measure

The map sending a sequence to the real it denotes fails to be injective only at dyadic
endpoints, and those are not random. `measure_setOf_measureReal_eq_eq_zero` says the sequences
denoting a computable real form a null set, whence
`measureReal_ne_treeEnd_of_isMartinLofRandom` and
`measureReal_ne_div_two_pow_of_isMartinLofRandom`: for a random sequence the denoted real is
neither an endpoint of an interval `π_x` nor a dyadic rational. Consequently the reverse interval
map is total at every random sequence (`exists_infinite_invArithMap_of_isMartinLofRandom`),
which is obligation (a) of Theorem 121; the uniform side, obligation (b), is treated next
(`cantorMass_uniformMeasure_eq_lengthMeasure`, `uniformMeasure_singleton`), followed by the
identification of the reverse map with the binary expansion and the two inversion identities.

Source: SUV §5.9.1, pp. 176–177, Theorem 121.
-/

namespace Kolmogorov
open MeasureTheory
open scoped ENNReal

/-- The `μ`-mass of the sequences denoting a computable real is zero. -/
theorem measure_setOf_measureReal_eq_eq_zero (ν : Measure CantorSeq) [IsProbabilityMeasure ν]
    (hν : IsComputableMeasure ν) (haν : ∀ u : CantorSeq, ν {u} = 0)
    (E : ℝ) (M : ℕ) (app : ℕ → ℕ) (happ : Computable app)
    (herr : ∀ s, |(app s : ℝ) - 2 ^ s * E| ≤ (M : ℝ)) :
    ν {w : CantorSeq | measureReal ν w = E} = 0 :=
  IsEffectivelyNull.measure_eq_zero
    (isEffectivelyNull_setOf_measureReal_eq ν hν haν E M app happ herr)

/-- **Both endpoints of every interval `π_x` are avoided.**  For computable
measures `ν` (atomless) and `μ`, a `ν`-random sequence denotes neither the left
nor the right endpoint of any interval of `μ`.  This is SUV p. 177's "the
endpoints of the segments ... are not random", in the generality both sides of
Theorem 121 need: on the `μ`-side one takes `ν = μ`, on the uniform side
`ν = uniformMeasure`. -/
theorem measureReal_ne_treeEnd_of_isMartinLofRandom (ν μ : Measure CantorSeq)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (hν : IsComputableMeasure ν)
    (haν : ∀ u : CantorSeq, ν {u} = 0) (hμ : IsComputableMeasure μ) (x : BitString)
    {w : CantorSeq} (hw : IsMartinLofRandom ν w) :
    measureReal ν w ≠ treeLeftEnd (cantorMass μ) x ∧
      measureReal ν w
        ≠ treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal := by
  obtain ⟨a, ha_comp, ha⟩ := hμ
  constructor
  · refine measureReal_ne_of_computable_approx ν hν haν _ x.length
      (fun s => treeLeftEndApprox a x s) ((computable_treeLeftEndApprox ha_comp).comp
        (Computable.const x) Computable.id) (fun s => ?_) hw
    exact abs_treeLeftEndApprox_sub_le μ ha x s
  · refine measureReal_ne_of_computable_approx ν hν haν _ (x.length + 1)
      (fun s => treeLeftEndApprox a x s + a x s)
      (Primrec.nat_add.to_comp.comp
        ((computable_treeLeftEndApprox ha_comp).comp (Computable.const x) Computable.id)
        (ha_comp.comp (Computable.const x) Computable.id)) (fun s => ?_) hw
    have h1 := abs_treeLeftEndApprox_sub_le μ ha x s
    have h2 := abs_approx_sub_le_one μ ha x s
    have hrw : ((treeLeftEndApprox a x s + a x s : ℕ) : ℝ)
        - 2 ^ s * (treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal)
        = ((treeLeftEndApprox a x s : ℝ) - 2 ^ s * treeLeftEnd (cantorMass μ) x)
          + ((a x s : ℝ) - 2 ^ s * (cantorMass μ x).toReal) := by
      push_cast
      ring
    rw [hrw]
    refine le_trans (abs_add_le _ _) ?_
    push_cast
    linarith


/-- **SUV p. 177, "the endpoints of the segments are not random".**  For a
computable atomless measure the real number denoted by a `μ`-random sequence is
not a dyadic rational: the dyadic rational `k/2^m` is approximated exactly by
the numerators `⌊k·2^s/2^m⌋`, to within one unit. -/
theorem measureReal_ne_div_two_pow_of_isMartinLofRandom (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) (haμ : ∀ v : CantorSeq, μ {v} = 0)
    {w : CantorSeq} (hw : IsMartinLofRandom μ w) (m k : ℕ) :
    measureReal μ w ≠ (k : ℝ) / 2 ^ m := by
  refine measureReal_ne_of_computable_approx μ hμ haμ _ 1 (fun s => k * 2 ^ s / 2 ^ m)
    (Primrec.nat_div.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const k)
        (primrec_two_pow_aux.to_comp.comp Computable.id))
      (Computable.const (2 ^ m))) (fun s => ?_) hw
  have hd : (0 : ℕ) < 2 ^ m := by positivity
  have hdm := Nat.div_add_mod' (k * 2 ^ s) (2 ^ m)
  have hmod : k * 2 ^ s % 2 ^ m < 2 ^ m := Nat.mod_lt _ hd
  have h1 : (k * 2 ^ s / 2 ^ m) * 2 ^ m ≤ k * 2 ^ s := by omega
  have h2 : k * 2 ^ s < (k * 2 ^ s / 2 ^ m) * 2 ^ m + 2 ^ m := by omega
  have hdR : (0 : ℝ) < 2 ^ m := by positivity
  have h1R : ((k * 2 ^ s / 2 ^ m : ℕ) : ℝ) * 2 ^ m ≤ (k : ℝ) * 2 ^ s := by exact_mod_cast h1
  have h2R : (k : ℝ) * 2 ^ s < ((k * 2 ^ s / 2 ^ m : ℕ) : ℝ) * 2 ^ m + 2 ^ m := by
    exact_mod_cast h2
  have hval : (2 : ℝ) ^ s * ((k : ℝ) / 2 ^ m) = (k : ℝ) * 2 ^ s / 2 ^ m := by
    field_simp
    try ring
  have hA1 : ((k * 2 ^ s / 2 ^ m : ℕ) : ℝ) ≤ (k : ℝ) * 2 ^ s / 2 ^ m := by
    rw [le_div_iff₀ hdR]
    exact h1R
  have hA2 : (k : ℝ) * 2 ^ s / 2 ^ m < ((k * 2 ^ s / 2 ^ m : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hdR, add_mul, one_mul]
    exact h2R
  rw [hval, abs_le]
  constructor <;> push_cast <;> linarith

/-- **SUV Theorem 121, obligation (a).**  The reverse interval map is total on
the `μ`-random sequences of a computable atomless measure. -/
theorem exists_infinite_invArithMap_of_isMartinLofRandom (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) (haμ : ∀ v : CantorSeq, μ {v} = 0)
    {w : CantorSeq} (hw : IsMartinLofRandom μ w) :
    ∃ v : CantorSeq, invArithMap μ (BitStream.infinite w) = BitStream.infinite v := by
  refine exists_infinite_invArithMap μ (haμ w) (fun m => ?_)
  have hne := measureReal_ne_div_two_pow_of_isMartinLofRandom μ hμ haμ hw m
  have h0 := measureReal_nonneg μ w
  have h1 := measureReal_le_one μ w
  have hppos : (0 : ℝ) < 2 ^ m := by positivity
  have htnn : (0 : ℝ) ≤ 2 ^ m * measureReal μ w := by positivity
  have hfl : ((⌊(2 : ℝ) ^ m * measureReal μ w⌋₊ : ℕ) : ℝ) ≤ 2 ^ m * measureReal μ w :=
    Nat.floor_le htnn
  have hfl2 : (2 : ℝ) ^ m * measureReal μ w
      < ((⌊(2 : ℝ) ^ m * measureReal μ w⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hkne : ((⌊(2 : ℝ) ^ m * measureReal μ w⌋₊ : ℕ) : ℝ) ≠ 2 ^ m * measureReal μ w := by
    intro hcon
    refine hne ⌊(2 : ℝ) ^ m * measureReal μ w⌋₊ ?_
    rw [eq_div_iff (ne_of_gt hppos)]
    linarith
  have hklt : ((⌊(2 : ℝ) ^ m * measureReal μ w⌋₊ : ℕ) : ℝ) < 2 ^ m * measureReal μ w :=
    lt_of_le_of_ne hfl hkne
  refine ⟨⌊(2 : ℝ) ^ m * measureReal μ w⌋₊, ?_, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    have h2 : ((2 : ℝ) ^ m) ≤ ((⌊(2 : ℝ) ^ m * measureReal μ w⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast hcon
    nlinarith [mul_le_mul_of_nonneg_left h1 hppos.le]
  · exact (div_lt_iff₀ hppos).mpr (by linarith)
  · exact (lt_div_iff₀ hppos).mpr (by linarith)

/-! ## The uniform side (SUV Theorem 121, obligation (b))

On the uniform side the input real is `treeReal lengthMeasure v = 0.v` and the
cells it must avoid are the *left endpoints* of the intervals `π_x` of `μ`.
The asymmetry the source points out ("the `μ₁`-measure of some `Ω_x` can be
zero", p. 177) is exactly why the condition is stated as an endpoint condition
for `μ` rather than a dyadic one: a degenerate cell of `μ` contributes an
endpoint but no interior.  Two facts do the work: a random `v` denotes no
dyadic rational (that is `measureReal_ne_div_two_pow_of_isMartinLofRandom`
applied to the *uniform* measure, whose cell masses are `lengthMeasure`), and a
random `v` denotes none of the countably many computable reals
`treeLeftEnd (cantorMass μ) x`. -/

/-- The cylinder masses of the uniform measure are the uniform tree measure. -/
lemma cantorMass_uniformMeasure_eq_lengthMeasure :
    cantorMass uniformMeasure = lengthMeasure := by
  funext x
  rw [cantorMass_uniformMeasure, lengthMeasure]

/-- The uniform measure of a single sequence is zero. -/
lemma uniformMeasure_singleton (w : CantorSeq) : uniformMeasure {w} = 0 := by
  have hle : ∀ n : ℕ, uniformMeasure {w} ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    have h1 : uniformMeasure {w} ≤ cantorMass uniformMeasure (cantorPrefix w n) :=
      measure_mono (Set.singleton_subset_iff.2 (mem_cantorCylinder_cantorPrefix w n))
    rwa [cantorMass_uniformMeasure, cantorPrefix_length] at h1
  refine le_antisymm ?_ (zero_le _)
  exact ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
    (Filter.Eventually.of_forall hle)

/-- **The left endpoints of the intervals `π_x` are not denoted by a random
sequence.**  For each `x` the set of sequences whose real is `treeLeftEnd
(cantorMass μ) x` is covered, at level `c`, by the strings whose dyadic interval
falls inside a window of width `2(|x|+1)·2^{-s}` around the computable
approximation of that endpoint. -/
theorem treeReal_ne_treeLeftEnd_of_isMartinLofRandom (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) (x : BitString) {v : CantorSeq}
    (hv : IsMartinLofRandom uniformMeasure v) :
    treeReal lengthMeasure v ≠ treeLeftEnd (cantorMass μ) x := by
  have hmeq : measureReal uniformMeasure v = treeReal lengthMeasure v := by
    simp only [measureReal_eq_treeReal, cantorMass_uniformMeasure_eq_lengthMeasure]
  rw [← hmeq]
  exact (measureReal_ne_treeEnd_of_isMartinLofRandom uniformMeasure μ
    isComputableMeasure_uniform uniformMeasure_singleton hμ x hv).1

/-- The level-`m` cells of a probability measure tile `[0,1)`: the children of a
cell partition it exactly, because `cantorMass` is additive. -/
lemma exists_length_eq_mem_treeIco (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : r ∈ Set.Ico (0 : ℝ) 1) (m : ℕ) :
    ∃ x : BitString, x.length = m ∧ r ∈ treeIco (cantorMass μ) x := by
  induction m with
  | zero =>
      refine ⟨[], rfl, ?_⟩
      rw [treeIco_nil (isContinuousTreeSemimeasure_cantorMass μ)]
      exact hr
  | succ m ih =>
      obtain ⟨x, hxlen, hx⟩ := ih
      rw [treeIco, Set.mem_Ico] at hx
      have hf0 : cantorMass μ (x ++ [false]) ≠ ⊤ := measure_ne_top μ _
      have hf1 : cantorMass μ (x ++ [true]) ≠ ⊤ := measure_ne_top μ _
      have hadd : (cantorMass μ x).toReal
          = (cantorMass μ (x ++ [false])).toReal + (cantorMass μ (x ++ [true])).toReal := by
        rw [cantorMass_add μ x, ENNReal.toReal_add hf0 hf1]
      by_cases hlt : r < treeLeftEnd (cantorMass μ) x + (cantorMass μ (x ++ [false])).toReal
      · refine ⟨x ++ [false], by simp [hxlen], ?_⟩
        rw [treeIco, treeLeftEnd_append_false, Set.mem_Ico]
        exact ⟨hx.1, hlt⟩
      · refine ⟨x ++ [true], by simp [hxlen], ?_⟩
        push_neg at hlt
        rw [treeIco, treeLeftEnd_append_true, Set.mem_Ico]
        constructor
        · exact hlt
        · have h2 := hx.2
          rw [hadd] at h2
          linarith

/-- The real coded by a Martin-Löf random sequence lies in `[0, 1)`. -/
lemma treeReal_lengthMeasure_mem_Ico {v : CantorSeq}
    (hv : IsMartinLofRandom uniformMeasure v) :
    treeReal lengthMeasure v ∈ Set.Ico (0 : ℝ) 1 := by
  have hmeq : measureReal uniformMeasure v = treeReal lengthMeasure v := by
    simp only [measureReal_eq_treeReal, cantorMass_uniformMeasure_eq_lengthMeasure]
  have h0 : 0 ≤ treeReal lengthMeasure v := by
    rw [← hmeq]
    exact measureReal_nonneg uniformMeasure v
  have h1 : treeReal lengthMeasure v ≤ 1 := by
    rw [← hmeq]
    exact measureReal_le_one uniformMeasure v
  refine ⟨h0, lt_of_le_of_ne h1 ?_⟩
  have hne := measureReal_ne_div_two_pow_of_isMartinLofRandom uniformMeasure
    isComputableMeasure_uniform uniformMeasure_singleton hv 0 1
  rw [hmeq] at hne
  simpa using hne

/-- **SUV Theorem 121, obligation (b).**  The forward interval map is total on
the uniformly random sequences. -/
theorem exists_infinite_arithMap_of_isMartinLofRandom (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {v : CantorSeq}
    (hv : IsMartinLofRandom uniformMeasure v) :
    ∃ u : CantorSeq, arithMap μ (BitStream.infinite v) = BitStream.infinite u := by
  refine exists_infinite_arithMap μ v (fun m => ?_)
  obtain ⟨x, hxlen, hx⟩ := exists_length_eq_mem_treeIco μ (treeReal_lengthMeasure_mem_Ico hv) m
  rw [treeIco, Set.mem_Ico] at hx
  refine ⟨x, hxlen, ?_, hx.2⟩
  rcases lt_or_eq_of_le hx.1 with h | h
  · exact h
  · exact absurd h.symm (treeReal_ne_treeLeftEnd_of_isMartinLofRandom μ hμ x hv)

/-! ## The reverse map prints the binary expansion of `measureReal μ w`

This is the bridge obligation (c)'s mutual-inversion half runs on, and it needs
neither randomness nor atomlessness: whenever `invArithMap μ` produces an
infinite output at all, that output is the binary expansion of the real number
the input denotes. -/

/-- The left endpoint of the interval of a prefix is at most the real coded by the sequence. -/
lemma treeLeftEnd_le_measureReal (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (w : CantorSeq) (n : ℕ) :
    treeLeftEnd (cantorMass μ) (cantorPrefix w n) ≤ measureReal μ w := by
  refine le_ciSup (f := fun i => treeLeftEnd (cantorMass μ) (cantorPrefix w i)) ⟨1, ?_⟩ n
  rintro _ ⟨i, rfl⟩
  exact treeLeftEnd_cantorMass_le_one μ _

/-- The real coded by a sequence is at most the right endpoint of the interval of a prefix. -/
lemma measureReal_le_treeRightEnd (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (w : CantorSeq) (n : ℕ) :
    measureReal μ w ≤ treeLeftEnd (cantorMass μ) (cantorPrefix w n)
      + (cantorMass μ (cantorPrefix w n)).toReal := by
  refine ciSup_le fun i => ?_
  rcases le_total i n with h | h
  · refine le_trans (treeLeftEnd_le_of_prefix (isContinuousTreeSemimeasure_cantorMass μ)
      (cantorPrefix_mono w h)) ?_
    exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  · have h1 : treeLeftEnd (cantorMass μ) (cantorPrefix w i)
        ≤ treeLeftEnd (cantorMass μ) (cantorPrefix w i)
          + (cantorMass μ (cantorPrefix w i)).toReal :=
      le_add_of_nonneg_right ENNReal.toReal_nonneg
    exact le_trans h1 (treeRightEnd_le_of_prefix (isContinuousTreeSemimeasure_cantorMass μ)
      (cantorPrefix_mono w h))

/-- Every finite prefix of a sequence is below the sequence in the stream order. -/
lemma finite_cantorPrefix_le_infinite (v : CantorSeq) (j : ℕ) :
    BitStream.finite (cantorPrefix v j) ≤ BitStream.infinite v :=
  (isCantorPrefix_iff_cantorPrefix_eq _ v).2 (by rw [cantorPrefix_length])

/-- **The output of `invArithMap μ` denotes the same real as its input.**  No
randomness and no atomlessness is used: only that the output is infinite. -/
theorem treeReal_invArithMap_eq_measureReal (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {w v : CantorSeq} (hv : invArithMap μ (BitStream.infinite w) = BitStream.infinite v) :
    treeReal lengthMeasure v = measureReal μ w := by
  -- every prefix of the output is forced by some prefix of the input
  have hgraph : ∀ j : ℕ, ∃ n, invArithGraph μ (cantorPrefix w n) (cantorPrefix v j) := by
    intro j
    have h1 : BitStream.finite (cantorPrefix v j) ≤ invArithMap μ (BitStream.infinite w) := by
      rw [hv]
      exact finite_cantorPrefix_le_infinite v j
    exact (streamLowerGraph_invArithMap_infinite μ w _).1 h1
  -- the two endpoint inequalities carried by a nonempty prefix of the output
  have hends : ∀ j : ℕ, treeLeftEnd lengthMeasure (cantorPrefix v (j + 1)) < measureReal μ w ∧
      measureReal μ w
        < treeLeftEnd lengthMeasure (cantorPrefix v (j + 1)) + ((2 : ℝ)⁻¹) ^ (j + 1) := by
    intro j
    obtain ⟨n, hn⟩ := hgraph (j + 1)
    have hne : cantorPrefix v (j + 1) ≠ [] := by
      intro h
      have := cantorPrefix_length v (j + 1)
      rw [h] at this
      simp at this
    rw [invArithGraph_iff_endpoints μ _ _ hne, cantorPrefix_length] at hn
    rw [treeLeftEnd_lengthMeasure_eq_div, cantorPrefix_length]
    have hsplit : ((devBitsToNat (cantorPrefix v (j + 1)) : ℝ) + 1) / 2 ^ (j + 1)
        = (devBitsToNat (cantorPrefix v (j + 1)) : ℝ) / 2 ^ (j + 1) + ((2 : ℝ)⁻¹) ^ (j + 1) := by
      rw [inv_pow]
      field_simp
    constructor
    · exact lt_of_lt_of_le hn.1 (treeLeftEnd_le_measureReal μ w n)
    · refine lt_of_le_of_lt (measureReal_le_treeRightEnd μ w n) ?_
      rw [← hsplit]
      exact hn.2
  -- upper bound
  have hup : treeReal lengthMeasure v ≤ measureReal μ w := by
    refine ciSup_le fun j => ?_
    cases j with
    | zero =>
        have h0 : cantorPrefix v 0 = [] := by
          have := cantorPrefix_length v 0
          exact List.eq_nil_of_length_eq_zero this
        rw [h0, treeLeftEnd_nil]
        exact measureReal_nonneg μ w
    | succ j => exact (hends j).1.le
  -- lower bound
  have hlow : measureReal μ w ≤ treeReal lengthMeasure v := by
    have hstep : ∀ j : ℕ, measureReal μ w ≤ treeReal lengthMeasure v + ((2 : ℝ)⁻¹) ^ (j + 1) := by
      intro j
      have hle : treeLeftEnd lengthMeasure (cantorPrefix v (j + 1)) ≤ treeReal lengthMeasure v := by
        refine le_ciSup (f := fun i => treeLeftEnd lengthMeasure (cantorPrefix v i)) ⟨1, ?_⟩ (j + 1)
        rintro _ ⟨i, rfl⟩
        exact treeLeftEnd_le_one lengthMeasure_isContinuousTreeSemimeasure _
      have := (hends j).2
      linarith
    have hb : Filter.Tendsto (fun j : ℕ => ((2 : ℝ)⁻¹) ^ j) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h0 : Filter.Tendsto (fun j : ℕ => ((2 : ℝ)⁻¹) ^ (j + 1)) Filter.atTop (nhds 0) :=
      hb.comp (Filter.tendsto_add_atTop_nat 1)
    have hlim : Filter.Tendsto (fun j : ℕ => treeReal lengthMeasure v + ((2 : ℝ)⁻¹) ^ (j + 1))
        Filter.atTop (nhds (treeReal lengthMeasure v)) := by
      simpa using Filter.Tendsto.const_add (treeReal lengthMeasure v) h0
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall hstep)
  exact le_antisymm hup hlow

/-! ## Mutual inversion: the forward map inverts the reverse map

Given the bridge above, this is a pure lower-graph computation.  `arithMap μ`
prints exactly the strings `x` whose interval `π_x` contains the real denoted by
its input **in the interior**; for the output of `invArithMap μ` on a `μ`-random
`w` that real is `measureReal μ w`, and the cells containing it in the interior
are exactly the prefixes of `w` -- the two endpoint cases being excluded by
`measureReal_ne_treeEnd_of_isMartinLofRandom`, and cells of equal length being
separated by `prefix_or_prefix_of_mem_treeIco`. -/

/-- **The forward map inverts the reverse map on the `μ`-random sequences**
(SUV Theorem 121, the third conjunct of obligation (c)). -/
theorem arithMap_invArithMap_of_isMartinLofRandom (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) (haμ : ∀ u : CantorSeq, μ {u} = 0)
    {w : CantorSeq} (hw : IsMartinLofRandom μ w) :
    arithMap μ (invArithMap μ (BitStream.infinite w)) = BitStream.infinite w := by
  obtain ⟨v, hv⟩ := exists_infinite_invArithMap_of_isMartinLofRandom μ hμ haμ hw
  rw [hv]
  have hreal : treeReal lengthMeasure v = measureReal μ w :=
    treeReal_invArithMap_eq_measureReal μ hv
  have huni : measureReal uniformMeasure v = measureReal μ w := by
    rw [← hreal]
    simp only [measureReal_eq_treeReal, cantorMass_uniformMeasure_eq_lengthMeasure]
  have hstrict : ∀ n : ℕ, treeLeftEnd (cantorMass μ) (cantorPrefix w n) < measureReal μ w ∧
      measureReal μ w < treeLeftEnd (cantorMass μ) (cantorPrefix w n)
        + (cantorMass μ (cantorPrefix w n)).toReal := by
    intro n
    obtain ⟨hne1, hne2⟩ := measureReal_ne_treeEnd_of_isMartinLofRandom μ μ hμ haμ hμ
      (cantorPrefix w n) hw
    exact ⟨lt_of_le_of_ne (treeLeftEnd_le_measureReal μ w n) (Ne.symm hne1),
      lt_of_le_of_ne (measureReal_le_treeRightEnd μ w n) hne2⟩
  have hsandL : ∀ j : ℕ, treeLeftEnd lengthMeasure (cantorPrefix v j) ≤ measureReal μ w := by
    intro j
    have h := treeLeftEnd_le_measureReal uniformMeasure v j
    rw [cantorMass_uniformMeasure_eq_lengthMeasure, huni] at h
    exact h
  have hsandR : ∀ j : ℕ, measureReal μ w
      ≤ treeLeftEnd lengthMeasure (cantorPrefix v j)
        + (lengthMeasure (cantorPrefix v j)).toReal := by
    intro j
    have h := measureReal_le_treeRightEnd uniformMeasure v j
    rw [cantorMass_uniformMeasure_eq_lengthMeasure, huni] at h
    exact h
  have hlen := lengthMeasure_isContinuousTreeSemimeasure
  have hL := tendsto_treeLeftEnd_treeReal hlen v
  have hR := tendsto_treeRightEnd_treeReal hlen v (tendsto_lengthMeasure_cantorPrefix v)
  rw [hreal] at hL hR
  refine BitStream.eq_of_forall_finite_le_iff _ _ (fun y => ?_)
  constructor
  · intro hle
    rw [streamLowerGraph_arithMap_infinite] at hle
    obtain ⟨j, hj⟩ := hle
    rcases hj with hnil | hsub
    · subst hnil
      exact fun i hi => absurd hi (by simp)
    have hrmem : measureReal μ w ∈ binaryClosedInterval (cantorPrefix v j) := by
      simp only [binaryClosedInterval, Set.mem_Icc]
      exact ⟨hsandL j, hsandR j⟩
    have hint := hsub hrmem
    rw [treeIco, interior_Ico, Set.mem_Ioo] at hint
    have h1 : measureReal μ w ∈ treeIco (cantorMass μ) y := by
      rw [treeIco, Set.mem_Ico]
      exact ⟨hint.1.le, hint.2⟩
    have h2 : measureReal μ w ∈ treeIco (cantorMass μ) (cantorPrefix w y.length) := by
      rw [treeIco, Set.mem_Ico]
      exact ⟨(hstrict y.length).1.le, (hstrict y.length).2⟩
    have heq : y = cantorPrefix w y.length := by
      rcases prefix_or_prefix_of_mem_treeIco (isContinuousTreeSemimeasure_cantorMass μ) h1 h2
        with h | h
      · exact h.eq_of_length (by rw [cantorPrefix_length])
      · exact (h.eq_of_length (by rw [cantorPrefix_length])).symm
    rw [heq]
    exact finite_cantorPrefix_le_infinite w y.length
  · intro hle
    have hyw : cantorPrefix w y.length = y := (isCantorPrefix_iff_cantorPrefix_eq y w).1 hle
    rw [streamLowerGraph_arithMap_infinite]
    have hs := hstrict y.length
    rw [hyw] at hs
    have e1 : ∀ᶠ j in Filter.atTop, treeLeftEnd (cantorMass μ) y
        < treeLeftEnd lengthMeasure (cantorPrefix v j) :=
      hL.eventually (eventually_gt_nhds hs.1)
    have e2 : ∀ᶠ j in Filter.atTop, treeLeftEnd lengthMeasure (cantorPrefix v j)
        + (lengthMeasure (cantorPrefix v j)).toReal
        < treeLeftEnd (cantorMass μ) y + (cantorMass μ y).toReal :=
      hR.eventually (eventually_lt_nhds hs.2)
    obtain ⟨j, hj1, hj2⟩ := (e1.and e2).exists
    refine ⟨j, Or.inr ?_⟩
    rw [treeIco, interior_Ico]
    intro z hz
    simp only [binaryClosedInterval, Set.mem_Icc] at hz
    exact ⟨lt_of_lt_of_le hj1 hz.1, lt_of_le_of_lt hz.2 hj2⟩

/-! ## Mutual inversion: the reverse map inverts the forward map -/

/-- The real coded by a Martin-Löf random sequence is never a dyadic rational. -/
lemma treeReal_lengthMeasure_ne_div_two_pow {v : CantorSeq}
    (hv : IsMartinLofRandom uniformMeasure v) (m k : ℕ) :
    treeReal lengthMeasure v ≠ (k : ℝ) / 2 ^ m := by
  have hmeq : measureReal uniformMeasure v = treeReal lengthMeasure v := by
    simp only [measureReal_eq_treeReal, cantorMass_uniformMeasure_eq_lengthMeasure]
  rw [← hmeq]
  exact measureReal_ne_div_two_pow_of_isMartinLofRandom uniformMeasure
    isComputableMeasure_uniform uniformMeasure_singleton hv m k

/-- **The output of `arithMap μ` denotes the same real as its input**, provided
`μ` is atomless. -/
theorem measureReal_arithMap_eq_treeReal (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (haμ : ∀ u : CantorSeq, μ {u} = 0) {v u : CantorSeq}
    (hu : arithMap μ (BitStream.infinite v) = BitStream.infinite u) :
    measureReal μ u = treeReal lengthMeasure v := by
  have hsandL : ∀ j : ℕ,
      treeLeftEnd lengthMeasure (cantorPrefix v j) ≤ treeReal lengthMeasure v := by
    intro j
    have h := treeLeftEnd_le_measureReal uniformMeasure v j
    rw [cantorMass_uniformMeasure_eq_lengthMeasure] at h
    simpa only [measureReal_eq_treeReal, cantorMass_uniformMeasure_eq_lengthMeasure] using h
  have hsandR : ∀ j : ℕ, treeReal lengthMeasure v
      ≤ treeLeftEnd lengthMeasure (cantorPrefix v j)
        + (lengthMeasure (cantorPrefix v j)).toReal := by
    intro j
    have h := measureReal_le_treeRightEnd uniformMeasure v j
    rw [cantorMass_uniformMeasure_eq_lengthMeasure] at h
    simpa only [measureReal_eq_treeReal, cantorMass_uniformMeasure_eq_lengthMeasure] using h
  have hgraph : ∀ n : ℕ, ∃ j, arithmeticCodingLowerGraph μ (cantorPrefix v j)
      (cantorPrefix u n) := by
    intro n
    have h1 : BitStream.finite (cantorPrefix u n) ≤ arithMap μ (BitStream.infinite v) := by
      rw [hu]
      exact finite_cantorPrefix_le_infinite u n
    exact (streamLowerGraph_arithMap_infinite μ v _).1 h1
  have hends : ∀ n : ℕ,
      treeLeftEnd (cantorMass μ) (cantorPrefix u (n + 1)) < treeReal lengthMeasure v ∧
      treeReal lengthMeasure v < treeLeftEnd (cantorMass μ) (cantorPrefix u (n + 1))
        + (cantorMass μ (cantorPrefix u (n + 1))).toReal := by
    intro n
    obtain ⟨j, hj⟩ := hgraph (n + 1)
    rcases hj with hnil | hsub
    · exfalso
      have := cantorPrefix_length u (n + 1)
      rw [hnil] at this
      simp at this
    have hrmem : treeReal lengthMeasure v ∈ binaryClosedInterval (cantorPrefix v j) := by
      simp only [binaryClosedInterval, Set.mem_Icc]
      exact ⟨hsandL j, hsandR j⟩
    have hint := hsub hrmem
    rwa [treeIco, interior_Ico, Set.mem_Ioo] at hint
  refine le_antisymm ?_ ?_
  · refine ciSup_le fun n => ?_
    cases n with
    | zero =>
        have h0 : cantorPrefix u 0 = [] := List.eq_nil_of_length_eq_zero (cantorPrefix_length u 0)
        rw [h0, treeLeftEnd_nil]
        have h := hsandL 0
        have h1 : treeLeftEnd lengthMeasure (cantorPrefix v 0) = 0 := by
          have hv0 : cantorPrefix v 0 = [] :=
            List.eq_nil_of_length_eq_zero (cantorPrefix_length v 0)
          rw [hv0, treeLeftEnd_nil]
        linarith [h, h1.symm.le]
    | succ n => exact (hends n).1.le
  · have hstep : ∀ n : ℕ, treeReal lengthMeasure v ≤ measureReal μ u
        + (cantorMass μ (cantorPrefix u (n + 1))).toReal := by
      intro n
      have h := (hends n).2
      have hle := treeLeftEnd_le_measureReal μ u (n + 1)
      linarith
    have h0 := tendsto_cantorMass_cantorPrefix_atom_free μ (haμ u)
    have h0R : Filter.Tendsto (fun n => (cantorMass μ (cantorPrefix u n)).toReal)
        Filter.atTop (nhds 0) := by
      have := (ENNReal.tendsto_toReal (by simp)).comp h0
      simpa using this
    have h1R : Filter.Tendsto (fun n => (cantorMass μ (cantorPrefix u (n + 1))).toReal)
        Filter.atTop (nhds 0) := h0R.comp (Filter.tendsto_add_atTop_nat 1)
    have hlim : Filter.Tendsto
        (fun n => measureReal μ u + (cantorMass μ (cantorPrefix u (n + 1))).toReal)
        Filter.atTop (nhds (measureReal μ u)) := by
      simpa using Filter.Tendsto.const_add (measureReal μ u) h1R
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall hstep)

end Kolmogorov
