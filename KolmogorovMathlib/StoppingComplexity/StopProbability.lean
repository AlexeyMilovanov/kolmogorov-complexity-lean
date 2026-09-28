import KolmogorovMathlib.StoppingComplexity.Machine
import KolmogorovMathlib.StoppingComplexity.TimeSemimeasure

/-!
# Stopping probability of an operational machine

Blueprint 03 §2, Definition and Lemma M4, and F4. For a stopping controller `R` and an input
`z`, `haltEvent R z` is the set of random tapes on which `R` halts after consuming exactly `z`,
and the stopping probability `stopProb R z` is *defined* as its fair-coin measure (F0). The
witness sum `∑ 2^{-|p|}` over exact witnesses is the theorem `stopProb_eq_tsum` (M4), the
stopping probability is a time semimeasure (`stopProb_isTimeSemimeasure`), and for the
enumerated machines it is lower semicomputable with the stage approximation `stopProbApprox`
(primitive recursive in the index, the budget and the input).
-/

namespace Kolmogorov

open scoped ENNReal

/-- The random tapes on which `R` halts after consuming exactly the input `z`: those with a
finite prefix `p` such that `(z, p)` is an exact-consumption witness.
Blueprint 03 §2 Definition M4 (03-M4-DEF). -/
def haltEvent (R : StoppingController) (z : BitString) : Set CantorSeq :=
  {w | ∃ p, IsCantorPrefix p w ∧ Witness R z p}

/-- The halt event is the union of the witness cylinders.
Blueprint 03 §2 Definition M4 (03-M4-DEF). -/
theorem haltEvent_eq_iUnion (R : StoppingController) (z : BitString) :
    haltEvent R z = ⋃ p, ⋃ (_ : Witness R z p), cantorCylinder p := by
  ext w
  simp [haltEvent, cantorCylinder, and_comm]

/-- The halt event is open in Cantor space (a union of cylinders).
Blueprint 03 Lemma M4 (03-M4). -/
theorem isOpen_haltEvent (R : StoppingController) (z : BitString) : IsOpen (haltEvent R z) := by
  rw [haltEvent_eq_iUnion]
  exact isOpen_iUnion fun p => isOpen_iUnion fun _ => isOpen_cantorCylinder p

/-- The halt event is measurable. Blueprint 03 Lemma M4 (03-M4). -/
theorem measurableSet_haltEvent (R : StoppingController) (z : BitString) :
    MeasurableSet (haltEvent R z) := by
  exact (isOpen_haltEvent R z).measurableSet

/-- `M_R(z)`: the probability, under the fair random tape, that `R` stops after consuming
exactly the input `z` (F0; the `τ_R` of Blueprint 03 §2). Blueprint 03 §2 Definition M4
(03-M4-DEF). -/
noncomputable def stopProb (R : StoppingController) (z : BitString) : ℝ≥0∞ :=
  uniformMeasure (haltEvent R z)

/-- The stopping probability is the sum of `2^{-|p|}` over the exact witnesses `p`, which have
pairwise disjoint cylinders by M3. Blueprint 03 Lemma M4, F4 `stopping_probability_eq_sum`
(03-M4). -/
theorem stopProb_eq_tsum (R : StoppingController) (z : BitString) :
    stopProb R z =
      ∑' p : {p : BitString // Witness R z p}, (2 : ℝ≥0∞)⁻¹ ^ (p : BitString).length := by
  have hU : haltEvent R z = ⋃ p : {p : BitString // Witness R z p}, cantorCylinder p := by
    ext w
    simp [haltEvent, cantorCylinder, and_comm]
  have hdisj : Pairwise (Function.onFun Disjoint fun p : {p : BitString // Witness R z p} =>
      cantorCylinder (p : BitString)) := by
    intro p p' hne
    have hne' : (p : BitString) ≠ p' := fun h => hne (Subtype.ext h)
    exact cantorCylinder_disjoint_of_incompatible
      (fun h => hne' (isPrefixFree_witness R z p.2 p'.2 h))
      (fun h => hne' (isPrefixFree_witness R z p'.2 p.2 h).symm)
  unfold stopProb
  rw [hU, MeasureTheory.measure_iUnion hdisj fun p => measurableSet_cantorCylinder _]
  exact tsum_congr fun p => cantorMass_uniformMeasure p

/-- The stopping probability is at most one. Blueprint 03 Lemma M4 (03-M4). -/
theorem stopProb_le_one (R : StoppingController) (z : BitString) : stopProb R z ≤ 1 := by
  exact MeasureTheory.prob_le_one

/-- The stopping probability is finite. Blueprint 03 Lemma M4 (03-M4). -/
theorem stopProb_ne_top (R : StoppingController) (z : BitString) : stopProb R z ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (stopProb_le_one R z)

/-- Every witness contributes its cylinder weight: `2^{-|p|} ≤ M_R(z)`.
Blueprint 03 Lemma M4 (03-M4). -/
theorem two_pow_neg_le_stopProb_of_witness {R : StoppingController} {z p : BitString}
    (h : Witness R z p) : (2 : ℝ≥0∞)⁻¹ ^ p.length ≤ stopProb R z := by
  rw [← cantorMass_uniformMeasure]
  exact MeasureTheory.measure_mono fun w hw => ⟨p, hw, h⟩

/-- M3 along an input chain: the halt events of two distinct comparable inputs are disjoint,
since a common tape would carry two comparable witnesses of distinct comparable inputs.
Blueprint 03 Lemma M4 (03-M4-TS). -/
private theorem disjoint_haltEvent_of_isComparable {R : StoppingController} {u v : BitString}
    (h : IsComparable u v) (hne : u ≠ v) : Disjoint (haltEvent R u) (haltEvent R v) := by
  rw [Set.disjoint_left]
  rintro w ⟨p, hpw, hp⟩ ⟨p', hp'w, hp'⟩
  exact Set.disjoint_left.1 ((disjoint_cantorCylinder_iff p p').2
    (hp.isIncomparable_of_ne hp' h hne)) hpw hp'w

/-- The stopping probability is a time semimeasure: along any input chain the witness
cylinders are pairwise disjoint (M3), so the prefix sums are at most one.
Blueprint 03 Lemma M4, F4 `stopping_probability_timeSemimeasure` (03-M4-TS). -/
theorem stopProb_isTimeSemimeasure (R : StoppingController) :
    IsTimeSemimeasure (stopProb R) := by
  intro v
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (v.length + 1)))
      fun k => haltEvent R (v.take k) := by
    intro k hk k' hk' hne
    simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
    refine disjoint_haltEvent_of_isComparable
      (isComparable_of_prefix_of_prefix (List.take_prefix _ _) (List.take_prefix _ _)) ?_
    intro heq
    have hlen := congrArg List.length heq
    simp only [List.length_take] at hlen
    omega
  calc prefixLoad (stopProb R) v
      = uniformMeasure (⋃ k ∈ Finset.range (v.length + 1), haltEvent R (v.take k)) := by
        rw [MeasureTheory.measure_biUnion_finset hdisj fun k _ => measurableSet_haltEvent R _]
        rfl
    _ ≤ 1 := MeasureTheory.prob_le_one

/-- Stage approximation of the stopping probability of the `e`-th machine: the rational sum of
`2^{-|p|}` over the random strings `p` of length `≤ t` accepted by the bounded simulation with
budget `t`. Blueprint 03 Lemma M4 (03-M4-LSC). -/
def stopProbApprox (e t : ℕ) (z : BitString) : ℚ :=
  (((boundedPrograms t).filter fun p => witnessWithin e t z p).map
    fun p => (1 / 2 : ℚ) ^ p.length).sum

/-- The stage-`t` numerator of `stopProbApprox e t z` over the common denominator `2^t`: the sum
of `2^{t - |p|}` over the accepted random strings `p` of length `≤ t`.
Blueprint 03 Lemma M4 (03-M4-LSC). -/
private def stopProbNum (e t : ℕ) (z : BitString) : ℕ :=
  (((boundedPrograms t).filter fun p => witnessWithin e t z p).map
    fun p => 2 ^ (t - p.length)).sum

/-- The stage approximation is the dyadic rational `stopProbNum e t z / 2^t`: every accepted
string has length `≤ t`. Blueprint 03 Lemma M4 (03-M4-LSC). -/
private theorem stopProbApprox_eq_div (e t : ℕ) (z : BitString) :
    stopProbApprox e t z = (stopProbNum e t z : ℚ) / 2 ^ t := by
  unfold stopProbApprox stopProbNum
  rw [Nat.cast_list_sum, List.map_map, eq_div_iff (by positivity), ← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  have hlen : p.length ≤ t := (mem_boundedPrograms_iff p t).1 (List.mem_filter.1 hp).1
  simp only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_sub₀ (2 : ℚ) two_ne_zero hlen, one_div_pow, div_mul_eq_mul_div, one_mul,
    div_eq_mul_inv]

/-- The stage approximation as a finite sum of the weights `2^{-|p|}` over the stage-`t`
accepted strings (the filtered list has no duplicates). Blueprint 03 Lemma M4 (03-M4-LSC). -/
private theorem stopProbApprox_eq_sum (e t : ℕ) (z : BitString) :
    stopProbApprox e t z =
      ∑ p ∈ ((boundedPrograms t).filter fun p => witnessWithin e t z p).toFinset,
        (1 / 2 : ℚ) ^ p.length := by
  unfold stopProbApprox
  rw [List.sum_toFinset _ ((boundedPrograms_nodup t).filter _)]

/-- The stage-`t` approximation, read in `ℝ≥0∞`, is the sum of the cylinder weights `2^{-|p|}`
over the stage-`t` accepted strings. Blueprint 03 Lemma M4 (03-M4-LSC). -/
private theorem ofReal_stopProbApprox (e t : ℕ) (z : BitString) :
    ENNReal.ofReal (stopProbApprox e t z) =
      ∑ p ∈ ((boundedPrograms t).filter fun p => witnessWithin e t z p).toFinset,
        (2 : ℝ≥0∞)⁻¹ ^ p.length := by
  rw [stopProbApprox_eq_sum]
  push_cast
  rw [ENNReal.ofReal_sum_of_nonneg fun p _ => by positivity]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
    ENNReal.ofReal_ofNat]

/-- The dyadic value of the stage-`s` numerator is the stage approximation.
Blueprint 03 Lemma M4 (03-M4-LSC). -/
private theorem dyadicValue_stopProbNum (e s : ℕ) (z : BitString) :
    dyadicValue (stopProbNum e s z) s = ENNReal.ofReal (stopProbApprox e s z) := by
  rw [stopProbApprox_eq_div, dyadicValue]
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- The stage numerator is primitive recursive in the index, the stage and the input.
Blueprint 03 Lemma M4 (03-M4-LSC). -/
private theorem primrec_stopProbNum :
    Primrec fun a : ℕ × ℕ × BitString => stopProbNum a.1 a.2.1 a.2.2 := by
  have hpow : Primrec₂ fun a b : ℕ => a ^ b := Primrec.nat_iff.mpr Nat.Primrec.pow
  have hacc : Primrec₂ fun (a : ℕ × ℕ × BitString) (p : BitString) =>
      witnessWithin a.1 a.2.1 a.2.2 p :=
    (primrec_witnessWithin.comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))).of_eq
      fun _ => rfl
  have hfilt : Primrec fun a : ℕ × ℕ × BitString =>
      (boundedPrograms a.2.1).filter fun p => witnessWithin a.1 a.2.1 a.2.2 p :=
    Primrec.list_filter (primrec_boundedPrograms.comp (Primrec.fst.comp Primrec.snd)) hacc
  have hterm : Primrec₂ fun (a : ℕ × ℕ × BitString) (p : BitString) => 2 ^ (a.2.1 - p.length) :=
    (hpow.comp (Primrec.const 2) (Primrec.nat_sub.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_length.comp Primrec.snd))).of_eq fun _ => rfl
  have hmap := Primrec.list_map hfilt hterm
  exact (Primrec.list_foldr hmap (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

/-- The nonnegative dyadic rationals `M / 2^E` are primitive recursive in `(M, E)`: the code of
`M / 2^E` is computed from the reduced numerator and denominator by a gcd.
Blueprint 03 Lemma M4 (03-M4-LSC). -/
private theorem primrec_natCast_div_two_pow : Primrec₂ fun (M E : ℕ) => (M : ℚ) / 2 ^ E := by
  have hpow : Primrec₂ fun a b : ℕ => a ^ b := Primrec.nat_iff.mpr Nat.Primrec.pow
  have h2E : Primrec fun p : ℕ × ℕ => 2 ^ p.2 := hpow.comp (Primrec.const 2) Primrec.snd
  have hg : Primrec fun p : ℕ × ℕ => Nat.gcd (2 ^ p.2) p.1 :=
    ComputableReals.primrec_natGcd.comp h2E Primrec.fst
  have hcode : Primrec fun p : ℕ × ℕ =>
      ratCount (Nat.pair (2 * (p.1 / Nat.gcd (2 ^ p.2) p.1)) (2 ^ p.2 / Nat.gcd (2 ^ p.2) p.1)) :=
    primrec_ratCount.comp (Primrec₂.natPair.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_div.comp Primrec.fst hg))
      (Primrec.nat_div.comp h2E hg))
  refine Primrec.encode_iff.1 (hcode.of_eq fun p => ?_)
  have hq : (p.1 : ℚ) / 2 ^ p.2 = mkRat (p.1 : ℤ) (2 ^ p.2) := by
    rw [Rat.mkRat_eq_div]
    push_cast
    rfl
  have hne : 2 ^ p.2 ≠ 0 := by positivity
  have hnum : ((p.1 : ℚ) / 2 ^ p.2).num = ((p.1 / Nat.gcd (2 ^ p.2) p.1 : ℕ) : ℤ) := by
    rw [hq, Rat.num_mkRat, if_neg hne, Int.natAbs_natCast, Int.natCast_div]
  have hden : ((p.1 : ℚ) / 2 ^ p.2).den = 2 ^ p.2 / Nat.gcd (2 ^ p.2) p.1 := by
    rw [hq, Rat.den_mkRat, if_neg hne, Int.natAbs_natCast]
  rw [encode_eq_ratCount]
  dsimp only
  rw [ratCode, hnum, hden]
  rfl

/-- The stage approximation is primitive recursive in the index, the stage and the input; this
carries the uniformity in `e` of the lower semicomputability of `stopProb`.
Blueprint 03 Lemma M4 (03-M4-LSC). -/
theorem primrec_stopProbApprox :
    Primrec fun a : ℕ × ℕ × BitString => stopProbApprox a.1 a.2.1 a.2.2 := by
  exact (primrec_natCast_div_two_pow.comp primrec_stopProbNum
    (Primrec.fst.comp Primrec.snd)).of_eq fun a => (stopProbApprox_eq_div a.1 a.2.1 a.2.2).symm

/-- The stage approximation is nondecreasing in the stage.
Blueprint 03 Lemma M4 (03-M4-LSC). -/
theorem stopProbApprox_mono (e : ℕ) (z : BitString) :
    Monotone fun t => stopProbApprox e t z := by
  intro t t' htt'
  simp only [stopProbApprox_eq_sum]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => by positivity
  rw [List.mem_toFinset, List.mem_filter, mem_boundedPrograms_iff] at hp ⊢
  exact ⟨hp.1.trans htt', witnessWithin_mono htt' hp.2⟩

/-- The stopping probability of the `e`-th machine is the supremum of its stage approximations.
Blueprint 03 Lemma M4 (03-M4-LSC). -/
theorem stopProb_eq_iSup_stopProbApprox (e : ℕ) (z : BitString) :
    stopProb (stoppingMachine e) z = ⨆ t, ENNReal.ofReal (stopProbApprox e t z) := by
  classical
  rw [stopProb_eq_tsum]
  simp_rw [ofReal_stopProbApprox]
  apply le_antisymm
  · rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    choose tW htW using fun p : {p : BitString // Witness (stoppingMachine e) z p} =>
      (witness_iff_exists_witnessWithin e z p.1).1 p.2
    refine le_iSup_of_le (s.sup fun p => max (tW p) (p : BitString).length) ?_
    calc ∑ p ∈ s, (2 : ℝ≥0∞)⁻¹ ^ (p : BitString).length
        = ∑ p ∈ s.image Subtype.val, (2 : ℝ≥0∞)⁻¹ ^ p.length :=
          (Finset.sum_image (f := fun p : BitString => (2 : ℝ≥0∞)⁻¹ ^ p.length)
            fun x _ y _ h => Subtype.ext h).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset fun p hp => ?_
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    have hle := Finset.le_sup (f := fun p => max (tW p) (p : BitString).length) hq
    rw [List.mem_toFinset, List.mem_filter, mem_boundedPrograms_iff]
    exact ⟨le_trans (le_max_right _ _) hle,
      witnessWithin_mono (le_trans (le_max_left _ _) hle) (htW q)⟩
  · refine iSup_le fun t => ?_
    have hW : ∀ p ∈ ((boundedPrograms t).filter fun p => witnessWithin e t z p).toFinset,
        Witness (stoppingMachine e) z p := fun p hp => by
      rw [List.mem_toFinset, List.mem_filter] at hp
      exact (witness_iff_exists_witnessWithin e z p).2 ⟨t, hp.2⟩
    rw [← Finset.sum_subtype_of_mem (fun p : BitString => (2 : ℝ≥0∞)⁻¹ ^ p.length) hW]
    exact ENNReal.sum_le_tsum _

/-- For each index `e`, the stopping probability of the `e`-th machine is a lower
semicomputable time semimeasure. The statement is per index (`IsLSC` chooses its approximation
per function); the uniformity in `e` is `primrec_stopProbApprox` together with
`stopProbApprox_mono` and `stopProb_eq_iSup_stopProbApprox` (deviation 03-M4-LSC).
Blueprint 03 Lemma M4, F4 `stopping_probability_lowerSemicomputable` (03-M4-LSC). -/
theorem stopProb_stoppingMachine_isLSC (e : ℕ) :
    IsLowerSemicomputableTimeSemimeasure (stopProb (stoppingMachine e)) := by
  refine ⟨stopProb_isTimeSemimeasure _, fun s out _ => stopProbNum e s out, ?_, ?_, ?_⟩
  · intro s out _
    dsimp only
    rw [dyadicValue_stopProbNum, dyadicValue_stopProbNum]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast stopProbApprox_mono e out (Nat.le_succ s))
  · intro out _
    dsimp only
    simp_rw [dyadicValue_stopProbNum]
    exact (stopProb_eq_iSup_stopProbApprox e out).symm
  · exact (primrec_stopProbNum.comp (Primrec.pair (Primrec.const e)
      (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))).to_comp

end Kolmogorov
