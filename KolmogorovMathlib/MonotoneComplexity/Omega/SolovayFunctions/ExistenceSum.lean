import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.BusyBeaver
import KolmogorovMathlib.Complexity.NatComplexity
import KolmogorovMathlib.MonotoneComplexity.Dimension.PostponeTrim
import KolmogorovMathlib.MonotoneComplexity.Omega.AntitoneSplit
import KolmogorovMathlib.MonotoneComplexity.Omega.BusyBeaverInfra
import KolmogorovMathlib.MonotoneComplexity.Omega.BusyBeaverSearch
import KolmogorovMathlib.MonotoneComplexity.Omega.CappedScaling
import KolmogorovMathlib.MonotoneComplexity.Omega.IntervalCover
import KolmogorovMathlib.MonotoneComplexity.Omega.ModulusRandom
import KolmogorovMathlib.MonotoneComplexity.Omega.NeighbourhoodCover
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealCantor
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealKraft
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaBitsFromApprox
import KolmogorovMathlib.MonotoneComplexity.Omega.Prediction
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctionComputable
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.SolovayProperty
import KolmogorovMathlib.Prefix.UpperSemicomputableBound

/-!
# Solovay functions exist, and the property depends only on the sum

`exists_isSolovayFunction` and `exists_monotone_isSolovayFunction` produce Solovay functions, the
second non-decreasing. The rest of the module shows how little the property depends on the
presentation: it is invariant under computable permutations
(`exists_const_apriori_comp_perm`, `hasSolovayProperty_comp_perm`) and depends only on the value
of the sum (`hasSolovayProperty_congr_of_sum_eq`). The pair a priori probability `aprioriPair`
with its identification `aprioriPair_eq`, the marginal computation and the flattening lemma
`tendsto_partialSums_unpair` are the ingredients of the strengthening of §5.7.6.

Source: SUV §5.7.5–5.7.6, pp. 166–168.
-/



namespace Kolmogorov
open MeasureTheory ENNReal

/-- **SUV p. 166.** Solovay functions exist. -/
theorem exists_isSolovayFunction {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ S : ℕ → ℕ, IsSolovayFunction U S := by
  obtain ⟨m, hm⟩ := exists_isUniversalSemimeasureNat
  obtain ⟨r, α, hr, hr01, hsum, hrand⟩ := exists_computable_series_isMartinLofRandomReal_sum
  obtain ⟨S, hS, hround⟩ := exists_computable_dyadicRounding hr hr01
  refine ⟨S, ?_⟩
  rw [← hasSolovayProperty_iff_isSolovayFunction_of_tsum_ne_top hm hU hr
    (fun i => (hr01 i).1) hS hround
    (tsum_ofReal_ne_top_of_partialSums_tendsto (fun i => (hr01 i).1.le) hsum)]
  exact (isMartinLofRandomReal_iff_hasSolovayProperty hm hr
    (fun i => (hr01 i).1.le) hsum).1 hrand

/-- **SUV p. 166.** There exist computable *non-decreasing* Solovay functions: take a
computable series of rationals with random sum and make it non-increasing without
changing the sum, by splitting too big terms into small pieces. -/
theorem exists_monotone_isSolovayFunction {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ S : ℕ → ℕ, Monotone S ∧ IsSolovayFunction U S := by
  obtain ⟨m, hm⟩ := exists_isUniversalSemimeasureNat
  obtain ⟨r, α, hr, hr01, hanti, hsum, hrand⟩ :=
    exists_antitone_computable_series_isMartinLofRandomReal_sum
  obtain ⟨S, hS, hround⟩ := exists_computable_dyadicRounding hr hr01
  refine ⟨S, monotone_of_dyadicRounding hround hanti, ?_⟩
  rw [← hasSolovayProperty_iff_isSolovayFunction_of_tsum_ne_top hm hU hr
    (fun i => (hr01 i).1) hS hround
    (tsum_ofReal_ne_top_of_partialSums_tendsto (fun i => (hr01 i).1.le) hsum)]
  exact (isMartinLofRandomReal_iff_hasSolovayProperty hm hr
    (fun i => (hr01 i).1.le) hsum).1 hrand

/-! ### Section 5.7.6: the Solovay property as a property of the sum (SUV p. 167) -/

/-- **SUV p. 167.** A computable permutation changes the a priori
probability only by a constant factor, `m(π(i)) = Θ(m(i))`. -/
theorem exists_const_apriori_comp_perm {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    {π : ℕ → ℕ} (hπ : Function.Bijective π) (hπc : Computable π) :
    ∃ c : ℝ≥0∞, 0 < c ∧ (∀ i, c * m i ≤ m (π i)) ∧ (∀ i, c * m (π i) ≤ m i) := by
  have hlsc := hm.isLowerSemicomputableSemimeasureNat
  have hinv : Computable (Equiv.ofBijective π hπ).symm := computable_symm_of_bijective hπ hπc
  obtain ⟨c₁, hc₁, h₁⟩ := hm.dominates (isLowerSemicomputableSemimeasureNat_comp hlsc hπ hπc)
  obtain ⟨c₂, hc₂, h₂⟩ := hm.dominates
    (isLowerSemicomputableSemimeasureNat_comp hlsc
      (Equiv.ofBijective π hπ).symm.bijective hinv)
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, fun i => ?_, fun i => ?_⟩
  · have hkey : c₂ * m ((Equiv.ofBijective π hπ).symm (π i)) ≤ m (π i) := h₂ (π i)
    have hsym : (Equiv.ofBijective π hπ).symm (π i) = i :=
      (Equiv.ofBijective π hπ).symm_apply_apply i
    rw [hsym] at hkey
    exact le_trans (mul_le_mul_left (min_le_right _ _) _) hkey
  · exact le_trans (mul_le_mul_left (min_le_left _ _) _) (h₁ i)

/-- **SUV p. 167.** The Solovay property is invariant under computable permutations,
because a computable permutation changes the a priori probability only by a constant
factor: `m(π(i)) = Θ(m(i))`. -/
theorem hasSolovayProperty_comp_perm {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    {π : ℕ → ℕ} (hπ : Function.Bijective π) (hπc : Computable π) (r : ℕ → ℚ) :
    HasSolovayProperty m (r ∘ π) ↔ HasSolovayProperty m r := by
  obtain ⟨c, hc, hfwd, hbwd⟩ := exists_const_apriori_comp_perm hm hπ hπc
  constructor
  · rintro ⟨ε, hε, hinf⟩
    refine ⟨ε * c, ENNReal.mul_pos hε.ne' hc.ne', ?_⟩
    refine Set.Infinite.mono ?_ (hinf.image hπ.injective.injOn)
    rintro _ ⟨i, hi, rfl⟩
    calc ε * c * m (π i) = ε * (c * m (π i)) := by ring
      _ ≤ ε * m i := by gcongr; exact hbwd i
      _ ≤ ENNReal.ofReal (((r ∘ π) i : ℚ) : ℝ) := hi
  · rintro ⟨ε, hε, hinf⟩
    refine ⟨ε * c, ENNReal.mul_pos hε.ne' hc.ne', ?_⟩
    set e := Equiv.ofBijective π hπ with he
    refine Set.Infinite.mono ?_ (hinf.image e.symm.injective.injOn)
    rintro _ ⟨j, hj, rfl⟩
    have hπe : π (e.symm j) = j := e.apply_symm_apply j
    calc ε * c * m (e.symm j) = ε * (c * m (e.symm j)) := by ring
      _ ≤ ε * m (π (e.symm j)) := by gcongr; exact hfwd _
      _ = ε * m j := by rw [hπe]
      _ ≤ ENNReal.ofReal ((r j : ℚ) : ℝ) := hj
      _ = ENNReal.ofReal (((r ∘ π) (e.symm j) : ℚ) : ℝ) := by simp [Function.comp, hπe]

/-- **SUV p. 167.** `m(i,j)`, the a priori probability of the *pair* `(i,j)`, taken
through the shared canonical pair coding `natPairCode` of `SharedCoding` (audit
item 9) rather than through an ad hoc `Nat.pair` occurrence.

Invariance remark: by `exists_const_KPPlain_natPairCode_invariant` any other
computable injective coding of pairs changes `K` — hence, by the coding theorem
`exists_const_KPNat_aprioriNat_equiv`, the a priori probability — only by an
`O(1)`-additive / `Θ(1)`-multiplicative amount, which is exactly the precision at
which every statement below is formulated. -/
noncomputable def aprioriPair (m : ℕ → ℝ≥0∞) (i j : ℕ) : ℝ≥0∞ :=
  m (bitStringToNat (natPairCode i j))

/-- The canonical pair coding is the Cantor pairing read through `natBitStringEquiv`,
so `aprioriPair` is the book's `m(i,j)`. -/
@[simp] theorem aprioriPair_eq (m : ℕ → ℝ≥0∞) (i j : ℕ) :
    aprioriPair m i j = m (Nat.pair i j) := by
  simp [aprioriPair, natPairCode]

/-! #### The pair marginal, decomposed

SUV p. 167 proves `m(i) = ∑ⱼ m(i,j)` up to an `O(1)`-factor in one sentence with two halves:
"*the sum in the right-hand side is lower semicomputable, so it is `O(m(i))` due to
maximality; on the other hand, already the first term `m(i,0)` is `Ω(m(i))`*".  Each half is a
single application of maximality to an explicitly described lower semicomputable semimeasure,
and is stated as its own leaf below. -/

/-- **New C11b leaf (SUV p. 167, "already the first term `m(i,0)` is `Ω(m(i))`").** -/
theorem exists_const_apriori_le_aprioriPair_zero {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ i, c * m i ≤ aprioriPair m i 0 := by
  classical
  obtain ⟨A, hAmono, hAsup, hAc⟩ := hm.isLowerSemicomputableSemimeasureNat.2
  have hsm : IsLowerSemicomputableSemimeasureNat
      (fun n : ℕ => if n.unpair.2 = 0 then m n.unpair.1 else 0) := by
    constructor
    · change (∑' x : BitString,
        (if (bitStringToNat x).unpair.2 = 0 then m (bitStringToNat x).unpair.1 else 0)) ≤ 1
      rw [tsum_comp_bitStringToNat
        (fun n : ℕ => if n.unpair.2 = 0 then m n.unpair.1 else 0)]
      rw [← Nat.pairEquiv.tsum_eq (fun n : ℕ => if n.unpair.2 = 0 then m n.unpair.1 else 0)]
      rw [tsum_congr (fun p : ℕ × ℕ => by
        change (if (Nat.pair p.1 p.2).unpair.2 = 0 then m (Nat.pair p.1 p.2).unpair.1 else 0) = _
        simp [Nat.unpair_pair] :
        ∀ p : ℕ × ℕ, (if (Nat.pairEquiv p).unpair.2 = 0 then m (Nat.pairEquiv p).unpair.1 else 0)
          = (if p.2 = 0 then m p.1 else 0))]
      rw [ENNReal.tsum_prod (f := fun i j : ℕ => if j = 0 then m i else 0)]
      have hrow : ∀ i : ℕ, (∑' j : ℕ, (if j = 0 then m i else 0)) = m i := by
        intro i
        simp
      rw [tsum_congr hrow]
      exact hm.tsum_le_one
    · refine ⟨fun s x _ => if (bitStringToNat x).unpair.2 = 0
        then A s (natToBitString (bitStringToNat x).unpair.1) [] else 0, ?_, ?_, ?_⟩
      · intro s out _
        by_cases h : (bitStringToNat out).unpair.2 = 0
        · simpa [h] using hAmono s (natToBitString (bitStringToNat out).unpair.1) []
        · simp [h, dyadicValue]
      · intro out _
        by_cases h : (bitStringToNat out).unpair.2 = 0
        · simpa [h] using hAsup (natToBitString (bitStringToNat out).unpair.1) []
        · simp [h, dyadicValue]
      · have hidx : Computable
            (fun p : ℕ × BitString × BitString => (bitStringToNat p.2.1).unpair.1) :=
          (Primrec.fst.comp (Primrec.unpair.comp
            (primrec_bitStringToNat.comp (Primrec.fst.comp Primrec.snd)))).to_comp
        have hstage : Primrec
            (fun p : ℕ × BitString × BitString => (bitStringToNat p.2.1).unpair.2) :=
          Primrec.snd.comp (Primrec.unpair.comp
            (primrec_bitStringToNat.comp (Primrec.fst.comp Primrec.snd)))
        have htest : Computable
            (fun p : ℕ × BitString × BitString =>
              decide ((bitStringToNat p.2.1).unpair.2 = 0)) :=
          (PrimrecPred.decide (PrimrecRel.comp Primrec.eq hstage (Primrec.const 0))).to_comp
        have hthen : Computable (fun p : ℕ × BitString × BitString =>
            A p.1 (natToBitString (bitStringToNat p.2.1).unpair.1) ([] : BitString)) :=
          hAc.comp (Computable.fst.pair
            ((computable_natToBitString.comp hidx).pair (Computable.const [])))
        refine (Computable.cond htest hthen (Computable.const 0)).of_eq (fun p => ?_)
        by_cases h : (bitStringToNat p.2.1).unpair.2 = 0 <;> simp [h]
  obtain ⟨c, hc, hdom⟩ := hm.dominates hsm
  refine ⟨c, hc, fun i => ?_⟩
  simpa using hdom (Nat.pair i 0)

/-- **New C11b leaf (SUV p. 167, "the sum in the right-hand side is lower semicomputable, so
it is `O(m(i))` due to maximality").** -/
theorem exists_const_tsum_aprioriPair_le {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∀ i, (∑' j, aprioriPair m i j) ≤ c * m i := by
  classical
  -- (heartbeat budget raised below; see the `set_option` before the docstring)
  obtain ⟨A, hAmono, hAsup, hAc⟩ := hm.isLowerSemicomputableSemimeasureNat.2
  have hdmono : ∀ n j : ℕ, Monotone
      (fun t : ℕ => dyadicValue (A t (natToBitString (Nat.pair n j)) []) t) :=
    fun n j => monotone_nat_of_le_succ (fun t => hAmono t _ [])
  have hdsup : ∀ n j : ℕ,
      (⨆ t : ℕ, dyadicValue (A t (natToBitString (Nat.pair n j)) []) t) = m (Nat.pair n j) := by
    intro n j
    simpa using hAsup (natToBitString (Nat.pair n j)) []
  -- the truncated stage sums converge to the row sum
  have hsup : ∀ n : ℕ, (⨆ s : ℕ, ∑ j ∈ Finset.range s,
      dyadicValue (A s (natToBitString (Nat.pair n j)) []) s) = ∑' j, m (Nat.pair n j) := by
    intro n
    calc (⨆ s : ℕ, ∑ j ∈ Finset.range s,
            dyadicValue (A s (natToBitString (Nat.pair n j)) []) s)
        = ⨆ s : ℕ, ⨆ t : ℕ, ∑ j ∈ Finset.range s,
            dyadicValue (A t (natToBitString (Nat.pair n j)) []) t := by
          refine le_antisymm (iSup_le fun s => le_iSup_of_le s (le_iSup_of_le s le_rfl)) ?_
          refine iSup_le fun s => iSup_le fun t => le_iSup_of_le (max s t) ?_
          refine le_trans (Finset.sum_le_sum
            (fun j _ => hdmono n j (le_max_right s t))) ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => Finset.mem_range.2
              (lt_of_lt_of_le (Finset.mem_range.1 hx) (le_max_left s t)))
            (fun _ _ _ => zero_le)
      _ = ⨆ s : ℕ, ∑ j ∈ Finset.range s, ⨆ t : ℕ,
            dyadicValue (A t (natToBitString (Nat.pair n j)) []) t :=
          iSup_congr fun s => (ENNReal.finsetSum_iSup_of_monotone (fun j => hdmono n j)).symm
      _ = ⨆ s : ℕ, ∑ j ∈ Finset.range s, m (Nat.pair n j) :=
          iSup_congr fun s => Finset.sum_congr rfl (fun j _ => hdsup n j)
      _ = ∑' j, m (Nat.pair n j) := ENNReal.tsum_eq_iSup_nat.symm
  have hsm : IsLowerSemicomputableSemimeasureNat (fun n => ∑' j, m (Nat.pair n j)) := by
    constructor
    · change (∑' x : BitString, ∑' j, m (Nat.pair (bitStringToNat x) j)) ≤ 1
      rw [tsum_comp_bitStringToNat (fun n => ∑' j, m (Nat.pair n j)),
        ← ENNReal.tsum_prod (f := fun n j => m (Nat.pair n j))]
      have hbij : (∑' p : ℕ × ℕ, m (Nat.pair p.1 p.2)) = ∑' k : ℕ, m k := by
        have h_eq : (∑' (p : ℕ × ℕ), m (Nat.pair p.1 p.2)) =
            ∑' (c : ℕ × ℕ), m (Nat.pairEquiv c) := rfl
        rw [h_eq]
        exact Nat.pairEquiv.tsum_eq m
      rw [hbij]
      exact hm.tsum_le_one
    · refine ⟨fun s x _ => ((List.range s).map
        (fun j => A s (natToBitString (Nat.pair (bitStringToNat x) j)) [])).sum, ?_, ?_, ?_⟩
      · intro s out _
        dsimp only
        rw [sum_list_range_eq_finset_sum', sum_list_range_eq_finset_sum', dyadicValue_sum_range,
          dyadicValue_sum_range]
        refine le_trans (Finset.sum_le_sum
          (fun j _ => hdmono (bitStringToNat out) j (Nat.le_succ s))) ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => Finset.mem_range.2
            (lt_of_lt_of_le (Finset.mem_range.1 hx) (Nat.le_succ s)))
          (fun _ _ _ => zero_le)
      · intro out _
        dsimp only
        have hfun : (fun s : ℕ => dyadicValue (((List.range s).map
              (fun j => A s (natToBitString (Nat.pair (bitStringToNat out) j)) [])).sum) s)
            = fun s : ℕ => ∑ j ∈ Finset.range s,
              dyadicValue (A s (natToBitString (Nat.pair (bitStringToNat out) j)) []) s :=
          funext fun s => by rw [sum_list_range_eq_finset_sum', dyadicValue_sum_range]
        simpa [hfun] using hsup (bitStringToNat out)
      · have hcode : Computable (fun q : (ℕ × BitString × BitString) × ℕ =>
            natToBitString (Nat.pair (bitStringToNat q.1.2.1) q.2)) :=
          (primrec_natToBitString.comp (Primrec₂.natPair.comp
            (primrec_bitStringToNat.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
            Primrec.snd)).to_comp
        -- `.of_eq (fun _ => rfl)` rather than a bare ascription: matching the `.comp` result
        -- against an annotated `Computable …` makes `whnf` unfold the `Primcodable` instances
        -- of `ℕ × BitString × BitString` (cf. the note in `CommonInformation/Relativized.lean`)
        have hbody : Computable₂ (fun (p : ℕ × BitString × BitString) (j : ℕ) =>
            A p.1 (natToBitString (Nat.pair (bitStringToNat p.2.1) j)) ([] : BitString)) :=
          (hAc.comp ((Computable.fst.comp Computable.fst).pair
            (hcode.pair (Computable.const ([] : BitString))))).of_eq (fun _ => rfl)
        exact primrec_listSum.to_comp.comp
          (Computable.list_map (Primrec.list_range.to_comp.comp Computable.fst) hbody)
  obtain ⟨c, hc, hdom⟩ := hm.dominates hsm
  have hc1pos : 0 < min c 1 := lt_min hc (by norm_num)
  have hc1top : min c 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  refine ⟨(min c 1)⁻¹, ENNReal.inv_pos.2 hc1top, ENNReal.inv_ne_top.2 hc1pos.ne', fun i => ?_⟩
  have hstep : min c 1 * (∑' j, m (Nat.pair i j)) ≤ m i :=
    le_trans (mul_le_mul_left (min_le_left _ _) _) (hdom i)
  have hkey : (∑' j, m (Nat.pair i j)) ≤ (min c 1)⁻¹ * m i := by
    calc (∑' j, m (Nat.pair i j))
        = (min c 1)⁻¹ * (min c 1 * ∑' j, m (Nat.pair i j)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc1pos.ne' hc1top, one_mul]
      _ ≤ (min c 1)⁻¹ * m i := mul_le_mul_right hstep _
  simpa using hkey

/-- **SUV p. 167, recalled in the proof of Theorem 112.** `m(i) = ∑ⱼ m(i,j)` up to an
`O(1)`-factor, where `m(i,j)` is the a priori probability of the pair `(i,j)`. -/
theorem exists_const_apriori_pair_marginal {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∀ i,
      c * m i ≤ (∑' j, aprioriPair m i j) ∧ (∑' j, aprioriPair m i j) ≤ c⁻¹ * m i := by
  obtain ⟨c₁, hc₁, h₁⟩ := exists_const_apriori_le_aprioriPair_zero hm
  obtain ⟨c₂, hc₂, hc₂top, h₂⟩ := exists_const_tsum_aprioriPair_le hm
  have hinvpos : 0 < c₂⁻¹ := ENNReal.inv_pos.2 hc₂top
  refine ⟨min c₁ (min c₂⁻¹ 1), lt_min hc₁ (lt_min hinvpos (by norm_num)),
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (min_le_right _ _) (min_le_right _ _)),
    fun i => ⟨?_, ?_⟩⟩
  · exact le_trans (le_trans (mul_le_mul_left (min_le_left _ _) _) (h₁ i)) (ENNReal.le_tsum 0)
  · refine le_trans (h₂ i) (mul_le_mul_left ?_ _)
    have hle : min c₁ (min c₂⁻¹ 1) ≤ c₂⁻¹ := le_trans (min_le_right _ _) (min_le_left _ _)
    have := ENNReal.inv_le_inv.2 hle
    rwa [inv_inv] at this

/-- If `aᵢⱼ/m(i,j) → 0` then `Aᵢ/m(i) → 0`. *Proof (SUV p. 167: "only finitely many pairs have
`aᵢⱼ > ε·m(i,j)`, and they appear only in finitely many groups").* Fix `ε > 0` and pick a
threshold `δ = 2^{-d}` strictly below `ε·c`, where `c` is the constant of
`exists_const_apriori_pair_marginal`. The bad pairs at `δ` form a finite set `S`; every
index outside the finite set `Prod.fst '' S` satisfies `aᵢⱼ < δ·m(i,j)` for **every** `j`,
hence `Aᵢ ≤ δ·∑ⱼ m(i,j) ≤ δ·c⁻¹·m(i) < ε·m(i)`. The frozen hypotheses `ha`, `h0` and `hfin`
are unused here: the source needs "only finitely many non-zero terms per group" for the
*hard* direction only (p. 167), and computability of `a` plays no role in either. They are
kept because the statement is frozen. The cancellation in the last step needs `m(i) ≠ 0`,
which the hypothesis itself supplies: if `m(i) = 0` then the marginal bound forces `m(i,j) =
0` for all `j`, and then the whole row `{i} × ℕ` would consist of bad pairs, contradicting
their finiteness.  SUV Theorem 112 (Section 5.7, p. 167), easy direction. -/
theorem ratioTendstoZero_group_of_pair {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    {a : ℕ → ℕ → ℚ} (_ha : Computable₂ a) (_h0 : ∀ i j, 0 ≤ a i j)
    (_hfin : ∀ i, {j : ℕ | a i j ≠ 0}.Finite)
    (h : ∀ ε : ℝ≥0∞, 0 < ε →
      {p : ℕ × ℕ | ε * aprioriPair m p.1 p.2 ≤ ENNReal.ofReal ((a p.1 p.2 : ℝ))}.Finite) :
    ∀ ε : ℝ≥0∞, 0 < ε →
      {i : ℕ | ε * m i ≤ ∑' j, ENNReal.ofReal ((a i j : ℝ))}.Finite := by
  intro ε hε
  obtain ⟨c, hc, hctop, hmarg⟩ := exists_const_apriori_pair_marginal hm
  obtain ⟨d, hd⟩ := ENNReal.exists_inv_two_pow_lt (ENNReal.mul_pos hε.ne' hc.ne').ne'
  set δ : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ d with hδdef
  have hδpos : 0 < δ := pos_iff_ne_zero.2 (pow_ne_zero _ (by simp))
  have hbad := h δ hδpos
  -- the threshold really is below `ε` after the marginal renormalisation
  have hδc : δ * c⁻¹ < ε := by
    have h1 : c⁻¹ * δ < c⁻¹ * (ε * c) :=
      ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.2 hctop)
        (ENNReal.inv_ne_top.2 hc.ne') hd
    have h2 : c⁻¹ * (ε * c) = ε := by
      rw [mul_comm ε c, ← mul_assoc, ENNReal.inv_mul_cancel hc.ne' hctop, one_mul]
    rw [h2, mul_comm] at h1
    exact h1
  -- the hypothesis forces every `m i` to be non-zero
  have hmne : ∀ i, m i ≠ 0 := by
    intro i hi
    have hz : ∀ j, aprioriPair m i j = 0 := by
      have hle : (∑' j, aprioriPair m i j) ≤ 0 := by
        have hmi := (hmarg i).2
        rwa [hi, mul_zero] at hmi
      exact fun j => le_antisymm (le_trans (ENNReal.le_tsum j) hle) (zero_le)
    have hsub : (Set.range (fun j : ℕ => ((i, j) : ℕ × ℕ))) ⊆
        {p : ℕ × ℕ | δ * aprioriPair m p.1 p.2 ≤ ENNReal.ofReal ((a p.1 p.2 : ℝ))} := by
      rintro _ ⟨j, rfl⟩
      simp only [Set.mem_ofPred_eq, hz j, mul_zero]
      exact zero_le
    exact hbad.not_infinite
      (Set.Infinite.mono hsub (Set.infinite_range_of_injective (fun j₁ j₂ hj => by simpa using hj)))
  refine Set.Finite.subset (hbad.image Prod.fst) ?_
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi
  by_contra hni
  have hall : ∀ j, ENNReal.ofReal ((a i j : ℝ)) < δ * aprioriPair m i j := by
    intro j
    by_contra hcon
    rw [not_lt] at hcon
    exact hni ⟨(i, j), hcon, rfl⟩
  have hsum : (∑' j, ENNReal.ofReal ((a i j : ℝ))) ≤ δ * c⁻¹ * m i := by
    calc (∑' j, ENNReal.ofReal ((a i j : ℝ))) ≤ ∑' j, δ * aprioriPair m i j :=
          ENNReal.tsum_le_tsum (fun j => (hall j).le)
      _ = δ * ∑' j, aprioriPair m i j := ENNReal.tsum_mul_left
      _ ≤ δ * (c⁻¹ * m i) := mul_le_mul_right (hmarg i).2 δ
      _ = δ * c⁻¹ * m i := by ring
  have hlt : δ * c⁻¹ * m i < ε * m i := by
    have h1 := ENNReal.mul_lt_mul_right (hmne i) (apriori_ne_top hm i) hδc
    rwa [mul_comm (m i) (δ * c⁻¹), mul_comm (m i) ε] at h1
  exact absurd hi (not_le.2 (lt_of_le_of_lt hsum hlt))

/-- If `Aᵢ/m(i) → 0` then `aᵢⱼ/m(i,j) → 0`. This is where the hypothesis that each group has
only finitely many non-zero terms is used.  SUV Theorem 112 (Section 5.7, p. 167), hard
direction. -/
theorem ratioTendstoZero_pair_of_group {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    {a : ℕ → ℕ → ℚ} (ha : Computable₂ a) (h0 : ∀ i j, 0 ≤ a i j)
    (hfin : ∀ i, {j : ℕ | a i j ≠ 0}.Finite)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → {i : ℕ | ε * m i ≤ ∑' j, ENNReal.ofReal ((a i j : ℝ))}.Finite) :
    ∀ ε : ℝ≥0∞, 0 < ε →
      {p : ℕ × ℕ | ε * aprioriPair m p.1 p.2 ≤ ENNReal.ofReal ((a p.1 p.2 : ℝ))}.Finite := by
  classical
  intro ε hε
  obtain ⟨μ, hμsm, hμdom⟩ := exists_cappedScaling hm ha h0
  obtain ⟨γ, hγpos, hγ⟩ := hm.dominates hμsm
  obtain ⟨n, hn⟩ :=
    exists_inv_two_pow_lt (ENNReal.mul_pos (ne_of_gt hε) (ne_of_gt hγpos)).ne'
  have hpow0 : (2 : ℝ≥0∞) ^ (2 * n + 1) ≠ 0 := by positivity
  have hpowt : (2 : ℝ≥0∞) ^ (2 * n + 1) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hbad := h ((2 : ℝ≥0∞) ^ (2 * n + 1))⁻¹ (ENNReal.inv_pos.2 hpowt)
  refine Set.Finite.subset (Set.Finite.biUnion hbad
    (fun i _ => (hfin i).image (fun j => ((i, j) : ℕ × ℕ)))) ?_
  rintro ⟨i, j⟩ hp
  simp only [Set.mem_ofPred_eq] at hp
  have hPpos : 0 < m (Nat.pair i j) := apriori_pos_of_universal hm _
  have hPtop : m (Nat.pair i j) ≠ ⊤ := apriori_ne_top hm _
  have hPeq : aprioriPair m i j = m (Nat.pair i j) := aprioriPair_eq m i j
  -- the term is nonzero
  have hanz : a i j ≠ 0 := by
    intro hz
    rw [hz] at hp
    simp only [Rat.cast_zero, ENNReal.ofReal_zero] at hp
    have : 0 < ε * aprioriPair m i j := by
      rw [hPeq]
      exact ENNReal.mul_pos (ne_of_gt hε) (ne_of_gt hPpos)
    exact absurd hp (not_le.2 this)
  -- and the group is one of the finitely many bad ones
  have hibad : i ∈ {i : ℕ | ((2 : ℝ≥0∞) ^ (2 * n + 1))⁻¹ * m i
      ≤ ∑' j, ENNReal.ofReal ((a i j : ℝ))} := by
    by_contra hi
    simp only [Set.mem_ofPred_eq, not_le] at hi
    have hAlt : (2 : ℝ≥0∞) ^ (2 * n + 1) * (∑' j', ENNReal.ofReal ((a i j' : ℚ) : ℝ)) < m i := by
      have hmul := ENNReal.mul_lt_mul_left hpow0 hpowt hi
      have hcancel : ((2 : ℝ≥0∞) ^ (2 * n + 1))⁻¹ * m i * (2 : ℝ≥0∞) ^ (2 * n + 1) = m i := by
        rw [mul_comm (((2 : ℝ≥0∞) ^ (2 * n + 1))⁻¹) (m i), mul_assoc,
          ENNReal.inv_mul_cancel hpow0 hpowt, mul_one]
      rw [hcancel] at hmul
      rwa [mul_comm]
    have h1 : (2 : ℝ≥0∞) ^ n * ENNReal.ofReal ((a i j : ℚ) : ℝ) ≤ μ (Nat.pair i j) :=
      hμdom n i j hAlt
    have h2 : γ * μ (Nat.pair i j) ≤ m (Nat.pair i j) := hγ _
    have h3 : γ * ((2 : ℝ≥0∞) ^ n * ENNReal.ofReal ((a i j : ℚ) : ℝ)) ≤ m (Nat.pair i j) :=
      le_trans (by gcongr) h2
    have h4 : γ * ((2 : ℝ≥0∞) ^ n * (ε * m (Nat.pair i j))) ≤ m (Nat.pair i j) := by
      refine le_trans ?_ h3
      gcongr
      rw [← hPeq]
      exact hp
    have h5 : (γ * (2 : ℝ≥0∞) ^ n * ε) * m (Nat.pair i j) ≤ 1 * m (Nat.pair i j) := by
      rw [one_mul]
      calc (γ * (2 : ℝ≥0∞) ^ n * ε) * m (Nat.pair i j)
          = γ * ((2 : ℝ≥0∞) ^ n * (ε * m (Nat.pair i j))) := by ring
        _ ≤ m (Nat.pair i j) := h4
    have h6 : γ * (2 : ℝ≥0∞) ^ n * ε ≤ 1 :=
      (ENNReal.mul_le_mul_iff_left (ne_of_gt hPpos) hPtop).1 h5
    -- but `2^{-n} < ε·γ` says the opposite
    have h7 : (1 : ℝ≥0∞) < ε * γ * (2 : ℝ≥0∞) ^ n := by
      have h8 : (2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞) ^ n = 1 := by
        rw [← ENNReal.inv_pow, ENNReal.inv_mul_cancel (by positivity)
          (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]
      calc (1 : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞) ^ n := h8.symm
        _ < ε * γ * (2 : ℝ≥0∞) ^ n :=
            ENNReal.mul_lt_mul_left (ne_of_gt (by positivity))
              (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hn
    have h9 : γ * (2 : ℝ≥0∞) ^ n * ε = ε * γ * (2 : ℝ≥0∞) ^ n := by ring
    rw [h9] at h6
    exact absurd h6 (not_le.2 h7)
  exact Set.mem_biUnion hibad ⟨j, hanz, rfl⟩

/-- Assume that each group `Aᵢ = ∑ⱼ aᵢⱼ` contains only finitely many non-zero terms. Then the
properties `Aᵢ/m(i) → 0` and `aᵢⱼ/m(i,j) → 0` are equivalent.  SUV Theorem 112 (Section 5.7,
p. 167). -/
theorem ratioTendstoZero_group_iff_pair {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    {a : ℕ → ℕ → ℚ} (ha : Computable₂ a) (h0 : ∀ i j, 0 ≤ a i j)
    (hfin : ∀ i, {j : ℕ | a i j ≠ 0}.Finite) :
    (∀ ε : ℝ≥0∞, 0 < ε → {i : ℕ | ε * m i ≤ ∑' j, ENNReal.ofReal ((a i j : ℝ))}.Finite) ↔
      (∀ ε : ℝ≥0∞, 0 < ε →
        {p : ℕ × ℕ | ε * aprioriPair m p.1 p.2 ≤ ENNReal.ofReal ((a p.1 p.2 : ℝ))}.Finite) :=
  ⟨ratioTendstoZero_pair_of_group hm ha h0 hfin, ratioTendstoZero_group_of_pair hm ha h0 hfin⟩

/-- **SUV p. 168, corollary of Theorem 112.** The Solovay property depends only on the
sum of the series: two computable series of nonnegative rationals with the same sum
have the Solovay property simultaneously. -/
theorem hasSolovayProperty_congr_of_sum_eq {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    {r r' : ℕ → ℚ} (hr : Computable r) (hr' : Computable r')
    (hr0 : ∀ i, 0 ≤ r i) (hr0' : ∀ i, 0 ≤ r' i) {α : ℝ}
    (hsum : Filter.Tendsto (fun n => (partialSums r n : ℝ)) Filter.atTop (nhds α))
    (hsum' : Filter.Tendsto (fun n => (partialSums r' n : ℝ)) Filter.atTop (nhds α)) :
    HasSolovayProperty m r ↔ HasSolovayProperty m r' := by
  rw [← isMartinLofRandomReal_iff_hasSolovayProperty hm hr hr0 hsum,
    ← isMartinLofRandomReal_iff_hasSolovayProperty hm hr' hr0' hsum']

/-! #### Flattening a double series (SUV p. 168, the step behind the strengthening) -/

/-- **Flattening along `Nat.pair` preserves the sum.**  If every group of a double series of
nonnegative rationals is a *finite* sum equal to `rᵢ`, and the partial sums of `∑ rᵢ`
converge to `α`, then so do the partial sums of the flattened series
`bₖ = a_{(k)₀,(k)₁}`. -/
theorem tendsto_partialSums_unpair {a : ℕ → ℕ → ℚ} (h0 : ∀ i j, 0 ≤ a i j) {r : ℕ → ℚ}
    (hgroup : ∀ i : ℕ, ∃ J : ℕ, ∀ K : ℕ, J ≤ K → ∑ j ∈ Finset.range (K + 1), a i j = r i)
    (hrow : ∀ (i J : ℕ), ∑ j ∈ Finset.range J, a i j ≤ r i)
    {α : ℝ} (hsum : Filter.Tendsto (fun n => (partialSums r n : ℝ)) Filter.atTop (nhds α)) :
    Filter.Tendsto (fun n => (partialSums (fun k => a k.unpair.1 k.unpair.2) n : ℝ))
      Filter.atTop (nhds α) := by
  classical
  set b : ℕ → ℚ := fun k => a k.unpair.1 k.unpair.2 with hb
  have hb0 : ∀ k, 0 ≤ b k := fun k => h0 _ _
  have hr0 : ∀ i, 0 ≤ r i := fun i => le_trans (by simp) (hrow i 0)
  have hbmono : Monotone (fun n : ℕ => ((partialSums b n : ℚ) : ℝ)) := by
    refine monotone_nat_of_le_succ fun n => ?_
    have hstep : partialSums b (n + 1) = partialSums b n + b n := by
      rw [partialSums, partialSums, Finset.sum_range_succ]
    have := hb0 n
    have hcast : ((partialSums b (n + 1) : ℚ) : ℝ)
        = ((partialSums b n : ℚ) : ℝ) + ((b n : ℚ) : ℝ) := by
      rw [hstep]; push_cast; ring
    have hbn : (0 : ℝ) ≤ ((b n : ℚ) : ℝ) := by exact_mod_cast hb0 n
    rw [hcast]
    linarith
  have hrmono : Monotone (fun n : ℕ => ((partialSums r n : ℚ) : ℝ)) := by
    refine monotone_nat_of_le_succ fun n => ?_
    have hstep : partialSums r (n + 1) = partialSums r n + r n := by
      rw [partialSums, partialSums, Finset.sum_range_succ]
    have hrn : (0 : ℝ) ≤ ((r n : ℚ) : ℝ) := by exact_mod_cast hr0 n
    have hcast : ((partialSums r (n + 1) : ℚ) : ℝ)
        = ((partialSums r n : ℚ) : ℝ) + ((r n : ℚ) : ℝ) := by
      rw [hstep]; push_cast; ring
    rw [hcast]
    linarith
  have hrle : ∀ n, ((partialSums r n : ℚ) : ℝ) ≤ α := hrmono.ge_of_tendsto hsum
  -- every partial sum of the flattened series is below a partial sum of `∑ rᵢ`
  have hinj : ∀ n : ℕ, Set.InjOn Nat.unpair (↑(Finset.range n) : Set ℕ) := by
    intro n x _ y _ hxy
    have hp := congrArg (fun p : ℕ × ℕ => Nat.pair p.1 p.2) hxy
    simpa [Nat.pair_unpair] using hp
  have hble : ∀ n : ℕ, partialSums b n ≤ partialSums r n := by
    intro n
    have himg : (Finset.range n).image Nat.unpair ⊆ Finset.range n ×ˢ Finset.range n := by
      intro p hp
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
      have hk' : k < n := Finset.mem_range.1 hk
      refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩
      · exact lt_of_le_of_lt (Nat.unpair_left_le k) hk'
      · exact lt_of_le_of_lt (Nat.unpair_right_le k) hk'
    calc partialSums b n = ∑ k ∈ Finset.range n, a (Nat.unpair k).1 (Nat.unpair k).2 := rfl
      _ = ∑ p ∈ (Finset.range n).image Nat.unpair, a p.1 p.2 := by
          rw [Finset.sum_image (hinj n)]
      _ ≤ ∑ p ∈ Finset.range n ×ˢ Finset.range n, a p.1 p.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun p _ _ => h0 p.1 p.2)
      _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, a i j :=
          Finset.sum_product (Finset.range n) (Finset.range n) (fun p => a p.1 p.2)
      _ ≤ ∑ i ∈ Finset.range n, r i := Finset.sum_le_sum (fun i _ => hrow i n)
      _ = partialSums r n := rfl
  have hbleα : ∀ n, ((partialSums b n : ℚ) : ℝ) ≤ α := by
    intro n
    have h1 : ((partialSums b n : ℚ) : ℝ) ≤ ((partialSums r n : ℚ) : ℝ) := by
      exact_mod_cast hble n
    exact le_trans h1 (hrle n)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨I, hI⟩ := Metric.tendsto_atTop.1 hsum ε hε
  have hIval := hI I le_rfl
  rw [Real.dist_eq, abs_lt] at hIval
  -- a common cut-off for the finitely many groups below `I`
  obtain ⟨Jf, hJf⟩ : ∃ Jf : ℕ, ∀ i ∈ Finset.range I,
      ∑ j ∈ Finset.range (Jf + 1), a i j = r i := by
    choose J hJ using hgroup
    refine ⟨(Finset.range I).sup J, fun i hi => ?_⟩
    exact hJ i _ (Finset.le_sup hi)
  set S : Finset (ℕ × ℕ) := Finset.range I ×ˢ Finset.range (Jf + 1) with hS
  set N : ℕ := (S.sup fun p => Nat.pair p.1 p.2) + 1 with hN
  have hsub : S.image (fun p : ℕ × ℕ => Nat.pair p.1 p.2) ⊆ Finset.range N := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hk
    exact Finset.mem_range.2 (Nat.lt_succ_of_le
      (Finset.le_sup (f := fun p : ℕ × ℕ => Nat.pair p.1 p.2) hp))
  have hpairinj : Set.InjOn (fun p : ℕ × ℕ => Nat.pair p.1 p.2) (↑S : Set (ℕ × ℕ)) := by
    intro x _ y _ hxy
    have hq := congrArg Nat.unpair hxy
    simpa [Nat.unpair_pair, Prod.ext_iff] using hq
  have hbig : partialSums r I ≤ partialSums b N := by
    calc partialSums r I = ∑ i ∈ Finset.range I, r i := rfl
      _ = ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range (Jf + 1), a i j :=
          (Finset.sum_congr rfl (fun i hi => hJf i hi)).symm
      _ = ∑ p ∈ S, a p.1 p.2 :=
          (Finset.sum_product (Finset.range I) (Finset.range (Jf + 1))
            (fun p => a p.1 p.2)).symm
      _ = ∑ k ∈ S.image (fun p : ℕ × ℕ => Nat.pair p.1 p.2), b k := by
          rw [Finset.sum_image hpairinj]
          exact Finset.sum_congr rfl (fun p _ => by simp [hb, Nat.unpair_pair])
      _ ≤ ∑ k ∈ Finset.range N, b k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hb0 k)
      _ = partialSums b N := rfl
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ((partialSums b N : ℚ) : ℝ) ≤ ((partialSums b n : ℚ) : ℝ) := hbmono hn
  have h2 : ((partialSums r I : ℚ) : ℝ) ≤ ((partialSums b N : ℚ) : ℝ) := by
    exact_mod_cast hbig
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith [hIval.1], by linarith [hbleα n]⟩

end Kolmogorov
