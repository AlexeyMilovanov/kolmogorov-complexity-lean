/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Lower.NullCovers
import KolmogorovMathlib.PointToSet.Pressure.Lower.PointwiseTails

/-!
# The point-to-set principle for lower pressure and lower entropy

This module proves the lower half of Main A of the point-to-set principle: for a pressure
datum `D` and any set `Z`, the classical lower pressure of `Z` is the minimum, over all
oracles `A`, of the supremum over `x ∈ Z` of the `A`-relative pointwise lower pressure, and
the minimum is attained on a whole upper cone of oracles.

* `pointwiseLower_le_of_effectiveNullCover` (blueprint node `pressure:code-null`): the
  relativized coding theorem turns an `A`-enumerable null cover of rational exponent `s`
  into the bound `K^A(i) ≤ s n - S_n φ(ι_i) + c` on the codes of its elements, hence into
  the bound `s` on the pointwise lower pressure of every covered point.
* `effectiveLowerPressure_eq_iSup_pointwise` (blueprint node
  `pressure:effective-lower-equality`): for admissible `A`, the effective lower pressure of
  `Z` is the supremum of the pointwise lower pressures over `Z`.
* `exists_oracle_effectiveLower_eq` and `exists_oracle_effectiveLower_eq_cone` (blueprint node
  `pressure:lower-attainment`): the countably many null covers of rational exponents above
  the lower pressure are encoded into one oracle; joined with an admissibility oracle, it
  makes the effective lower pressure equal to the classical one, and so does every stronger
  oracle.
* `lowerPressure_pointToSet`, `lowerPressure_pointToSet_all_oracles` and
  `lowerPressure_pointToSet_cone` (blueprint node `pressure:lower-pts`): the principle itself.
* `entropiesAndOrbitComplexities_attained`, `entropiesAndOrbitComplexities_rate`,
  `entropiesAndOrbitComplexities_lower_rate`, `entropiesAndOrbitComplexities_upper_rate` and
  the `entropiesAndOrbitComplexities_empty*` lemmas (blueprint node
  `pressure:entropy-definitions`): the orbit complexity is attained at a center of the Bowen
  ball, the zero-potential cost is its normalized natural shadow, and all four set entropies
  of the empty set vanish.

The results are used by the entropy characterizations, the packing equivalences, the Bowen
equations and the conformal dimension theorem.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-! ### Coding an effective null cover -/

/-- The canonical codes of the pairs `(i, n)` occurring in an enumerable set of triples
`(i, n, p)` form an enumerable set of bitstrings. -/
lemma isREIn_pairCode_image (A : Set ℕ) (E : Set (ℕ × ℕ × ℕ)) (hRE : IsREIn A E) :
    IsREIn A (fun w : BitString ↦ ∃ i n p : ℕ,
      w = pairCode (natBits i) (natBits n) ∧ (i, n, p) ∈ E) := by
  obtain ⟨e, he, henum⟩ := (relative_enumeration A E).mp hRE
  let code : (ℕ × ℕ × ℕ) → BitString := fun t ↦
    pairCode (natBits t.1) (natBits t.2.1)
  have hcode : Computable code :=
    Computable₂.comp pairCode_computable (natBits_computable.comp Computable.fst)
      (natBits_computable.comp (Computable.fst.comp Computable.snd))
  refine (relative_enumeration A _).mpr ⟨fun j ↦ (e j).map code, ?_, ?_⟩
  · have hm : Computable (fun o : Option (ℕ × ℕ × ℕ) ↦ o.map code) :=
      Computable.option_map Computable.id (hcode.comp Computable.snd).to₂
    exact hm.computableIn.comp he
  · intro w
    constructor
    · rintro ⟨i, n, p, rfl, ht⟩
      obtain ⟨j, hj⟩ := (henum (i, n, p)).mp ht
      exact ⟨j, by simp only [hj, Option.map_some, code]⟩
    · rintro ⟨j, hj⟩
      obtain ⟨t, ht, hw⟩ := Option.map_eq_some_iff.mp hj
      exact ⟨t.1, t.2.1, t.2.2, hw.symm, (henum t).mpr ⟨j, ht⟩⟩

/-- Admissibility supplies enumerable, sound, arbitrarily close rational upper bounds for the
decoded pressure cost `s n - S_n φ(ι_i)` of a coded pair `(i, n)` on any enumerable
bitstring domain. -/
theorem isUpperSemicomputableOnIn_decodedCost
    (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A)
    (s : ℚ) (F : BitString → Prop) (hF : IsREIn A F) :
    IsUpperSemicomputableOnIn A F (fun w ↦
      (s : ℝ) * decodeBits (decodeSecond w.val) -
        birkhoffSum D.T D.φ (decodeBits (decodeSecond w.val))
          (D.presentation.ι (decodeBits (decodeFirst w.val)))) := by
  let I : BitString → ℕ := fun w ↦ decodeBits (decodeFirst w)
  let J : BitString → ℕ := fun w ↦ decodeBits (decodeSecond w)
  let g : BitString → ℝ := fun w ↦
    (s : ℝ) * J w - birkhoffSum D.T D.φ (J w) (D.presentation.ι (I w))
  have hI : Computable I :=
    (primrec_decodeBits.comp CodedFiniteDistribution.decodeFirst_primrec).to_comp
  have hJ : Computable J :=
    (primrec_decodeBits.comp CodedFiniteDistribution.decodeSecond_primrec).to_comp
  obtain ⟨q, hq, hqerr⟩ :=
    birkhoff_computableIn D.presentation D.T (fun _ : Fin 1 => D.φ) A hA
  have hg : IsComputableRealFamilyIn A g := by
    refine ⟨fun wp ↦ s * (J wp.1 : ℚ) - q ((0, J wp.1, I wp.1), wp.2), ?_, ?_⟩
    · have hargs : Computable (fun wp : BitString × ℕ ↦
          (((0 : Fin 1), J wp.1, I wp.1), wp.2)) :=
        ((Computable.const (0 : Fin 1)).pair
          ((hJ.comp Computable.fst).pair (hI.comp Computable.fst))).pair Computable.snd
      have hlinear : Computable (fun wp : BitString × ℕ ↦ s * (J wp.1 : ℚ)) :=
        computable₂_ratMul.comp (Computable.const s)
          (computable_nat_to_rat.comp (hJ.comp Computable.fst))
      exact computable₂_ratSub.computableIn₂.comp
        hlinear.computableIn (hq.comp hargs.computableIn)
    · intro w m
      dsimp only [g]
      push_cast
      rw [show (s : ℝ) * (J w : ℝ) - (q ((0, J w, I w), m) : ℝ) -
          ((s : ℝ) * J w - birkhoffSum D.T D.φ (J w) (D.presentation.ι (I w))) =
          -((q ((0, J w, I w), m) : ℝ) -
            birkhoffSum D.T D.φ (J w) (D.presentation.ι (I w))) by ring, abs_neg]
      exact hqerr (0, J w, I w) m
  have hcut := birkhoff_computableIn_lt A g hg
  have hdom : IsREIn A (fun wq : BitString × ℚ ↦ F wq.1) := by
    obtain ⟨f, hf, hfd⟩ := hF
    exact ⟨fun wq ↦ f wq.1, hf.comp ComputableIn.fst, fun wq ↦ hfd wq.1⟩
  refine ⟨fun wq ↦ F wq.1 ∧ g wq.1 < (wq.2 : ℝ),
    IsREIn.and hdom hcut, ?_, ?_⟩
  · intro w q h
    exact ⟨h.1, h.2⟩
  · intro w ε hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right (g w.val) hε)
    exact ⟨q, ⟨w.property, hq1⟩, hq2⟩

/-- Choosing one covering triple for each canonical pair code gives an injection into the
cover, so the mass `∑ 2^(-(s n - S_n φ(ι_i)))` over the coded pairs is bounded by the mass
of the cover. -/
private lemma tsum_two_rpow_neg_cost_le_nullPressureMass
    (D : PressureData X) (s : ℚ) (E : Set (ℕ × ℕ × ℕ)) (F : BitString → Prop)
    (hF : ∀ w, F w → ∃ i n p : ℕ,
      w = pairCode (natBits i) (natBits n) ∧ (i, n, p) ∈ E)
    (g : BitString → ℝ)
    (hg : ∀ i n, g (pairCode (natBits i) (natBits n)) =
      (s : ℝ) * n - birkhoffSum D.T D.φ n (D.presentation.ι i)) :
    (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w.val)) ≤
      nullPressureMass D.presentation D.T D.φ s E := by
  classical
  choose i n p hw he using (fun w : Subtype F ↦ hF w.val w.property)
  let f : Subtype F → E := fun w ↦ ⟨(i w, n w, p w), he w⟩
  have hf : Function.Injective f := by
    intro u v huv
    have hi : i u = i v := congrArg (fun t : E ↦ t.val.1) huv
    have hn : n u = n v := congrArg (fun t : E ↦ t.val.2.1) huv
    apply Subtype.ext
    rw [hw u, hw v, hi, hn]
  have hterm : ∀ w : Subtype F, (2 : ℝ≥0∞) ^ (-g w.val) =
      (2 : ℝ≥0∞) ^ (-(s : ℝ) * (f w).val.2.1 +
        birkhoffSum D.T D.φ (f w).val.2.1 (D.presentation.ι (f w).val.1)) := by
    intro w
    rw [hw w, hg]
    dsimp only [f]
    congr 1
    ring
  calc
    (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w.val)) =
        ∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-(s : ℝ) * (f w).val.2.1 +
          birkhoffSum D.T D.φ (f w).val.2.1 (D.presentation.ι (f w).val.1)) :=
      tsum_congr hterm
    _ ≤ nullPressureMass D.presentation D.T D.φ s E :=
      ENNReal.tsum_comp_le_tsum_of_injective hf
        (fun t : E ↦ (2 : ℝ≥0∞) ^ (-(s : ℝ) * t.val.2.1 +
          birkhoffSum D.T D.φ t.val.2.1 (D.presentation.ι t.val.1)))

/-- Coding an `A`-enumerable null cover of finite mass: the complexity of every center index
is bounded by its cost `s n - S_n φ(ι_i)` up to one additive constant. -/
private lemma exists_oracleNatComplexity_le_cost (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A) (s : ℚ)
    (E : Set (ℕ × ℕ × ℕ)) (hE_mass : nullPressureMass D.presentation D.T D.φ s E < ⊤)
    (hRE : IsREIn A E) :
    ∃ c : ℕ, ∀ t ∈ E, (oracleNatComplexity A t.1 : ℝ) ≤
      (s : ℝ) * t.2.1 - birkhoffSum D.T D.φ t.2.1 (D.presentation.ι t.1) + c := by
  let F : BitString → Prop := fun w ↦ ∃ i n p : ℕ,
    w = pairCode (natBits i) (natBits n) ∧ (i, n, p) ∈ E
  let g : BitString → ℝ := fun w ↦ (s : ℝ) * decodeBits (decodeSecond w) -
    birkhoffSum D.T D.φ (decodeBits (decodeSecond w))
      (D.presentation.ι (decodeBits (decodeFirst w)))
  have hF : IsREIn A F := isREIn_pairCode_image A E hRE
  have hg : IsUpperSemicomputableOnIn A F (fun w ↦ g w.val) :=
    isUpperSemicomputableOnIn_decodedCost D A hA s F hF
  have hgeval : ∀ i n, g (pairCode (natBits i) (natBits n)) =
      (s : ℝ) * n - birkhoffSum D.T D.φ n (D.presentation.ι i) := by
    intro i n
    simp only [g, decodeFirst_pairCode, decodeSecond_pairCode, natBits, decodeBits_natBits]
  have hmass := tsum_two_rpow_neg_cost_le_nullPressureMass D s E F (fun _ hw ↦ hw) g hgeval
  obtain ⟨c, hc⟩ := oracle_coding_finite_mass A F (fun w ↦ g w.val) hg
    (nullPressureMass D.presentation D.T D.φ s E) hmass hE_mass
  obtain ⟨d, hd⟩ := oracle_tuple_bounds A
  refine ⟨c + d, fun t ht ↦ ?_⟩
  have hw : F (pairCode (natBits t.1) (natBits t.2.1)) :=
    ⟨t.1, t.2.1, t.2.2, rfl, ht⟩
  have hcode := hc ⟨pairCode (natBits t.1) (natBits t.2.1), hw⟩
  change (oracleComplexity A (pairCode (natBits t.1) (natBits t.2.1)) : ℝ) ≤
    g (pairCode (natBits t.1) (natBits t.2.1)) + c at hcode
  rw [hgeval] at hcode
  have hproj : (oracleNatComplexity A t.1 : ℝ) ≤
      (oracleComplexity A (pairCode (natBits t.1) (natBits t.2.1)) : ℝ) + d := by
    exact_mod_cast hd t.1 t.2.1
  push_cast
  linarith

/-- A center index inside the Bowen ball bounds the finite-scale rate by its normalized
cost `(K^A(i) + S_n φ(ι_i)) / n`. -/
private lemma finiteScalePressureRate_le_of_mem_bowenBall (P : Presentation X) (T : X → X)
    (φ : X → ℝ) (A : Set ℕ) {x : X} {n : ℕ} (hn : n ≠ 0) {r : ℝ} {i : ℕ}
    (hi : P.ι i ∈ bowenBall T n x r) :
    finiteScalePressureRate P T φ A x n r ≤
      (((oracleNatComplexity A i + birkhoffSum T φ n (P.ι i)) / n : ℝ) : EReal) := by
  simp only [finiteScalePressureRate, hn, ↓reduceIte]
  exact iInf₂_le i hi

/-- Coding an effective rational-exponent null cover bounds every covered point's pressure.
Blueprint node `pressure:code-null`. -/
theorem pointwiseLower_le_of_effectiveNullCover (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A) (Z : Set X) (s : ℚ)
    (E : Set (ℕ × ℕ × ℕ)) (hE : IsNullPressureCover D.presentation D.T D.φ D.p₀ Z s E)
    (hRE : IsREIn A E) (x : X) (hx : x ∈ Z) :
    (pointwisePressure D.presentation D.T D.φ A x).1 ≤ ((s : ℝ) : EReal) := by
  obtain ⟨-, hE_mass, hE_cover⟩ := hE
  obtain ⟨c, hc⟩ := exists_oracleNatComplexity_le_cost D A hA s E hE_mass hRE
  rw [pointwisePressure_eq_tail]
  refine iSup₂_le fun p hp ↦ ?_
  have hfreq : ∃ᶠ n in atTop, ∃ i, (i, n, p) ∈ E ∧
      x ∈ bowenBall D.T n (D.presentation.ι i) (dyadicRadius p) := by
    rw [frequently_atTop]
    intro a
    obtain ⟨i, n, hn, hi, hxi⟩ := hE_cover p hp (max 1 a) (le_max_left 1 a) x hx
    exact ⟨n, (le_max_right 1 a).trans hn, i, hi, hxi⟩
  have hle : ∃ᶠ n in atTop,
      finiteScalePressureRate D.presentation D.T D.φ A x n (dyadicRadius p) ≤
        (((s : ℝ) + (c : ℝ) / n : ℝ) : EReal) := by
    refine (hfreq.and_eventually (eventually_gt_atTop 0)).mono ?_
    rintro n ⟨⟨i, hiE, hxi⟩, hn0⟩
    refine (finiteScalePressureRate_le_of_mem_bowenBall D.presentation D.T D.φ A hn0.ne'
      (mem_bowenBall_symm hxi)).trans (EReal.coe_le_coe_iff.mpr ?_)
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
    have hcost := hc (i, n, p) hiE
    dsimp only at hcost
    calc ((oracleNatComplexity A i : ℝ) + birkhoffSum D.T D.φ n (D.presentation.ι i)) / n
        ≤ ((s : ℝ) * n + c) / n := div_le_div_of_nonneg_right (by linarith) hn_pos.le
      _ = (s : ℝ) + c / n := by field_simp
  have hlim : Tendsto (fun n : ℕ ↦ (((s : ℝ) + (c : ℝ) / n : ℝ) : EReal)) atTop
      (𝓝 ((s : ℝ) : EReal)) := by
    refine EReal.tendsto_coe.mpr ?_
    simpa only [add_zero] using
      tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))
  exact (liminf_le_limsup_of_frequently_le hle).trans hlim.limsup_eq.le

/-! ### Effective lower pressure equals the pointwise supremum -/

/-- If a statement `b ≤ q` holds for every rational `q` above `a`, then `b ≤ a`. -/
private lemma le_of_forall_rat_lt_imp_le {a b : EReal}
    (h : ∀ q : ℚ, a < ((q : ℝ) : EReal) → b ≤ ((q : ℝ) : EReal)) : b ≤ a := by
  by_contra hba
  obtain ⟨q, haq, hqb⟩ := EReal.exists_rat_btwn_of_lt (lt_of_not_ge hba)
  exact (not_lt_of_ge (h q haq)) hqb

/-- The pointwise supremum is a lower bound for the effective lower pressure: an effective
null cover of exponent `s` bounds every pointwise pressure by `s`, using a rational exponent
between the supremum and `s`. -/
private theorem iSup_pointwisePressure_le_effectiveLowerPressure
    (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A) (Z : Set X) :
    (⨆ x ∈ Z, (pointwisePressure D.presentation D.T D.φ A x).1) ≤
      effectiveLowerPressure D.presentation D.T D.φ D.p₀ A Z := by
  unfold effectiveLowerPressure
  refine le_iInf fun s ↦ le_iInf fun E ↦ le_iInf fun hE ↦ ?_
  by_contra hs
  obtain ⟨q, hsq, hq⟩ := EReal.exists_rat_btwn_of_lt (lt_of_not_ge hs)
  have hsq' : s < (q : ℝ) := EReal.coe_lt_coe_iff.mp hsq
  have hmass : nullPressureMass D.presentation D.T D.φ (q : ℝ) E ≤
      nullPressureMass D.presentation D.T D.φ s E := by
    unfold nullPressureMass
    refine ENNReal.tsum_le_tsum fun t ↦ ?_
    apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
    have hn : 0 ≤ (t.val.2.1 : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hcover : IsNullPressureCover D.presentation D.T D.φ D.p₀ Z (q : ℝ) E :=
    ⟨hE.1.1, hmass.trans_lt hE.1.2.1, hE.1.2.2⟩
  exact (not_le.mpr hq) (iSup₂_le fun x hx ↦
    pointwiseLower_le_of_effectiveNullCover D A hA Z q E hcover hE.2 x hx)

/-- For admissible `A`, the effective lower pressure of the sublevel set of the pointwise
pressure below a rational `s` is at most `s`: the threshold cover is enumerable. -/
private lemma effectiveLowerPressure_sublevel_le
    (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A) (s : ℚ) :
    effectiveLowerPressure D.presentation D.T D.φ D.p₀ A
      {x | (pointwisePressure D.presentation D.T D.φ A x).1 < ((s : ℝ) : EReal)} ≤
        ((s : ℝ) : EReal) := by
  refine iInf_le_of_le (s : ℝ) ?_
  refine iInf_le_of_le (lowerPressureThreshold D.presentation D.T D.φ D.p₀ A s) ?_
  exact iInf_le_of_le
    ⟨lowerThreshold_isNullCover D A hA s, lowerThreshold_isNullCover_re D A hA s⟩ le_rfl

/-- For admissible `A`, the effective lower pressure is at most the pointwise supremum: for
each rational above the supremum, `Z` lies in the corresponding sublevel set. -/
private theorem effectiveLowerPressure_le_iSup_pointwisePressure
    (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A) (Z : Set X) :
    effectiveLowerPressure D.presentation D.T D.φ D.p₀ A Z ≤
      (⨆ x ∈ Z, (pointwisePressure D.presentation D.T D.φ A x).1) := by
  refine le_of_forall_rat_lt_imp_le fun q hq ↦ ?_
  refine (effectiveLowerPressure_mono D A Z _ ?_).trans
    (effectiveLowerPressure_sublevel_le D A hA q)
  intro x hx
  exact (le_iSup₂ (f := fun x _ ↦ (pointwisePressure D.presentation D.T D.φ A x).1)
    x hx).trans_lt hq

/-- Effective lower pressure equals the pointwise supremum for admissible oracles.
Blueprint node `pressure:effective-lower-equality`. -/
theorem effectiveLowerPressure_eq_iSup_pointwise (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A) (Z : Set X) :
    effectiveLowerPressure D.presentation D.T D.φ D.p₀ A Z =
      ⨆ x ∈ Z, (pointwisePressure D.presentation D.T D.φ A x).1 :=
  le_antisymm (effectiveLowerPressure_le_iSup_pointwisePressure D A hA Z)
    (iSup_pointwisePressure_le_effectiveLowerPressure D A hA Z)

/-! ### Attaining the lower pressure by an oracle -/

/-- Choosing, for every rational exponent above the lower pressure, a null cover of `Z`. -/
private lemma exists_nullPressureCover_family (D : PressureData X) (Z : Set X) :
    ∃ E : ℚ → Set (ℕ × ℕ × ℕ), ∀ q : ℚ, lowerPressure D.T D.φ D.p₀ Z < ((q : ℝ) : EReal) →
      IsNullPressureCover D.presentation D.T D.φ D.p₀ Z (q : ℝ) (E q) := by
  have h_choose (q : ℚ) : ∃ E, (lowerPressure D.T D.φ D.p₀ Z < ((q : ℝ) : EReal) →
      IsNullPressureCover D.presentation D.T D.φ D.p₀ Z (q : ℝ) E) := by
    by_cases hq : lowerPressure D.T D.φ D.p₀ Z < ((q : ℝ) : EReal)
    · obtain ⟨E, hE⟩ := exists_nullCover_of_lowerPressure_lt D Z (q : ℝ) hq
      exact ⟨E, fun _ ↦ hE⟩
    · exact ⟨∅, fun h ↦ (hq h).elim⟩
  choose E hE using h_choose
  exact ⟨E, hE⟩

/-- Joining the codes of countably many null covers with an admissibility oracle gives an
admissible oracle relative to which every cover is enumerable. -/
private lemma exists_admissible_isREIn_covers (D : PressureData X)
    (E : ℚ → Set (ℕ × ℕ × ℕ)) :
    ∃ B : Set ℕ, IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) B ∧
      ∀ q : ℚ, IsREIn B (E q) := by
  let E_nat : ℕ → Set ℕ := fun j ↦ Encodable.encode '' (E (Denumerable.ofNat ℚ j))
  obtain ⟨C, hC⟩ := exists_admissible_base D.presentation D.T D.continuous_T
    (fun _ : Fin 1 => D.φ) (fun _ ↦ D.uniformContinuous_φ.continuous)
  refine ⟨oracleJoin (oracleCountableJoin E_nat) C,
    hC _ (oracle_joins_right (oracleCountableJoin E_nat) C), fun q ↦ ?_⟩
  let j := @Encodable.encode ℚ Rat.instDenumerable.toEncodable q
  have h_red : TuringReducible (charOracle (E_nat j))
      (charOracle (oracleJoin (oracleCountableJoin E_nat) C)) :=
    TuringReducible.trans (oracle_joins_countable E_nat j)
      (oracle_joins (oracleCountableJoin E_nat) C)
  have hRE : IsREIn (E_nat j) (E (Denumerable.ofNat ℚ j)) :=
    isREIn_encode_image (E (Denumerable.ofNat ℚ j))
  rw [show Denumerable.ofNat ℚ j = q from Denumerable.ofNat_encode q] at hRE
  exact hRE.mono_oracle h_red

/-- If a family of null covers at the rational exponents above the lower pressure is
enumerable relative to `B`, the effective lower pressure relative to `B` is at most the
classical lower pressure. -/
private lemma effectiveLowerPressure_le_lowerPressure_of_isREIn_covers
    (D : PressureData X) (Z : Set X) (E : ℚ → Set (ℕ × ℕ × ℕ))
    (hE : ∀ q : ℚ, lowerPressure D.T D.φ D.p₀ Z < ((q : ℝ) : EReal) →
      IsNullPressureCover D.presentation D.T D.φ D.p₀ Z (q : ℝ) (E q))
    (B : Set ℕ) (hB : ∀ q : ℚ, IsREIn B (E q)) :
    effectiveLowerPressure D.presentation D.T D.φ D.p₀ B Z ≤ lowerPressure D.T D.φ D.p₀ Z := by
  refine le_of_forall_rat_lt_imp_le fun q hq ↦ ?_
  rw [effectiveLowerPressure]
  refine iInf_le_of_le (q : ℝ) (iInf_le_of_le (E q) ?_)
  exact iInf_le_of_le ⟨hE q hq, hB q⟩ le_rfl

/-- Some admissible oracle makes effective and classical lower pressure equal.
Blueprint node `pressure:lower-attainment`. -/
theorem exists_oracle_effectiveLower_eq (D : PressureData X) (Z : Set X) :
    ∃ B : Set ℕ, IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) B ∧
      effectiveLowerPressure D.presentation D.T D.φ D.p₀ B Z =
        lowerPressure D.T D.φ D.p₀ Z := by
  obtain ⟨E, hE⟩ := exists_nullPressureCover_family D Z
  obtain ⟨B, hB1, hB2⟩ := exists_admissible_isREIn_covers D E
  exact ⟨B, hB1, le_antisymm
    (effectiveLowerPressure_le_lowerPressure_of_isREIn_covers D Z E hE B hB2)
    (effectiveLowerPressure_ge D B Z)⟩

/-- One admissible base oracle attains equality throughout its upper cone.
Blueprint node `pressure:lower-attainment`. -/
theorem exists_oracle_effectiveLower_eq_cone (D : PressureData X) (Z : Set X) :
    ∃ B : Set ℕ, ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
      IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A ∧
      effectiveLowerPressure D.presentation D.T D.φ D.p₀ A Z =
        lowerPressure D.T D.φ D.p₀ Z := by
  obtain ⟨C, hC⟩ := exists_admissible_base D.presentation D.T D.continuous_T
    (fun _ : Fin 1 => D.φ) (fun _ ↦ D.uniformContinuous_φ.continuous)
  obtain ⟨B', -, hB'⟩ := exists_oracle_effectiveLower_eq D Z
  refine ⟨oracleJoin C B', fun A hA ↦ ⟨hC A (TuringReducible.trans (oracle_joins C B') hA),
    le_antisymm ?_ (effectiveLowerPressure_ge D A Z)⟩⟩
  rw [← hB']
  exact effectiveLowerPressure_mono_oracle D B' A
    (TuringReducible.trans (oracle_joins_right C B') hA) Z

/-! ### The point-to-set principle -/

/-- Every oracle gives a pointwise supremum at least the classical lower pressure.
Blueprint node `pressure:lower-pts`. -/
theorem lowerPressure_pointToSet_all_oracles (D : PressureData X) (Z : Set X) (A : Set ℕ) :
    lowerPressure D.T D.φ D.p₀ Z ≤
      ⨆ x ∈ Z, (pointwisePressure D.presentation D.T D.φ A x).1 := by
  obtain ⟨B, hB⟩ := exists_oracle_effectiveLower_eq_cone D Z
  obtain ⟨hC_adm, hC_eq⟩ := hB (oracleJoin A B) (oracle_joins_right A B)
  rw [← hC_eq, effectiveLowerPressure_eq_iSup_pointwise D _ hC_adm Z]
  exact iSup₂_mono fun x _ ↦ pointwisePressure_mono_oracle D A _ (oracle_joins A B) x

/-- The lower point-to-set infimum is attained on an entire upper cone.
Blueprint node `pressure:lower-pts`. -/
theorem lowerPressure_pointToSet_cone (D : PressureData X) (Z : Set X) :
    ∃ B : Set ℕ, ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
      lowerPressure D.T D.φ D.p₀ Z =
        ⨆ x ∈ Z, (pointwisePressure D.presentation D.T D.φ A x).1 := by
  obtain ⟨B, hB⟩ := exists_oracle_effectiveLower_eq_cone D Z
  refine ⟨B, fun A hA ↦ ?_⟩
  obtain ⟨h_adm, h_eq⟩ := hB A hA
  rw [← h_eq]
  exact effectiveLowerPressure_eq_iSup_pointwise D A h_adm Z

/-- The lower point-to-set infimum ranges over all oracles.
Blueprint node `pressure:lower-pts`. -/
theorem lowerPressure_pointToSet (D : PressureData X) (Z : Set X) :
    lowerPressure D.T D.φ D.p₀ Z =
      ⨅ A : Set ℕ, ⨆ x ∈ Z, (pointwisePressure D.presentation D.T D.φ A x).1 := by
  obtain ⟨B, hB⟩ := lowerPressure_pointToSet_cone D Z
  exact le_antisymm (le_iInf fun A ↦ lowerPressure_pointToSet_all_oracles D Z A)
    ((iInf_le _ B).trans (hB B (TuringReducible.refl _)).ge)

/-! ### Orbit complexities and entropies -/

/-- Orbit complexity is finite and attained without any oracle admissibility assumption.
Blueprint node `pressure:entropy-definitions`. -/
theorem entropiesAndOrbitComplexities_attained (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (x : X) (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    ∃ i, P.ι i ∈ bowenBall T n x r ∧
      orbitComplexity P T A x n r = (oracleNatComplexity A i : ENat) := by
  obtain ⟨i₀, hi₀⟩ := bowen_ball_dense P T hT x n hn r hr
  let S : Set ℕ := {i | P.ι i ∈ bowenBall T n x r}
  have hS : S.Nonempty := ⟨i₀, hi₀⟩
  refine ⟨Function.argminOn (oracleNatComplexity A) S hS,
    Function.argminOn_mem _ S hS, le_antisymm (iInf₂_le _ (Function.argminOn_mem _ S hS)) ?_⟩
  refine le_iInf₂ fun j hj ↦ ?_
  exact_mod_cast Function.argminOn_le (oracleNatComplexity A) S hj

/-- At positive orders the frozen BS cost for potential one is the normalized natural
orbit complexity. Blueprint node `pressure:entropy-definitions`. -/
theorem entropiesAndOrbitComplexities_rate (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (x : X) (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    finiteScaleBSCost P T (fun _ => 1) A x n r =
      (orbitComplexityNat P T A x n r : ℝ≥0∞) / n := by
  obtain ⟨i₀, hi₀_ball, hi₀_eq⟩ := entropiesAndOrbitComplexities_attained P T hT A x n hn r hr
  have hsum : ∀ y : X, birkhoffSum T (fun _ ↦ (1 : ℝ)) n y = n := by
    intro y
    simp only [birkhoffSum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  obtain ⟨i₁, hi₁_ball, hi₁_eq⟩ := finite_scale_min_attained_ratio P T hT (fun _ ↦ 1) A x n hn
    r hr 1 n zero_lt_one fun i _ ↦ by
      rw [hsum]
      exact ⟨by exact_mod_cast hn, le_rfl⟩
  rw [hi₁_eq, hsum, orbitComplexityNat, hi₀_eq, ENat.toNat_natCast, ENNReal.ofReal_natCast]
  have h_bound : oracleNatComplexity A i₀ ≤ oracleNatComplexity A i₁ := by
    have h_inf : orbitComplexity P T A x n r ≤ (oracleNatComplexity A i₁ : ENat) :=
      iInf₂_le i₁ hi₁_ball
    rw [hi₀_eq] at h_inf
    exact WithTop.coe_le_coe.mp h_inf
  refine le_antisymm ?_ (ENNReal.div_le_div (by exact_mod_cast h_bound) le_rfl)
  have H_val : finiteScaleBSCost P T (fun _ ↦ 1) A x n r ≤
      (oracleNatComplexity A i₀ : ℝ≥0∞) / n := by
    have hn_ne : n ≠ 0 := by omega
    have H_cond : (0 : ℝ) < birkhoffSum T (fun _ ↦ 1) n (P.ι i₀) := by
      rw [hsum]
      exact_mod_cast (by omega : 0 < n)
    simp only [finiteScaleBSCost, hn_ne, ↓reduceIte]
    refine iInf_le_of_le i₀ (iInf_le_of_le hi₀_ball (iInf_le_of_le H_cond ?_))
    rw [hsum, ENNReal.ofReal_natCast]
  rwa [hi₁_eq, hsum, ENNReal.ofReal_natCast] at H_val

/-- The lower orbit rate has the blueprint's natural-complexity liminf formula.
Blueprint node `pressure:entropy-definitions`. -/
theorem entropiesAndOrbitComplexities_lower_rate (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (x : X) :
    (orbitComplexities P T A x).1 = ⨆ p : ℕ,
      liminf (fun n => (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ≥0∞) / n)
        atTop := by
  dsimp only [orbitComplexities, pointwiseBSDimension]
  congr 1
  ext p
  apply Filter.liminf_congr
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩] with n hn
  exact entropiesAndOrbitComplexities_rate P T hT A x n hn (dyadicRadius p)
    (by dsimp only [dyadicRadius]; positivity)

/-- The upper orbit rate has the corresponding natural-complexity limsup formula.
Blueprint node `pressure:entropy-definitions`. -/
theorem entropiesAndOrbitComplexities_upper_rate (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (x : X) :
    (orbitComplexities P T A x).2 = ⨆ p : ℕ,
      limsup (fun n => (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ≥0∞) / n)
        atTop := by
  dsimp only [orbitComplexities, pointwiseBSDimension]
  congr 1
  ext p
  apply Filter.limsup_congr
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩] with n hn
  exact entropiesAndOrbitComplexities_rate P T hT A x n hn (dyadicRadius p)
    (by dsimp only [dyadicRadius]; positivity)

/-! ### Entropies of the empty set -/

/-- The empty set has zero lower content at every order: the empty Bowen cover costs nothing. -/
private lemma lowerContent_empty (T : X → X) (s r : ℝ) (N : ℕ) :
    lowerContent T (fun _ ↦ 0) .centered ∅ s r N = 0 := by
  dsimp only [lowerContent]
  refine le_antisymm ?_ bot_le
  let C : BowenCoverFamily X :=
    { index := ∅
      center := fun j ↦ j.2.elim
      order := fun j ↦ j.2.elim }
  have hC : IsBowenCover T ∅ r N C := ⟨fun j ↦ j.2.elim, fun x hx ↦ hx.elim⟩
  have hc : bowenCoverCost T (fun _ ↦ 0) .centered s r C = 0 := by
    dsimp only [bowenCoverCost]
    exact ENNReal.tsum_eq_zero.mpr fun j ↦ j.2.elim
  exact iInf_le_of_le C (iInf_le_of_le hC hc.le)

/-- The empty set has zero lower content limit at every exponent and scale. -/
private lemma lowerContentLimit_empty (T : X → X) (s r : ℝ) :
    lowerContentLimit T (fun _ ↦ 0) .centered ∅ s r = 0 := by
  dsimp only [lowerContentLimit]
  simp [lowerContent_empty]

/-- Classical lower entropy gives zero to the empty set.
Blueprint node `pressure:entropy-definitions`. -/
theorem entropiesAndOrbitComplexities_empty (T : X → X) : lowerEntropy T ∅ = 0 := by
  rw [lowerEntropy]
  have h_limit : ∀ p s, lowerContentLimit T (fun _ => 0) .centered ∅ s (dyadicRadius p) = 0 :=
    fun p s ↦ lowerContentLimit_empty T s (dyadicRadius p)
  simp_rw [h_limit]
  refine le_antisymm ?_ bot_le
  refine iSup_le fun p ↦ ?_
  refine iInf_le_of_le 0 ?_
  refine iInf_le_of_le le_rfl ?_
  refine iInf_le_of_le trivial ?_
  exact ENNReal.ofReal_zero.le

/-- The empty family is a uniform net of the empty set at every exponent: all its slice
sums vanish, so the logarithmic rates are `⊥`. -/
private lemma isUniformPressureNet_empty (P : Presentation X) (T : X → X) (s : ℝ) :
    IsUniformPressureNet P T (fun _ => 0) 0 ∅ s ∅ := by
  refine ⟨fun t ht ↦ (Set.notMem_empty t ht).elim, fun p _ k ↦ ?_,
    fun p _ x hx ↦ (Set.notMem_empty x hx).elim⟩
  have hrate : pressureRate (fun n ↦ uniformPressureSum P T (fun _ ↦ 0) ∅ n p k) =
      fun _ ↦ ⊥ := by
    funext n
    by_cases hn : n = 0
    · simp only [pressureRate, hn, ↓reduceIte]
    · have hsum : uniformPressureSum P T (fun _ ↦ 0) ∅ n p k = 0 := by
        simp [uniformPressureSum]
      have hlog : (0 : EReal) < ((Real.log 2)⁻¹ : ℝ) :=
        EReal.coe_pos.mpr (inv_pos.mpr (Real.log_pos one_lt_two))
      have hinv : (0 : EReal) < ((n : ℝ)⁻¹ : ℝ) :=
        EReal.coe_pos.mpr (inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))
      simp only [pressureRate, hn, ↓reduceIte, hsum, pressureLog, ENNReal.log_zero]
      rw [EReal.bot_mul_of_pos hlog, EReal.bot_mul_of_pos hinv]
  rw [hrate]
  exact limsup_const_bot.trans_le bot_le

/-- Classical upper entropy gives zero to the empty set.
Blueprint node `pressure:entropy-definitions`. -/
theorem entropiesAndOrbitComplexities_empty_upper (P : Presentation X) (T : X → X) :
    upperEntropy P T ∅ = 0 := by
  dsimp only [upperEntropy]
  refine le_antisymm ?_ bot_le
  refine iInf_le_of_le 0 ?_
  refine iInf_le_of_le le_rfl ?_
  refine iInf_le_of_le ∅ ?_
  refine iInf_le_of_le (isUniformPressureNet_empty P T 0) ?_
  simp

/-- Effective lower entropy of the empty set is zero for every oracle.
Blueprint node `pressure:entropy-definitions`. -/
theorem entropiesAndOrbitComplexities_empty_effective_lower (P : Presentation X)
    (T : X → X) (A : Set ℕ) : effectiveLowerEntropy P T A ∅ = 0 := by
  dsimp only [effectiveLowerEntropy]
  refine le_antisymm ?_ bot_le
  refine iInf_le_of_le 0 ?_
  refine iInf_le_of_le le_rfl ?_
  refine iInf_le_of_le ∅ ?_
  have hmass : nullPressureMass P T (fun _ ↦ 0) 0 ∅ = 0 := by
    unfold nullPressureMass
    exact tsum_empty
  refine iInf_le_of_le ⟨⟨fun t ht ↦ (Set.notMem_empty t ht).elim,
    hmass ▸ ENNReal.zero_lt_top, fun _ _ _ _ x hx ↦ (Set.notMem_empty x hx).elim⟩,
    isREIn_empty A⟩ ?_
  simp

/-- Effective upper entropy of the empty set is zero for every oracle.
Blueprint node `pressure:entropy-definitions`. -/
theorem entropiesAndOrbitComplexities_empty_effective_upper (P : Presentation X)
    (T : X → X) (A : Set ℕ) : effectiveUpperEntropy P T A ∅ = 0 := by
  dsimp only [effectiveUpperEntropy]
  refine le_antisymm ?_ bot_le
  refine iInf_le_of_le 0 ?_
  refine iInf_le_of_le le_rfl ?_
  refine iInf_le_of_le ∅ ?_
  refine iInf_le_of_le ⟨isUniformPressureNet_empty P T 0, isREIn_empty A⟩ ?_
  simp

end Kolmogorov.PointToSet
