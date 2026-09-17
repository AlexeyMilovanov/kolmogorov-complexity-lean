/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint.GapCover
import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint.MapTotality
import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint

/-!
# The interval construction preserves measure (SUV Theorem 121, p. 177)

This module proves the two identities that SUV's sentence

> "The computability of the measure guarantees that effectively null sets with
> respect to `μ₁` correspond to the effectively null sets with respect to the
> uniform measure, therefore we get a bijection between the sets of ML-random
> sequences with respect to corresponding measures." (p. 177)

rests on, namely that the two interval maps of Theorem 121 push each measure
forward to the other:

* `measure_prefixHitSet_invArithGraph` --
  `μ (prefixHitSet {x | invArithGraph μ x p}) = cantorMass uniformMeasure p`;
* `uniformMeasure_prefixHitSet_arithmeticCodingLowerGraph` --
  `uniformMeasure (prefixHitSet {p | arithmeticCodingLowerGraph μ p x}) = cantorMass μ x`.

Both are instances of one statement about a computable atomless probability
measure `ν` and a window `(α, β) ⊆ [0,1]` whose two endpoints are denoted by no
positive-mass set of sequences:

* `measure_prefixHitSet_treeWindowSet` --
  `ν (prefixHitSet (treeWindowSet ν α β)) = ENNReal.ofReal (β - α)`,

where `treeWindowSet ν α β` is the set of strings whose closed interval `π_x`
sits strictly inside `(α, β)`.  The `≤` half is the antichain-plus-Lebesgue
bound of `Dimension/DyadicEndpoint.lean`, restated for a window with arbitrary
real endpoints (the dyadicity of the window is only ever needed for
enumerability, `isRE_treeGapSet`, never for the mass bound).  The `≥` half is a
complementation argument, which is what lets the module avoid the *ordering* of
the same-length cells that the library does not have: instead of summing the
cells left of `α` one bounds the two tails

* `measure_setOf_measureReal_lt_le` -- `ν {w | r(w) < α} ≤ ofReal α`,
* `measure_setOf_lt_measureReal_le` -- `ν {w | β < r(w)} ≤ ofReal (1 - β)`,

each again by the antichain bound, and subtracts them from `ν(Ω) = 1`; the two
endpoint fibres `{r = α}`, `{r = β}` are null by the endpoint tests of
`Dimension/DyadicEndpoint.lean`, whose measure-zero readings are
`measure_setOf_measureReal_eq_div_two_pow` and
`measure_setOf_measureReal_eq_treeEnd` below.

The dyadic side (`invArithGraph`) uses the window `(k/2^n, (k+1)/2^n)`; the
uniform side (`arithmeticCodingLowerGraph`) uses the window
`(L_μ(x), L_μ(x) + μ(Ω_x))`, whose endpoints are *not* dyadic -- which is
exactly why the real-window generalisation is needed.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ## Windows with arbitrary real endpoints -/

/-- The strings `x` whose closed interval `π_x` lies strictly inside the real
window `(α, β)`.  This is `treeGapSet` with the two dyadic endpoints replaced by
arbitrary reals and without the shift by `1`, which was only there to keep the
numerators natural. -/
def treeWindowSet (ν : Measure CantorSeq) (α β : ℝ) : Set BitString :=
  {x : BitString | α < treeLeftEnd (cantorMass ν) x ∧
    treeLeftEnd (cantorMass ν) x + (cantorMass ν x).toReal < β}

/-- Strings in the window set have their whole arithmetic interval inside `(α, β)`. -/
lemma treeIco_subset_Ioo_of_mem_treeWindowSet {ν : Measure CantorSeq} {α β : ℝ} {x : BitString}
    (hx : x ∈ treeWindowSet ν α β) : treeIco (cantorMass ν) x ⊆ Set.Ioo α β := by
  intro r hr
  rw [treeIco, Set.mem_Ico] at hr
  exact ⟨lt_of_lt_of_le hx.1 hr.1, lt_trans hr.2 hx.2⟩

/-- **The `≤` half.**  `measure_prefixHitSet_treeGapSet_le` for a window with
arbitrary real endpoints: the prefix-minimal elements form an antichain, so their
half-open intervals are pairwise disjoint subsets of `(α, β)`, and Lebesgue
measure on the line bounds the sum of their lengths. -/
theorem measure_prefixHitSet_treeWindowSet_le (ν : Measure CantorSeq) [IsProbabilityMeasure ν]
    (α β : ℝ) :
    ν (prefixHitSet (treeWindowSet ν α β)) ≤ ENNReal.ofReal (β - α) := by
  refine le_trans (measure_prefixHitSet_le_tsum_minimalPrefixElements ν _) ?_
  exact tsum_cantorMass_le_of_antichain ν _ (minimalPrefixElements_antichain _)
    (fun x hx => treeIco_subset_Ioo_of_mem_treeWindowSet (minimalPrefixElements_subset _ hx))

/-! ## The two tails -/

/-- A sequence whose real is below `α` has a prefix whose whole interval is below
`α`: the right endpoints of its prefixes decrease to that real.  Atomlessness is
what makes the right endpoints converge. -/
lemma setOf_measureReal_lt_subset (ν : Measure CantorSeq) [IsProbabilityMeasure ν]
    (haν : ∀ u : CantorSeq, ν {u} = 0) (α : ℝ) :
    {w : CantorSeq | measureReal ν w < α}
      ⊆ prefixHitSet {x : BitString |
          treeLeftEnd (cantorMass ν) x + (cantorMass ν x).toReal < α} := by
  intro w hw
  obtain ⟨n, hn⟩ :=
    ((tendsto_treeRightEnd_measureReal ν (haν w)).eventually_lt_const hw).exists
  exact ⟨n, hn⟩

/-- The left tail of the real is at most as heavy as its length. -/
lemma measure_setOf_measureReal_lt_le (ν : Measure CantorSeq) [IsProbabilityMeasure ν]
    (haν : ∀ u : CantorSeq, ν {u} = 0) (α : ℝ) :
    ν {w : CantorSeq | measureReal ν w < α} ≤ ENNReal.ofReal α := by
  have hsub : ∀ x ∈ minimalPrefixElements {x : BitString |
        treeLeftEnd (cantorMass ν) x + (cantorMass ν x).toReal < α},
      treeIco (cantorMass ν) x ⊆ Set.Ico (0 : ℝ) α := by
    intro x hx
    rw [treeIco]
    exact Set.Ico_subset_Ico (treeLeftEnd_nonneg _ _)
      (le_of_lt (minimalPrefixElements_subset _ hx))
  have h := tsum_cantorMass_le_of_antichain_Ico ν _ (minimalPrefixElements_antichain _) hsub
  rw [sub_zero] at h
  exact le_trans (measure_mono (setOf_measureReal_lt_subset ν haν α))
    (le_trans (measure_prefixHitSet_le_tsum_minimalPrefixElements ν _) h)

/-- A sequence whose real is above `β` has a prefix whose interval starts above
`β`: the left endpoints of its prefixes increase to that real. -/
lemma setOf_lt_measureReal_subset (ν : Measure CantorSeq) [IsProbabilityMeasure ν] (β : ℝ) :
    {w : CantorSeq | β < measureReal ν w}
      ⊆ prefixHitSet {x : BitString | β < treeLeftEnd (cantorMass ν) x} := by
  intro w hw
  obtain ⟨n, hn⟩ := ((tendsto_treeLeftEnd_measureReal ν w).eventually_const_lt hw).exists
  exact ⟨n, hn⟩

/-- The right tail of the real is at most as heavy as its length. -/
lemma measure_setOf_lt_measureReal_le (ν : Measure CantorSeq) [IsProbabilityMeasure ν] (β : ℝ) :
    ν {w : CantorSeq | β < measureReal ν w} ≤ ENNReal.ofReal (1 - β) := by
  have hsub : ∀ x ∈ minimalPrefixElements {x : BitString | β < treeLeftEnd (cantorMass ν) x},
      treeIco (cantorMass ν) x ⊆ Set.Ico β 1 := by
    intro x hx
    rw [treeIco]
    exact Set.Ico_subset_Ico (le_of_lt (minimalPrefixElements_subset _ hx))
      (treeRightEnd_cantorMass_le_one ν x)
  have h := tsum_cantorMass_le_of_antichain_Ico ν _ (minimalPrefixElements_antichain _) hsub
  exact le_trans (measure_mono (setOf_lt_measureReal_subset ν β))
    (le_trans (measure_prefixHitSet_le_tsum_minimalPrefixElements ν _) h)

/-! ## The window mass is exactly the window length -/

/-- **The measure-preservation lemma.**  For a computable atomless probability
measure the sequences having a prefix whose interval sits strictly inside
`(α, β) ⊆ [0,1]` have mass exactly `β - α`, provided the two endpoint fibres
`{w | r(w) = α}` and `{w | r(w) = β}` are null.

The `≤` half is `measure_prefixHitSet_treeWindowSet_le`.  For `≥`: a sequence
whose real lies strictly inside the window has such a prefix, because its
intervals shrink onto that real; and the complement of `{α < r < β}` is covered
by the two tails and the two endpoint fibres, of total mass at most
`α + (1 - β)`. -/
theorem measure_prefixHitSet_treeWindowSet (ν : Measure CantorSeq) [IsProbabilityMeasure ν]
    (haν : ∀ u : CantorSeq, ν {u} = 0) {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1)
    (h0 : ν {w : CantorSeq | measureReal ν w = α} = 0)
    (h1 : ν {w : CantorSeq | measureReal ν w = β} = 0) :
    ν (prefixHitSet (treeWindowSet ν α β)) = ENNReal.ofReal (β - α) := by
  refine le_antisymm (measure_prefixHitSet_treeWindowSet_le ν α β) ?_
  have hsub : {w : CantorSeq | α < measureReal ν w ∧ measureReal ν w < β}
      ⊆ prefixHitSet (treeWindowSet ν α β) := by
    intro w hw
    have e1 := (tendsto_treeLeftEnd_measureReal ν w).eventually_const_lt hw.1
    have e2 := (tendsto_treeRightEnd_measureReal ν (haν w)).eventually_lt_const hw.2
    obtain ⟨n, hn1, hn2⟩ := (e1.and e2).exists
    exact ⟨n, hn1, hn2⟩
  refine le_trans ?_ (measure_mono hsub)
  have hcover : (Set.univ : Set CantorSeq)
      ⊆ {w : CantorSeq | measureReal ν w < α} ∪ {w : CantorSeq | measureReal ν w = α}
        ∪ {w : CantorSeq | α < measureReal ν w ∧ measureReal ν w < β}
        ∪ {w : CantorSeq | measureReal ν w = β} ∪ {w : CantorSeq | β < measureReal ν w} := by
    intro w _
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rcases lt_trichotomy (measureReal ν w) α with h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · rcases lt_trichotomy (measureReal ν w) β with h2 | h2 | h2
      · exact Or.inl (Or.inl (Or.inr ⟨h, h2⟩))
      · exact Or.inl (Or.inr h2)
      · exact Or.inr h2
  have hunion : ν (Set.univ : Set CantorSeq)
      ≤ ν {w : CantorSeq | measureReal ν w < α} + ν {w : CantorSeq | measureReal ν w = α}
        + ν {w : CantorSeq | α < measureReal ν w ∧ measureReal ν w < β}
        + ν {w : CantorSeq | measureReal ν w = β}
        + ν {w : CantorSeq | β < measureReal ν w} := by
    refine le_trans (measure_mono hcover) ?_
    refine le_trans (measure_union_le _ _) (add_le_add ?_ (le_refl _))
    refine le_trans (measure_union_le _ _) (add_le_add ?_ (le_refl _))
    refine le_trans (measure_union_le _ _) (add_le_add ?_ (le_refl _))
    exact measure_union_le _ _
  rw [measure_univ, h0, h1] at hunion
  have hCle : (1 : ℝ≥0∞)
      ≤ ν {w : CantorSeq | α < measureReal ν w ∧ measureReal ν w < β}
        + (ENNReal.ofReal α + ENNReal.ofReal (1 - β)) := by
    have hA := measure_setOf_measureReal_lt_le ν haν α
    have hE := measure_setOf_lt_measureReal_le ν β
    calc (1 : ℝ≥0∞)
        ≤ ν {w : CantorSeq | measureReal ν w < α} + 0
            + ν {w : CantorSeq | α < measureReal ν w ∧ measureReal ν w < β} + 0
            + ν {w : CantorSeq | β < measureReal ν w} := hunion
      _ = ν {w : CantorSeq | α < measureReal ν w ∧ measureReal ν w < β}
            + (ν {w : CantorSeq | measureReal ν w < α}
              + ν {w : CantorSeq | β < measureReal ν w}) := by ring
      _ ≤ ν {w : CantorSeq | α < measureReal ν w ∧ measureReal ν w < β}
            + (ENNReal.ofReal α + ENNReal.ofReal (1 - β)) := by gcongr
  have hXne : ENNReal.ofReal α + ENNReal.ofReal (1 - β) ≠ ⊤ := by
    simp [ENNReal.add_eq_top]
  have hadd1 : ENNReal.ofReal α + ENNReal.ofReal (1 - β)
      = ENNReal.ofReal (α + (1 - β)) := (ENNReal.ofReal_add hα (by linarith)).symm
  have hadd2 : ENNReal.ofReal (β - α) + ENNReal.ofReal (α + (1 - β))
      = ENNReal.ofReal ((β - α) + (α + (1 - β))) :=
    (ENNReal.ofReal_add (by linarith) (by linarith)).symm
  have harith : (β - α) + (α + (1 - β)) = 1 := by ring
  have hkey : ENNReal.ofReal (β - α) + (ENNReal.ofReal α + ENNReal.ofReal (1 - β)) = 1 := by
    rw [hadd1, hadd2, harith, ENNReal.ofReal_one]
  refine ENNReal.le_of_add_le_add_right hXne ?_
  rw [hkey]
  exact hCle

/-! ## The endpoint fibres are null

The measure-zero readings of the two endpoint tests of `DyadicEndpoint.lean`.
Both are the corresponding computable approximation fed to
`measure_setOf_measureReal_eq_eq_zero` instead of to
`measureReal_ne_of_computable_approx`. -/

/-- **The dyadic fibres are null.**  `k/2^m` is approximated by the numerators
`⌊k·2^s/2^m⌋` to within one unit (division algorithm). -/
theorem measure_setOf_measureReal_eq_div_two_pow (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) (haμ : ∀ v : CantorSeq, μ {v} = 0)
    (m k : ℕ) : μ {w : CantorSeq | measureReal μ w = (k : ℝ) / 2 ^ m} = 0 := by
  refine measure_setOf_measureReal_eq_eq_zero μ hμ haμ _ 1 (fun s => k * 2 ^ s / 2 ^ m)
    (Primrec.nat_div.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const k)
        (primrec_two_pow_aux.to_comp.comp Computable.id))
      (Computable.const (2 ^ m))) (fun s => ?_)
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

/-- **The endpoint fibres of another computable measure's intervals are null.**
The measure-zero reading of `measureReal_ne_treeEnd_of_isMartinLofRandom`. -/
theorem measure_setOf_measureReal_eq_treeEnd (ν μ : Measure CantorSeq)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (hν : IsComputableMeasure ν)
    (haν : ∀ u : CantorSeq, ν {u} = 0) (hμ : IsComputableMeasure μ) (x : BitString) :
    ν {w : CantorSeq | measureReal ν w = treeLeftEnd (cantorMass μ) x} = 0 ∧
      ν {w : CantorSeq | measureReal ν w
        = treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal} = 0 := by
  obtain ⟨a, ha_comp, ha⟩ := hμ
  constructor
  · refine measure_setOf_measureReal_eq_eq_zero ν hν haν _ x.length
      (fun s => treeLeftEndApprox a x s) ((computable_treeLeftEndApprox ha_comp).comp
        (Computable.const x) Computable.id) (fun s => ?_)
    exact abs_treeLeftEndApprox_sub_le μ ha x s
  · refine measure_setOf_measureReal_eq_eq_zero ν hν haν _ (x.length + 1)
      (fun s => treeLeftEndApprox a x s + a x s)
      (Primrec.nat_add.to_comp.comp
        ((computable_treeLeftEndApprox ha_comp).comp (Computable.const x) Computable.id)
        (ha_comp.comp (Computable.const x) Computable.id)) (fun s => ?_)
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

/-! ## The two measure-preservation identities -/

/-- Every sequence has a prefix in the set of all strings. -/
lemma prefixHitSet_univ : prefixHitSet (Set.univ : Set BitString) = Set.univ := by
  ext w
  exact ⟨fun _ => Set.mem_univ _, fun _ => ⟨0, Set.mem_univ _⟩⟩

/-- The step of the uniform tree: the right endpoint of the dyadic cell of `p`. -/
lemma treeLeftEnd_lengthMeasure_add (p : BitString) :
    (devBitsToNat p : ℝ) / 2 ^ p.length + ((2 : ℝ)⁻¹) ^ p.length
      = ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length := by
  rw [inv_pow]
  field_simp

/-- **SUV Theorem 121, p. 177: the map `ω ↦ r(ω)` pushes `μ` to the uniform
measure.**  The set of `μ`-names whose interval sits strictly inside the dyadic
cell of `p` is the window set of the window `(k/2^n, (k+1)/2^n)`, so its mass is
that window's length `2^{-n} = uniform(Ω_p)`. -/
theorem measure_prefixHitSet_invArithGraph (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (hμ : IsComputableMeasure μ) (haμ : ∀ v : CantorSeq, μ {v} = 0) (p : BitString) :
    μ (prefixHitSet {x : BitString | invArithGraph μ x p}) = cantorMass uniformMeasure p := by
  rcases eq_or_ne p [] with rfl | hp
  · have hset : {x : BitString | invArithGraph μ x ([] : BitString)} = Set.univ := by
      ext x
      simp [invArithGraph]
    rw [hset, prefixHitSet_univ, measure_univ, cantorMass_uniformMeasure]
    simp
  · have hpos : (0 : ℝ) < 2 ^ p.length := by positivity
    have hval : ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length - (devBitsToNat p : ℝ) / 2 ^ p.length
        = ((2 : ℝ)⁻¹) ^ p.length := by
      rw [inv_pow]
      field_simp
      ring
    have hset : {x : BitString | invArithGraph μ x p}
        = treeWindowSet μ ((devBitsToNat p : ℝ) / 2 ^ p.length)
            (((devBitsToNat p : ℝ) + 1) / 2 ^ p.length) := by
      ext x
      simp only [Set.mem_ofPred_eq, treeWindowSet]
      exact invArithGraph_iff_endpoints μ x p hp
    have hα : (0 : ℝ) ≤ (devBitsToNat p : ℝ) / 2 ^ p.length := by positivity
    have hαβ : (devBitsToNat p : ℝ) / 2 ^ p.length
        ≤ ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length := by
      rw [← sub_nonneg, hval]
      positivity
    have hβ : ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length ≤ 1 := by
      rw [div_le_one hpos]
      have hlt : devBitsToNat p + 1 ≤ 2 ^ p.length := bitsToNat_lt p
      exact_mod_cast hlt
    have hz0 := measure_setOf_measureReal_eq_div_two_pow μ hμ haμ p.length (devBitsToNat p)
    have hz1 : μ {w : CantorSeq |
        measureReal μ w = ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length} = 0 := by
      have h := measure_setOf_measureReal_eq_div_two_pow μ hμ haμ p.length (devBitsToNat p + 1)
      push_cast at h
      exact h
    rw [hset, measure_prefixHitSet_treeWindowSet μ haμ hα hαβ hβ hz0 hz1, hval,
      ofReal_inv_two_pow, cantorMass_uniformMeasure]

/-- **SUV Theorem 121, p. 177: the map `r ↦ the μ-name of r` pushes the uniform
measure to `μ`.**  The set of dyadic cells sitting strictly inside `π_x` is the
window set, *at the uniform measure*, of the window
`(L_μ(x), L_μ(x) + μ(Ω_x))`; its two endpoints are not dyadic, which is why the
real-window form of the lemma is needed. -/
theorem uniformMeasure_prefixHitSet_arithmeticCodingLowerGraph (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) (x : BitString) :
    uniformMeasure (prefixHitSet {p : BitString | arithmeticCodingLowerGraph μ p x})
      = cantorMass μ x := by
  rcases eq_or_ne x [] with rfl | hx
  · have hset : {p : BitString | arithmeticCodingLowerGraph μ p ([] : BitString)} = Set.univ := by
      ext p
      simp [arithmeticCodingLowerGraph]
    rw [hset, prefixHitSet_univ, measure_univ, (isContinuousTreeSemimeasure_cantorMass μ).1]
  · have hset : {p : BitString | arithmeticCodingLowerGraph μ p x}
        = treeWindowSet uniformMeasure (treeLeftEnd (cantorMass μ) x)
            (treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal) := by
      ext p
      rw [Set.mem_ofPred_eq, arithmeticCodingLowerGraph_iff_endpoints μ p x hx]
      simp only [treeWindowSet, Set.mem_ofPred_eq, cantorMass_uniformMeasure_eq_lengthMeasure,
        treeLeftEnd_lengthMeasure_eq_div, lengthMeasure_toReal, treeLeftEnd_lengthMeasure_add]
    obtain ⟨hz0, hz1⟩ := measure_setOf_measureReal_eq_treeEnd uniformMeasure μ
      isComputableMeasure_uniform uniformMeasure_singleton hμ x
    rw [hset, measure_prefixHitSet_treeWindowSet uniformMeasure uniformMeasure_singleton
      (treeLeftEnd_nonneg _ _) (le_add_of_nonneg_right ENNReal.toReal_nonneg)
      (treeRightEnd_cantorMass_le_one μ x) hz0 hz1, add_sub_cancel_left]
    exact ENNReal.ofReal_toReal (measure_ne_top μ _)

end Kolmogorov
