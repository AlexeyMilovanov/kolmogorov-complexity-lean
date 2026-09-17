/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.ArithmeticCoding
import KolmogorovMathlib.MonotoneComplexity.StreamGapFill

/-!
# The interval construction `π_x` as a computable stream map

SUV Theorem 121 (§5.9.1, pp. 176-177) proves that the ML-random sequences of two
computable atomless measures are in a computable bijection, by splitting `[0,1]`
into the intervals `π_x` of length `μ(Ω_x)` and reading a sequence as the real
number that is the common point of the `π_{(ω)_n}`.

The interval family `π_x` and the *decoding* half of that correspondence are
already in the library: `arithmeticCodingLowerGraph μ p x` (`ArithmeticCoding.lean`)
says that the dyadic interval of `p` sits inside the interior of `π_x`, and it is
proved there to be a stream lower graph (`arithmeticCodingLowerGraph_isStreamLowerGraph`)
and recursively enumerable for a computable measure (`arithmeticCodingLowerGraph_isRE`).

This module packages that relation as an actual **computable stream map**
`arithMap μ : BitStream → BitStream` in the sense of SUV §5.4.1, using
`streamMapOfLowerGraph` and the gap-filling realisation of `StreamGapFill.lean`,
and records its defining specification.  `arithMap μ` is the map "read the input
bits as a real number `r ∈ [0,1]` and print the `μ`-name of `r`", i.e. the map
`[0,1] → Ω` of the source's proof, and it is what SUV Theorem 121's uniform case
needs in the direction *uniform → μ*.

The opposite direction, `ω ↦ r(ω)`, and the transfer of randomness in both
directions are still open; see §(k) of the C12 design document for the
decomposition.
-/

namespace Kolmogorov

open MeasureTheory

open scoped ENNReal

/-- The arithmetic-coding relation of a probability measure is consistent, hence
gap-fillable. -/
lemma arithmeticCodingLowerGraph_isConsistentStreamRelation (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] :
    IsConsistentStreamRelation (arithmeticCodingLowerGraph μ) :=
  (arithmeticCodingLowerGraph_isStreamLowerGraph μ).isConsistentStreamRelation

/-- **The interval construction `π_x` of SUV Theorem 121 as a stream map.**  On an
input stream `p` (read as a real number `r ∈ [0,1]`) it prints the longest string
`x` whose interval `π_x` contains the dyadic interval of `p`. -/
noncomputable def arithMap (μ : Measure CantorSeq) [IsProbabilityMeasure μ] :
    BitStream → BitStream :=
  streamMapOfLowerGraph (streamGapFill (arithmeticCodingLowerGraph μ))
    (streamGapFill_isStreamLowerGraph
      (arithmeticCodingLowerGraph_isConsistentStreamRelation μ))

/-- **`arithMap μ` is a computable stream map** for a computable probability
measure `μ`. -/
theorem isComputableStreamMap_arithMap (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (hμ : IsComputableMeasure μ) : IsComputableStreamMap (arithMap μ) :=
  streamMapOfLowerGraph_streamGapFill_isComputableStreamMap
    (arithmeticCodingLowerGraph_isConsistentStreamRelation μ)
    (arithmeticCodingLowerGraph_isRE μ hμ)

/-- The lower graph of `arithMap μ` is exactly the arithmetic-coding relation: on
a finite input `p` the map prints exactly those `x` with
`binaryClosedInterval p ⊆ interior π_x`. -/
theorem streamLowerGraph_arithMap (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (p x : BitString) :
    streamLowerGraph (arithMap μ) p x ↔ arithmeticCodingLowerGraph μ p x := by
  rw [streamLowerGraph, arithMap,
    streamMapOfLowerGraph_finite_spec
      (streamGapFill_isStreamLowerGraph (arithmeticCodingLowerGraph_isConsistentStreamRelation μ))]
  exact streamGapFill_eq_self (arithmeticCodingLowerGraph_isStreamLowerGraph μ) p x

/-- On an infinite input the map prints exactly the strings that some finite
approximation already forces. -/
theorem streamLowerGraph_arithMap_infinite (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (w : CantorSeq) (x : BitString) :
    BitStream.finite x ≤ arithMap μ (.infinite w) ↔
      ∃ n, arithmeticCodingLowerGraph μ (cantorPrefix w n) x := by
  rw [arithMap,
    streamMapOfLowerGraph_infinite_spec
      (streamGapFill_isStreamLowerGraph (arithmeticCodingLowerGraph_isConsistentStreamRelation μ))]
  exact exists_congr fun n =>
    streamGapFill_eq_self (arithmeticCodingLowerGraph_isStreamLowerGraph μ) _ x


/-! ## The reverse direction: from a `μ`-name to the real number it denotes -/

/-- The **closed** interval allocated to `x` by a tree semimeasure.  For
`lengthMeasure` this is `binaryClosedInterval`; the closed interval is the right
object on the *input* side of an arithmetic-coding relation, because the relation
has to be monotone in the input and the closure is what survives a degenerate
(measure-zero) cylinder. -/
noncomputable def treeIcc (a : BitString → ℝ≥0∞) (x : BitString) : Set ℝ :=
  Set.Icc (treeLeftEnd a x) (treeLeftEnd a x + (a x).toReal)

/-- For the length measure, the closed tree interval of a string is its binary cell. -/
lemma binaryClosedInterval_eq_treeIcc (p : BitString) :
    binaryClosedInterval p = treeIcc lengthMeasure p := rfl

/-- Closed tree intervals are nonempty. -/
lemma treeIcc_nonempty (a : BitString → ℝ≥0∞) (x : BitString) : (treeIcc a x).Nonempty :=
  ⟨treeLeftEnd a x, Set.left_mem_Icc.2 (le_add_of_nonneg_right ENNReal.toReal_nonneg)⟩

/-- The half-open tree interval is contained in the closed one. -/
lemma treeIco_subset_treeIcc (a : BitString → ℝ≥0∞) (x : BitString) :
    treeIco a x ⊆ treeIcc a x := Set.Ico_subset_Icc_self

/-- The closed interval of a child is contained in that of its parent. -/
lemma treeIcc_append_subset {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a)
    (x : BitString) (b : Bool) : treeIcc a (x ++ [b]) ⊆ treeIcc a x := by
  have hsum := ha.toReal_children_le x
  have h0 : (0 : ℝ) ≤ (a (x ++ [false])).toReal := ENNReal.toReal_nonneg
  have h1 : (0 : ℝ) ≤ (a (x ++ [true])).toReal := ENNReal.toReal_nonneg
  cases b
  · rw [treeIcc, treeIcc, treeLeftEnd_append_false]
    exact Set.Icc_subset_Icc le_rfl (by linarith)
  · rw [treeIcc, treeIcc, treeLeftEnd_append_true]
    exact Set.Icc_subset_Icc (by linarith) (by linarith)

/-- The closed interval of an extension is contained in that of the prefix. -/
lemma treeIcc_prefix_subset {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a)
    {x y : BitString} (h : x <+: y) : treeIcc a y ⊆ treeIcc a x := by
  obtain ⟨z, rfl⟩ := h
  induction z using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton z b ih =>
      rw [← List.append_assoc]
      exact (treeIcc_append_subset ha (x ++ z) b).trans ih

/-- **The reverse arithmetic-coding relation.**  From a `μ`-name `x` it prints the
binary digits of the real `r(x)` that the interval `π_x` already determines: the
dyadic interval of the output must contain the whole closed interval `π_x` in its
interior.  This is the map `ω ↦ r(ω)` of SUV Theorem 121, in the direction
*`μ` → uniform*. -/
def invArithGraph (μ : Measure CantorSeq) (x p : BitString) : Prop :=
  p = [] ∨ treeIcc (cantorMass μ) x ⊆ interior (treeIco lengthMeasure p)

/-- The reverse relation is a stream lower graph.  Only the order structure is
used, so no computability and no atomlessness is needed here. -/
lemma invArithGraph_isStreamLowerGraph (μ : Measure CantorSeq) [IsProbabilityMeasure μ] :
    IsStreamLowerGraph (invArithGraph μ) := by
  have hlen := lengthMeasure_isContinuousTreeSemimeasure
  have hmu := isContinuousTreeSemimeasure_cantorMass μ
  refine ⟨fun _ => Or.inl rfl, ?_, ?_, ?_⟩
  · intro x p p' h hp
    rcases h with rfl | h
    · exact Or.inl (List.eq_nil_of_prefix_nil hp)
    · by_cases hp' : p' = []
      · exact Or.inl hp'
      · exact Or.inr (h.trans (interior_mono (treeIco_prefix_subset hlen hp)))
  · intro x x' p h hx
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr ((treeIcc_prefix_subset hmu hx).trans h)
  · intro x p p' hp hp'
    rcases hp with rfl | hp
    · exact Or.inl List.nil_prefix
    · rcases hp' with rfl | hp'
      · exact Or.inr List.nil_prefix
      · obtain ⟨r, hr⟩ := treeIcc_nonempty (cantorMass μ) x
        exact prefix_or_prefix_of_mem_treeIco hlen (interior_subset (hp hr))
          (interior_subset (hp' hr))

/-- The graph of the inverse arithmetic coding of a probability measure is a consistent stream
relation. -/
lemma invArithGraph_isConsistentStreamRelation (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] : IsConsistentStreamRelation (invArithGraph μ) :=
  (invArithGraph_isStreamLowerGraph μ).isConsistentStreamRelation

/-- **The map `ω ↦ r(ω)` of SUV Theorem 121 as a stream map.** -/
noncomputable def invArithMap (μ : Measure CantorSeq) [IsProbabilityMeasure μ] :
    BitStream → BitStream :=
  streamMapOfLowerGraph (streamGapFill (invArithGraph μ))
    (streamGapFill_isStreamLowerGraph (invArithGraph_isConsistentStreamRelation μ))

/-- The inverse arithmetic coding of a probability measure is a continuous stream map. -/
theorem isContinuousStreamMap_invArithMap (μ : Measure CantorSeq) [IsProbabilityMeasure μ] :
    IsContinuousStreamMap (invArithMap μ) :=
  streamMapOfLowerGraph_isContinuousStreamMap _

/-- The lower graph of the inverse arithmetic coding is the relation it was built from. -/
theorem streamLowerGraph_invArithMap (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (x p : BitString) : streamLowerGraph (invArithMap μ) x p ↔ invArithGraph μ x p := by
  rw [streamLowerGraph, invArithMap,
    streamMapOfLowerGraph_finite_spec
      (streamGapFill_isStreamLowerGraph (invArithGraph_isConsistentStreamRelation μ))]
  exact streamGapFill_eq_self (invArithGraph_isStreamLowerGraph μ) x p

/-- A finite string `p` lies below the inverse arithmetic image of the stream `w` exactly when some
finite prefix of `w` already forces `p` through the inverse arithmetic graph. -/
theorem streamLowerGraph_invArithMap_infinite (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (w : CantorSeq) (p : BitString) :
    BitStream.finite p ≤ invArithMap μ (.infinite w) ↔
      ∃ n, invArithGraph μ (cantorPrefix w n) p := by
  rw [invArithMap,
    streamMapOfLowerGraph_infinite_spec
      (streamGapFill_isStreamLowerGraph (invArithGraph_isConsistentStreamRelation μ))]
  exact exists_congr fun n => streamGapFill_eq_self (invArithGraph_isStreamLowerGraph μ) _ p

/-! ## Enumerability of the reverse relation -/

/-- For the uniform measure the interval attached to `p` is the dyadic interval of length
`2 ^ (-|p|)` starting at the value of `p` read as a binary fraction. -/
lemma treeIco_lengthMeasure_eq (p : BitString) :
    treeIco lengthMeasure p = Set.Ico ((devBitsToNat p : ℝ) / 2 ^ p.length)
      (((devBitsToNat p : ℝ) + 1) / 2 ^ p.length) := by
  have hstep : (devBitsToNat p : ℝ) / 2 ^ p.length + (2 : ℝ)⁻¹ ^ p.length
      = ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length := by
    rw [inv_pow]
    field_simp
  rw [treeIco, treeLeftEnd_lengthMeasure_eq_div, lengthMeasure_toReal, hstep]

/-- For a nonempty output, the reverse relation is the strict containment of the
closed interval `π_x` in the open dyadic interval of `p`. -/
lemma invArithGraph_iff_endpoints (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (x p : BitString) (hp : p ≠ []) :
    invArithGraph μ x p ↔
      ((devBitsToNat p : ℝ) / 2 ^ p.length < treeLeftEnd (cantorMass μ) x ∧
        treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal
          < ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length) := by
  rw [invArithGraph, or_iff_right hp, treeIco_lengthMeasure_eq, interior_Ico, treeIcc]
  have hle : treeLeftEnd (cantorMass μ) x
      ≤ treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal :=
    le_add_of_nonneg_right ENNReal.toReal_nonneg
  constructor
  · intro h
    exact ⟨(h (Set.left_mem_Icc.mpr hle)).1, (h (Set.right_mem_Icc.mpr hle)).2⟩
  · rintro ⟨h1, h2⟩ y hy
    rw [Set.mem_Icc] at hy
    exact ⟨lt_of_lt_of_le h1 hy.1, lt_of_le_of_lt hy.2 h2⟩

/-- Arithmetic core of the reverse stage characterisation: strict containment of
`[L, L+M]` in the open dyadic interval `(k/2^n, (k+1)/2^n)` is witnessed at some
finite stage of any approximation with the stated error bounds. -/
lemma dyadic_interval_iff_exists_stage_core (N k n : ℕ) (L M : ℝ) (LA A : ℕ → ℕ)
    (hA : ∀ s, |(LA s : ℝ) - 2 ^ s * L| ≤ (N : ℝ))
    (hB : ∀ s, |((LA s : ℝ) + (A s : ℝ)) - 2 ^ s * (L + M)| ≤ (N : ℝ) + 1) :
    ((k : ℝ) / 2 ^ n < L ∧ L + M < ((k : ℝ) + 1) / 2 ^ n) ↔
      ∃ s, n ≤ s ∧ k * 2 ^ (s - n) + N < LA s ∧
        LA s + A s + N + 1 < (k + 1) * 2 ^ (s - n) := by
  have hpowsplit : ∀ s : ℕ, n ≤ s → (2 : ℝ) ^ s = 2 ^ (s - n) * 2 ^ n := by
    intro s hs
    rw [← pow_add]
    congr 1
    omega
  have hPL : ∀ s : ℕ, n ≤ s → (2 : ℝ) ^ s * ((k : ℝ) / 2 ^ n) = (k : ℝ) * 2 ^ (s - n) := by
    intro s hs
    rw [hpowsplit s hs]
    field_simp
  have hPR : ∀ s : ℕ, n ≤ s →
      (2 : ℝ) ^ s * (((k : ℝ) + 1) / 2 ^ n) = ((k : ℝ) + 1) * 2 ^ (s - n) := by
    intro s hs
    rw [hpowsplit s hs]
    field_simp
  constructor
  · rintro ⟨h1, h2⟩
    set δ : ℝ := min (L - (k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n - (L + M)) with hδ
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    obtain ⟨m, hm⟩ := exists_nat_gt ((2 * (N : ℝ) + 2) / δ)
    have hmlt : (m : ℝ) ≤ 2 ^ m := by
      have hmm : m < 2 ^ m := Nat.lt_two_pow_self
      exact_mod_cast hmm.le
    set s : ℕ := max m n with hsdef
    have hsn : n ≤ s := le_max_right _ _
    have hpow : (2 : ℝ) ^ m ≤ 2 ^ s :=
      pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
    have hApos : (0 : ℝ) < 2 ^ s := by positivity
    have hbig : 2 * (N : ℝ) + 2 < δ * 2 ^ s := by
      have h0 : (2 * (N : ℝ) + 2) / δ < 2 ^ s := lt_of_lt_of_le hm (le_trans hmlt hpow)
      calc 2 * (N : ℝ) + 2 = ((2 * (N : ℝ) + 2) / δ) * δ := by field_simp
        _ < 2 ^ s * δ := mul_lt_mul_of_pos_right h0 hδpos
        _ = δ * 2 ^ s := mul_comm _ _
    have hδ1 : δ ≤ L - (k : ℝ) / 2 ^ n := min_le_left _ _
    have hδ2 : δ ≤ ((k : ℝ) + 1) / 2 ^ n - (L + M) := min_le_right _ _
    have hPLs := hPL s hsn
    have hPRs := hPR s hsn
    have hL1 : (k : ℝ) * 2 ^ (s - n) + δ * 2 ^ s ≤ 2 ^ s * L := by
      have hmul : δ * 2 ^ s ≤ (L - (k : ℝ) / 2 ^ n) * 2 ^ s :=
        mul_le_mul_of_nonneg_right hδ1 hApos.le
      have hexp : (L - (k : ℝ) / 2 ^ n) * 2 ^ s = 2 ^ s * L - (k : ℝ) * 2 ^ (s - n) := by
        rw [sub_mul, ← hPLs]; ring
      rw [hexp] at hmul
      linarith
    have hL2 : (2 : ℝ) ^ s * (L + M) ≤ ((k : ℝ) + 1) * 2 ^ (s - n) - δ * 2 ^ s := by
      have hmul : δ * 2 ^ s ≤ (((k : ℝ) + 1) / 2 ^ n - (L + M)) * 2 ^ s :=
        mul_le_mul_of_nonneg_right hδ2 hApos.le
      have hexp : (((k : ℝ) + 1) / 2 ^ n - (L + M)) * 2 ^ s
          = ((k : ℝ) + 1) * 2 ^ (s - n) - 2 ^ s * (L + M) := by
        rw [sub_mul, ← hPRs]; ring
      rw [hexp] at hmul
      linarith
    have hLA := hA s
    have hAB := hB s
    rw [abs_le] at hLA hAB
    refine ⟨s, hsn, ?_, ?_⟩
    · have hreal : ((k * 2 ^ (s - n) + N : ℕ) : ℝ) < ((LA s : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hreal
    · have hreal : ((LA s + A s + N + 1 : ℕ) : ℝ) < (((k + 1) * 2 ^ (s - n) : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hreal
  · rintro ⟨s, hsn, C1, C2⟩
    have hpos : (0 : ℝ) < 2 ^ s := by positivity
    have hC1 : ((k : ℝ)) * 2 ^ (s - n) + (N : ℝ) < (LA s : ℝ) := by exact_mod_cast C1
    have hC2 : (LA s : ℝ) + (A s : ℝ) + (N : ℝ) + 1 < ((k : ℝ) + 1) * 2 ^ (s - n) := by
      exact_mod_cast C2
    have hLA := hA s
    have hAB := hB s
    rw [abs_le] at hLA hAB
    constructor
    · have h1 : (2 : ℝ) ^ s * ((k : ℝ) / 2 ^ n) < 2 ^ s * L := by
        rw [hPL s hsn]; linarith
      exact lt_of_mul_lt_mul_left h1 hpos.le
    · have h2 : (2 : ℝ) ^ s * (L + M) < 2 ^ s * (((k : ℝ) + 1) / 2 ^ n) := by
        rw [hPR s hsn]; linarith
      exact lt_of_mul_lt_mul_left h2 hpos.le

/-- The stage test of the reverse relation. -/
def invArithStage (a : BitString → ℕ → ℕ) (s : ℕ) (x p : BitString) : Bool :=
  if p.isEmpty then true else
  if s < p.length then false else
  let p_L := devBitsToNat p * 2 ^ (s - p.length)
  let p_R := (devBitsToNat p + 1) * 2 ^ (s - p.length)
  let l_approx := treeLeftEndApprox a x s
  let r_approx := l_approx + a x s
  (p_L + x.length < l_approx) ∧ (r_approx + x.length + 1 < p_R)

/-- Given a two-sided dyadic approximation `a` of the mass function, the inverse arithmetic graph
relates `x` and `p` precisely when some finite stage `s` already witnesses the relation. -/
lemma invArithGraph_iff_exists_stage (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (a : BitString → ℕ → ℕ)
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (x p : BitString) :
    invArithGraph μ x p ↔ ∃ s : ℕ, invArithStage a s x p := by
  by_cases hpnil : p = []
  · subst hpnil
    exact ⟨fun _ => ⟨0, by simp [invArithStage]⟩, fun _ => Or.inl rfl⟩
  have hpe : ¬ p.isEmpty = true := by simpa using hpnil
  have hstage : ∀ s : ℕ, p.length ≤ s → (invArithStage a s x p = true ↔
      (devBitsToNat p * 2 ^ (s - p.length) + x.length < treeLeftEndApprox a x s ∧
        treeLeftEndApprox a x s + a x s + x.length + 1
          < (devBitsToNat p + 1) * 2 ^ (s - p.length))) := by
    intro s hs
    simp [invArithStage, hpe, Nat.not_lt.mpr hs, Nat.add_assoc]
  have hB : ∀ s : ℕ, |((treeLeftEndApprox a x s : ℝ) + (a x s : ℝ))
      - 2 ^ s * (treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal)|
      ≤ (x.length : ℝ) + 1 := by
    intro s
    have h1 := abs_treeLeftEndApprox_sub_le μ ha x s
    have h2 := abs_approx_sub_le_one μ ha x s
    have hrw : ((treeLeftEndApprox a x s : ℝ) + (a x s : ℝ))
        - 2 ^ s * (treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal)
        = ((treeLeftEndApprox a x s : ℝ) - 2 ^ s * treeLeftEnd (cantorMass μ) x)
          + ((a x s : ℝ) - 2 ^ s * (cantorMass μ x).toReal) := by ring
    rw [hrw]
    exact le_trans (abs_add_le _ _) (by linarith)
  rw [invArithGraph_iff_endpoints μ x p hpnil,
    dyadic_interval_iff_exists_stage_core x.length (devBitsToNat p) p.length
      (treeLeftEnd (cantorMass μ) x) ((cantorMass μ x).toReal)
      (fun s => treeLeftEndApprox a x s) (fun s => a x s)
      (fun s => abs_treeLeftEndApprox_sub_le μ ha x s) hB]
  constructor
  · rintro ⟨s, hsn, C1, C2⟩
    exact ⟨s, (hstage s hsn).mpr ⟨C1, C2⟩⟩
  · rintro ⟨s, hstg⟩
    have hsn : p.length ≤ s := by
      by_contra hc
      push Not at hc
      simp [invArithStage, hpe, Nat.not_le.mpr hc] at hstg
    obtain ⟨C1, C2⟩ := (hstage s hsn).mp hstg
    exact ⟨s, hsn, C1, C2⟩

/-- For a computable dyadic approximation the stage-`s` approximation to the inverse arithmetic
graph is decidable uniformly in the stage and both strings. -/
lemma computable_invArithStage {a : BitString → ℕ → ℕ} (ha : Computable₂ a) :
    Computable (fun r : (BitString × BitString) × ℕ =>
      invArithStage a r.2 r.1.1 r.1.2) := by
  have hx : Computable (fun r : (BitString × BitString) × ℕ => r.1.1) :=
    Computable.fst.comp Computable.fst
  have hp : Computable (fun r : (BitString × BitString) × ℕ => r.1.2) :=
    Computable.snd.comp Computable.fst
  have hs : Computable (fun r : (BitString × BitString) × ℕ => r.2) := Computable.snd
  have hplen : Computable (fun r : (BitString × BitString) × ℕ => r.1.2.length) :=
    Computable.list_length.comp hp
  have hxlen : Computable (fun r : (BitString × BitString) × ℕ => r.1.1.length) :=
    Computable.list_length.comp hx
  have hempty : Computable (fun r : (BitString × BitString) × ℕ => r.1.2.isEmpty) :=
    primrec_decide_list_isEmpty.to_comp.comp hp
  have hlt : Computable₂ (fun m n : ℕ => decide (m < n)) := primrec_decide_nat_lt.to_comp
  have hshort : Computable
      (fun r : (BitString × BitString) × ℕ => decide (r.2 < r.1.2.length)) :=
    hlt.comp hs hplen
  have hpow : Computable (fun r : (BitString × BitString) × ℕ => 2 ^ (r.2 - r.1.2.length)) :=
    primrec_two_pow_aux.to_comp.comp (Primrec.nat_sub.to_comp.comp hs hplen)
  have hdev : Computable (fun r : (BitString × BitString) × ℕ => devBitsToNat r.1.2) :=
    primrec_devBitsToNat.to_comp.comp hp
  have hpL : Computable (fun r : (BitString × BitString) × ℕ =>
      devBitsToNat r.1.2 * 2 ^ (r.2 - r.1.2.length)) :=
    Primrec.nat_mul.to_comp.comp hdev hpow
  have hpR : Computable (fun r : (BitString × BitString) × ℕ =>
      (devBitsToNat r.1.2 + 1) * 2 ^ (r.2 - r.1.2.length)) :=
    Primrec.nat_mul.to_comp.comp (Primrec.succ.to_comp.comp hdev) hpow
  have hla : Computable (fun r : (BitString × BitString) × ℕ =>
      treeLeftEndApprox a r.1.1 r.2) := (computable_treeLeftEndApprox ha).comp hx hs
  have hax : Computable (fun r : (BitString × BitString) × ℕ => a r.1.1 r.2) := ha.comp hx hs
  have hc1 := hlt.comp (Primrec.nat_add.to_comp.comp hpL hxlen) hla
  have hc2 := hlt.comp
    (Primrec.succ.to_comp.comp (Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp hla hax) hxlen)) hpR
  have hbody := Primrec.and.to_comp.comp hc1 hc2
  refine ((Computable.cond hempty (Computable.const true)
    (Computable.cond hshort (Computable.const false) hbody))).of_eq ?_
  rintro ⟨⟨x, p⟩, s⟩
  simp only [invArithStage]
  by_cases h1 : p.isEmpty = true
  · simp [h1]
  · by_cases h2 : s < p.length
    · simp [h1, h2]
    · simp [h1, h2, Nat.add_assoc]

/-- **The reverse arithmetic-coding relation is enumerable** for a computable
probability measure. -/
theorem invArithGraph_isRE (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (hμ : IsComputableMeasure μ) :
    IsRE (fun q : BitString × BitString => invArithGraph μ q.1 q.2) := by
  obtain ⟨a, ha_comp, ha⟩ := hμ
  have hstage : IsRE (fun r : (BitString × BitString) × ℕ =>
      invArithStage a r.2 r.1.1 r.1.2 = true) :=
    isRE_of_computable_bool _ (fun r => invArithStage a r.2 r.1.1 r.1.2)
      (fun _ => Iff.rfl) (computable_invArithStage ha_comp)
  have hex : IsRE (fun q : BitString × BitString => ∃ s : ℕ,
      invArithStage a s q.1 q.2 = true) :=
    IsRE.exists_encodable (R := fun (q : BitString × BitString) (s : ℕ) =>
      invArithStage a s q.1 q.2 = true) hstage
  exact hex.of_iff (fun q => (invArithGraph_iff_exists_stage μ a ha q.1 q.2).symm)

/-- **`invArithMap μ` is a computable stream map** for a computable probability
measure `μ`.  Together with `isComputableStreamMap_arithMap` this supplies both
maps of the source's proof of SUV Theorem 121's uniform case. -/
theorem isComputableStreamMap_invArithMap (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (hμ : IsComputableMeasure μ) : IsComputableStreamMap (invArithMap μ) :=
  streamMapOfLowerGraph_streamGapFill_isComputableStreamMap
    (invArithGraph_isConsistentStreamRelation μ) (invArithGraph_isRE μ hμ)

/-! ## Atomlessness: the intervals along a sequence shrink to a point

This is the one place where `IsAtomlessMeasure` enters SUV Theorem 121's proof
("Since `μ₁` has no atoms, such a common point is unique", p. 176).  It is stated
with the hypothesis `μ {w} = 0` rather than with `IsAtomlessMeasure`, which lives
in `Dimension/ChangeOfMeasure.lean`, so that this module stays below it. -/

/-- A sequence lies in the cylinder of the length-`n` prefix of `w` exactly when it agrees with `w`
on the first `n` coordinates. -/
lemma mem_cantorCylinder_cantorPrefix_iff (w v : CantorSeq) (n : ℕ) :
    v ∈ cantorCylinder (cantorPrefix w n) ↔ ∀ i < n, v i = w i := by
  constructor
  · intro h i hi
    have hlen : i < (cantorPrefix w n).length := by simpa using hi
    simpa [cantorPrefix] using h i hlen
  · intro h i hi
    have hin : i < n := by simpa using hi
    simpa [cantorPrefix] using h i hin

/-- The cylinders over longer prefixes of `w` are nested inside those over shorter prefixes. -/
lemma antitone_cantorCylinder_cantorPrefix (w : CantorSeq) :
    Antitone (fun n => cantorCylinder (cantorPrefix w n)) := by
  intro m n hmn v hv
  rw [mem_cantorCylinder_cantorPrefix_iff] at hv ⊢
  exact fun i hi => hv i (lt_of_lt_of_le hi hmn)

/-- The cylinders over all prefixes of `w` intersect in `w` alone. -/
lemma iInter_cantorCylinder_cantorPrefix (w : CantorSeq) :
    (⋂ n, cantorCylinder (cantorPrefix w n)) = {w} := by
  ext v
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    exact (mem_cantorCylinder_cantorPrefix_iff w v (i + 1)).1 (h (i + 1)) i (Nat.lt_succ_self i)
  · rintro rfl
    exact fun n => (mem_cantorCylinder_cantorPrefix_iff _ _ n).2 (fun _ _ => rfl)

/-- **The cylinder masses along a sequence tend to the mass of its singleton.**
For an atomless measure this limit is `0`, which is what makes the common point
of the intervals `π_{(ω)_n}` unique. -/
theorem tendsto_cantorMass_cantorPrefix (μ : Measure CantorSeq) [IsFiniteMeasure μ]
    (w : CantorSeq) :
    Filter.Tendsto (fun n => cantorMass μ (cantorPrefix w n)) Filter.atTop
      (nhds (μ ({w} : Set CantorSeq))) := by
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (s := fun n => cantorCylinder (cantorPrefix w n))
    (fun n => (measurableSet_cantorCylinder _).nullMeasurableSet)
    (antitone_cantorCylinder_cantorPrefix w) ⟨0, measure_ne_top μ _⟩
  rw [iInter_cantorCylinder_cantorPrefix] at h
  exact h

/-- The atomless case of `tendsto_cantorMass_cantorPrefix`. -/
theorem tendsto_cantorMass_cantorPrefix_atom_free (μ : Measure CantorSeq) [IsFiniteMeasure μ]
    {w : CantorSeq} (hw : μ ({w} : Set CantorSeq) = 0) :
    Filter.Tendsto (fun n => cantorMass μ (cantorPrefix w n)) Filter.atTop (nhds 0) := by
  have h := tendsto_cantorMass_cantorPrefix μ w
  rwa [hw] at h

/-! ## Totality of the reverse map on a non-atom

The output of `invArithMap μ` on an infinite input is infinite as soon as the
real number it denotes lies in the *interior* of a dyadic cell of every length.
SUV's remark that "the endpoints of the segments, as well as corresponding
sequences `x000⋯` and `x111⋯`, are not random" (p. 177) is exactly the statement
that a random `w` satisfies that hypothesis. -/

/-- A stream that has finite approximations of unbounded length is the stream of an infinite
sequence. -/
lemma exists_infinite_of_forall_exists_le {S : BitStream}
    (h : ∀ n : ℕ, ∃ p : BitString, n < p.length ∧ BitStream.finite p ≤ S) :
    ∃ v : CantorSeq, S = BitStream.infinite v := by
  cases S with
  | finite x =>
      obtain ⟨p, hlen, hle⟩ := h x.length
      have hpx : p <+: x := hle
      exact absurd hpx.length_le (not_le.2 hlen)
  | infinite v => exact ⟨v, rfl⟩

/-- Passing to an extension moves the left endpoint of the arithmetic interval to the right. -/
lemma treeLeftEnd_le_of_prefix {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a)
    {x y : BitString} (h : x <+: y) : treeLeftEnd a x ≤ treeLeftEnd a y := by
  have hmem : treeLeftEnd a y ∈ treeIcc a y :=
    Set.left_mem_Icc.2 (le_add_of_nonneg_right ENNReal.toReal_nonneg)
  exact (Set.mem_Icc.1 (treeIcc_prefix_subset ha h hmem)).1

/-- Passing to an extension moves the right endpoint of the arithmetic interval to the left, so the
intervals are nested. -/
lemma treeRightEnd_le_of_prefix {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a)
    {x y : BitString} (h : x <+: y) :
    treeLeftEnd a y + (a y).toReal ≤ treeLeftEnd a x + (a x).toReal := by
  have hmem : treeLeftEnd a y + (a y).toReal ∈ treeIcc a y :=
    Set.right_mem_Icc.2 (le_add_of_nonneg_right ENNReal.toReal_nonneg)
  exact (Set.mem_Icc.1 (treeIcc_prefix_subset ha h hmem)).2

/-- The left endpoint of every arithmetic interval of a continuous tree semimeasure is at most `1`.
-/
lemma treeLeftEnd_le_one {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a)
    (x : BitString) : treeLeftEnd a x ≤ 1 := by
  have hmem : treeLeftEnd a x ∈ treeIcc a x :=
    Set.left_mem_Icc.2 (le_add_of_nonneg_right ENNReal.toReal_nonneg)
  have hsub := treeIcc_prefix_subset ha (List.nil_prefix (l := x)) hmem
  have h2 := (Set.mem_Icc.1 hsub).2
  simpa [treeIcc, ha.1] using h2

/-- For the mass function of a probability measure the left endpoint of every arithmetic interval is
at most `1`. -/
lemma treeLeftEnd_cantorMass_le_one (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (x : BitString) : treeLeftEnd (cantorMass μ) x ≤ 1 :=
  treeLeftEnd_le_one (isContinuousTreeSemimeasure_cantorMass μ) x

/-- **The real number denoted by `w` under `μ`** (SUV p. 176): the common point
of the intervals `π_{(w)_n}`, realised as the supremum of their left endpoints. -/
noncomputable def measureReal (μ : Measure CantorSeq) (w : CantorSeq) : ℝ :=
  ⨆ n, treeLeftEnd (cantorMass μ) (cantorPrefix w n)

/-- Along the prefixes of a sequence the left endpoints of the arithmetic intervals increase. -/
lemma monotone_treeLeftEnd_cantorPrefix (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (w : CantorSeq) :
    Monotone (fun n => treeLeftEnd (cantorMass μ) (cantorPrefix w n)) := by
  intro a b hab
  exact treeLeftEnd_le_of_prefix (isContinuousTreeSemimeasure_cantorMass μ)
    (cantorPrefix_mono w hab)

/-- The left endpoints of the arithmetic intervals of the prefixes of `w` converge to the real
number that arithmetic coding assigns to `w`. -/
lemma tendsto_treeLeftEnd_measureReal (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (w : CantorSeq) :
    Filter.Tendsto (fun n => treeLeftEnd (cantorMass μ) (cantorPrefix w n)) Filter.atTop
      (nhds (measureReal μ w)) := by
  refine tendsto_atTop_ciSup (monotone_treeLeftEnd_cantorPrefix μ w) ?_
  refine ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact treeLeftEnd_cantorMass_le_one μ _

/-- If `w` is an atom of measure zero then the right endpoints of the arithmetic intervals of its
prefixes also converge to the real number coding `w`. -/
lemma tendsto_treeRightEnd_measureReal (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {w : CantorSeq} (hw : μ ({w} : Set CantorSeq) = 0) :
    Filter.Tendsto (fun n => treeLeftEnd (cantorMass μ) (cantorPrefix w n)
        + (cantorMass μ (cantorPrefix w n)).toReal) Filter.atTop (nhds (measureReal μ w)) := by
  have h1 := tendsto_treeLeftEnd_measureReal μ w
  have h0 := tendsto_cantorMass_cantorPrefix_atom_free μ hw
  have h2 : Filter.Tendsto (fun n => (cantorMass μ (cantorPrefix w n)).toReal) Filter.atTop
      (nhds 0) := by
    have := (ENNReal.tendsto_toReal (by simp)).comp h0
    exact this
  simpa using h1.add h2

/-- **The reverse map is total on a sequence whose real number avoids every
dyadic endpoint.**  This is the totality half of SUV Theorem 121's uniform case;
the remaining obligation is that a `μ`-random `w` satisfies the hypothesis. -/
theorem exists_infinite_invArithMap (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {w : CantorSeq} (hw : μ ({w} : Set CantorSeq) = 0)
    (hdy : ∀ m : ℕ, ∃ k : ℕ, k < 2 ^ m ∧
      (k : ℝ) / 2 ^ m < measureReal μ w ∧ measureReal μ w < ((k : ℝ) + 1) / 2 ^ m) :
    ∃ v : CantorSeq, invArithMap μ (BitStream.infinite w) = BitStream.infinite v := by
  refine exists_infinite_of_forall_exists_le (fun N => ?_)
  obtain ⟨k, hk, hk1, hk2⟩ := hdy (N + 1)
  set p : BitString := natToBits (N + 1) k with hp
  have hplen : p.length = N + 1 := by rw [hp, natToBits_length]
  have hpne : p ≠ [] := by
    intro h
    rw [h] at hplen
    simp at hplen
  have hdev : devBitsToNat p = k := by rw [hp]; exact devBitsToNat_natToBits hk
  refine ⟨p, by rw [hplen]; omega, ?_⟩
  rw [streamLowerGraph_invArithMap_infinite]
  have hL := tendsto_treeLeftEnd_measureReal μ w
  have hR := tendsto_treeRightEnd_measureReal μ hw
  have e1 : ∀ᶠ n in Filter.atTop,
      (k : ℝ) / 2 ^ (N + 1) < treeLeftEnd (cantorMass μ) (cantorPrefix w n) :=
    hL.eventually (eventually_gt_nhds hk1)
  have e2 : ∀ᶠ n in Filter.atTop,
      treeLeftEnd (cantorMass μ) (cantorPrefix w n)
        + (cantorMass μ (cantorPrefix w n)).toReal < ((k : ℝ) + 1) / 2 ^ (N + 1) :=
    hR.eventually (eventually_lt_nhds hk2)
  obtain ⟨n, hn1, hn2⟩ := (e1.and e2).exists
  refine ⟨n, ?_⟩
  rw [invArithGraph_iff_endpoints μ (cantorPrefix w n) p hpne, hdev, hplen]
  exact ⟨hn1, hn2⟩

/-! ## The same for the forward map

`arithMap μ` prints a `μ`-name of the real number carried by its input, so the
totality statement is the mirror one, with the roles of the two tree
semimeasures exchanged.  It is *not* symmetric in strength: a uniformly random
input can land in a cell of `μ`-measure zero, whose interval has empty interior,
so the hypothesis below genuinely has to be assumed here (SUV p. 177: "the
`μ₁`-measure of some `Ω_x` can be zero … all the sequences starting with `x` are
then non-random"). -/

/-- The real number carried by a stream for a tree semimeasure: the supremum of
the left endpoints of the intervals allocated to its prefixes. -/
noncomputable def treeReal (a : BitString → ℝ≥0∞) (w : CantorSeq) : ℝ :=
  ⨆ n, treeLeftEnd a (cantorPrefix w n)

/-- Arithmetic coding with respect to a measure is arithmetic coding with respect to its mass
function. -/
lemma measureReal_eq_treeReal (μ : Measure CantorSeq) (w : CantorSeq) :
    measureReal μ w = treeReal (cantorMass μ) w := rfl

/-- For any continuous tree semimeasure the left endpoints along the prefixes of a sequence
increase. -/
lemma monotone_treeLeftEnd_cantorPrefix' {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (w : CantorSeq) :
    Monotone (fun n => treeLeftEnd a (cantorPrefix w n)) := by
  intro i j hij
  exact treeLeftEnd_le_of_prefix ha (cantorPrefix_mono w hij)

/-- The left endpoints along the prefixes of `w` converge to the arithmetic code of `w`. -/
lemma tendsto_treeLeftEnd_treeReal {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (w : CantorSeq) :
    Filter.Tendsto (fun n => treeLeftEnd a (cantorPrefix w n)) Filter.atTop
      (nhds (treeReal a w)) := by
  refine tendsto_atTop_ciSup (monotone_treeLeftEnd_cantorPrefix' ha w) ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact treeLeftEnd_le_one ha _

/-- If the semimeasure of the prefixes of `w` tends to zero then the right endpoints along those
prefixes converge to the arithmetic code of `w`. -/
lemma tendsto_treeRightEnd_treeReal {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (w : CantorSeq)
    (h0 : Filter.Tendsto (fun n => (a (cantorPrefix w n)).toReal) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => treeLeftEnd a (cantorPrefix w n)
      + (a (cantorPrefix w n)).toReal) Filter.atTop (nhds (treeReal a w)) := by
  simpa using (tendsto_treeLeftEnd_treeReal ha w).add h0

/-- Under the uniform measure the mass `2 ^ (-n)` of the length-`n` prefix of a sequence tends to
zero. -/
lemma tendsto_lengthMeasure_cantorPrefix (v : CantorSeq) :
    Filter.Tendsto (fun n => (lengthMeasure (cantorPrefix v n)).toReal) Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine hbase.congr (fun n => ?_)
  rw [lengthMeasure_toReal, cantorPrefix_length]

/-- **The forward map is total on a stream whose real number lies strictly inside
a `μ`-interval of every length.** -/
theorem exists_infinite_arithMap (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (v : CantorSeq)
    (hx : ∀ m : ℕ, ∃ x : BitString, x.length = m ∧
      treeLeftEnd (cantorMass μ) x < treeReal lengthMeasure v ∧
      treeReal lengthMeasure v
        < treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal) :
    ∃ u : CantorSeq, arithMap μ (BitStream.infinite v) = BitStream.infinite u := by
  refine exists_infinite_of_forall_exists_le (fun N => ?_)
  obtain ⟨x, hxlen, hx1, hx2⟩ := hx (N + 1)
  refine ⟨x, by rw [hxlen]; omega, ?_⟩
  rw [streamLowerGraph_arithMap_infinite]
  have hlen := lengthMeasure_isContinuousTreeSemimeasure
  have hL := tendsto_treeLeftEnd_treeReal hlen v
  have hR := tendsto_treeRightEnd_treeReal hlen v (tendsto_lengthMeasure_cantorPrefix v)
  have e1 : ∀ᶠ n in Filter.atTop,
      treeLeftEnd (cantorMass μ) x < treeLeftEnd lengthMeasure (cantorPrefix v n) :=
    hL.eventually (eventually_gt_nhds hx1)
  have e2 : ∀ᶠ n in Filter.atTop,
      treeLeftEnd lengthMeasure (cantorPrefix v n)
          + (lengthMeasure (cantorPrefix v n)).toReal
        < treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal :=
    hR.eventually (eventually_lt_nhds hx2)
  obtain ⟨n, hn1, hn2⟩ := (e1.and e2).exists
  refine ⟨n, ?_⟩
  have hxne : x ≠ [] := by
    intro h
    rw [h] at hxlen
    simp at hxlen
  refine Or.inr ?_
  rw [binaryClosedInterval, treeIco, interior_Ico]
  intro y hy
  rw [Set.mem_Icc] at hy
  exact ⟨lt_of_lt_of_le hn1 hy.1, lt_of_le_of_lt hy.2 hn2⟩

end Kolmogorov
