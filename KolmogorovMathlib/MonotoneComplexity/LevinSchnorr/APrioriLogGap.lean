/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.MonotoneOptimality
import KolmogorovMathlib.MonotoneComplexity.NatLogCode
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelGreedy.AddressState
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelGreedy.GreedyStages
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelGreedy

/-!
# `KM(x) ≤ KA(x) + O(log KA(x))` (SUV Problem 140, p. 144)

The source's hint, verbatim:

> In fact `KM(x | KA(x)) ≤ KA(x) + O(1)`.  Indeed, if `KA(x) = k`, then `x` at some point
> appears in the growing subtree of strings whose a priori complexity is less than `k + 1`.
> This tree at all times has width (the cardinality of maximal antichain) at most `2^{k+1}`, so
> looking at the maximal elements of this tree, we cover it by `2^{k+1}` growing branches.  For
> details see Theorem 127, p. 194.

The growing subtree is `kaSublevel k = {x : 2^{-k} < a(x)}` and the branch covering is
`exists_kaSublevel_addressRelation` (`APrioriSublevelGreedy.lean`): a family `Rel k` of stream
lower graphs, r.e. *uniformly in `k`*, which gives every `x ∈ kaSublevel k` an address of
length exactly `k`.  That is the conditional bound `KM(x | k) ≤ k + O(1)`.

This module removes the condition.  Prefixing the address by the self-delimiting `natLogCode k`
(of length `≤ 2·log₂(k + 1) + 3`, `NatLogCode.lean`) turns the uniform family into one machine:
`logTaggedStreamLowerGraph Rel` reads `natLogCode k ++ p` and runs `Rel k` on `p`.  It is a
stream lower graph because `natLogCode` is prefix-free (`natLogCode_append_inj`), and it is r.e.
because the family is.  With `k = ⌊KA x⌋₊ + 1` — so that `KA x < k ≤ KA x + 1` and hence
`x ∈ kaSublevel k` — optimality of `D` gives

`KM_D(x) ≤ |natLogCode k| + k + O(1) ≤ KA x + 2·log₂(KA x + 2) + O(1)`.

This is the `natLogCode` analogue of `taggedStreamLowerGraph` (`MonotoneOptimality.lean`),
which uses the *unary* `natCode` and would cost `k + 1` extra bits instead of `2 log₂ k + 3`.

## Main results

* `logTaggedStreamLowerGraph` and its two structural lemmas;
* `KA_nonneg`;
* `exists_const_KMOf_le_KA_add_log`, `exists_const_KMOf_le_KA_add_log` — Problem 140.
-/

namespace Kolmogorov

/-! ### Tagging a uniformly enumerable family with a logarithmic self-delimiting code -/

/-- The `natLogCode`-tagged union of a family `U` of stream lower graphs: a program is read as
`natLogCode k ++ p`, the self-delimiting `k` selecting the member of the family and `p` being
its program.  Compare `taggedStreamLowerGraph`, which uses the unary `natCode`. -/
def logTaggedStreamLowerGraph (U : ℕ → BitString → BitString → Prop) (x y : BitString) : Prop :=
  y = [] ∨ ∃ k p, x = natLogCode k ++ p ∧ U k p y

/-- The tagged family is again a stream lower graph: `natLogCode` is prefix-free, so the tag
and the program are recovered from the concatenation. -/
lemma logTaggedStreamLowerGraph_isStreamLowerGraph (U : ℕ → BitString → BitString → Prop)
    (hU : ∀ k, IsStreamLowerGraph (U k)) :
    IsStreamLowerGraph (logTaggedStreamLowerGraph U) := by
  refine ⟨fun _ => Or.inl rfl, ?_, ?_, ?_⟩
  · intro x y y' hy hy'
    rcases hy with rfl | ⟨k, p, rfl, hUy⟩
    · have hnil : y' = [] := by
        rcases hy' with ⟨s, hs⟩
        have hlen : (y' ++ s).length = 0 := by rw [hs, List.length_nil]
        rw [List.length_append] at hlen
        exact List.eq_nil_of_length_eq_zero (by omega)
      exact Or.inl hnil
    · exact Or.inr ⟨k, p, rfl, (hU k).2.1 p y y' hUy hy'⟩
  · intro x x' y hy hx
    rcases hy with rfl | ⟨k, p, rfl, hUy⟩
    · exact Or.inl rfl
    · rcases hx with ⟨s, hs⟩
      refine Or.inr ⟨k, p ++ s, ?_, ?_⟩
      · rw [← hs, List.append_assoc]
      · exact (hU k).2.2.1 p (p ++ s) y hUy (List.prefix_append p s)
  · intro x y y' hy hy'
    rcases hy with rfl | ⟨k, p, rfl, hUy⟩
    · exact Or.inl List.nil_prefix
    · rcases hy' with rfl | ⟨l, q, hx, hUy'⟩
      · exact Or.inr List.nil_prefix
      · obtain ⟨hkl, hpq⟩ := natLogCode_append_inj hx.symm
        subst hkl
        subst hpq
        exact (hU l).2.2.2 q y y' hUy hUy'

/-- The tagged family is recursively enumerable when the family is, uniformly in the tag. -/
lemma logTaggedStreamLowerGraph_isRE {U : ℕ → BitString → BitString → Prop}
    (hU : IsRE fun q : ℕ × (BitString × BitString) => U q.1 q.2.1 q.2.2) :
    IsRE fun p : BitString × BitString => logTaggedStreamLowerGraph U p.1 p.2 := by
  classical
  have hnil : IsRE fun p : BitString × BitString => p.2 = [] := by
    refine isRE_of_computable_bool _ (fun p : BitString × BitString => decide (p.2 = []))
      (fun _ => decide_eq_true_iff) ?_
    exact Primrec.to_comp (PrimrecPred.decide (Primrec.eq.comp Primrec.snd (Primrec.const [])))
  have hmap : Computable fun w : (BitString × BitString) × (ℕ × BitString) =>
      (w.2.1, (w.2.2, w.1.2)) :=
    Computable.pair (Computable.fst.comp Computable.snd)
      (Computable.pair (Computable.snd.comp Computable.snd)
        (Computable.snd.comp Computable.fst))
  have hUcomp : IsRE fun w : (BitString × BitString) × (ℕ × BitString) =>
      U w.2.1 w.2.2 w.1.2 := hU.comp_computable hmap
  have hpred : Computable fun w : (BitString × BitString) × (ℕ × BitString) =>
      decide (w.1.1 = natLogCode w.2.1 ++ w.2.2) := by
    refine Primrec.to_comp (PrimrecPred.decide ?_)
    exact Primrec.eq.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_append.comp (primrec_natLogCode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  have hand : IsRE fun w : (BitString × BitString) × (ℕ × BitString) =>
      w.1.1 = natLogCode w.2.1 ++ w.2.2 ∧ U w.2.1 w.2.2 w.1.2 :=
    (hUcomp.and_computable hpred).of_iff fun _ => by rw [decide_eq_true_iff]
  have hright : IsRE fun p : BitString × BitString =>
      ∃ k q, p.1 = natLogCode k ++ q ∧ U k q p.2 := by
    refine (IsRE.exists_encodable
      (R := fun (p : BitString × BitString) (b : ℕ × BitString) =>
        p.1 = natLogCode b.1 ++ b.2 ∧ U b.1 b.2 p.2) hand).of_iff fun p => ?_
    constructor
    · rintro ⟨⟨k, q⟩, h⟩
      exact ⟨k, q, h⟩
    · rintro ⟨k, q, h⟩
      exact ⟨(k, q), h⟩
  exact (hnil.or hright).of_iff fun _ => Iff.rfl

/-! ### `KA` is non-negative -/

/-- The a priori complexity is non-negative: `a [] = 1` and `a` is antitone along prefixes. -/
lemma KA_nonneg (x : BitString) : 0 ≤ KA x := by
  have h0 : KA ([] : BitString) = 0 := by
    rw [KA, universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.1]
    simp
  rw [← h0]
  exact KA_mono List.nil_prefix

/-! ### Problem 140 -/

/-- The machine of Problem 140: the `natLogCode`-tagged branch addresses of the a priori
sublevel trees.  For every `x` and every `k` with `KA x < k`, it produces `x` from a program of
length `|natLogCode k| + k`, so an optimal monotone decompressor needs at most that many bits
plus its own coding constant. -/
lemma exists_const_toNat_KMOf_le_natLogCode_add {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) :
    ∃ c₀ : ℕ, ∀ (x : BitString) (k : ℕ), KA x < (k : ℝ) →
      (KMOf D x).toNat ≤ (natLogCode k).length + k + c₀ := by
  obtain ⟨Rel, hLG, hRE, hcov⟩ := exists_kaSublevel_addressRelation
  have hT : IsStreamLowerGraph (logTaggedStreamLowerGraph Rel) :=
    logTaggedStreamLowerGraph_isStreamLowerGraph Rel hLG
  have hD₀ : IsComputableStreamMap (streamMapOfLowerGraph (logTaggedStreamLowerGraph Rel) hT) := by
    refine ⟨streamMapOfLowerGraph_isContinuousStreamMap _, ?_⟩
    refine (logTaggedStreamLowerGraph_isRE hRE).of_iff fun p => ?_
    exact (streamMapOfLowerGraph_finite_spec hT p.1 p.2).symm
  obtain ⟨c₀, hc₀⟩ := hD.2 _ hD₀
  refine ⟨c₀, fun x k hk => ?_⟩
  obtain ⟨p, hplen, hp⟩ := hcov k x (mem_kaSublevel_of_KA_lt hk)
  have hprod : monotoneProduces (streamMapOfLowerGraph (logTaggedStreamLowerGraph Rel) hT)
      (natLogCode k ++ p) x := by
    rw [monotoneProduces, streamMapOfLowerGraph_finite_spec]
    exact Or.inr ⟨k, p, rfl, hp⟩
  have h1 : KMOf (streamMapOfLowerGraph (logTaggedStreamLowerGraph Rel) hT) x
      ≤ ((natLogCode k ++ p).length : ℕ∞) :=
    KMOf_le_length_of_monotoneProduces hprod
  have h2 : KMOf D x ≤ (((natLogCode k ++ p).length + c₀ : ℕ) : ℕ∞) := by
    have hstep : KMOf D x ≤ ((natLogCode k ++ p).length : ℕ∞) + (c₀ : ℕ∞) :=
      le_trans (hc₀ x) (add_le_add h1 (le_refl (c₀ : ℕ∞)))
    have hcast : (((natLogCode k ++ p).length + c₀ : ℕ) : ℕ∞)
        = ((natLogCode k ++ p).length : ℕ∞) + (c₀ : ℕ∞) := by
      push_cast
      ring
    rw [hcast]
    exact hstep
  have h3 : (KMOf D x).toNat ≤ (natLogCode k ++ p).length + c₀ := by
    have h4 := ENat.toNat_le_toNat h2 (ENat.natCast_ne_top _)
    rwa [ENat.toNat_natCast] at h4
  rw [List.length_append, hplen] at h3
  exact h3

/-- **SUV Problem 140 (Section 5.5, p. 144)**: `KM(x) ≤ KA(x) + O(log KA(x))`. -/
theorem exists_const_KMOf_le_KA_add_log {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) :
    ∃ c : ℝ, ∀ x : BitString,
      ((KMOf D x).toNat : ℝ) ≤ KA x + c * Real.logb 2 (KA x + 2) + c := by
  obtain ⟨c₀, hc₀⟩ := exists_const_toNat_KMOf_le_natLogCode_add hD
  refine ⟨max 2 (4 + (c₀ : ℝ)), fun x => ?_⟩
  have hKA0 : 0 ≤ KA x := KA_nonneg x
  have hlt : KA x < ((⌊KA x⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one (KA x)
  have hkle : ((⌊KA x⌋₊ + 1 : ℕ) : ℝ) ≤ KA x + 1 := by
    push_cast
    have hfl := Nat.floor_le hKA0
    linarith
  have hbound := hc₀ x (⌊KA x⌋₊ + 1) hlt
  have hcode : ((natLogCode (⌊KA x⌋₊ + 1)).length : ℝ)
      ≤ 2 * Real.logb 2 ((⌊KA x⌋₊ + 1 : ℕ) + 1) + 3 :=
    length_natLogCode_le _
  have hlog : Real.logb 2 (((⌊KA x⌋₊ + 1 : ℕ) : ℝ) + 1) ≤ Real.logb 2 (KA x + 2) := by
    refine (Real.logb_le_logb (by norm_num) (by positivity) (by linarith)).mpr ?_
    linarith
  have hlognn : 0 ≤ Real.logb 2 (KA x + 2) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hreal : ((KMOf D x).toNat : ℝ)
      ≤ ((natLogCode (⌊KA x⌋₊ + 1)).length : ℝ) + ((⌊KA x⌋₊ + 1 : ℕ) : ℝ) + (c₀ : ℝ) := by
    exact_mod_cast hbound
  have hmax1 : (2 : ℝ) * Real.logb 2 (KA x + 2)
      ≤ max 2 (4 + (c₀ : ℝ)) * Real.logb 2 (KA x + 2) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hlognn
  have hmax2 : 4 + (c₀ : ℝ) ≤ max 2 (4 + (c₀ : ℝ)) := le_max_right _ _
  linarith

end Kolmogorov
