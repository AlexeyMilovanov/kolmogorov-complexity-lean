import KolmogorovMathlib.Complexity.NatComplexity
import KolmogorovMathlib.MonotoneComplexity.MonotoneAPriori
import KolmogorovMathlib.MonotoneComplexity.MonotoneOptimality
import KolmogorovMathlib.Prefix.Optimal

/-!
# Simulation lemmas for monotone-complexity properties

This file contains only the order-theoretic assembly needed for SUV Theorem
85(h).  It deliberately does not state that theorem yet: the source quantifies
over a computable map `E → ℕ⊥`, whereas a total computable function on finite
bitstrings is neither the same interface nor sufficient for the conclusion.
-/

namespace Kolmogorov

/-- An arbitrary total computable `BitString → ℕ` is insufficient for the
conclusion of SUV Theorem 85(h).  On the computable all-zero branch, monotone
complexity is bounded, whereas the plain complexities of the prefix lengths are
unbounded.  This certificate guards against replacing the source's computable
map `E → ℕ⊥` and prefix-complexity conclusion by that false formulation. -/
theorem not_forall_computable_plainKNat_comp_le_KMOf
    (U : Map) {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) :
    ¬ (∀ f : BitString → ℕ, Computable f →
      ∃ c : ℕ, ∀ x, plainKNat U (f x) ≤ KMOf D x + (c : ℕ∞)) := by
  intro h
  let w : CantorSeq := fun _ => false
  have hw : Computable w := Computable.const false
  obtain ⟨b, hb⟩ :=
    (computable_iff_KMOf_prefixes_bounded hD w).mp hw
  obtain ⟨c, hc⟩ := h (fun x : BitString => x.length) Computable.list_length
  obtain ⟨n, hn⟩ := exists_plainKNat_gt U (b + c)
  have hc' := hc (cantorPrefix w n)
  rw [cantorPrefix_length] at hc'
  have hupper : plainKNat U n ≤ ((b + c : ℕ) : ℕ∞) := by
    calc
      plainKNat U n ≤ KMOf D (cantorPrefix w n) + (c : ℕ∞) := hc'
      _ ≤ (b : ℕ∞) + (c : ℕ∞) := add_le_add (hb n) le_rfl
      _ = ((b + c : ℕ) : ℕ∞) := by simp
  exact (not_lt_of_ge hupper) hn

/-- If every monotone program for `x` can be converted to a no-longer prefix
program for `z`, then the prefix complexity of `z` is at most the monotone
complexity of `x`.  This is the infimum step in Theorem 85(h); constructing the
prefix simulator from a computable map `E → ℕ⊥` is a separate obligation. -/
lemma KP_le_KMOf_of_prefix_simulation {M : Map} {D : BitStream → BitStream}
    {x z : BitString}
    (hsim : ∀ p, monotoneProduces D p x →
      ∃ q, produces M q [] z ∧ q.length ≤ p.length) :
    KP M z [] ≤ KMOf D x := by
  rw [KP_eq_condK, condK]
  unfold KMOf
  apply le_sInf
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hlen⟩ := hsim p hp
  exact le_trans (sInf_le ⟨q, hq, rfl⟩) (by exact_mod_cast hlen)

/-- Prefix optimality turns a single uniform prefix simulator into a single
additive constant, chosen before `x`. -/
theorem exists_const_KP_le_KMOf_of_prefix_simulation
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (D : BitStream → BitStream) (M : Map) (hM : IsPrefixDecompressor M)
    (g : BitString → BitString)
    (hsim : ∀ x p, monotoneProduces D p x →
      ∃ q, produces M q [] (g x) ∧ q.length ≤ p.length) :
    ∃ c : ℕ, ∀ x, KP U (g x) [] ≤ KMOf D x + (c : ℕ∞) := by
  obtain ⟨c, hc⟩ := hU.invariance hM
  refine ⟨c, fun x => ?_⟩
  exact le_trans (hc (g x) [])
    (add_le_add (KP_le_KMOf_of_prefix_simulation (hsim x)) le_rfl)

/-- Consumer specialization of `exists_const_KP_le_KMOf_of_prefix_simulation` to a
numerical output map `f : BitString → ℕ`, transported to bitstrings through
`Nat.bits`.  This is the shape in which SUV Theorem 85(h) is consumed once the
source-faithful prefix simulator has been constructed. -/
theorem exists_const_KP_natBits_le_KMOf_of_prefix_simulation
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (D : BitStream → BitStream) (M : Map) (hM : IsPrefixDecompressor M)
    (f : BitString → ℕ)
    (hsim : ∀ x p, monotoneProduces D p x →
      ∃ q, produces M q [] (Nat.bits (f x)) ∧ q.length ≤ p.length) :
    ∃ c : ℕ, ∀ x,
      KP U (Nat.bits (f x)) [] ≤ KMOf D x + (c : ℕ∞) :=
  exists_const_KP_le_KMOf_of_prefix_simulation U hU D M hM
    (fun x => Nat.bits (f x)) hsim

/-- Normal form of the *qualitative* half of SUV Theorem 87: saying that the
monotone complexity is not bounded by the a priori complexity up to an additive
constant is the same as producing, for every constant, a witness string on which
the gap is exceeded.  This is only the negation normalization; it does not
replace the quantitative `log log n - O(log log log n)` clause for infinitely
many lengths. -/
lemma not_exists_const_KMOf_le_KA_add_iff_forall_exists_witness
    (D : BitStream → BitStream) :
    (¬ ∃ c : ℝ, ∀ x : BitString, ((KMOf D x).toNat : ℝ) ≤ KA x + c)
      ↔ ∀ c : ℝ, ∃ x : BitString, KA x + c < ((KMOf D x).toNat : ℝ) := by
  push_neg
  rfl

end Kolmogorov
