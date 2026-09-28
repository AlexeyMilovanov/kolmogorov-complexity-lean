import KolmogorovMathlib.MonotoneComplexity.TreeSemimeasureEnumeration

/-!
# Prefix-free envelopes

This file implements the envelope construction used in SUV Theorem 80.  A
lower-semicomputable function whose mass is at most one on every finite
prefix-free family extends pointwise to a lower-semicomputable continuous tree
semimeasure.
-/

namespace Kolmogorov

open scoped ENNReal BigOperators

/-- Fixing the context of a uniformly lower-semicomputable conditional
function preserves lower semicomputability, with a dummy context in the result. -/
theorem IsLSC.fix_context {f : BitString → BitString → ℝ≥0∞}
    (hf : IsLSC f) (ctx : BitString) :
    IsLSC (fun out _ => f out ctx) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hf
  refine ⟨fun s out _ => approx s out ctx, ?_, ?_, ?_⟩
  · exact fun s out _ => hmono s out ctx
  · exact fun out _ => hsup out ctx
  · exact hcomp.comp (Computable.fst.pair
      ((Computable.fst.comp Computable.snd).pair (Computable.const ctx)))

private lemma append_bool_not_common_prefix (x : BitString) {b c : Bool}
    (hbc : b ≠ c) {y : BitString} (hb : x ++ [b] <+: y)
    (hc : x ++ [c] <+: y) : False := by
  have heq : x ++ [b] = x ++ [c] := by
    calc
      x ++ [b] = y.take (x ++ [b]).length :=
        List.prefix_iff_eq_take.mp hb
      _ = y.take (x ++ [c]).length := by simp
      _ = x ++ [c] := (List.prefix_iff_eq_take.mp hc).symm
  have : b = c := by
    simpa using List.append_cancel_left heq
  exact hbc this

private lemma prefixFree_union_children (x : BitString)
    (S₀ S₁ : Finset BitString)
    (hfree₀ : IsPrefixFree (S₀ : Set BitString))
    (hfree₁ : IsPrefixFree (S₁ : Set BitString))
    (hext₀ : ∀ y ∈ S₀, x ++ [false] <+: y)
    (hext₁ : ∀ y ∈ S₁, x ++ [true] <+: y) :
    IsPrefixFree ((S₀ ∪ S₁ : Finset BitString) : Set BitString) ∧
      Disjoint S₀ S₁ ∧ ∀ y ∈ S₀ ∪ S₁, x <+: y := by
  have hdisj : Disjoint S₀ S₁ := Finset.disjoint_left.mpr (by
    intro y hy₀ hy₁
    exact append_bool_not_common_prefix x (by decide)
      (hext₀ y hy₀) (hext₁ y hy₁))
  refine ⟨?_, hdisj, ?_⟩
  · rw [Finset.coe_union]
    intro y hy z hz hyz
    rcases hy with hy₀ | hy₁ <;> rcases hz with hz₀ | hz₁
    · exact hfree₀ hy₀ hz₀ hyz
    · exact False.elim <| append_bool_not_common_prefix x (by decide)
        ((hext₀ y hy₀).trans hyz) (hext₁ z hz₁)
    · exact False.elim <| append_bool_not_common_prefix x (by decide)
        (hext₀ z hz₀) ((hext₁ y hy₁).trans hyz)
    · exact hfree₁ hy₁ hz₁ hyz
  · intro y hy
    rw [Finset.mem_union] at hy
    rcases hy with hy₀ | hy₁
    · exact (List.prefix_append x [false]).trans (hext₀ y hy₀)
    · exact (List.prefix_append x [true]).trans (hext₁ y hy₁)

private lemma simpleApproxClosure_exists_prefixFree_support
    (approx : ℕ → BitString → BitString → ℕ) (s d : ℕ) (x : BitString) :
    ∃ S : Finset BitString,
      IsPrefixFree (S : Set BitString) ∧
      (∀ y ∈ S, x <+: y) ∧
      simpleApproxClosure approx s d x = ∑ y ∈ S, approx s y [] := by
  induction d generalizing x with
  | zero =>
      refine ⟨{x}, ?_, ?_, ?_⟩
      · simpa only [Finset.coe_singleton] using isPrefixFree_singleton x
      · simp
      · simp [simpleApproxClosure]
  | succ d ih =>
      by_cases hle : approx s x [] ≤
          simpleApproxClosure approx s d (x ++ [false]) +
            simpleApproxClosure approx s d (x ++ [true])
      · obtain ⟨S₀, hfree₀, hext₀, heq₀⟩ := ih (x ++ [false])
        obtain ⟨S₁, hfree₁, hext₁, heq₁⟩ := ih (x ++ [true])
        obtain ⟨hfree, hdisj, hext⟩ :=
          prefixFree_union_children x S₀ S₁ hfree₀ hfree₁ hext₀ hext₁
        refine ⟨S₀ ∪ S₁, hfree, hext, ?_⟩
        rw [simpleApproxClosure, max_eq_right hle, heq₀, heq₁,
          Finset.sum_union hdisj]
      · refine ⟨{x}, ?_, ?_, ?_⟩
        · simpa only [Finset.coe_singleton] using isPrefixFree_singleton x
        · simp
        · rw [simpleApproxClosure, max_eq_left (Nat.le_of_not_ge hle)]
          simp

private lemma simpleApprox_exists_prefixFree_support
    (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (x : BitString)
    (hx : x ≠ []) (hlen : x.length ≤ s) :
    ∃ S : Finset BitString,
      IsPrefixFree (S : Set BitString) ∧
      (∀ y ∈ S, x <+: y) ∧
      simpleApprox approx s x = ∑ y ∈ S, approx s y [] := by
  rw [simpleApprox_eq_closure approx s x hx hlen]
  exact simpleApproxClosure_exists_prefixFree_support approx s (s - x.length) x

private lemma dyadicValue_finset_sum (S : Finset BitString)
    (f : BitString → ℕ) (s : ℕ) :
    dyadicValue (∑ x ∈ S, f x) s = ∑ x ∈ S, dyadicValue (f x) s := by
  induction S using Finset.induction_on with
  | empty => simp [dyadicValue_zero]
  | @insert x S hx ih => simp [hx, ih, dyadicValue_add]

/-- An approximation whose limit satisfies the Kraft inequality on finite prefix-free sets never
exceeds its root budget. -/
lemma rootBudgetOK_of_prefixFree_bound
    (m : BitString → ℝ≥0∞)
    (approx : ℕ → BitString → BitString → ℕ)
    (hsup : ∀ x ctx, ⨆ s, dyadicValue (approx s x ctx) s = m x)
    (hfree : ∀ S : Finset BitString,
      IsPrefixFree (S : Set BitString) → ∑ x ∈ S, m x ≤ 1)
    (s : ℕ) : rootBudgetOK approx s := by
  cases s with
  | zero => exact rootBudgetOK_zero approx
  | succ s =>
      obtain ⟨S₀, hfree₀, hext₀, heq₀⟩ :=
        simpleApprox_exists_prefixFree_support approx (s + 1) [false]
          (by simp) (by simp)
      obtain ⟨S₁, hfree₁, hext₁, heq₁⟩ :=
        simpleApprox_exists_prefixFree_support approx (s + 1) [true]
          (by simp) (by simp)
      obtain ⟨hfree', hdisj, _⟩ :=
        prefixFree_union_children [] S₀ S₁ hfree₀ hfree₁ hext₀ hext₁
      apply le_two_pow_of_dyadicValue_le_one
      rw [heq₀, heq₁, ← Finset.sum_union hdisj,
        dyadicValue_finset_sum]
      calc
        (∑ x ∈ S₀ ∪ S₁, dyadicValue (approx (s + 1) x []) (s + 1))
            ≤ ∑ x ∈ S₀ ∪ S₁, m x := by
              apply Finset.sum_le_sum
              intro x hx
              rw [← hsup x []]
              exact le_iSup (fun t => dyadicValue (approx t x []) t) (s + 1)
        _ ≤ 1 := hfree (S₀ ∪ S₁) hfree'

/-- A lower-semicomputable function satisfying all finite prefix-free mass
bounds has a pointwise-dominating lower-semicomputable continuous tree
semimeasure.  This is the envelope construction in SUV Theorem 80. -/
theorem exists_lsc_continuousTreeSemimeasure_dominating_prefixFree
    (m : BitString → ℝ≥0∞)
    (hlsc : IsLSC (fun x _ => m x))
    (hfree : ∀ S : Finset BitString,
      IsPrefixFree (S : Set BitString) → ∑ x ∈ S, m x ≤ 1) :
    ∃ a : BitString → ℝ≥0∞,
      IsLowerSemicomputableContinuousSemimeasure a ∧ ∀ x, m x ≤ a x := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hlsc
  have hsup' : ∀ x ctx, ⨆ s, dyadicValue (approx s x ctx) s = m x := by
    simpa only using hsup
  let a : BitString → ℝ≥0∞ :=
    fun x => ⨆ s, dyadicValue (simpleApprox approx s x) s
  have hbudget : ∀ s, rootBudgetOK approx s :=
    rootBudgetOK_of_prefixFree_bound m approx hsup' hfree
  have ha : IsLowerSemicomputableContinuousSemimeasure a := by
    apply isLowerSemicomputableContinuousSemimeasure_iSup_of_stage
    · exact simpleApprox_root approx
    · intro s x
      by_cases hx : x = []
      · subst x
        simpa [rootBudgetOK] using hbudget s
      · exact simpleApprox_coherent_of_ne_nil approx s x hx
    · exact simpleApprox_stage_mono approx hmono
    · exact computable_simpleApprox approx hcomp
  refine ⟨a, ha, fun x => ?_⟩
  rw [← hsup' x []]
  refine iSup_le fun t => ?_
  let s := max t x.length
  have hraw_mono : Monotone (fun k => dyadicValue (approx k x []) k) :=
    monotone_nat_of_le_succ (fun k => hmono k x [])
  have hraw_le : approx s x [] ≤ simpleApprox approx s x := by
    unfold simpleApprox
    rw [if_neg (not_lt.mpr (Nat.le_max_right t x.length))]
    by_cases hx : x = []
    · rw [if_pos hx]
      subst x
      apply le_two_pow_of_dyadicValue_le_one
      calc
        dyadicValue (approx s [] []) s ≤ m [] := by
          rw [← hsup' [] []]
          exact le_iSup (fun k => dyadicValue (approx k [] []) k) s
        _ ≤ 1 := by
          have hsingleton : IsPrefixFree (({[]} : Finset BitString) : Set BitString) := by
            simpa only [Finset.coe_singleton] using isPrefixFree_singleton []
          simpa using hfree {[]} hsingleton
    · rw [if_neg hx]
      exact simpleApproxClosure_ge_raw approx s (s - x.length) x
  calc
    dyadicValue (approx t x []) t ≤ dyadicValue (approx s x []) s :=
      hraw_mono (Nat.le_max_left t x.length)
    _ ≤ dyadicValue (simpleApprox approx s x) s :=
      dyadicValue_le _ _ _ hraw_le
    _ ≤ ⨆ k, dyadicValue (simpleApprox approx k x) k :=
      le_iSup (fun k => dyadicValue (simpleApprox approx k x) k) s

end Kolmogorov
