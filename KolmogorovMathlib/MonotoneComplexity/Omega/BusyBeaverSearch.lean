/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaPrefixCore

/-!
# The stage search behind SUV Theorem 116 (Section 5.7, p. 171)

`Omega/OmegaPrefixCore.lean` builds the partial computable map of SUV p. 157: from a
string `x` it searches for a stage `s` at which the approximated mass `diagSum A s s`
of a lower semicomputable semimeasure exceeds `bitsValue x − 2^{-|x|}`, and then
returns an *index* that has received no mass yet (`omegaSearch`).  Theorem 116 needs
the same search, but the answer it wants is the **stage** rather than the index: once
the stage `s` has been reached, every index `i ≥ s` still carries a mass smaller than
the residual `2·2^{-|x|}`, so `s` already exceeds every integer of small prefix
complexity, which is what the busy-beaver function measures.

This module therefore provides

* `stageProbe` / `stageSearch` — the same `Nat.rfindOpt` search, reporting `s + K` for
  a constant shift `K` chosen by the caller, with its computability
  (`partrec_stageSearch`) and its two characterisations (`stageSearch_spec`,
  `stageSearch_dom`);
* `diagSum_add_mass_le_of_stage_le` — the generalisation of
  `diagSum_add_mass_le` from the *particular* untouched index `omegaZero A s` to
  *every* index `i ≥ s`: such an `i` contributes nothing to `diagSum A s s`, which is
  a sum over `Finset.range s`, so its mass is still entirely unaccounted for;
* `mass_le_two_pow_of_diagSum` — the arithmetic tail of `omegaSearch_mass_le`, split
  off so that it can be reused with an arbitrary index.

Nothing here mentions machines; the busy-beaver conclusion is drawn in
`Omega/SolovayFunctions.lean`, where `BP` lives.
-/

namespace Kolmogorov

open ENNReal

/-! ### A search that reports the stage -/

/-- The probe of stage `s`: fire as soon as the stage-`s` mass exceeds
`bitsValue x − 2^{-|x|}`, and then report the stage itself, shifted by `K`.

The shift is what lets the caller make the answer exceed a fixed finite quantity —
in Theorem 116, the busy-beaver value `BP U 0`, which is not covered by the mass
argument because it concerns prefixes shorter than the additive constant. -/
def stageProbe (A : ℕ → ℕ → ℕ) (K : ℕ) (x : BitString) (s : ℕ) : Option ℕ :=
  cond (ratLtPair (bitsValue x - 1 / 2 ^ x.length, diagSum A s s)) (some (s + K)) none

/-- "From the first `n` bits of `Ω`, compute a stage by which all the mass of every
object of prefix complexity `≤ n − O(1)` has appeared": the map is *partial*, because
on strings that are not prefixes of `Ω` the search may run forever. -/
def stageSearch (A : ℕ → ℕ → ℕ) (K : ℕ) (x : BitString) : Part ℕ :=
  Nat.rfindOpt (stageProbe A K x)

/-- The stage probe is computable in the prefix and the stage. -/
theorem computable₂_stageProbe {A : ℕ → ℕ → ℕ} (K : ℕ)
    (hA : Computable (fun p : ℕ × ℕ => A p.1 p.2)) : Computable₂ (stageProbe A K) := by
  have hv : Computable (fun q : BitString × ℕ => bitsValue q.1) :=
    computable_bitsValue.comp Computable.fst
  have hlen : Computable (fun q : BitString × ℕ => (1 : ℚ) / 2 ^ q.1.length) :=
    computable_invPow2.comp (Primrec.list_length.to_comp.comp Computable.fst)
  have hleft := Computable₂.comp computable₂_ratSub hv hlen
  have hright : Computable (fun q : BitString × ℕ => diagSum A q.2 q.2) :=
    (computable_diagSum_diag hA).comp Computable.snd
  have htest := computable_ratLtPair.comp (Computable.pair hleft hright)
  have hshift : Computable (fun q : BitString × ℕ => some (q.2 + K)) :=
    Computable.option_some.comp
      ((Primrec.nat_add.comp Primrec.id (Primrec.const K)).to_comp.comp Computable.snd)
  have h := Computable.cond htest hshift
    (Computable.const (none : Option ℕ) :
      Computable (fun _ : BitString × ℕ => (none : Option ℕ)))
  exact h.of_eq (fun q => rfl)

/-- The search for a stage carrying all the mass below the given level is partial recursive. -/
theorem partrec_stageSearch {A : ℕ → ℕ → ℕ} (K : ℕ)
    (hA : Computable (fun p : ℕ × ℕ => A p.1 p.2)) : Partrec (stageSearch A K) :=
  Partrec.rfindOpt (computable₂_stageProbe K hA)

/-- What a value of the search means: some stage fired, and the answer is that stage
shifted by `K`. -/
theorem stageSearch_spec {A : ℕ → ℕ → ℕ} {K : ℕ} {x : BitString} {t : ℕ}
    (h : t ∈ stageSearch A K x) :
    ∃ s : ℕ, bitsValue x - 1 / 2 ^ x.length < diagSum A s s ∧ t = s + K := by
  obtain ⟨s, hs⟩ := Nat.rfindOpt_spec h
  refine ⟨s, ?_, ?_⟩
  · rcases ht : ratLtPair (bitsValue x - 1 / 2 ^ x.length, diagSum A s s) with _ | _
    · rw [stageProbe, ht] at hs
      exact absurd hs (by simp)
    · rw [ratLtPair] at ht
      exact of_decide_eq_true ht
  · rcases ht : ratLtPair (bitsValue x - 1 / 2 ^ x.length, diagSum A s s) with _ | _
    · rw [stageProbe, ht] at hs
      exact absurd hs (by simp)
    · rw [stageProbe, ht] at hs
      exact (Option.some_inj.1 hs).symm

/-- The search terminates as soon as some stage fires. -/
theorem stageSearch_dom {A : ℕ → ℕ → ℕ} {K : ℕ} {x : BitString} {s : ℕ}
    (h : bitsValue x - 1 / 2 ^ x.length < diagSum A s s) :
    ∃ t, t ∈ stageSearch A K x := by
  have hprobe : stageProbe A K x s = some (s + K) := by
    have ht : ratLtPair (bitsValue x - 1 / 2 ^ x.length, diagSum A s s) = true := by
      rw [ratLtPair]
      exact decide_eq_true h
    rw [stageProbe, ht]
    rfl
  have hdom : (stageSearch A K x).Dom :=
    Nat.rfindOpt_dom.2 ⟨s, s + K, by rw [hprobe]; rfl⟩
  exact ⟨(stageSearch A K x).get hdom, Part.get_mem hdom⟩

/-! ### Every index beyond the firing stage is still unaccounted for -/

/-- **The generalisation of `diagSum_add_mass_le`.**  `diagSum A s s` is a sum over
`Finset.range s`, so an index `i ≥ s` contributes nothing to it and its whole mass is
still available inside the total.

`diagSum_add_mass_le` is the special case of the index `omegaZero A s`, which is
handled by the hypothesis `A s (omegaZero A s) = 0` instead of by `s ≤ i`. -/
theorem diagSum_add_mass_le_of_stage_le {A : ℕ → ℕ → ℕ} {m : ℕ → ℝ≥0∞} {s i : ℕ}
    (hle : ∀ s i, dyadicValue (A s i) s ≤ m i) (hi : s ≤ i) :
    ENNReal.ofReal ((diagSum A s s : ℚ) : ℝ) + m i ≤ ∑' k, m k := by
  classical
  set f : ℕ → ℝ≥0∞ := fun k => (if k < s then dyadicValue (A s k) s else 0) with hf
  set g : ℕ → ℝ≥0∞ := fun k => (if k = i then m k else 0) with hg
  have hfval : ∀ k, f k = if k < s then dyadicValue (A s k) s else 0 := fun _ => rfl
  have hgval : ∀ k, g k = if k = i then m k else 0 := fun _ => rfl
  have hfg : ∀ k, f k + g k ≤ m k := by
    intro k
    rw [hfval k, hgval k]
    by_cases hk : k = i
    · rw [if_pos hk, if_neg (by omega : ¬ k < s), zero_add]
    · rw [if_neg hk, add_zero]
      by_cases hks : k < s
      · rw [if_pos hks]
        exact hle s k
      · rw [if_neg hks]
        exact zero_le
  have hsum : (∑' k, f k) + (∑' k, g k) ≤ ∑' k, m k := by
    rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum hfg
  have hfsum : (∑' k, f k) = ∑ k ∈ Finset.range s, dyadicValue (A s k) s := by
    rw [tsum_eq_sum (s := Finset.range s)
      (fun k hk => by rw [hfval k, if_neg (by simpa using hk)])]
    exact Finset.sum_congr rfl (fun k hk => by rw [hfval k, if_pos (Finset.mem_range.1 hk)])
  have hgsum : (∑' k, g k) = m i := by
    have := tsum_ite_eq i m
    rw [hg]
    exact this
  rw [ofReal_diagSum, ← hfsum, ← hgsum]
  exact hsum

/-- **The arithmetic tail of `omegaSearch_mass_le`, for an arbitrary index.**  If the
string `x` sandwiches the total mass between `bitsValue x` and `bitsValue x + 2^{-|x|}`
and the accounted mass `D` already exceeds `bitsValue x − 2^{-|x|}`, then whatever mass
is still unaccounted for is at most `2·2^{-|x|}`. -/
theorem mass_le_two_pow_of_diagSum {m : ℕ → ℝ≥0∞} {x : BitString} {i : ℕ} {D : ℚ}
    (hkey : ENNReal.ofReal ((D : ℚ) : ℝ) + m i ≤ ∑' k, m k)
    (hhigh : (∑' k, m k)
      ≤ ENNReal.ofReal (((bitsValue x : ℚ) : ℝ) + (1 : ℝ) / 2 ^ x.length))
    (hfire : bitsValue x - 1 / 2 ^ x.length < D) :
    m i ≤ ENNReal.ofReal (2 * ((1 : ℝ) / 2 ^ x.length)) := by
  set v : ℝ := ((bitsValue x : ℚ) : ℝ) with hv
  set p : ℝ := (1 : ℝ) / 2 ^ x.length with hp
  have hppos : (0 : ℝ) < p := by rw [hp]; positivity
  have hfireR : v - p < ((D : ℚ) : ℝ) := by
    rw [hv, hp]
    have hc : ((bitsValue x - 1 / 2 ^ x.length : ℚ) : ℝ) < ((D : ℚ) : ℝ) := by
      exact_mod_cast hfire
    push_cast at hc
    linarith
  have hchain : ENNReal.ofReal (v - p) + m i ≤ ENNReal.ofReal (v + p) := by
    refine le_trans (add_le_add (ENNReal.ofReal_le_ofReal hfireR.le) le_rfl) ?_
    exact le_trans hkey hhigh
  rcases lt_or_ge p v with hvp | hvp
  · have hnn : (0 : ℝ) ≤ v - p := by linarith
    have hsplit : ENNReal.ofReal (v + p) = ENNReal.ofReal (v - p) + ENNReal.ofReal (2 * p) := by
      rw [← ENNReal.ofReal_add hnn (by positivity)]
      congr 1
      ring
    rw [hsplit] at hchain
    have hfin : ENNReal.ofReal (v - p) ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [add_comm (ENNReal.ofReal (v - p)) (m i),
      add_comm (ENNReal.ofReal (v - p)) (ENNReal.ofReal (2 * p))] at hchain
    exact (ENNReal.add_le_add_iff_right hfin).1 hchain
  · refine le_trans (le_trans le_add_self hchain) (ENNReal.ofReal_le_ofReal ?_)
    linarith

end Kolmogorov
