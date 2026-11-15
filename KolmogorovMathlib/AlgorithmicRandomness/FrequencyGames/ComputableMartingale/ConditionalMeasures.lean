/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale.RandomnessBasics

/-!
# Conditional Measures

Conditional measures along computably random sequences (SUV, Problem 269 and the surrounding
discussion).  A computable fair capital has a finite limit along every computably random
sequence (`hasFiniteLimit_of_isComputablyRandom`).  Applying this to the conditional
probabilities of a computable product measure `P` on `CantorSeq × CantorSeq`, we obtain for every
computably random first coordinate `α` a probability measure on the second coordinate whose
cylinder masses are the limits of `condSecond P (cantorCylinder y) (cantorPrefix α n)`
(`exists_conditional_measure_of_isComputablyRandom`).
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology ComputableReals

/-- Step 1 of the proof of `hasFiniteLimit_of_isComputablyRandom`: a non-negative real
sequence `m (cantorPrefix w k)` that is bounded above (`m` does not win on `w`) and has no finite
limit oscillates across some rational interval: there are rationals `p < q`, and reals `p' < p` and
`q < q'`, such that the values fall below `p'` infinitely often and rise above `q'` infinitely
often. -/
private lemma hasFiniteLimit_of_isComputablyRandom_osc {m : BitString → ℝ} {w : CantorSeq}
    (hnn : ∀ x, 0 ≤ m x) (hbdd : ¬ Wins m w) (hnolim : ¬ HasFiniteLimit m w) :
    ∃ p q : ℚ, (p : ℝ) < q ∧
      (∃ p' : ℝ, p' < p ∧ ∀ n, ∃ k ≥ n, m (cantorPrefix w k) < p') ∧
      (∃ q' : ℝ, (q : ℝ) < q' ∧ ∀ n, ∃ k ≥ n, q' < m (cantorPrefix w k)) := by
  set a : ℕ → ℝ := fun k => m (cantorPrefix w k) with ha
  have hbdd' : BddAbove (Set.range a) := by
    unfold Wins at hbdd
    exact not_not.mp hbdd
  obtain ⟨B, hB⟩ := hbdd'
  have hBa : ∀ k, a k ≤ B := fun k => hB ⟨k, rfl⟩
  have hbu : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop a :=
    Filter.isBoundedUnder_of ⟨B, hBa⟩
  have hbl : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop a :=
    Filter.isBoundedUnder_of ⟨0, fun k => hnn _⟩
  have hcu : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop a := hbl.isCoboundedUnder_le
  have hcl : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop a := hbu.isCoboundedUnder_ge
  have hle : Filter.liminf a Filter.atTop ≤ Filter.limsup a Filter.atTop :=
    Filter.liminf_le_limsup hbu hbl
  have hlt : Filter.liminf a Filter.atTop < Filter.limsup a Filter.atTop := by
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      exact hnolim ⟨Filter.limsup a Filter.atTop, tendsto_of_liminf_eq_limsup h rfl hbu hbl⟩
  set l := Filter.liminf a Filter.atTop with hl
  set u := Filter.limsup a Filter.atTop with hu
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show l < (l + u) / 2 by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (l + u) / 2 < u by linarith)
  refine ⟨p, q, by linarith, ⟨(l + p) / 2, by linarith, ?_⟩, ⟨(q + u) / 2, by linarith, ?_⟩⟩
  · have hfreq : ∃ᶠ k in Filter.atTop, a k < (l + p) / 2 :=
      Filter.frequently_lt_of_liminf_lt hcl (by linarith)
    exact Filter.frequently_atTop.mp hfreq
  · have hfreq : ∃ᶠ k in Filter.atTop, (q + u) / 2 < a k :=
      Filter.frequently_lt_of_lt_limsup hcu (by linarith)
    exact Filter.frequently_atTop.mp hfreq

/-- One step of the hysteresis state machine: the state is `(prefix, holding)`; reading the bit `b`
extends the prefix to `y = prefix ++ [b]` and the new state is `!S y` if we were holding and `B y`
otherwise. -/
private def hasFiniteLimit_of_isComputablyRandom_aux2_step (B S : BitString → Bool)
    (u : (BitString × Bool) × Bool) : BitString × Bool :=
  (u.1.1 ++ [u.2], bif u.1.2 then !S (u.1.1 ++ [u.2]) else B (u.1.1 ++ [u.2]))

/-- The hysteresis state after reading `x`, as a left fold over the bits of `x`. -/
private def hasFiniteLimit_of_isComputablyRandom_aux2_st (B S : BitString → Bool)
    (x : BitString) : Bool :=
  (x.foldl (fun s b => hasFiniteLimit_of_isComputablyRandom_aux2_step B S (s, b)) ([], B [])).2

/-- The first component of the fold is the prefix read so far. -/
private lemma hasFiniteLimit_of_isComputablyRandom_aux2_fold_fst (B S : BitString → Bool) :
    ∀ (x pre : BitString) (s : Bool),
      (x.foldl (fun s b => hasFiniteLimit_of_isComputablyRandom_aux2_step B S (s, b))
        (pre, s)).1 = pre ++ x := by
  intro x
  induction x with
  | nil => intro pre s; simp
  | cons b t ih =>
    intro pre s
    rw [List.foldl_cons]
    refine (ih (hasFiniteLimit_of_isComputablyRandom_aux2_step B S ((pre, s), b)).1
      (hasFiniteLimit_of_isComputablyRandom_aux2_step B S ((pre, s), b)).2).trans ?_
    simp [hasFiniteLimit_of_isComputablyRandom_aux2_step]

private lemma hasFiniteLimit_of_isComputablyRandom_aux2_st_nil (B S : BitString → Bool) :
    hasFiniteLimit_of_isComputablyRandom_aux2_st B S [] = B [] := rfl

private lemma hasFiniteLimit_of_isComputablyRandom_aux2_st_snoc (B S : BitString → Bool)
    (x : BitString) (b : Bool) :
    hasFiniteLimit_of_isComputablyRandom_aux2_st B S (x ++ [b]) =
      bif hasFiniteLimit_of_isComputablyRandom_aux2_st B S x then !S (x ++ [b])
        else B (x ++ [b]) := by
  have h1 := hasFiniteLimit_of_isComputablyRandom_aux2_fold_fst B S x [] (B [])
  unfold hasFiniteLimit_of_isComputablyRandom_aux2_st
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  generalize x.foldl (fun s b => hasFiniteLimit_of_isComputablyRandom_aux2_step B S (s, b))
    ([], B []) = F at h1 ⊢
  obtain ⟨pre, s⟩ := F
  simp only [List.nil_append] at h1
  subst h1
  simp [hasFiniteLimit_of_isComputablyRandom_aux2_step]

private lemma hasFiniteLimit_of_isComputablyRandom_aux2_st_computable {B S : BitString → Bool}
    (hB : Computable B) (hS : Computable S) :
    Computable (hasFiniteLimit_of_isComputablyRandom_aux2_st B S) := by
  have hy : Computable (fun u : (BitString × Bool) × Bool => u.1.1 ++ [u.2]) :=
    Computable.list_concat.comp (Computable.fst.comp Computable.fst) Computable.snd
  have hstep0 : Computable (hasFiniteLimit_of_isComputablyRandom_aux2_step B S) :=
    Computable.pair hy
      (Computable.cond (Computable.snd.comp Computable.fst)
        (Primrec.not.to_comp.comp (hS.comp hy)) (hB.comp hy))
  have hstep : Computable₂ (fun (_ : BitString) (u : (BitString × Bool) × Bool) =>
      hasFiniteLimit_of_isComputablyRandom_aux2_step B S u) :=
    (hstep0.comp Computable.snd).to₂
  have hfold := Kolmogorov.computable_list_foldl (f := fun x : BitString => x)
    (g := fun _ => (([] : BitString), B [])) Computable.id (Computable.const _) hstep
  exact (Computable.snd.comp hfold).of_eq (fun x => rfl)

/-- Step 2 of the proof of `hasFiniteLimit_of_isComputablyRandom`: the "buy low, sell
high" state machine.  For a computable real function `m` on strings and rationals `p < q` there is a
computable Boolean `st` on strings ("the strategy holds `m` after reading `x`"), which turns on
(`false → true`) only where `m < p + (q - p)/4`, turns off (`true → false`) only where
`m > q - (q - p)/4`, is on at the root only if `m [] < p + (q - p)/4`, and is forced on where
`m < p` (when it was off) and forced off where `m > q` (when it was on).  Construction: with
`ε = (q - p)/8` and `2⁻ˢ⁰ ≤ ε`, put `B y = decide (qm (y, s₀) < p + ε)` and
`S y = decide (q - ε < qm (y, s₀))` for the rational approximation `qm` of `m`, and let
`st [] = B []`, `st (x ++ [b]) = if st x then !S (x ++ [b]) else B (x ++ [b])`; computability
through `computable_list_foldl` on `x.inits` (or on pairs `(prefix, state)`). -/
private lemma hasFiniteLimit_of_isComputablyRandom_state {m : BitString → ℝ}
    (hc : IsComputableOnStrings m) (p q : ℚ) (hpq : p < q) :
    ∃ st : BitString → Bool, Computable st ∧
      (st [] = true → m [] < (p : ℝ) + ((q : ℝ) - p) / 4) ∧
      (∀ x b, st x = false → st (x ++ [b]) = true → m (x ++ [b]) < (p : ℝ) + ((q : ℝ) - p) / 4) ∧
      (∀ x b, st x = true → st (x ++ [b]) = false → (q : ℝ) - ((q : ℝ) - p) / 4 < m (x ++ [b])) ∧
      (∀ x b, st x = false → m (x ++ [b]) < p → st (x ++ [b]) = true) ∧
      (∀ x b, st x = true → (q : ℝ) < m (x ++ [b]) → st (x ++ [b]) = false) := by
  obtain ⟨qm, hqm, hbound⟩ := hc
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℚ, ε = (q - p) / 8 := ⟨_, rfl⟩
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
  have hεR : (ε : ℝ) = ((q : ℝ) - p) / 8 := by
    rw [hεdef]; push_cast; ring
  have hε : (0 : ℝ) < (ε : ℝ) := by rw [hεR]; linarith
  obtain ⟨s0, hs0⟩ := exists_pow_lt_of_lt_one hε (show (2 : ℝ)⁻¹ < 1 by norm_num)
  obtain ⟨B, hBdef⟩ : ∃ B : BitString → Bool, ∀ y, B y = decide (qm (y, s0) < p + ε) :=
    ⟨fun y => decide (qm (y, s0) < p + ε), fun _ => rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : BitString → Bool, ∀ y, S y = decide (q - ε < qm (y, s0)) :=
    ⟨fun y => decide (q - ε < qm (y, s0)), fun _ => rfl⟩
  have hqm0 : Computable (fun y : BitString => qm (y, s0)) :=
    hqm.comp (Computable.pair Computable.id (Computable.const s0))
  have hlt : Computable₂ (fun a b : ℚ => decide (a < b)) :=
    (PrimrecRel.decide primrec_ratLt).to_comp
  have hB : Computable B :=
    (hlt.comp hqm0 (Computable.const (p + ε))).of_eq (fun y => (hBdef y).symm)
  have hS : Computable S :=
    (hlt.comp (Computable.const (q - ε)) hqm0).of_eq (fun y => (hSdef y).symm)
  have hbd : ∀ y, |(qm (y, s0) : ℝ) - m y| ≤ (ε : ℝ) := fun y => (hbound y s0).trans hs0.le
  have hB1 : ∀ y, m y < p → B y = true := by
    intro y hy
    have h := (abs_le.mp (hbd y)).2
    have h2 : ((qm (y, s0) : ℚ) : ℝ) < ((p + ε : ℚ) : ℝ) := by
      push_cast
      linarith
    rw [hBdef]
    exact decide_eq_true (by exact_mod_cast h2)
  have hS1 : ∀ y, (q : ℝ) < m y → S y = true := by
    intro y hy
    have h := (abs_le.mp (hbd y)).1
    have h2 : ((q - ε : ℚ) : ℝ) < ((qm (y, s0) : ℚ) : ℝ) := by
      push_cast
      linarith
    rw [hSdef]
    exact decide_eq_true (by exact_mod_cast h2)
  have hB2 : ∀ y, B y = true → m y < (p : ℝ) + ((q : ℝ) - p) / 4 := by
    intro y hy
    rw [hBdef] at hy
    have h1 : qm (y, s0) < p + ε := of_decide_eq_true hy
    have h2 : ((qm (y, s0) : ℚ) : ℝ) < ((p + ε : ℚ) : ℝ) := by exact_mod_cast h1
    have h := (abs_le.mp (hbd y)).1
    push_cast at h2
    rw [hεR] at h h2
    linarith
  have hS2 : ∀ y, S y = true → (q : ℝ) - ((q : ℝ) - p) / 4 < m y := by
    intro y hy
    rw [hSdef] at hy
    have h1 : q - ε < qm (y, s0) := of_decide_eq_true hy
    have h2 : ((q - ε : ℚ) : ℝ) < ((qm (y, s0) : ℚ) : ℝ) := by exact_mod_cast h1
    have h := (abs_le.mp (hbd y)).2
    push_cast at h2
    rw [hεR] at h h2
    linarith
  refine ⟨hasFiniteLimit_of_isComputablyRandom_aux2_st B S,
    hasFiniteLimit_of_isComputablyRandom_aux2_st_computable hB hS, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [hasFiniteLimit_of_isComputablyRandom_aux2_st_nil] at h
    exact hB2 [] h
  · intro x b hx h
    rw [hasFiniteLimit_of_isComputablyRandom_aux2_st_snoc, hx] at h
    exact hB2 _ h
  · intro x b hx h
    rw [hasFiniteLimit_of_isComputablyRandom_aux2_st_snoc, hx] at h
    apply hS2
    cases hs : S (x ++ [b])
    · rw [hs] at h
      simp at h
    · rfl
  · intro x b hx hm
    rw [hasFiniteLimit_of_isComputablyRandom_aux2_st_snoc, hx]
    exact hB1 _ hm
  · intro x b hx hm
    rw [hasFiniteLimit_of_isComputablyRandom_aux2_st_snoc, hx]
    simp [hS1 _ hm]

/-- Rational approximant of the additive transform in step 3 of the proof of
`hasFiniteLimit_of_isComputablyRandom`: the rational partial sums with the approximation `qm` of `m`
at fixed precision `t`. -/
private def hasFiniteLimit_of_isComputablyRandom_aux3_approx (qm : BitString × ℕ → ℚ)
    (st : BitString → Bool) (c : ℚ) (x : BitString) (t : ℕ) : ℚ :=
  (List.range x.length).foldl (fun acc i =>
    acc + cond (st (x.take i)) (qm (x.take (i + 1), t) - qm (x.take i, t)) 0) c

private lemma hasFiniteLimit_of_isComputablyRandom_aux3_foldl (f : ℕ → ℚ) (a : ℚ) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) a = a + ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp [add_assoc]

private lemma hasFiniteLimit_of_isComputablyRandom_aux3_approx_cast (qm : BitString × ℕ → ℚ)
    (st : BitString → Bool) (c : ℚ) (x : BitString) (t : ℕ) :
    ((hasFiniteLimit_of_isComputablyRandom_aux3_approx qm st c x t : ℚ) : ℝ) =
      (c : ℝ) + ∑ i ∈ Finset.range x.length,
        (if st (x.take i) then ((qm (x.take (i + 1), t) : ℝ) - (qm (x.take i, t) : ℝ)) else 0) := by
  unfold hasFiniteLimit_of_isComputablyRandom_aux3_approx
  rw [hasFiniteLimit_of_isComputablyRandom_aux3_foldl
    (fun i => cond (st (x.take i)) (qm (x.take (i + 1), t) - qm (x.take i, t)) 0) c x.length]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases h : st (x.take i) <;> simp

private lemma hasFiniteLimit_of_isComputablyRandom_aux3_computable {qm : BitString × ℕ → ℚ}
    (hqm : Computable qm) {st : BitString → Bool} (hst : Computable st) (c : ℚ) :
    Computable (fun p : BitString × ℕ =>
      hasFiniteLimit_of_isComputablyRandom_aux3_approx qm st c p.1 p.2) := by
  have hf : Computable (fun p : BitString × ℕ => List.range p.1.length) :=
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)).to_comp
  have hg : Computable (fun _ : BitString × ℕ => c) := Computable.const c
  have hx : Computable (fun v : (BitString × ℕ) × (ℚ × ℕ) => v.1.1) :=
    Computable.fst.comp Computable.fst
  have ht : Computable (fun v : (BitString × ℕ) × (ℚ × ℕ) => v.1.2) :=
    Computable.snd.comp Computable.fst
  have hacc : Computable (fun v : (BitString × ℕ) × (ℚ × ℕ) => v.2.1) :=
    Computable.fst.comp Computable.snd
  have hi : Computable (fun v : (BitString × ℕ) × (ℚ × ℕ) => v.2.2) :=
    Computable.snd.comp Computable.snd
  have hi1 : Computable (fun v : (BitString × ℕ) × (ℚ × ℕ) => v.2.2 + 1) :=
    Primrec.succ.to_comp.comp hi
  have htake : Computable (fun v : (BitString × ℕ) × (ℚ × ℕ) => v.1.1.take v.2.2) :=
    Computable₂.comp (f := fun (n : ℕ) (l : BitString) => l.take n) Primrec.list_take.to_comp hi hx
  have htake1 : Computable (fun v : (BitString × ℕ) × (ℚ × ℕ) => v.1.1.take (v.2.2 + 1)) :=
    Computable₂.comp (f := fun (n : ℕ) (l : BitString) => l.take n) Primrec.list_take.to_comp hi1 hx
  have hq1 : Computable (fun v : (BitString × ℕ) × (ℚ × ℕ) =>
      qm (v.1.1.take (v.2.2 + 1), v.1.2)) := hqm.comp (Computable.pair htake1 ht)
  have hq0 : Computable (fun v : (BitString × ℕ) × (ℚ × ℕ) =>
      qm (v.1.1.take v.2.2, v.1.2)) := hqm.comp (Computable.pair htake ht)
  have hdiff : Computable (fun v : (BitString × ℕ) × (ℚ × ℕ) =>
      qm (v.1.1.take (v.2.2 + 1), v.1.2) - qm (v.1.1.take v.2.2, v.1.2)) :=
    computable₂_ratSub.comp hq1 hq0
  have hcond : Computable (fun v : (BitString × ℕ) × (ℚ × ℕ) =>
      cond (st (v.1.1.take v.2.2))
        (qm (v.1.1.take (v.2.2 + 1), v.1.2) - qm (v.1.1.take v.2.2, v.1.2)) 0) :=
    Computable.cond (hst.comp htake) hdiff (Computable.const 0)
  have hh : Computable₂ (fun (p : BitString × ℕ) (u : ℚ × ℕ) =>
      u.1 + cond (st (p.1.take u.2))
        (qm (p.1.take (u.2 + 1), p.2) - qm (p.1.take u.2, p.2)) 0) :=
    (computable₂_ratAdd.comp hacc hcond)
  have key := Kolmogorov.computable_list_foldl (f := fun p : BitString × ℕ => List.range p.1.length)
    (g := fun _ => c)
    (h := fun (p : BitString × ℕ) (u : ℚ × ℕ) =>
      u.1 + cond (st (p.1.take u.2)) (qm (p.1.take (u.2 + 1), p.2) - qm (p.1.take u.2, p.2)) 0)
    hf hg hh
  refine key.of_eq (fun p => ?_)
  rfl

private lemma hasFiniteLimit_of_isComputablyRandom_aux3_nat_mul_pow_le (n : ℕ) :
    (n : ℝ) * (2⁻¹ : ℝ) ^ n ≤ 1 := by
  rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
  exact_mod_cast (Nat.lt_two_pow_self (n := n)).le

/-- Step 3 of the proof of `hasFiniteLimit_of_isComputablyRandom`: the additive
transform.  For a computable real function `m` on strings, a computable Boolean `st` and a rational
`c`, the capital `M` with `M [] = c` and `M (x ++ [b]) = M x + (m (x ++ [b]) - m x)` when `st x` and
`M (x ++ [b]) = M x` otherwise is again a computable real function.  Construction:
`M x = c + ∑_{i < |x|} [st (x.take i)] (m (x.take (i + 1)) - m (x.take i))`; the approximant at
precision `s` adds the same terms with `m` replaced by its rational approximation at precision
`s + |x| + 1` (error `≤ 2 |x| 2^{-(s + |x| + 1)} ≤ 2⁻ˢ`). -/
private lemma hasFiniteLimit_of_isComputablyRandom_capital {m : BitString → ℝ}
    (hc : IsComputableOnStrings m) {st : BitString → Bool} (hst : Computable st) (c : ℚ) :
    ∃ M : BitString → ℝ, IsComputableOnStrings M ∧ M [] = c ∧
      ∀ x b, M (x ++ [b]) = M x + if st x then m (x ++ [b]) - m x else 0 := by
  obtain ⟨qm, hqm, hbound⟩ := hc
  refine ⟨fun x => (c : ℝ) + ∑ i ∈ Finset.range x.length,
      (if st (x.take i) then m (x.take (i + 1)) - m (x.take i) else 0), ?_, ?_, ?_⟩
  · refine ⟨fun p => hasFiniteLimit_of_isComputablyRandom_aux3_approx qm st c p.1
      (p.2 + p.1.length + 1), ?_, ?_⟩
    · have hF := hasFiniteLimit_of_isComputablyRandom_aux3_computable hqm hst c
      have hg : Computable (fun p : BitString × ℕ => (p.1, p.2 + p.1.length + 1)) := by
        have h1 : Computable (fun p : BitString × ℕ => p.1) := Computable.fst
        have hlen : Computable (fun p : BitString × ℕ => p.1.length) :=
          Primrec.list_length.to_comp.comp Computable.fst
        have h2 : Computable (fun p : BitString × ℕ => p.2 + p.1.length + 1) :=
          Primrec.succ.to_comp.comp
            (Computable₂.comp (f := fun a b : ℕ => a + b) Primrec.nat_add.to_comp
              Computable.snd hlen)
        exact h1.pair h2
      exact (hF.comp hg).of_eq (fun p => rfl)
    · intro x s
      dsimp only
      rw [hasFiniteLimit_of_isComputablyRandom_aux3_approx_cast, add_sub_add_left_eq_sub,
        ← Finset.sum_sub_distrib]
      have hterm : ∀ i ∈ Finset.range x.length,
          |(if st (x.take i) then ((qm (x.take (i + 1), s + x.length + 1) : ℝ) -
              (qm (x.take i, s + x.length + 1) : ℝ)) else 0) -
            (if st (x.take i) then m (x.take (i + 1)) - m (x.take i) else 0)| ≤
          2 * (2⁻¹ : ℝ) ^ (s + x.length + 1) := by
        intro i _
        by_cases h : st (x.take i) = true
        · simp only [h, ite_true]
          have h1 := hbound (x.take (i + 1)) (s + x.length + 1)
          have h0 := hbound (x.take i) (s + x.length + 1)
          have e : ((qm (x.take (i + 1), s + x.length + 1) : ℝ) -
                (qm (x.take i, s + x.length + 1) : ℝ)) - (m (x.take (i + 1)) - m (x.take i)) =
              ((qm (x.take (i + 1), s + x.length + 1) : ℝ) - m (x.take (i + 1))) -
                ((qm (x.take i, s + x.length + 1) : ℝ) - m (x.take i)) := by ring
          rw [e]
          calc _ ≤ |(qm (x.take (i + 1), s + x.length + 1) : ℝ) - m (x.take (i + 1))| +
                |(qm (x.take i, s + x.length + 1) : ℝ) - m (x.take i)| := abs_sub _ _
            _ ≤ 2 * (2⁻¹ : ℝ) ^ (s + x.length + 1) := by linarith
        · simp [h]
      calc _ ≤ ∑ i ∈ Finset.range x.length,
            |(if st (x.take i) then ((qm (x.take (i + 1), s + x.length + 1) : ℝ) -
              (qm (x.take i, s + x.length + 1) : ℝ)) else 0) -
            (if st (x.take i) then m (x.take (i + 1)) - m (x.take i) else 0)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range x.length, 2 * (2⁻¹ : ℝ) ^ (s + x.length + 1) :=
            Finset.sum_le_sum hterm
        _ = (x.length : ℝ) * (2 * (2⁻¹ : ℝ) ^ (s + x.length + 1)) := by simp
        _ = ((x.length : ℝ) * (2⁻¹ : ℝ) ^ x.length) * (2⁻¹ : ℝ) ^ s := by ring
        _ ≤ 1 * (2⁻¹ : ℝ) ^ s := by
            apply mul_le_mul_of_nonneg_right
              (hasFiniteLimit_of_isComputablyRandom_aux3_nat_mul_pow_le x.length)
            positivity
        _ = (2⁻¹ : ℝ) ^ s := one_mul _
  · simp
  · intro x b
    dsimp only
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
    have h1 : ∀ i ∈ Finset.range x.length,
        (if st ((x ++ [b]).take i) = true then
          m ((x ++ [b]).take (i + 1)) - m ((x ++ [b]).take i) else 0) =
        (if st (x.take i) = true then m (x.take (i + 1)) - m (x.take i) else 0) := by
      intro i hi
      have hi' : i < x.length := Finset.mem_range.mp hi
      have e1 : (x ++ [b]).take i = x.take i := List.take_append_of_le_length (by omega)
      have e2 : (x ++ [b]).take (i + 1) = x.take (i + 1) :=
        List.take_append_of_le_length (by omega)
      rw [e1, e2]
    rw [Finset.sum_congr rfl h1]
    have h2 : (x ++ [b]).take x.length = x := by simp
    have h3 : (x ++ [b]).take (x.length + 1) = x ++ [b] := by simp
    rw [h2, h3]
    ring

/-- The potential of the "buy low, sell high" strategy: the capital `M x`, minus the unrealised
profit `m x - a` while the strategy holds `m`. -/
private def hasFiniteLimit_of_isComputablyRandom_pot (m M : BitString → ℝ) (st : BitString → Bool)
    (a : ℝ) (x : BitString) : ℝ :=
  M x - if st x then m x - a else 0

/-- Step 4 of the proof of `hasFiniteLimit_of_isComputablyRandom`: the potential
`pot m M st a x = M x - [st x] (m x - a)` with `a = p + (q - p)/4` never decreases along `x ↦ x ++
[b]`
(buying at `m < a` can only raise it, holding keeps it constant, selling at `m > q - (q - p)/4`
keeps it or raises it) and rises by at least `(q - p)/2` when the strategy sells
(`st x = true`, `st (x ++ [b]) = false`).  Four cases on `(st x, st (x ++ [b]))`. -/
private lemma hasFiniteLimit_of_isComputablyRandom_potential
    {m M : BitString → ℝ} {st : BitString → Bool} {p q : ℝ} (hpq : p < q)
    (hMrec : ∀ x b, M (x ++ [b]) = M x + if st x then m (x ++ [b]) - m x else 0)
    (hbuy : ∀ x b, st x = false → st (x ++ [b]) = true → m (x ++ [b]) < p + (q - p) / 4)
    (hsell : ∀ x b, st x = true → st (x ++ [b]) = false → q - (q - p) / 4 < m (x ++ [b]))
    (x : BitString) (b : Bool) :
    hasFiniteLimit_of_isComputablyRandom_pot m M st (p + (q - p) / 4) x ≤
        hasFiniteLimit_of_isComputablyRandom_pot m M st (p + (q - p) / 4) (x ++ [b]) ∧
      (st x = true → st (x ++ [b]) = false →
        hasFiniteLimit_of_isComputablyRandom_pot m M st (p + (q - p) / 4) x + (q - p) / 2 ≤
          hasFiniteLimit_of_isComputablyRandom_pot m M st (p + (q - p) / 4) (x ++ [b])) := by
  unfold hasFiniteLimit_of_isComputablyRandom_pot
  have hrec := hMrec x b
  have hb := hbuy x b
  have hs := hsell x b
  cases hx : st x <;> cases hy : st (x ++ [b])
  · -- off, off
    rw [hx] at hrec
    simp only [Bool.false_eq_true, ite_false] at hrec ⊢
    refine ⟨by linarith, fun h => by simp at h⟩
  · -- off, on : buy
    rw [hx] at hrec
    have := hb hx hy
    simp only [Bool.false_eq_true, ite_false, ite_true] at hrec ⊢
    refine ⟨by linarith, fun h => by simp at h⟩
  · -- on, off : sell
    rw [hx] at hrec
    have := hs hx hy
    simp only [Bool.false_eq_true, ite_false, ite_true] at hrec ⊢
    refine ⟨by linarith, fun _ _ => by linarith⟩
  · -- on, on : hold
    rw [hx] at hrec
    simp only [ite_true] at hrec ⊢
    refine ⟨by linarith, fun _ h => by simp at h⟩

/-- Step 6 of the proof of `hasFiniteLimit_of_isComputablyRandom`: infinitely many sells.
Let `s k` be the state and `μ k` the value of `m` at the `k`-th prefix.  If the state is forced on
when it is off and `μ (k + 1) < p`, forced off when it is on and `q < μ (k + 1)`, and `μ` is below
some `p' < p` infinitely often and above some `q' > q` infinitely often, then for every `n` there
is `k ≥ n` with `s k = true` and `s (k + 1) = false`.  (Otherwise `s` stays on from the first moment
`≥ n` where it is on, which exists by the `hlow` clause, contradicting the `hhigh` clause.) -/
private lemma hasFiniteLimit_of_isComputablyRandom_sells {s : ℕ → Bool} {μ : ℕ → ℝ}
    {p q : ℝ}
    (hbuy : ∀ k, s k = false → μ (k + 1) < p → s (k + 1) = true)
    (hsell : ∀ k, s k = true → q < μ (k + 1) → s (k + 1) = false)
    (hlow : ∃ p' : ℝ, p' < p ∧ ∀ n, ∃ k ≥ n, μ k < p')
    (hhigh : ∃ q' : ℝ, q < q' ∧ ∀ n, ∃ k ≥ n, q' < μ k) :
    ∀ n, ∃ k ≥ n, s k = true ∧ s (k + 1) = false := by
  intro n
  by_contra hcon
  obtain ⟨p', hp'p, hp'⟩ := hlow
  obtain ⟨q', hqq', hq'⟩ := hhigh
  -- no sell at or after `n`: once on, the state stays on
  have hstay : ∀ k ≥ n, s k = true → s (k + 1) = true := by
    intro k hk hsk
    by_contra hne
    exact hcon ⟨k, hk, hsk, by simpa using hne⟩
  -- the state is on at some moment `k0 ≥ n`
  have h0 : ∃ k0 ≥ n, s k0 = true := by
    obtain ⟨k1, hk1n, hk1⟩ := hp' (n + 1)
    obtain ⟨k, rfl⟩ : ∃ k, k1 = k + 1 := ⟨k1 - 1, by omega⟩
    by_cases hsk : s k = true
    · exact ⟨k, by omega, hsk⟩
    · have hsk' : s k = false := by simpa using hsk
      exact ⟨k + 1, by omega, hbuy k hsk' (by linarith)⟩
  obtain ⟨k0, hk0n, hk0⟩ := h0
  have hall : ∀ j ≥ k0, s j = true := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact hk0
    | succ j hj ih => exact hstay j (le_trans hk0n hj) ih
  obtain ⟨k2, hk2, hk2'⟩ := hq' (k0 + 1)
  obtain ⟨j, rfl⟩ : ∃ j, k2 = j + 1 := ⟨k2 - 1, by omega⟩
  have hsj : s j = true := hall j (by omega)
  have hoff : s (j + 1) = false := hsell j hsj (by linarith)
  have hon : s (j + 1) = true := hall (j + 1) (by omega)
  rw [hoff] at hon
  exact absurd hon (by simp)

/-- A non-decreasing real sequence that jumps by at least `d > 0` infinitely often is unbounded
above. -/
private lemma hasFiniteLimit_of_isComputablyRandom_aux7_unbounded {Φ : ℕ → ℝ} {d : ℝ}
    (hd : 0 < d) (hmono : ∀ k, Φ k ≤ Φ (k + 1))
    (hjump : ∀ n, ∃ k ≥ n, Φ k + d ≤ Φ (k + 1)) (B : ℝ) : ∃ K, B < Φ K := by
  have hΦ : Monotone Φ := monotone_nat_of_le_succ hmono
  have hclaim : ∀ J : ℕ, ∃ K, ∀ k ≥ K, Φ 0 + J * d ≤ Φ k := by
    intro J
    induction J with
    | zero =>
      refine ⟨0, fun k _ => ?_⟩
      simpa using hΦ (Nat.zero_le k)
    | succ J ih =>
      obtain ⟨K, hK⟩ := ih
      obtain ⟨k, hkK, hk⟩ := hjump K
      refine ⟨k + 1, fun k' hk' => ?_⟩
      have h1 : Φ 0 + J * d ≤ Φ k := hK k hkK
      have h2 : Φ (k + 1) ≤ Φ k' := hΦ hk'
      push_cast
      linarith
  obtain ⟨J, hJ⟩ := exists_nat_gt ((B - Φ 0) / d)
  obtain ⟨K, hK⟩ := hclaim J
  refine ⟨K, ?_⟩
  have h1 : B - Φ 0 < J * d := by
    have := (div_lt_iff₀ hd).mp hJ
    exact this
  have h2 := hK K le_rfl
  linarith

/-- **Effective form of Doob's theorem used in Problem 269, SUV p. 282.**  A computable martingale
has a finite limit along a computably random sequence. -/
theorem hasFiniteLimit_of_isComputablyRandom {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (_hπ : IsComputableMeasure π) (_hpos : ∀ x, 0 < cantorMass π x) {m : BitString → ℝ}
    (hm : IsFairCapital π m) (hc : IsComputableOnStrings m) {w : CantorSeq}
    (hw : IsComputablyRandom π w) : HasFiniteLimit m w := by
  by_contra hnolim
  have hbdd : ¬ Wins m w := hw m hm hc
  obtain ⟨p, q, hpq, hlow, hhigh⟩ :=
    hasFiniteLimit_of_isComputablyRandom_osc hm.nonneg hbdd hnolim
  obtain ⟨st, hst, hst0, hbuy, hsell, hfbuy, hfsell⟩ :=
    hasFiniteLimit_of_isComputablyRandom_state hc p q (by exact_mod_cast hpq)
  have hq0 : (0 : ℝ) ≤ q := by
    obtain ⟨p', hp'p, hp'⟩ := hlow
    obtain ⟨k, -, hk⟩ := hp' 0
    have := hm.nonneg (cantorPrefix w k)
    linarith
  obtain ⟨M, hMc, hM0, hMrec⟩ := hasFiniteLimit_of_isComputablyRandom_capital hc hst q
  have hcp : (p : ℝ) + ((q : ℝ) - p) / 4 ≤ (q : ℝ) := by
    have : (p : ℝ) < q := hpq
    linarith
  -- Step 5: `M` is a fair capital.  By step 4 the potential is `≥ q` everywhere (at the root by
  -- `hst0`); as `a = p + (q - p)/4 ≤ q`, this gives `M ≥ q ≥ 0` where the strategy is out and
  -- `M ≥ q + m - a ≥ 0` where it holds `m`.  And `M` follows the increments of `m` where the
  -- strategy holds `m` and stays put elsewhere, so it inherits the fairness of `m`.
  have hpot : ∀ x, (q : ℝ) ≤
      hasFiniteLimit_of_isComputablyRandom_pot m M st ((p : ℝ) + ((q : ℝ) - p) / 4) x := by
    intro x
    induction x using List.reverseRecOn with
    | nil =>
      unfold hasFiniteLimit_of_isComputablyRandom_pot
      rw [hM0]
      cases h : st [] with
      | false => simp
      | true =>
        have := hst0 h
        simp only [ite_true]
        linarith
    | append_singleton x b ih =>
      exact le_trans ih
        (hasFiniteLimit_of_isComputablyRandom_potential hpq hMrec hbuy hsell x b).1
  have hfair : IsFairCapital π M := by
    constructor
    · intro x
      have h := hpot x
      unfold hasFiniteLimit_of_isComputablyRandom_pot at h
      have hmx := hm.nonneg x
      cases hx : st x with
      | false => simp only [hx, Bool.false_eq_true, ite_false] at h; linarith
      | true => simp only [hx, ite_true] at h; linarith
    · intro x
      have hmfair := hm.fair x
      have hadd := massR_add (π := π) x
      have h0 := hMrec x false
      have h1 := hMrec x true
      rw [h0, h1]
      cases hx : st x with
      | false => simp only [Bool.false_eq_true, ite_false]; rw [hadd]; ring
      | true =>
        simp only [ite_true]
        rw [hadd] at hmfair ⊢
        linear_combination hmfair
  refine hw M hfair hMc ?_
  -- Step 7: `M` wins on `w`.  Along `w` the potential is monotone and rises by at least
  -- `(q - p)/2` at every sell, and there are infinitely many sells (step 6); so the potential is
  -- unbounded, and so is `M`, since the potential is at most `M + |p + (q - p)/4|` (as `m ≥ 0`).
  have hstep : ∀ k,
      hasFiniteLimit_of_isComputablyRandom_pot m M st ((p : ℝ) + ((q : ℝ) - p) / 4)
          (cantorPrefix w k) ≤
        hasFiniteLimit_of_isComputablyRandom_pot m M st ((p : ℝ) + ((q : ℝ) - p) / 4)
          (cantorPrefix w (k + 1)) ∧
      (st (cantorPrefix w k) = true → st (cantorPrefix w (k + 1)) = false →
        hasFiniteLimit_of_isComputablyRandom_pot m M st ((p : ℝ) + ((q : ℝ) - p) / 4)
            (cantorPrefix w k) + ((q : ℝ) - p) / 2 ≤
          hasFiniteLimit_of_isComputablyRandom_pot m M st ((p : ℝ) + ((q : ℝ) - p) / 4)
            (cantorPrefix w (k + 1))) := by
    intro k
    rw [cantorPrefix_succ]
    exact hasFiniteLimit_of_isComputablyRandom_potential hpq hMrec hbuy hsell
      (cantorPrefix w k) (w k)
  have hsells : ∀ n, ∃ k ≥ n,
      st (cantorPrefix w k) = true ∧ st (cantorPrefix w (k + 1)) = false := by
    refine hasFiniteLimit_of_isComputablyRandom_sells
      (s := fun k => st (cantorPrefix w k)) (μ := fun k => m (cantorPrefix w k)) (p := p) (q := q)
      ?_ ?_ hlow hhigh
    · intro k hk hμ
      have h := hfbuy (cantorPrefix w k) (w k) hk
      rw [← cantorPrefix_succ] at h
      exact h hμ
    · intro k hk hμ
      have h := hfsell (cantorPrefix w k) (w k) hk
      rw [← cantorPrefix_succ] at h
      exact h hμ
  have hunb := hasFiniteLimit_of_isComputablyRandom_aux7_unbounded
    (Φ := fun k => hasFiniteLimit_of_isComputablyRandom_pot m M st
      ((p : ℝ) + ((q : ℝ) - p) / 4) (cantorPrefix w k)) (d := ((q : ℝ) - p) / 2)
    (by linarith) (fun k => (hstep k).1)
    (fun n => by
      obtain ⟨k, hk, h1, h2⟩ := hsells n
      exact ⟨k, hk, (hstep k).2 h1 h2⟩)
  rintro ⟨B, hB⟩
  obtain ⟨K, hK⟩ := hunb (B + |(p : ℝ) + ((q : ℝ) - p) / 4|)
  have hMK : M (cantorPrefix w K) ≤ B := hB ⟨K, rfl⟩
  have hΦK : hasFiniteLimit_of_isComputablyRandom_pot m M st ((p : ℝ) + ((q : ℝ) - p) / 4)
      (cantorPrefix w K) ≤ M (cantorPrefix w K) + |(p : ℝ) + ((q : ℝ) - p) / 4| := by
    unfold hasFiniteLimit_of_isComputablyRandom_pot
    have h0 := hm.nonneg (cantorPrefix w K)
    have h1 : (p : ℝ) + ((q : ℝ) - p) / 4 ≤ |(p : ℝ) + ((q : ℝ) - p) / 4| := le_abs_self _
    have h2 : 0 ≤ |(p : ℝ) + ((q : ℝ) - p) / 4| := abs_nonneg _
    split_ifs
    · linarith
    · linarith
  linarith

/-- The masses of the rectangles `Ω_x × Ω_y` of a measure on `Ω × Ω` are uniformly computable. -/
def IsComputableProductMeasure (P : Measure (CantorSeq × CantorSeq)) : Prop :=
  ∃ q : BitString × BitString × ℕ → ℚ, Computable q ∧ ∀ x y s,
    |(q (x, y, s) : ℝ) - (P (cantorCylinder x ×ˢ cantorCylinder y)).toReal| ≤ (2 : ℝ)⁻¹ ^ s


/-- The cylinder of a string is the union of the cylinders of its two children. -/
private lemma exists_conditional_measure_of_isComputablyRandom_fair_union (x : BitString) :
    cantorCylinder x = cantorCylinder (x ++ [false]) ∪ cantorCylinder (x ++ [true]) := by
  ext w
  change IsCantorPrefix x w ↔ IsCantorPrefix (x ++ [false]) w ∨ IsCantorPrefix (x ++ [true]) w
  rw [isCantorPrefix_append_singleton, isCantorPrefix_append_singleton]
  constructor
  · intro hw
    cases hb : w x.length
    · exact Or.inl ⟨hw, rfl⟩
    · exact Or.inr ⟨hw, rfl⟩
  · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw

/-- The cylinders of the two children of a string are disjoint. -/
private lemma exists_conditional_measure_of_isComputablyRandom_fair_disjoint
    (x : BitString) :
    Disjoint (cantorCylinder (x ++ [false])) (cantorCylinder (x ++ [true])) := by
  rw [Set.disjoint_left]
  intro w h0 h1
  have h0' := ((isCantorPrefix_append_singleton x false w).1 h0).2
  have h1' := ((isCantorPrefix_append_singleton x true w).1 h1).2
  rw [h0'] at h1'
  exact Bool.false_ne_true h1'

/-- The mass of `Ω_a` for the first marginal of `P` is `P(Ω_a × Ω)`. -/
private lemma exists_conditional_measure_of_isComputablyRandom_fair_massR
    (P : Measure (CantorSeq × CantorSeq)) (a : BitString) :
    massR (P.map Prod.fst) a = (P (cantorCylinder a ×ˢ Set.univ)).toReal := by
  rw [massR, cantorMass, Measure.map_apply measurable_fst (measurableSet_cantorCylinder a),
    Set.prod_univ]

/-- The conditional probability times the mass of the condition is the mass of the rectangle
(also when that mass is `0`, where the conditional probability is the junk value `0`). -/
private lemma exists_conditional_measure_of_isComputablyRandom_fair_mul
    (P : Measure (CantorSeq × CantorSeq)) [IsProbabilityMeasure P] (B : Set CantorSeq)
    (a : BitString) :
    condSecond P B a * massR (P.map Prod.fst) a = (P (cantorCylinder a ×ˢ B)).toReal := by
  rw [exists_conditional_measure_of_isComputablyRandom_fair_massR, condSecond]
  rcases eq_or_ne (P (cantorCylinder a ×ˢ Set.univ)).toReal 0 with h | h
  · have hle : (P (cantorCylinder a ×ˢ B)).toReal ≤ (P (cantorCylinder a ×ˢ Set.univ)).toReal :=
      ENNReal.toReal_mono (measure_ne_top P _)
        (measure_mono (Set.prod_mono le_rfl (Set.subset_univ B)))
    have h0 : (0 : ℝ) ≤ (P (cantorCylinder a ×ˢ B)).toReal := ENNReal.toReal_nonneg
    rw [h, mul_zero]
    exact le_antisymm h0 (hle.trans h.le)
  · exact div_mul_cancel₀ _ h

/-- The mass of `Ω_a × B` is the sum of the masses of `Ω_{a0} × B` and `Ω_{a1} × B`. -/
private lemma exists_conditional_measure_of_isComputablyRandom_fair_add
    (P : Measure (CantorSeq × CantorSeq)) [IsProbabilityMeasure P] {B : Set CantorSeq}
    (hB : MeasurableSet B) (a : BitString) :
    (P (cantorCylinder a ×ˢ B)).toReal =
      (P (cantorCylinder (a ++ [false]) ×ˢ B)).toReal +
        (P (cantorCylinder (a ++ [true]) ×ˢ B)).toReal := by
  rw [← ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _),
    exists_conditional_measure_of_isComputablyRandom_fair_union a, Set.union_prod,
    measure_union (Set.disjoint_prod.2 (Or.inl
      (exists_conditional_measure_of_isComputablyRandom_fair_disjoint a)))
      ((measurableSet_cantorCylinder _).prod hB)]

private theorem exists_conditional_measure_of_isComputablyRandom_fair
    {P : Measure (CantorSeq × CantorSeq)} [IsProbabilityMeasure P] (y : BitString) :
    IsFairCapital (P.map Prod.fst)
      (fun a => condSecond P (cantorCylinder y) a) := by
  constructor
  · intro a
    change 0 ≤ (P (cantorCylinder a ×ˢ cantorCylinder y)).toReal /
      (P (cantorCylinder a ×ˢ Set.univ)).toReal
    exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · intro a
    show condSecond P (cantorCylinder y) a * massR (P.map Prod.fst) a =
      condSecond P (cantorCylinder y) (a ++ [false]) * massR (P.map Prod.fst) (a ++ [false]) +
        condSecond P (cantorCylinder y) (a ++ [true]) * massR (P.map Prod.fst) (a ++ [true])
    rw [exists_conditional_measure_of_isComputablyRandom_fair_mul,
      exists_conditional_measure_of_isComputablyRandom_fair_mul,
      exists_conditional_measure_of_isComputablyRandom_fair_mul]
    exact exists_conditional_measure_of_isComputablyRandom_fair_add P
      (measurableSet_cantorCylinder y) a

private lemma exists_conditional_measure_of_isComputablyRandom_computable_rat_div_pos
    {α : Type*} [Primcodable α] {f d : α → ℚ}
    (hf : Computable f) (hd : Computable d) (hdpos : ∀ a, 0 < d a) :
    Computable (fun a => f a / d a) := by
  have hnum : Computable (fun a => (f a).num * ((d a).den : ℤ)) :=
    Computable₂.comp primrec_intMul.to_comp (computable_ratNum.comp hf)
      (ComputableReals.primrec_natCastInt.to_comp.comp (computable_ratDen.comp hd))
  have hden : Computable (fun a => (f a).den * (d a).num.toNat) :=
    Computable₂.comp Primrec.nat_mul.to_comp (computable_ratDen.comp hf)
      (ComputableReals.primrec_intToNat.to_comp.comp (computable_ratNum.comp hd))
  refine computable_of_num_den (f := fun a => f a / d a) hnum hden (fun a => ?_) (fun a => ?_)
  · exact Nat.mul_pos (f a).pos (by have := Rat.num_pos.2 (hdpos a); omega)
  · have h1 : ((f a).num : ℚ) = f a * ((f a).den : ℚ) := (Rat.mul_den_eq_num (f a)).symm
    have h2 : ((d a).num : ℚ) = d a * ((d a).den : ℚ) := (Rat.mul_den_eq_num (d a)).symm
    have h3 : (((d a).num.toNat : ℕ) : ℚ) = ((d a).num : ℚ) := by
      have hh : ((d a).num.toNat : ℤ) = (d a).num :=
        Int.toNat_of_nonneg (Rat.num_pos.2 (hdpos a)).le
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hh
    have hd1 : ((f a).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (f a).den_nz
    have hd2 : ((d a).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (d a).den_nz
    have hda : d a ≠ 0 := (hdpos a).ne'
    push_cast
    rw [h3, h1, h2]
    field_simp

private theorem exists_conditional_measure_of_isComputablyRandom_computable_ratio_error
    (A D a d e : ℝ) (hD : 0 < D) (hA : 0 ≤ A) (hAD : A ≤ D)
    (he : e ≤ D / 2) (ha : |a - A| ≤ e) (hd : |d - D| ≤ e) :
    |a / d - A / D| ≤ 4 * e / D := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans ha
  have hdlo : D / 2 ≤ d := by linarith [(abs_le.mp hd).1]
  have hdpos : 0 < d := lt_of_lt_of_le (by linarith) hdlo
  have hnum : |a * D - A * d| ≤ 2 * e * D := by
    calc _ = |(a - A) * D + A * (D - d)| := by congr 1; ring
      _ ≤ |(a - A) * D| + |A * (D - d)| := abs_add_le _ _
      _ = |a - A| * D + A * |d - D| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hD.le, abs_of_nonneg hA, abs_sub_comm D d]
      _ ≤ e * D + A * e := add_le_add
        (mul_le_mul_of_nonneg_right ha hD.le) (mul_le_mul_of_nonneg_left hd hA)
      _ ≤ 2 * e * D := by nlinarith
  have heq : a / d - A / D = (a * D - A * d) / (d * D) := by field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hdpos hD)]
  apply (div_le_iff₀ (mul_pos hdpos hD)).mpr
  calc _ ≤ 2 * e * D := hnum
    _ ≤ 4 * e * d := by nlinarith
    _ = 4 * e / D * (d * D) := by field_simp

private theorem exists_conditional_measure_of_isComputablyRandom_computable_ratio_computable
    {α : Type*} [Primcodable α] (A D : α → ℝ)
    (hD : ∀ z, 0 < D z) (hAD : ∀ z, 0 ≤ A z ∧ A z ≤ D z)
    (R : α → ℕ) (hR : Computable R) (hRbound : ∀ z, 1 / D z ≤ (2 : ℝ) ^ R z)
    (qA qD : α × ℕ → ℚ) (hqA : Computable qA) (hqD : Computable qD)
    (heA : ∀ z s, |(qA (z, s) : ℝ) - A z| ≤ (2 : ℝ)⁻¹ ^ s)
    (heD : ∀ z s, |(qD (z, s) : ℝ) - D z| ≤ (2 : ℝ)⁻¹ ^ s) :
    ∃ q : α × ℕ → ℚ, Computable q ∧ ∀ z s,
      |(q (z, s) : ℝ) - A z / D z| ≤ (2 : ℝ)⁻¹ ^ s := by
  let T : α × ℕ → ℕ := fun p => p.2 + R p.1 + 3
  have hT : Computable T := Primrec.nat_add.to_comp.comp
    (Primrec.nat_add.to_comp.comp Computable.snd (hR.comp Computable.fst)) (Computable.const 3)
  have hlo : ∀ z, (2 : ℝ)⁻¹ ^ R z ≤ D z := by
    intro z
    rw [inv_pow, ← one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ R z)).mpr
    simpa [mul_comm] using (div_le_iff₀ (hD z)).mp (hRbound z)
  have herr : ∀ z s, (2 : ℝ)⁻¹ ^ T (z, s) ≤ D z / 2 := by
    intro z s
    calc _ ≤ (2 : ℝ)⁻¹ ^ (R z + 1) := pow_le_pow_of_le_one
          (by norm_num) (by norm_num) (by dsimp [T]; omega)
      _ = (2 : ℝ)⁻¹ ^ R z / 2 := by rw [pow_succ]; ring
      _ ≤ D z / 2 := div_le_div_of_nonneg_right (hlo z) (by norm_num)
  have hqpos : ∀ p, 0 < qD (p.1, T p) := by
    rintro ⟨z, s⟩
    have h1 := (abs_le.mp (heD z (T (z, s)))).1
    have h2 := herr z s
    have h3 : (0 : ℝ) < (qD (z, T (z, s)) : ℝ) := by linarith [hD z]
    exact Rat.cast_pos.mp h3
  refine ⟨fun p => qA (p.1, T p) / qD (p.1, T p), ?_, fun z s => ?_⟩
  · exact exists_conditional_measure_of_isComputablyRandom_computable_rat_div_pos
      (hqA.comp (Computable.fst.pair hT)) (hqD.comp (Computable.fst.pair hT)) hqpos
  · push_cast
    calc _ ≤ 4 * (2 : ℝ)⁻¹ ^ T (z, s) / D z :=
        exists_conditional_measure_of_isComputablyRandom_computable_ratio_error
          _ _ _ _ _ (hD z) (hAD z).1 (hAD z).2 (herr z s)
          (heA z (T (z, s))) (heD z (T (z, s)))
      _ ≤ (4 * (2 : ℝ)⁻¹ ^ T (z, s)) * 2 ^ R z := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hRbound z) (by positivity)
      _ = (2 : ℝ)⁻¹ ^ (s + 1) := by
        have hcancel : (2 : ℝ)⁻¹ ^ R z * 2 ^ R z = 1 := by
          rw [← mul_pow]; norm_num
        change 4 * (2 : ℝ)⁻¹ ^ (s + R z + 3) * 2 ^ R z = _
        calc _ = (4 * (2 : ℝ)⁻¹ ^ (s + 3)) * ((2 : ℝ)⁻¹ ^ R z * 2 ^ R z) := by
              rw [pow_add, pow_add, pow_add]; ring
          _ = _ := by rw [hcancel, mul_one]; rw [pow_succ, pow_succ]; ring
      _ ≤ (2 : ℝ)⁻¹ ^ s := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

private theorem exists_conditional_measure_of_isComputablyRandom_computable_dyadic
    : Computable (fun n : ℕ => (2 : ℚ)⁻¹ ^ n) := by
  apply computable_of_num_den (Computable.const (1 : ℤ)) comp_pow
    (fun n => by positivity)
  intro n
  simp [inv_pow, one_div]

private theorem exists_conditional_measure_of_isComputablyRandom_computable
    {P : Measure (CantorSeq × CantorSeq)} [IsProbabilityMeasure P]
    (hP : IsComputableProductMeasure P)
    (hpos : ∀ x, 0 < cantorMass (P.map Prod.fst) x) (y : BitString) :
    IsComputableOnStrings (fun a => condSecond P (cantorCylinder y) a) := by
  obtain ⟨q, hq, hqerr⟩ := hP
  let A : BitString → ℝ := fun a => (P (cantorCylinder a ×ˢ cantorCylinder y)).toReal
  let D : BitString → ℝ := fun a => (P (cantorCylinder a ×ˢ cantorCylinder ([] : BitString))).toReal
  have hnil : cantorCylinder ([] : BitString) = Set.univ := by
    ext w; simp [cantorCylinder, IsCantorPrefix]
  have hDpos : ∀ a, 0 < D a := by
    intro a
    have h : cantorMass (P.map Prod.fst) a = P (cantorCylinder a ×ˢ cantorCylinder ([] : BitString))
        := by
      rw [cantorMass, Measure.map_apply measurable_fst (measurableSet_cantorCylinder a), hnil,
        Set.prod_univ]
    have := hpos a
    rw [h] at this
    exact ENNReal.toReal_pos (ne_of_gt this) (measure_ne_top P _)
  have hAD : ∀ a, 0 ≤ A a ∧ A a ≤ D a := by
    intro a
    refine ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono (measure_ne_top P _) (measure_mono ?_)⟩
    rw [hnil]
    exact Set.prod_mono le_rfl (Set.subset_univ _)
  let qA : BitString × ℕ → ℚ := fun p => q (p.1, y, p.2)
  let qD : BitString × ℕ → ℚ := fun p => q (p.1, [], p.2)
  have hqA : Computable qA := hq.comp (Computable.fst.pair (Computable.const y |>.pair
      Computable.snd))
  have hqD : Computable qD := hq.comp (Computable.fst.pair ((Computable.const ([] : BitString)).pair
      Computable.snd))
  have hex : ∀ a, ∃ s, 2 * (2 : ℚ)⁻¹ ^ s ≤ qD (a, s) := by
    intro a
    obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one
      (div_pos (hDpos a) (by norm_num : (0 : ℝ) < 4))
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    refine ⟨s, ?_⟩
    have h := (abs_le.mp (hqerr a [] s)).1
    have hs' : 2 * (2 : ℝ)⁻¹ ^ s ≤ (qD (a, s) : ℝ) := by
      change _ ≤ (q (a, [], s) : ℝ)
      linarith [hDpos a]
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat]
    simpa only [one_div] using hs'
  have hc : Computable (fun x => Nat.find (hex x)) := by
    apply Computable.natFind (P := fun x s => 2 * (2 : ℚ)⁻¹ ^ s ≤ qD (x, s)) ?_ hex
    exact ComputableReals.primrec_ratLe.decide.to_comp.comp
      (computable₂_ratMul.comp (Computable.const 2)
        (exists_conditional_measure_of_isComputablyRandom_computable_dyadic.comp
          Computable.snd)) hqD
  have hRbound : ∀ a, 1 / D a ≤ (2 : ℝ) ^ Nat.find (hex a) := by
    intro a
    have hqlo : (2 : ℝ) * (2 : ℝ)⁻¹ ^ Nat.find (hex a) ≤ qD (a, Nat.find (hex a)) := by
      have h := (Rat.cast_le (K := ℝ)).mpr (Nat.find_spec (hex a))
      norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat] at h
      simpa only [one_div] using h
    have herr := (abs_le.mp (hqerr a [] (Nat.find (hex a)))).2
    have hlow : (2 : ℝ)⁻¹ ^ Nat.find (hex a) ≤ D a := by
      change _ ≤ (P (cantorCylinder a ×ˢ cantorCylinder ([] : BitString))).toReal
      change _ ≤ (q (a, [], Nat.find (hex a)) : ℝ) at hqlo
      linarith
    calc 1 / D a ≤ 1 / ((2 : ℝ)⁻¹ ^ Nat.find (hex a)) :=
        one_div_le_one_div_of_le (by positivity) hlow
      _ = 2 ^ Nat.find (hex a) := by simp [inv_pow]
  obtain ⟨Q, hQ, hQerr⟩ :=
    exists_conditional_measure_of_isComputablyRandom_computable_ratio_computable A D hDpos hAD
      (fun a => Nat.find (hex a)) hc hRbound qA qD hqA hqD (fun a s => hqerr a y s)
      (fun a s => hqerr a [] s)
  refine ⟨Q, hQ, fun a s => ?_⟩
  have hcs : condSecond P (cantorCylinder y) a = A a / D a := by
    simp only [condSecond, A, D, hnil]
  simpa only [hcs] using hQerr a s

private lemma exists_conditional_measure_of_isComputablyRandom_limits_aux_rounding
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ]
    (Q : BitString → ℕ → ℚ) (hQ_comp : Computable₂ Q)
    (hQ : ∀ x s, |(Q x s : ℝ) - massR μ x| ≤ (2 : ℝ)⁻¹ ^ (s + 2)) :
    IsComputableMeasure μ := by
  let a (x : BitString) (s : ℕ) : ℕ := (ratDyadicFloor (Q x s) (s + 1) + 1) / 2
  have ha_comp : Computable₂ a := by
    have hs : Computable (fun z : BitString × ℕ => z.2 + 1) :=
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)).to_comp
    have hfloor : Computable (fun z : BitString × ℕ =>
        ratDyadicFloor (Q z.1 z.2) (z.2 + 1)) :=
      computable_ratDyadicFloor.comp hQ_comp hs
    have hadd : Computable (fun z : BitString × ℕ =>
        ratDyadicFloor (Q z.1 z.2) (z.2 + 1) + 1) :=
      Primrec.nat_add.to_comp.comp hfloor (Computable.const 1)
    exact (Primrec.nat_div.to_comp.comp hadd (Computable.const 2)).to₂.of_eq fun _ => rfl
  refine ⟨a, ha_comp, fun x s => ?_⟩
  set A := ratDyadicFloor (Q x s) (s + 1) with hAdef
  have hm0 : 0 ≤ massR μ x := ENNReal.toReal_nonneg
  have ht : (0 : ℝ) < 2 ^ s := by positivity
  have hpow : (2 : ℝ) ^ (s + 1) = 2 * 2 ^ s := by ring
  have hinv : (2 : ℝ)⁻¹ ^ (s + 2) = 1 / (4 * 2 ^ s) := by
    rw [inv_pow, one_div, show (2:ℝ) ^ (s + 2) = 4 * 2 ^ s by ring]
  have hA : (A : ℝ) ≤ max (Q x s : ℝ) 0 * 2 ^ (s + 1) ∧
      max (Q x s : ℝ) 0 * 2 ^ (s + 1) ≤ A + 1 := by
    rw [hAdef, ratDyadicFloor_eq_floor]
    by_cases h0 : 0 ≤ Q x s
    · have hr : max (Q x s : ℝ) 0 = (Q x s : ℝ) := max_eq_left (by exact_mod_cast h0)
      rw [hr]
      have hm2 : (0:ℚ) ≤ Q x s * ((2 ^ (s + 1) : ℕ) : ℚ) := mul_nonneg h0 (by positivity)
      have h1 := Nat.floor_le hm2
      have h2 := Nat.lt_floor_add_one (Q x s * ((2 ^ (s + 1) : ℕ) : ℚ))
      constructor
      · exact_mod_cast h1
      · exact_mod_cast h2.le
    · push Not at h0
      have hr : max (Q x s : ℝ) 0 = 0 := max_eq_right (by exact_mod_cast h0.le)
      have : Q x s * ((2 ^ (s + 1) : ℕ) : ℚ) ≤ 0 :=
        (mul_neg_of_neg_of_pos h0 (by positivity)).le
      rw [Nat.floor_of_nonpos this, hr]
      simp
  have hr' : |max (Q x s : ℝ) 0 - massR μ x| ≤ (2 : ℝ)⁻¹ ^ (s + 2) := by
    have := hQ x s
    rw [abs_le] at this ⊢
    rcases le_total (Q x s : ℝ) 0 with h | h
    · rw [max_eq_right h]
      constructor <;> linarith
    · rw [max_eq_left h]
      exact this
  have hAn : A ≤ 2 * a x s ∧ 2 * a x s ≤ A + 1 := by
    dsimp only [a]
    have hmod := Nat.mod_lt (A + 1) (by omega : 0 < 2)
    have hdivmod := Nat.div_add_mod (A + 1) 2
    omega
  have hAR : (A : ℝ) ≤ 2 * (a x s : ℝ) ∧ 2 * (a x s : ℝ) ≤ A + 1 := by
    exact_mod_cast hAn
  set r' := max (Q x s : ℝ) 0 with hr'def
  set t : ℝ := 2 ^ s with htdef
  rw [hinv, abs_le] at hr'
  have e1 : (r' - massR μ x) * t ≤ 1 / 4 := by
    calc (r' - massR μ x) * t ≤ 1 / (4 * t) * t :=
          mul_le_mul_of_nonneg_right hr'.2 ht.le
      _ = 1 / 4 := by field_simp
  have e2 : -(1 / 4) ≤ (r' - massR μ x) * t := by
    calc -(1 / 4) = -(1 / (4 * t)) * t := by field_simp
      _ ≤ (r' - massR μ x) * t := mul_le_mul_of_nonneg_right hr'.1 ht.le
  have key : |(a x s : ℝ) - massR μ x * t| ≤ 1 := by
    rw [abs_le]
    rw [hpow] at hA
    constructor <;> nlinarith [hA.1, hA.2, hAR.1, hAR.2]
  have hd_eq : (dyadicValue (a x s) s).toReal = (a x s : ℝ) / t := by
    unfold dyadicValue
    simp [htdef]
  have hd1_eq : (dyadicValue 1 s).toReal = 1 / t := by
    unfold dyadicValue
    simp [htdef]
  have hbd : |(dyadicValue (a x s) s).toReal - (cantorMass μ x).toReal| ≤
      (dyadicValue 1 s).toReal := by
    rw [hd_eq, hd1_eq]
    have : (a x s : ℝ) / t - (cantorMass μ x).toReal = ((a x s : ℝ) - massR μ x * t) / t := by
      unfold massR
      field_simp
    rw [this, abs_div, abs_of_pos ht]
    exact div_le_div_of_nonneg_right key ht.le
  have hd_top : dyadicValue (a x s) s ≠ ⊤ := (dyadicValue_lt_top _ _).ne
  have hmass_top : cantorMass μ x ≠ ⊤ := (measure_lt_top _ _).ne
  have he_top : dyadicValue 1 s ≠ ⊤ := (dyadicValue_lt_top _ _).ne
  rw [abs_le] at hbd
  constructor
  · rw [← ENNReal.toReal_le_toReal hd_top (ENNReal.add_ne_top.mpr ⟨hmass_top, he_top⟩),
      ENNReal.toReal_add hmass_top he_top]
    linarith
  · rw [← ENNReal.toReal_le_toReal hmass_top (ENNReal.add_ne_top.mpr ⟨hd_top, he_top⟩),
      ENNReal.toReal_add hd_top he_top]
    linarith

private lemma exists_conditional_measure_of_isComputablyRandom_limits_aux_marginal
    {P : Measure (CantorSeq × CantorSeq)} [IsProbabilityMeasure P]
    (hP : IsComputableProductMeasure P) : IsComputableMeasure (P.map Prod.fst) := by
  obtain ⟨q, hq, hb⟩ := hP
  refine exists_conditional_measure_of_isComputablyRandom_limits_aux_rounding
    (fun x s => q (x, [], s + 2)) ?_ ?_
  · have hs : Computable (fun z : BitString × ℕ => z.2 + 2) :=
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 2)).to_comp
    exact hq.comp (Computable.pair Computable.fst
      (Computable.pair (Computable.const []) hs))
  · intro x s
    have hmass : massR (P.map Prod.fst) x = (P (cantorCylinder x ×ˢ cantorCylinder [])).toReal := by
      unfold massR cantorMass
      rw [Measure.map_apply measurable_fst (measurableSet_cantorCylinder x)]
      rw [cantorCylinder_nil, ← Set.prod_univ]
    rw [hmass]
    exact hb x [] (s + 2)

private theorem exists_conditional_measure_of_isComputablyRandom_limits
    {P : Measure (CantorSeq × CantorSeq)} [IsProbabilityMeasure P]
    (hP : IsComputableProductMeasure P)
    (hpos : ∀ x, 0 < cantorMass (P.map Prod.fst) x)
    {α : CantorSeq} (hα : IsComputablyRandom (P.map Prod.fst) α) :
    ∃ L : BitString → ℝ, ∀ y,
      Tendsto (fun n => condSecond P (cantorCylinder y) (cantorPrefix α n))
        atTop (𝓝 (L y)) := by
  have hμ : IsComputableMeasure (P.map Prod.fst) :=
    exists_conditional_measure_of_isComputablyRandom_limits_aux_marginal hP
  have h : ∀ y, HasFiniteLimit (fun a => condSecond P (cantorCylinder y) a) α := fun y =>
    hasFiniteLimit_of_isComputablyRandom hμ hpos
      (exists_conditional_measure_of_isComputablyRandom_fair y)
      (exists_conditional_measure_of_isComputablyRandom_computable hP hpos y) hα
  choose L hL using h
  exact ⟨L, hL⟩

private theorem exists_conditional_measure_of_isComputablyRandom_measure
    (L : BitString → ℝ) (hnonneg : ∀ y, 0 ≤ L y) (hroot : L [] = 1)
    (hadd : ∀ y, L y = L (y ++ [false]) + L (y ++ [true])) :
    ∃ ν : Measure CantorSeq, IsProbabilityMeasure ν ∧ ∀ y, massR ν y = L y := by
  have hadd' : ∀ x, ENNReal.ofReal (L x) =
      ENNReal.ofReal (L (x ++ [false])) + ENNReal.ofReal (L (x ++ [true])) := by
    intro x
    rw [← ENNReal.ofReal_add (hnonneg _) (hnonneg _), ← hadd x]
  have ha : IsContinuousTreeSemimeasure (fun y => ENNReal.ofReal (L y)) := by
    constructor
    · change ENNReal.ofReal (L []) = 1
      rw [hroot, ENNReal.ofReal_one]
    · intro x
      exact (hadd' x).ge
  obtain ⟨ν, hν⟩ := exists_measure_cantorSeq_of_isContinuousTreeSemimeasure_of_exact ha hadd'
  refine ⟨ν, ?_, fun y => ?_⟩
  · constructor
    have h0 := hν []
    have hcyl : cantorCylinder ([] : BitString) = Set.univ := by
      ext w
      simp [cantorCylinder, IsCantorPrefix]
    rw [cantorMass, hcyl, hroot, ENNReal.ofReal_one] at h0
    exact h0
  · change (cantorMass ν y).toReal = L y
    rw [hν y, ENNReal.toReal_ofReal (hnonneg y)]

private theorem exists_conditional_measure_of_isComputablyRandom_nonneg
    {P : Measure (CantorSeq × CantorSeq)} [IsProbabilityMeasure P] {α : CantorSeq}
    (L : BitString → ℝ)
    (hL : ∀ y, Tendsto (fun n => condSecond P (cantorCylinder y) (cantorPrefix α n)) atTop
        (𝓝 (L y)))
    (y : BitString) : 0 ≤ L y := by
  refine ge_of_tendsto' (hL y) (fun n => ?_)
  unfold condSecond
  exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

private theorem exists_conditional_measure_of_isComputablyRandom_root
    {P : Measure (CantorSeq × CantorSeq)} [IsProbabilityMeasure P]
    (hpos : ∀ x, 0 < cantorMass (P.map Prod.fst) x) {α : CantorSeq}
    (L : BitString → ℝ)
    (hL : ∀ y, Tendsto (fun n => condSecond P (cantorCylinder y) (cantorPrefix α n)) atTop
        (𝓝 (L y))) :
    L [] = 1 := by
  have hnil : cantorCylinder ([] : BitString) = Set.univ := by
    ext w; simp [cantorCylinder, IsCantorPrefix]
  have hone : ∀ n, condSecond P (cantorCylinder ([] : BitString)) (cantorPrefix α n) = 1 := by
    intro n
    have hm : cantorMass (P.map Prod.fst) (cantorPrefix α n) =
        P (cantorCylinder (cantorPrefix α n) ×ˢ Set.univ) := by
      rw [cantorMass, Measure.map_apply measurable_fst (measurableSet_cantorCylinder _),
        Set.prod_univ]
    have hp := hpos (cantorPrefix α n)
    rw [hm] at hp
    unfold condSecond
    rw [hnil]
    exact div_self (ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top P _)).ne'
  have h1 : Tendsto (fun n => condSecond P (cantorCylinder ([] : BitString)) (cantorPrefix α n))
      atTop (𝓝 1) := by
    simp only [hone]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (hL []) h1

private lemma exists_conditional_measure_of_isComputablyRandom_add_cyl_union (x : BitString) :
    cantorCylinder x
      = cantorCylinder (x ++ [false]) ∪ cantorCylinder (x ++ [true]) := by
  ext w
  simp only [Set.mem_union, cantorCylinder, Set.mem_ofPred_eq]
  rw [isCantorPrefix_append_singleton, isCantorPrefix_append_singleton]
  constructor
  · intro hw
    by_cases hb : w x.length = true
    · exact Or.inr ⟨hw, hb⟩
    · exact Or.inl ⟨hw, by simpa using hb⟩
  · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw

private lemma exists_conditional_measure_of_isComputablyRandom_add_cyl_disjoint
    (x : BitString) :
    Disjoint (cantorCylinder (x ++ [false])) (cantorCylinder (x ++ [true])) := by
  have hne : ∀ (b1 b2 : Bool), b1 ≠ b2 → ¬ (x ++ [b1]) <+: (x ++ [b2]) := by
    intro b1 b2 hb hpref
    have hlen : (x ++ [b1]).length = (x ++ [b2]).length := by simp
    have heq := List.IsPrefix.eq_of_length hpref hlen
    have hbb := List.append_cancel_left heq
    rw [List.cons.injEq] at hbb
    exact hb hbb.1
  exact cantorCylinder_disjoint_of_incompatible (hne false true (by decide))
    (hne true false (by decide))

private lemma exists_conditional_measure_of_isComputablyRandom_add_condSecond_add
    (P : Measure (CantorSeq × CantorSeq)) [IsProbabilityMeasure P] (y a : BitString) :
    condSecond P (cantorCylinder y) a
      = condSecond P (cantorCylinder (y ++ [false])) a
        + condSecond P (cantorCylinder (y ++ [true])) a := by
  unfold condSecond
  rw [← add_div, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    exists_conditional_measure_of_isComputablyRandom_add_cyl_union y, Set.prod_union,
    measure_union]
  · exact Set.disjoint_prod.2 (Or.inr
      (exists_conditional_measure_of_isComputablyRandom_add_cyl_disjoint y))
  · exact (measurableSet_cantorCylinder _).prod (measurableSet_cantorCylinder _)

private theorem exists_conditional_measure_of_isComputablyRandom_add
    {P : Measure (CantorSeq × CantorSeq)} [IsProbabilityMeasure P] {α : CantorSeq}
    (L : BitString → ℝ)
    (hL : ∀ y, Tendsto (fun n => condSecond P (cantorCylinder y) (cantorPrefix α n)) atTop
        (𝓝 (L y)))
    (y : BitString) : L y = L (y ++ [false]) + L (y ++ [true]) := by
  have hsum := (hL (y ++ [false])).add (hL (y ++ [true]))
  have heq : (fun n => condSecond P (cantorCylinder y) (cantorPrefix α n))
      = fun n => condSecond P (cantorCylinder (y ++ [false])) (cantorPrefix α n)
        + condSecond P (cantorCylinder (y ++ [true])) (cantorPrefix α n) :=
    funext fun n =>
      exists_conditional_measure_of_isComputablyRandom_add_condSecond_add P y _
  have h1 := hL y
  rw [heq] at h1
  exact tendsto_nhds_unique h1 hsum

/-- **SUV Problem 269, p. 282.**  For a computable measure `P` on `Ω × Ω` and a sequence `α`
computably random with respect to its first projection, the conditional distribution of the second
coordinate given "the first coordinate equals `α`" is defined through the effective Doob theorem:
the conditional probabilities along `α` converge, to the masses of a probability measure.  The
book's standing assumption of p. 279 applies to the first projection, so its cylinders are required
to be positive. -/
theorem exists_conditional_measure_of_isComputablyRandom {P : Measure (CantorSeq × CantorSeq)}
    [IsProbabilityMeasure P] (hP : IsComputableProductMeasure P)
    (hpos : ∀ x, 0 < cantorMass (P.map Prod.fst) x) {α : CantorSeq}
    (hα : IsComputablyRandom (P.map Prod.fst) α) :
    ∃ ν : Measure CantorSeq, IsProbabilityMeasure ν ∧ ∀ y,
      Tendsto (fun n => condSecond P (cantorCylinder y) (cantorPrefix α n)) atTop
        (𝓝 (massR ν y)) := by
  have hL := exists_conditional_measure_of_isComputablyRandom_limits hP hpos hα
  obtain ⟨L, hL⟩ := hL
  have hnonneg := exists_conditional_measure_of_isComputablyRandom_nonneg L hL
  have hroot := exists_conditional_measure_of_isComputablyRandom_root hpos L hL
  have hadd := exists_conditional_measure_of_isComputablyRandom_add L hL
  have hmeasure := exists_conditional_measure_of_isComputablyRandom_measure L hnonneg hroot
      hadd
  obtain ⟨ν, hprob, hmass⟩ := hmeasure
  use ν
  refine ⟨hprob, fun y => ?_⟩
  rw [hmass y]
  exact hL y



end Kolmogorov.FrequencyGames
