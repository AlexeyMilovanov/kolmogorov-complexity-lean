/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Solomonoff.ShenQuestion.Construction

/-!
# A4–A5.  Every component gets stuck, and dominates `Q` at the stuck vertex

The counting argument (A4): a trigger of component `R` at stage `s` certifies

  `∑_{u ∈ F} m(u) ≥ ∑_{u ∈ F} m_s(u) > ∑_{u ∈ F} q_u / (R+1) = δ_R / (R+1) > 0`,

and the fronts of successive generations are pairwise disjoint (they are level sets at
strictly increasing depths, `GenInv.front_len` and `level` strictly increasing).  Since
`∑_x m x ≤ 1`, at most `(R+1) · 2^{R+1}` triggers can occur, so the generation is
eventually constant.

At the final generation the trigger fails at every stage, so some fixed `u` in the (finite)
front fails infinitely often, whence `(R+1) · m(u) ≤ q_u` (A4.5); and below `u` the
construction simulates `Q(· | u)` scaled by `q_u` forever, whence `q_u · Q(y|u) ≤ ν(u y)`
for all `y` (A5.2).
-/

namespace Kolmogorov
namespace Shen

open scoped ENNReal

variable {Q : BitString → BitString → ℝ≥0∞} {m : BitString → ℝ≥0∞}

/-! ### Dyadic bookkeeping and list helpers -/

private lemma dv_eq (n s : ℕ) : dyadicValue n s = (n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ s := by
  rw [dyadicValue, div_eq_mul_inv, ENNReal.inv_pow]

private lemma dv_lt_iff (a b s : ℕ) : dyadicValue a s < dyadicValue b s ↔ a < b := by
  have h0 : ((2:ℝ≥0∞)⁻¹) ^ s ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp))
  have htop : ((2:ℝ≥0∞)⁻¹) ^ s ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by simp))
  rw [dv_eq, dv_eq, ENNReal.mul_lt_mul_iff_left h0 htop, Nat.cast_lt]

private lemma dv_le_of_le {a b : ℕ} (h : a ≤ b) (s : ℕ) : dyadicValue a s ≤ dyadicValue b s := by
  rw [dv_eq, dv_eq]; gcongr

private lemma dv_add (a b s : ℕ) : dyadicValue (a + b) s = dyadicValue a s + dyadicValue b s := by
  rw [dv_eq, dv_eq, dv_eq]; push_cast; ring

private lemma dv_nat_mul (c n s : ℕ) : dyadicValue (c * n) s = (c : ℝ≥0∞) * dyadicValue n s := by
  rw [dv_eq, dv_eq]; push_cast; ring

private lemma dv_mul (a b s t : ℕ) :
    dyadicValue a s * dyadicValue b t = dyadicValue (a * b) (s + t) := by
  rw [dv_eq, dv_eq, dv_eq, pow_add]; push_cast; ring

private lemma dv_zero_stage (n : ℕ) : dyadicValue n 0 = (n : ℝ≥0∞) := by simp [dv_eq]

private lemma dv_scale (n : ℕ) {k s : ℕ} (h : k ≤ s) :
    dyadicValue (n * 2 ^ (s - k)) s = dyadicValue n k := by
  obtain ⟨d, rfl⟩ : ∃ d, s = k + d := ⟨s - k, by omega⟩
  simp only [Nat.add_sub_cancel_left]
  have h2 : ((2:ℝ≥0∞)) ^ d * ((2:ℝ≥0∞)⁻¹) ^ d = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by simp) (by simp), one_pow]
  rw [dv_eq, dv_eq, pow_add]
  push_cast
  rw [show ((n:ℝ≥0∞) * 2 ^ d) * (((2:ℝ≥0∞)⁻¹) ^ k * ((2:ℝ≥0∞)⁻¹) ^ d)
      = ((n:ℝ≥0∞) * ((2:ℝ≥0∞)⁻¹) ^ k) * ((2:ℝ≥0∞) ^ d * ((2:ℝ≥0∞)⁻¹) ^ d) from by ring,
    h2, mul_one]

private lemma dv_list_sum (l : List ℕ) (s : ℕ) :
    dyadicValue l.sum s = (l.map (fun n => dyadicValue n s)).sum := by
  induction l with
  | nil => simp [dyadicValue]
  | cons a t ih => simp [List.sum_cons, dv_add, ih]

private lemma list_sum_const_mul {α : Type*} (c : ℝ≥0∞) (f : α → ℝ≥0∞) (l : List α) :
    (l.map (fun a => c * f a)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih, mul_add]

private lemma list_sum_le_sum {α : Type*} {f g : α → ℝ≥0∞} :
    ∀ (l : List α), (∀ a ∈ l, f a ≤ g a) → (l.map f).sum ≤ (l.map g).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

private lemma compIdx_pLabel_append (R : ℕ) (v : BitString) :
    compIdx (pLabel R ++ v) = R := by
  induction R with
  | zero => simp [compIdx, pLabel]
  | succ R ih =>
      have hcons : pLabel (R+1) ++ v = true :: (pLabel R ++ v) := by
        simp [pLabel, List.replicate_succ]
      rw [compIdx, hcons, List.takeWhile_cons_of_pos (by simp)]
      simpa [compIdx] using ih

private lemma find?_eq_of_unique {α : Type*} (pr : α → Bool) (a : α) :
    ∀ (l : List α), a ∈ l → pr a = true → (∀ x ∈ l, pr x = true → x = a) →
      l.find? pr = some a := by
  intro l
  induction l with
  | nil => intro ha; simp at ha
  | cons c t ih =>
      intro ha hpa hu
      by_cases hc : pr c = true
      · rw [List.find?_cons_of_pos hc, hu c (by simp) hc]
      · rw [List.find?_cons_of_neg hc]
        have hat : a ∈ t := by
          rcases List.mem_cons.mp ha with rfl | h
          · exact absurd hpa hc
          · exact h
        exact ih hat hpa (fun x hx => hu x (List.mem_cons_of_mem _ hx))

/-! ### Fronts as finsets, and the level bookkeeping -/

private def frontSet (g : Gen) : Finset BitString := (g.front.map Prod.fst).toFinset

private lemma mem_frontSet {g : Gen} {x : BitString} (hx : x ∈ frontSet g) :
    ∃ b : ℕ, (x, b) ∈ g.front := by
  simp only [frontSet, List.mem_toFinset, List.mem_map] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  exact ⟨q.2, by simpa using hq⟩

private lemma sum_frontSet {R : ℕ} {g : Gen} (hinv : GenInv R g) (m : BitString → ℝ≥0∞) :
    ∑ x ∈ frontSet g, m x = (g.front.map (fun p => m p.1)).sum := by
  classical
  rw [frontSet, List.sum_toFinset _ hinv.front_nodup, List.map_map]
  rfl

private lemma frontSet_length {R : ℕ} {g : Gen} (hinv : GenInv R g) {x : BitString}
    (hx : x ∈ frontSet g) : x.length = g.level := by
  obtain ⟨b, hb⟩ := mem_frontSet hx
  exact hinv.front_len _ hb

private lemma transition_level (qa : ℕ → BitString → BitString → ℕ) (g : Gen) (s : ℕ) :
    (transition qa g s).level = g.level + (s - g.start) + 1 := rfl

private lemma transition_start (qa : ℕ → BitString → BitString → ℕ) (g : Gen) (s : ℕ) :
    (transition qa g s).start = s + 1 := rfl

private lemma genAt_level_lt (qa ma : ℕ → BitString → BitString → ℕ) (R n : ℕ)
    (h : trig ma R (genAt qa ma R n) (R + 1 + n) = true) :
    (genAt qa ma R n).level < (genAt qa ma R (n + 1)).level := by
  rw [genAt, ite_eq_left (by simp [h]), transition_level]
  omega

private lemma genAt_level_le (qa ma : ℕ → BitString → BitString → ℕ) (R : ℕ) {n n' : ℕ}
    (h : n ≤ n') : (genAt qa ma R n).level ≤ (genAt qa ma R n').level := by
  induction n' with
  | zero => have : n = 0 := by omega
            subst this; exact le_rfl
  | succ k ih =>
      rcases Nat.lt_or_ge n (k + 1) with h1 | h1
      · refine le_trans (ih (by omega)) ?_
        rw [genAt]
        split
        · rw [transition_level]; omega
        · exact le_rfl
      · have : n = k + 1 := by omega
        subst this; exact le_rfl


/-- **A4.3 + A4.4 (finitely many triggers; the component gets stuck).**

Proof sketch.  Let `T ⊆ ℕ` be the set of `n` with `trig ma R (genAt qa ma R n) (R+1+n) = true`.
For `n ∈ T` put `F_n := (genAt qa ma R n).front`.  By `GenInv` the vertices of `F_n` all have
length `(genAt qa ma R n).level`, and `transition` strictly increases `level`, so distinct
`n, n' ∈ T` give disjoint `F_n, F_{n'}`.  By the trigger condition and `hmle`
(`dyadicValue (ma s x []) s ≤ m x`), `∑_{u ∈ F_n} m u > 2^{-(R+1)}/(R+1)`; summing over any
`k` elements of `T` and using `hmsum : ∑' x, m x ≤ 1` (via `ENNReal.sum_le_tsum` on the
disjoint union of the fronts) gives `k · 2^{-(R+1)}/(R+1) ≤ 1`, so `T` is finite.  Take
`n₀ := max T + 1`.  Difficulty **H**, ~150 lines. -/
theorem exists_stable (hmsm : IsSemimeasure m) {qa ma : ℕ → BitString → BitString → ℕ}
    (hmsup : ∀ x, ⨆ s, dyadicValue (ma s x []) s = m x)
    (hcoh : ∀ u t y,
      qHat qa u t (y ++ [false]) + qHat qa u t (y ++ [true]) ≤ qHat qa u t y) (R : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → genAt qa ma R n = genAt qa ma R n₀ := by
  classical
  have hmle : ∀ (s : ℕ) (x : BitString), dyadicValue (ma s x []) s ≤ m x := by
    intro s x
    rw [← hmsup x]
    exact le_iSup (fun s => dyadicValue (ma s x []) s) s
  set T : Set ℕ := {n | trig ma R (genAt qa ma R n) (R + 1 + n) = true} with hTdef
  have hTmem : ∀ n : ℕ, n ∈ T ↔ trig ma R (genAt qa ma R n) (R + 1 + n) = true := by
    intro n; rw [hTdef]; exact Iff.rfl
  have key : ∀ n ∈ T, dyadicValue 1 (R + 1)
      ≤ ((R : ℝ≥0∞) + 1) * ∑ x ∈ frontSet (genAt qa ma R n), m x := by
    intro n hn
    have hinv := genInv_genAt' qa ma hcoh R n
    have hstart : (genAt qa ma R n).start ≤ R + 1 + n := genAt_start_le qa ma R n
    have htr : ∀ p ∈ (genAt qa ma R n).front,
        p.2 * 2 ^ (R + 1 + n - (genAt qa ma R n).start) < ma (R + 1 + n) p.1 [] * (R + 1) := by
      intro p hp
      have h := List.all_eq_true.mp ((hTmem n).mp hn) p hp
      simpa using h
    have hpd : ∀ p ∈ (genAt qa ma R n).front,
        dyadicValue p.2 (genAt qa ma R n).start ≤ ((R : ℝ≥0∞) + 1) * m p.1 := by
      intro p hp
      have h2 := dv_le_of_le (le_of_lt (htr p hp)) (R + 1 + n)
      rw [dv_scale _ hstart, mul_comm (ma (R + 1 + n) p.1 []) (R + 1), dv_nat_mul] at h2
      refine h2.trans ?_
      push_cast
      gcongr
      exact hmle _ _
    calc dyadicValue 1 (R + 1)
        = ((genAt qa ma R n).front.map
            (fun p => dyadicValue p.2 (genAt qa ma R n).start)).sum := by
          rw [← dv_scale 1 hinv.start_ge, one_mul, ← hinv.budget_sum, dv_list_sum, List.map_map]
          rfl
      _ ≤ ((genAt qa ma R n).front.map (fun p => ((R : ℝ≥0∞) + 1) * m p.1)).sum :=
          list_sum_le_sum _ hpd
      _ = ((R : ℝ≥0∞) + 1) * ∑ x ∈ frontSet (genAt qa ma R n), m x := by
          rw [list_sum_const_mul, sum_frontSet hinv]
  have hdisj : ∀ a b : ℕ, a ∈ T → b ∈ T → a ≠ b →
      Disjoint (frontSet (genAt qa ma R a)) (frontSet (genAt qa ma R b)) := by
    intro a b ha hb hab
    have hlv : (genAt qa ma R a).level ≠ (genAt qa ma R b).level := by
      rcases Nat.lt_or_ge a b with h | h
      · have h1 := genAt_level_lt qa ma R a ((hTmem a).mp ha)
        have h2 := genAt_level_le qa ma R (show a + 1 ≤ b by omega)
        omega
      · have h1 := genAt_level_lt qa ma R b ((hTmem b).mp hb)
        have h2 := genAt_level_le qa ma R (show b + 1 ≤ a by omega)
        omega
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact hlv ((frontSet_length (genInv_genAt' qa ma hcoh R a) hx).symm.trans
      (frontSet_length (genInv_genAt' qa ma hcoh R b) hx'))
  have hcard : ∀ S : Finset ℕ, (↑S ⊆ T) →
      (S.card : ℝ≥0∞) * dyadicValue 1 (R + 1) ≤ (R : ℝ≥0∞) + 1 := by
    intro S hS
    have h1 : ∑ _n ∈ S, dyadicValue 1 (R + 1)
        ≤ ∑ n ∈ S, ((R : ℝ≥0∞) + 1) * ∑ x ∈ frontSet (genAt qa ma R n), m x :=
      Finset.sum_le_sum (fun n hn => key n (hS (by simpa using hn)))
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h1
    have hpw : (↑S : Set ℕ).PairwiseDisjoint (fun n => frontSet (genAt qa ma R n)) :=
      fun a ha b hb hab => hdisj a b (hS ha) (hS hb) hab
    have h2 : ∑ n ∈ S, ∑ x ∈ frontSet (genAt qa ma R n), m x ≤ 1 := by
      rw [← Finset.sum_biUnion hpw]
      exact le_trans (ENNReal.sum_le_tsum _) hmsm
    calc (S.card : ℝ≥0∞) * dyadicValue 1 (R + 1)
        ≤ ((R : ℝ≥0∞) + 1) * ∑ n ∈ S, ∑ x ∈ frontSet (genAt qa ma R n), m x := h1
      _ ≤ ((R : ℝ≥0∞) + 1) * 1 := by gcongr
      _ = (R : ℝ≥0∞) + 1 := mul_one _
  have hTfin : T.Finite := by
    by_contra hinf
    obtain ⟨t, hts, htc⟩ :=
      Set.Infinite.exists_subset_card_eq hinf ((R + 1) * 2 ^ (R + 1) + 1)
    have h := hcard t hts
    rw [htc] at h
    have h2 : dyadicValue ((R + 1) * 2 ^ (R + 1) + 1) (R + 1)
        ≤ dyadicValue ((R + 1) * 2 ^ (R + 1)) (R + 1) := by
      calc dyadicValue ((R + 1) * 2 ^ (R + 1) + 1) (R + 1)
          = (((R + 1) * 2 ^ (R + 1) + 1 : ℕ) : ℝ≥0∞) * dyadicValue 1 (R + 1) := by
            rw [← dv_nat_mul, mul_one]
        _ ≤ (R : ℝ≥0∞) + 1 := h
        _ = dyadicValue ((R + 1) * 2 ^ (R + 1)) (R + 1) := by
            rw [show (R + 1) * 2 ^ (R + 1) = (R + 1) * 2 ^ ((R + 1) - 0) by simp,
              dv_scale _ (Nat.zero_le (R + 1)), dv_zero_stage]
            push_cast; ring
    exact absurd h2
      (not_le.mpr ((dv_lt_iff ((R + 1) * 2 ^ (R + 1)) ((R + 1) * 2 ^ (R + 1) + 1)
        (R + 1)).mpr (by omega)))
  obtain ⟨M, hM⟩ := hTfin.bddAbove
  refine ⟨M + 1, ?_⟩
  have hno : ∀ n, M + 1 ≤ n → genAt qa ma R (n + 1) = genAt qa ma R n := by
    intro n hn
    have hnt : trig ma R (genAt qa ma R n) (R + 1 + n) = false := by
      by_contra hc
      have hmemT : n ∈ T := (hTmem n).mpr (by simpa using hc)
      have := hM hmemT
      omega
    rw [genAt, ite_eq_right (by simp [hnt])]
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = M + 1 + k := ⟨n - (M + 1), by omega⟩
  clear hn
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show M + 1 + (k + 1) = (M + 1 + k) + 1 by omega, hno _ (by omega), ih]

/-- **A4.5 (the stuck vertex).**  In a generation that never triggers again some front
vertex carries at most `q_u/(R+1)` discrete mass.

Proof sketch.  For every `n ≥ n₀` the trigger is `false`, so by `List.all_eq_false` some
`p ∈ front` has `ma (R+1+n) p.1 [] * (R+1) ≤ p.2 * 2^{R+1+n - start}`.  The front is finite,
so one `p` occurs for infinitely many `n` (pigeonhole: `Set.Infinite.exists_...` or the
finite-cover argument on `List`).  Dividing by `2^{R+1+n}` this reads
`(R+1) · Q̂-free: (R+1) * dyadicValue (ma s p.1 []) s ≤ dyadicValue p.2 start`; take the
supremum over those `s` using `hmsup` and monotonicity.  Difficulty **M**, ~90 lines. -/
theorem exists_stuck_vertex {qa ma : ℕ → BitString → BitString → ℕ}
    (hmmono : ∀ s x, dyadicValue (ma s x []) s ≤ dyadicValue (ma (s + 1) x []) (s + 1))
    (hmsup : ∀ x, ⨆ s, dyadicValue (ma s x []) s = m x) (R n₀ : ℕ)
    (hstab : ∀ n, n₀ ≤ n → genAt qa ma R n = genAt qa ma R n₀) :
    ∃ p ∈ (genAt qa ma R n₀).front,
      ((R : ℝ≥0∞) + 1) * m p.1 ≤ dyadicValue p.2 (genAt qa ma R n₀).start := by
  classical
  set g := genAt qa ma R n₀ with hg
  have hstart : g.start ≤ R + 1 + n₀ := by rw [hg]; exact genAt_start_le qa ma R n₀
  -- after `n₀` the trigger never fires again
  have hno : ∀ n, n₀ ≤ n → trig ma R g (R + 1 + n) = false := by
    intro n hn
    by_contra hc
    have htrue : trig ma R (genAt qa ma R n) (R + 1 + n) = true := by
      rw [hstab n hn]; simpa using hc
    have h1 : genAt qa ma R (n + 1) = transition qa (genAt qa ma R n) (R + 1 + n) := by
      rw [genAt, ite_eq_left (by simp [htrue])]
    have h2 : genAt qa ma R (n + 1) = g := hstab (n + 1) (by omega)
    have h3 : g.start = R + 1 + n + 1 := by
      rw [← h2, h1, transition_start]
    omega
  -- stage monotonicity of the discrete approximation
  have hmmono' : ∀ x : BitString, Monotone (fun s => dyadicValue (ma s x []) s) :=
    fun x => monotone_nat_of_le_succ (fun s => hmmono s x)
  by_contra hcon
  push Not at hcon
  have hex : ∀ l : List (BitString × ℕ),
      (∀ p ∈ l, dyadicValue p.2 g.start < ((R : ℝ≥0∞) + 1) * m p.1) →
      ∃ s₁ : ℕ, ∀ p ∈ l, ∀ s, s₁ ≤ s →
        dyadicValue p.2 g.start < ((R : ℝ≥0∞) + 1) * dyadicValue (ma s p.1 []) s := by
    intro l
    induction l with
    | nil => intro _; exact ⟨0, by simp⟩
    | cons c t ih =>
        intro h
        obtain ⟨s₁, hs₁⟩ := ih (fun p hp => h p (by simp [hp]))
        have hc := h c (by simp)
        rw [← hmsup c.1, ENNReal.mul_iSup, lt_iSup_iff] at hc
        obtain ⟨s₂, hs₂⟩ := hc
        refine ⟨max s₁ s₂, ?_⟩
        intro p hp s hs
        rcases List.mem_cons.mp hp with rfl | hp'
        · refine lt_of_lt_of_le hs₂ ?_
          gcongr
          exact hmmono' p.1 (le_trans (le_max_right _ _) hs)
        · exact hs₁ p hp' s (le_trans (le_max_left _ _) hs)
  obtain ⟨s₁, hs₁⟩ := hex g.front hcon
  have hfalse := hno (max n₀ s₁) (le_max_left _ _)
  have htrue : trig ma R g (R + 1 + max n₀ s₁) = true := by
    rw [trig, List.all_eq_true]
    intro p hp
    simp only [decide_eq_true_eq]
    refine (dv_lt_iff _ _ (R + 1 + max n₀ s₁)).mp ?_
    have hle : g.start ≤ R + 1 + max n₀ s₁ := by
      have := le_max_left n₀ s₁; omega
    rw [dv_scale _ hle, mul_comm (ma (R + 1 + max n₀ s₁) p.1 []) (R + 1), dv_nat_mul]
    push_cast
    exact hs₁ p hp (R + 1 + max n₀ s₁) (by have := le_max_right n₀ s₁; omega)
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

private lemma front_find? {R : ℕ} {g : Gen} (hinv : GenInv R g) {p : BitString × ℕ}
    (hp : p ∈ g.front) (y : BitString) :
    g.front.find? (fun q => q.1.isPrefixOf (p.1 ++ y)) = some p := by
  refine find?_eq_of_unique _ p g.front hp ?_ ?_
  · exact List.isPrefixOf_iff_prefix.mpr ⟨y, rfl⟩
  · intro x hx hpx
    have h1 : x.1 <+: p.1 ++ y := List.isPrefixOf_iff_prefix.mp hpx
    have hlx : x.1.length = g.level := hinv.front_len x hx
    have hlp : p.1.length = g.level := hinv.front_len p hp
    have hfst : x.1 = p.1 := by
      rw [List.prefix_iff_eq_take.mp h1, hlx, ← hlp, List.take_left]
    exact List.inj_on_of_nodup_map hinv.front_nodup hx hp hfst

private lemma qHat_mono_stage {qa : ℕ → BitString → BitString → ℕ}
    (hqmono : ∀ s y u, dyadicValue (qa s y u) s ≤ dyadicValue (qa (s + 1) y u) (s + 1))
    (u y : BitString) : Monotone (fun t => dyadicValue (qHat qa u t y) t) :=
  monotone_nat_of_le_succ (fun t => qHat_stage_mono hqmono u t y)

/-- **A5.1 + A5.2 (domination below the stuck vertex).**

Proof sketch.  Write `g := genAt qa ma R n₀`, `σ := g.start`, `(u, b) ∈ g.front`.  For every
stage `s ≥ max σ (R+1+n₀)` we have `genAt qa ma R (s - R - 1) = g` by `hstab`, the vertex
`u ++ y` lies in component `R` (`u` extends `p_R`, so `compIdx (u ++ y) = R` and
`(u ++ y).length > R`), and `g.front.find?` returns `(u, b)` because the front is an
antichain containing `u` (`GenInv.front_len`, `front_nodup`); hence

  `nuStage qa ma s (u ++ y) = b * qHat qa u (s - σ) y`.

Therefore `nu qa ma (u ++ y) ≥ ⨆_{t} dyadicValue (b * qHat qa u t y) (σ + t)
= dyadicValue b σ * ⨆_t dyadicValue (qHat qa u t y) t = dyadicValue b σ * Q y u`
by `ENNReal.mul_iSup` and `qHat_iSup`.  Difficulty **H**, ~120 lines. -/
theorem nu_ge_below_front (hQ : IsConditionalContinuousTreeSemimeasure Q)
    {qa ma : ℕ → BitString → BitString → ℕ}
    (hqmono : ∀ s y u, dyadicValue (qa s y u) s ≤ dyadicValue (qa (s + 1) y u) (s + 1))
    (hqsup : ∀ y u, ⨆ s, dyadicValue (qa s y u) s = Q y u)
    (hcoh : ∀ u t y,
      qHat qa u t (y ++ [false]) + qHat qa u t (y ++ [true]) ≤ qHat qa u t y) (R n₀ : ℕ)
    (hstab : ∀ n, n₀ ≤ n → genAt qa ma R n = genAt qa ma R n₀)
    (p : BitString × ℕ) (hp : p ∈ (genAt qa ma R n₀).front) (y : BitString) :
    dyadicValue p.2 (genAt qa ma R n₀).start * Q y p.1 ≤ nu qa ma (p.1 ++ y) := by
  classical
  set g := genAt qa ma R n₀ with hg
  have hinv : GenInv R g := by rw [hg]; exact genInv_genAt' qa ma hcoh R n₀
  obtain ⟨w, hw⟩ := hinv.front_ext p hp
  have hcomp : ∀ v : BitString, compIdx (p.1 ++ v) = R := by
    intro v
    rw [← hw, List.append_assoc]
    exact compIdx_pLabel_append R _
  have hlenp : p.1.length = g.level := hinv.front_len p hp
  have hlevel : R + 1 ≤ g.level := hinv.level_ge
  have hstage : ∀ s : ℕ, R + 1 + n₀ ≤ s →
      nuStage qa ma s (p.1 ++ y) = p.2 * qHat qa p.1 (s - g.start) y := by
    intro s hs
    have h1 : compIdx (p.1 ++ y) = R := hcomp y
    have hne : ¬ ((p.1 ++ y).length = compIdx (p.1 ++ y)) := by
      rw [h1, List.length_append, hlenp]; omega
    have hlt : compIdx (p.1 ++ y) < s := by rw [h1]; omega
    rw [nuStage, ite_eq_right hne, ite_eq_left hlt, h1, hstab (s - R - 1) (by omega), compVal,
      front_find? hinv hp y]
    simp
  have hbound : ∀ t : ℕ, R + 1 + n₀ ≤ g.start + t →
      dyadicValue p.2 g.start * dyadicValue (qHat qa p.1 t y) t ≤ nu qa ma (p.1 ++ y) := by
    intro t ht
    have h := hstage (g.start + t) ht
    rw [Nat.add_sub_cancel_left] at h
    have heq : dyadicValue p.2 g.start * dyadicValue (qHat qa p.1 t y) t
        = dyadicValue (nuStage qa ma (g.start + t) (p.1 ++ y)) (g.start + t) := by
      rw [h, dv_mul]
    rw [heq, nu]
    exact le_iSup (fun s => dyadicValue (nuStage qa ma s (p.1 ++ y)) s) (g.start + t)
  rw [← qHat_iSup hQ hqmono hqsup p.1 y, ENNReal.mul_iSup]
  refine iSup_le fun t => ?_
  refine le_trans ?_ (hbound (max t (R + 1 + n₀)) ?_)
  · gcongr
    exact qHat_mono_stage hqmono p.1 y (le_max_left t (R + 1 + n₀))
  · have := le_max_right t (R + 1 + n₀); omega

/-- **A4 + A5 packaged.**  For every `R` there is a vertex `u` with a positive dyadic
budget `b / 2^σ` such that `ν` dominates `q_u · Q(· | u)` below `u`, while `u` carries at
most `q_u/(R+1)` discrete mass.  No `sorry` in this assembly. -/
theorem exists_stuck (hQ : IsConditionalContinuousTreeSemimeasure Q)
    (hmsm : IsSemimeasure m) {qa ma : ℕ → BitString → BitString → ℕ}
    (hqmono : ∀ s y u, dyadicValue (qa s y u) s ≤ dyadicValue (qa (s + 1) y u) (s + 1))
    (hqsup : ∀ y u, ⨆ s, dyadicValue (qa s y u) s = Q y u)
    (hmmono : ∀ s x, dyadicValue (ma s x []) s ≤ dyadicValue (ma (s + 1) x []) (s + 1))
    (hmsup : ∀ x, ⨆ s, dyadicValue (ma s x []) s = m x) (R : ℕ) :
    ∃ (u : BitString) (b σ : ℕ), 0 < b ∧
      (∀ y, dyadicValue b σ * Q y u ≤ nu qa ma (u ++ y)) ∧
      ((R : ℝ≥0∞) + 1) * m u ≤ dyadicValue b σ := by
  have hcoh : ∀ u t y,
      qHat qa u t (y ++ [false]) + qHat qa u t (y ++ [true]) ≤ qHat qa u t y :=
    qHat_coh (Q := Q) hQ hqsup
  obtain ⟨n₀, hstab⟩ := exists_stable (m := m) hmsm hmsup hcoh (qa := qa) (ma := ma) R
  obtain ⟨p, hp, hmass⟩ := exists_stuck_vertex (m := m) hmmono hmsup R n₀ hstab
  refine ⟨p.1, p.2, (genAt qa ma R n₀).start, ?_, ?_, hmass⟩
  · exact (genInv_genAt' qa ma hcoh R n₀).front_pos p hp
  · intro y
    exact nu_ge_below_front hQ hqmono hqsup hcoh R n₀ hstab p hp y

end Shen
end Kolmogorov
