/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.MartinLofImpliesStochastic

/-!
# K L Betting

Kolmogorov-Loveland randomness: a sequence is Kolmogorov-Loveland random if no non-monotonic
betting strategy (one that chooses which bit to reveal next) wins on it.  The main result is that
every Martin-Lof random sequence is Kolmogorov-Loveland random (SUV p. 309).
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-! ### Non-monotonic martingales: Kolmogorov-Loveland randomness -/

/-- **SUV p. 309.**  A non-monotonic betting strategy: as for rules, `next` chooses the next card,
and the capital is a partial rational function on the strings of revealed bits, with the fairness
equation wherever all three values are defined. -/
structure KLBetting where
  /-- Which bit to reveal, given the bits revealed so far. -/
  next : BitString →. ℕ
  /-- The capital after a string of revealed bits. -/
  capital : BitString →. ℚ
  /-- The same bit is never revealed twice. -/
  noRepeat : ∀ x y, x <+: y → x ≠ y → ∀ a ∈ next x, ∀ b ∈ next y, a ≠ b
  /-- The capital is non-negative. -/
  nonneg : ∀ x, ∀ q ∈ capital x, 0 ≤ q
  /-- The game is fair. -/
  fair : ∀ x q q₀ q₁, q ∈ capital x → q₀ ∈ capital (x ++ [false]) → q₁ ∈ capital (x ++ [true]) →
    q = (q₀ + q₁) / 2

/-- The rule revealing bits in the order of a betting strategy; `G` is irrelevant. -/
def KLBetting.toRule (β : KLBetting) : KLRule where
  next := β.next
  sel := fun _ => Part.some false
  noRepeat := β.noRepeat

/-- The strategy wins on `ω`: it reveals infinitely many bits, its capital is defined along the run,
and it is unbounded there. -/
def KLBetting.Wins (β : KLBetting) (w : CantorSeq) : Prop :=
  (∀ t, t ≤ (β.toRule.revealed w t).length) ∧ (∀ t, (β.capital (β.toRule.revealed w t)).Dom) ∧
    ¬ BddAbove {r : ℝ | ∃ t, ∃ q ∈ β.capital (β.toRule.revealed w t), (q : ℝ) = r}

/-- **SUV p. 309.**  *Kolmogorov-Loveland random* ("unpredictable") sequences: no computable
non-monotonic betting strategy wins. -/
def IsKLRandom (w : CantorSeq) : Prop :=
  ∀ β : KLBetting, Partrec β.next → Partrec β.capital → ¬ β.Wins w

/-- A *gain step* of a partial function `m` at `x` with bit `b`: both `m x` and `m (x ++ [b])` are
defined and `m (x ++ [b]) > 2 * m x`. -/
private def isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep
    (m : BitString →. ℚ) (x : BitString) (b : Bool) : Prop :=
  ∃ q ∈ m x, ∃ q' ∈ m (x ++ [b]), 2 * q < q'

namespace isKLRandom_of_isMartinLofRandom_step1_partialComputablyRandom_step1_gainCapital_aux

/-- `y` is alive: `m` is defined on every prefix of `y`. -/
private def GC_alive (m : BitString →. ℚ) (y : BitString) : Prop :=
  ∀ k, k ≤ y.length → (m (y.take k)).Dom

open Classical in
/-- The number of gain steps of `m` along `y` at positions `< n`. -/
private noncomputable def GC_count (m : BitString →. ℚ) (y : BitString) : ℕ → ℕ
  | 0 => 0
  | n + 1 => GC_count m y n +
      if isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m (y.take n)
        (y.getD n false) then 1 else 0

open Classical in
/-- The gain-counting capital of the proof. -/
private noncomputable def GC_cap (m : BitString →. ℚ) (y : BitString) : ℝ :=
  if GC_alive m y then (2 : ℝ) ^ GC_count m y y.length else 0

private lemma GC_alive_append (m : BitString →. ℚ) (x : BitString) (b : Bool) :
    GC_alive m (x ++ [b]) ↔ GC_alive m x ∧ (m (x ++ [b])).Dom := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · have := h k (by simp; omega)
      rwa [List.take_append_of_le_length hk] at this
    · have := h (x.length + 1) (by simp)
      rwa [List.take_of_length_le (by simp)] at this
  · rintro ⟨h1, h2⟩ k hk
    by_cases hk' : k ≤ x.length
    · rw [List.take_append_of_le_length hk']
      exact h1 k hk'
    · have : k = x.length + 1 := by simp at hk; omega
      subst this
      rwa [List.take_of_length_le (by simp)]

private lemma GC_count_append_le (m : BitString →. ℚ) (x : BitString) (b : Bool) :
    ∀ n, n ≤ x.length → GC_count m (x ++ [b]) n = GC_count m x n := by
  classical
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hlt : n < x.length := by omega
    simp only [GC_count, ih hlt.le, List.take_append_of_le_length hlt.le,
      List.getD_append _ _ _ _ hlt]

open Classical in
private lemma GC_count_append (m : BitString →. ℚ) (x : BitString) (b : Bool) :
    GC_count m (x ++ [b]) (x ++ [b]).length = GC_count m x x.length +
      if isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m x b
        then 1 else 0 := by
  classical
  have hl : (x ++ [b]).length = x.length + 1 := by simp
  rw [hl, GC_count, GC_count_append_le m x b x.length le_rfl,
    List.take_append_of_le_length le_rfl, List.take_length]
  simp

private lemma GC_cap_nonneg (m : BitString →. ℚ) (y : BitString) : 0 ≤ GC_cap m y := by
  unfold GC_cap
  split_ifs
  · positivity
  · exact le_rfl

private lemma GC_not_gain {m : BitString →. ℚ} (hmart : IsPartialMartingale m) {x : BitString}
    (h0 : (m (x ++ [false])).Dom) (h1 : (m (x ++ [true])).Dom) (b : Bool) :
    ¬ isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m x b := by
  rintro ⟨q, hq, q', hq', hlt⟩
  have hf := hmart.fair x q _ _ hq (Part.get_mem h0) (Part.get_mem h1)
  have n0 := hmart.nonneg _ _ (Part.get_mem h0)
  have n1 := hmart.nonneg _ _ (Part.get_mem h1)
  cases b
  · have e : q' = (m (x ++ [false])).get h0 := Part.mem_unique hq' (Part.get_mem h0)
    rw [e, hf] at hlt
    linarith
  · have e : q' = (m (x ++ [true])).get h1 := Part.mem_unique hq' (Part.get_mem h1)
    rw [e, hf] at hlt
    linarith

private lemma GC_cap_superfair {m : BitString →. ℚ} (hmart : IsPartialMartingale m)
    (x : BitString) :
    GC_cap m (x ++ [false]) + GC_cap m (x ++ [true]) ≤ 2 * GC_cap m x := by
  classical
  by_cases hx : GC_alive m x
  · have hcx : GC_cap m x = (2 : ℝ) ^ GC_count m x x.length := by
      unfold GC_cap; rw [ite_eq_left hx]
    have hchild : ∀ b, GC_cap m (x ++ [b]) =
        if (m (x ++ [b])).Dom then (2 : ℝ) ^ (GC_count m x x.length +
          if isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m x b
            then 1 else 0) else 0 := by
      intro b
      unfold GC_cap
      rw [GC_count_append]
      by_cases hd : (m (x ++ [b])).Dom
      · rw [ite_eq_left ((GC_alive_append m x b).2 ⟨hx, hd⟩), ite_eq_left hd]
      · rw [ite_eq_right (fun h => hd ((GC_alive_append m x b).1 h).2), ite_eq_right hd]
    have hle : ∀ b, GC_cap m (x ++ [b]) ≤ 2 * (2 : ℝ) ^ GC_count m x x.length := by
      intro b
      rw [hchild b]
      have hp : (0 : ℝ) < (2 : ℝ) ^ GC_count m x x.length := by positivity
      split_ifs
      · rw [pow_succ]; linarith
      · rw [add_zero]; linarith
      · linarith
    have hzero : ∀ b, ¬ (m (x ++ [b])).Dom → GC_cap m (x ++ [b]) = 0 := by
      intro b hd
      rw [hchild b, ite_eq_right hd]
    rw [hcx]
    have hp : (0 : ℝ) < (2 : ℝ) ^ GC_count m x x.length := by positivity
    by_cases d0 : (m (x ++ [false])).Dom <;> by_cases d1 : (m (x ++ [true])).Dom
    · rw [hchild false, hchild true, ite_eq_left d0, ite_eq_left d1,
        ite_eq_right (GC_not_gain hmart d0 d1 false), ite_eq_right (GC_not_gain hmart d0 d1 true)]
      simp only [add_zero]
      linarith
    · rw [hzero true d1]
      have := hle false
      linarith
    · rw [hzero false d0]
      have := hle true
      linarith
    · rw [hzero false d0, hzero true d1]
      linarith
  · have h0 : ∀ b, GC_cap m (x ++ [b]) = 0 := by
      intro b
      unfold GC_cap
      rw [ite_eq_right (fun h => hx ((GC_alive_append m x b).1 h).1)]
    have hcx : GC_cap m x = 0 := by
      unfold GC_cap; rw [ite_eq_right hx]
    rw [h0, h0, hcx]
    simp

private lemma GC_cap_isSuperfair {m : BitString →. ℚ} (hmart : IsPartialMartingale m) :
    IsSuperfairCapital uniformMeasure (GC_cap m) := by
  refine ⟨GC_cap_nonneg m, fun x => ?_⟩
  rw [massR_uniformMeasure, massR_uniformMeasure, massR_uniformMeasure]
  simp only [List.length_append, List.length_singleton, pow_succ]
  have h := GC_cap_superfair hmart x
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ x.length := by positivity
  nlinarith

open Classical in
private lemma GC_count_prefix_succ (m : BitString →. ℚ) (w : CantorSeq) (n : ℕ) :
    GC_count m (cantorPrefix w (n + 1)) (n + 1) = GC_count m (cantorPrefix w n) n +
      if isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m
        (cantorPrefix w n) (w n) then 1 else 0 := by
  have h := GC_count_append m (cantorPrefix w n) (w n)
  rw [← cantorPrefix_succ, cantorPrefix_length, cantorPrefix_length] at h
  exact h

private lemma GC_cap_wins {m : BitString →. ℚ} {w : CantorSeq}
    (hdom : ∀ n, (m (cantorPrefix w n)).Dom)
    (hinf : ∀ N, ∃ n ≥ N,
      isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m
        (cantorPrefix w n) (w n)) :
    Wins (GC_cap m) w := by
  classical
  have halive : ∀ n, GC_alive m (cantorPrefix w n) := by
    intro n k hk
    rw [cantorPrefix_take w k n (by simpa using hk)]
    exact hdom k
  set f : ℕ → ℕ := fun n => GC_count m (cantorPrefix w n) n with hf
  have hval : ∀ n, GC_cap m (cantorPrefix w n) = (2 : ℝ) ^ f n := by
    intro n
    unfold GC_cap
    rw [ite_eq_left (halive n), cantorPrefix_length]
  have hsucc : ∀ n, f (n + 1) = f n +
      if isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m
        (cantorPrefix w n) (w n) then 1 else 0 := fun n => GC_count_prefix_succ m w n
  have hmono : Monotone f := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rw [hsucc n]
    exact Nat.le_add_right _ _
  have hunb : ∀ K, ∃ n, K ≤ f n := by
    intro K
    induction K with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ K ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨n', hn', hg⟩ := hinf n
      refine ⟨n' + 1, ?_⟩
      rw [hsucc n', ite_eq_left hg]
      have := hmono hn'
      omega
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := hunb (⌈B⌉₊ + 1)
  have h2 : (⌈B⌉₊ + 1 : ℝ) < (2 : ℝ) ^ (⌈B⌉₊ + 1) := by
    exact_mod_cast Nat.lt_two_pow_self
  have h3 : (2 : ℝ) ^ (⌈B⌉₊ + 1) ≤ (2 : ℝ) ^ f n :=
    pow_le_pow_right₀ (by norm_num) hn
  have h4 : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  have h5 : (2 : ℝ) ^ f n ≤ B := by
    rw [← hval n]
    exact hB ⟨n, rfl⟩
  linarith

private def GC_scan (E : BitString → ℕ → Option ℚ) (y : BitString) (s : ℕ) (n : ℕ) :
    Option (ℚ × ℕ) :=
  Nat.rec ((E [] s).map (fun v => (v, 0)))
    (fun k IH => IH.bind (fun p => (E (y.take (k + 1)) s).map
      (fun v' => (v', cond (decide (2 * p.1 < v')) (p.2 + 1) p.2))))
    n

private lemma GC_scan_zero (E : BitString → ℕ → Option ℚ) (y : BitString) (s : ℕ) :
    GC_scan E y s 0 = (E [] s).map (fun v => (v, 0)) := rfl

private lemma GC_scan_succ (E : BitString → ℕ → Option ℚ) (y : BitString) (s k : ℕ) :
    GC_scan E y s (k + 1) = (GC_scan E y s k).bind (fun p => (E (y.take (k + 1)) s).map
      (fun v' => (v', cond (decide (2 * p.1 < v')) (p.2 + 1) p.2))) := rfl

private lemma GC_scan_sound {m : BitString →. ℚ} {E : BitString → ℕ → Option ℚ}
    (hEs : ∀ (a : BitString) (v : ℚ), v ∈ m a ↔ ∃ s, E a s = some v)
    (y : BitString) (s : ℕ) :
    ∀ n, n ≤ y.length → ∀ v c, GC_scan E y s n = some (v, c) →
      (∀ k, k ≤ n → (m (y.take k)).Dom) ∧ v ∈ m (y.take n) ∧ c = GC_count m y n := by
  classical
  intro n
  induction n with
  | zero =>
    intro _ v c h
    rw [GC_scan_zero] at h
    rcases hE : E [] s with _ | v0
    · rw [hE] at h; simp at h
    · rw [hE] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h2
      have hmem : v ∈ m [] := (hEs [] v).2 ⟨s, by rw [hE, h1]⟩
      refine ⟨fun k hk => ?_, by simpa using hmem, rfl⟩
      have : k = 0 := by omega
      subst this
      simpa using Part.dom_iff_mem.2 ⟨v, hmem⟩
  | succ n ih =>
    intro hn v c h
    rw [GC_scan_succ] at h
    rcases hp : GC_scan E y s n with _ | ⟨v0, c0⟩
    · rw [hp] at h; simp at h
    · rw [hp] at h
      rcases hE : E (y.take (n + 1)) s with _ | v1
      · rw [hE] at h; simp at h
      · rw [hE] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hal, hv0, hc0⟩ := ih (by omega) v0 c0 hp
        have hmem1 : v1 ∈ m (y.take (n + 1)) := (hEs _ v1).2 ⟨s, hE⟩
        have htake : y.take (n + 1) = y.take n ++ [y.getD n false] := by
          have hn' : n < y.length := by omega
          rw [List.take_add_one]
          simp [List.getElem?_eq_getElem hn']
        have hgain : isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m
            (y.take n) (y.getD n false) ↔ 2 * v0 < v1 := by
          unfold isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep
          rw [← htake]
          constructor
          · rintro ⟨q, hq, q', hq', hlt⟩
            rw [Part.mem_unique hq hv0, Part.mem_unique hq' hmem1] at hlt
            exact hlt
          · intro hlt
            exact ⟨v0, hv0, v1, hmem1, hlt⟩
        refine ⟨fun k hk => ?_, hmem1, ?_⟩
        · by_cases hkn : k ≤ n
          · exact hal k hkn
          · have : k = n + 1 := by omega
            subst this
            exact Part.dom_iff_mem.2 ⟨v1, hmem1⟩
        · rw [GC_count, ← hc0]
          by_cases hlt : 2 * v0 < v1
          · rw [ite_eq_left (hgain.2 hlt)]
            simp [hlt]
          · rw [ite_eq_right (fun h => hlt (hgain.1 h))]
            simp [hlt]

private lemma GC_scan_some {E : BitString → ℕ → Option ℚ} (y : BitString) (s : ℕ) :
    ∀ n, (∀ k, k ≤ n → (E (y.take k) s).isSome) → ∃ v c, GC_scan E y s n = some (v, c) := by
  intro n
  induction n with
  | zero =>
    intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (by simpa using h 0 le_rfl)
    exact ⟨v, 0, by rw [GC_scan_zero, hv]; rfl⟩
  | succ n ih =>
    intro h
    obtain ⟨v, c, hvc⟩ := ih (fun k hk => h k (by omega))
    obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.1 (h (n + 1) le_rfl)
    exact ⟨v', _, by rw [GC_scan_succ, hvc, hv']; rfl⟩

private lemma GC_stage_exists {m : BitString →. ℚ} {E : BitString → ℕ → Option ℚ}
    (hEs : ∀ (a : BitString) (v : ℚ), v ∈ m a ↔ ∃ s, E a s = some v)
    (hEm : ∀ (a : BitString) (s t : ℕ) (v : ℚ), s ≤ t → E a s = some v → E a t = some v)
    (y : BitString) (hy : GC_alive m y) :
    ∃ s, ∀ k, k ≤ y.length → (E (y.take k) s).isSome := by
  have : ∀ n, n ≤ y.length → ∃ s, ∀ k, k ≤ n → (E (y.take k) s).isSome := by
    intro n
    induction n with
    | zero =>
      intro _
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 (hy 0 (by omega))
      obtain ⟨s, hs⟩ := (hEs _ v).1 hv
      refine ⟨s, fun k hk => ?_⟩
      have : k = 0 := by omega
      subst this
      rw [hs]; rfl
    | succ n ih =>
      intro hn
      obtain ⟨s, hs⟩ := ih (by omega)
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 (hy (n + 1) hn)
      obtain ⟨s', hs'⟩ := (hEs _ v).1 hv
      refine ⟨max s s', fun k hk => ?_⟩
      by_cases hkn : k ≤ n
      · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hs k hkn)
        rw [hEm _ _ _ u (le_max_left _ _) hu]; rfl
      · have : k = n + 1 := by omega
        subst this
        rw [hEm _ _ _ v (le_max_right _ _) hs']; rfl
  exact this y.length le_rfl

private lemma GC_scan_computable {E : BitString → ℕ → Option ℚ} (hE : Computable₂ E) :
    Computable (fun p : BitString × ℕ => GC_scan E p.1 p.2 p.1.length) := by
  have hlen : Computable (fun p : BitString × ℕ => p.1.length) :=
    Primrec.list_length.to_comp.comp Computable.fst
  have hg : Computable (fun p : BitString × ℕ => (E [] p.2).map (fun v => (v, 0))) :=
    Computable.option_map (hE.comp (Computable.const []) Computable.snd)
      (Computable.pair Computable.snd (Computable.const 0)).to₂
  have hstep : Computable₂ (fun (a : BitString × ℕ) (z : ℕ × Option (ℚ × ℕ)) =>
      z.2.bind (fun p => (E (a.1.take (z.1 + 1)) a.2).map
        (fun v' => (v', cond (decide (2 * p.1 < v')) (p.2 + 1) p.2)))) := by
    refine Computable.option_bind (Computable.snd.comp Computable.snd) ?_
    refine Computable.option_map ?_ ?_
    · have h1 : Computable (fun r : ((BitString × ℕ) × (ℕ × Option (ℚ × ℕ))) × (ℚ × ℕ) =>
          r.1.2.1 + 1) :=
        Primrec.succ.to_comp.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
      have h2 : Computable (fun r : ((BitString × ℕ) × (ℕ × Option (ℚ × ℕ))) × (ℚ × ℕ) =>
          r.1.1.1.take (r.1.2.1 + 1)) :=
        Primrec.list_take.to_comp.comp h1 (Computable.fst.comp (Computable.fst.comp Computable.fst))
      exact hE.comp h2 (Computable.snd.comp (Computable.fst.comp Computable.fst))
    · have hmul : Computable (fun r : (((BitString × ℕ) × (ℕ × Option (ℚ × ℕ))) × (ℚ × ℕ)) × ℚ =>
          decide (2 * r.1.2.1 < r.2)) :=
        computable₂_ratLt.comp
          (computable₂_ratMul.comp (Computable.const 2)
            (Computable.fst.comp (Computable.snd.comp Computable.fst))) Computable.snd
      have hcnt : Computable (fun r : (((BitString × ℕ) × (ℕ × Option (ℚ × ℕ))) × (ℚ × ℕ)) × ℚ =>
          r.1.2.2) :=
        Computable.snd.comp (Computable.snd.comp Computable.fst)
      have hcnt1 : Computable (fun r : (((BitString × ℕ) × (ℕ × Option (ℚ × ℕ))) × (ℚ × ℕ)) × ℚ =>
          r.1.2.2 + 1) :=
        Primrec.succ.to_comp.comp hcnt
      have hcond : Computable (fun r : (((BitString × ℕ) × (ℕ × Option (ℚ × ℕ))) × (ℚ × ℕ)) × ℚ =>
          cond (decide (2 * r.1.2.1 < r.2)) (r.1.2.2 + 1) r.1.2.2) :=
        Computable.cond hmul hcnt1 hcnt
      exact (Computable.pair Computable.snd hcond).to₂
  exact (Computable.nat_rec hlen hg hstep).of_eq (fun p => rfl)

private def GC_test (E : BitString → ℕ → Option ℚ) (q : (ℚ × BitString) × ℕ) : Bool :=
  decide (q.1.1 < 0) ||
    ((GC_scan E q.1.2 q.2 q.1.2.length).map
      (fun p => decide (q.1.1 < ((2 ^ p.2 : ℕ) : ℚ)))).getD false

private lemma GC_test_computable {E : BitString → ℕ → Option ℚ} (hE : Computable₂ E) :
    Computable (GC_test E) := by
  have hF := GC_scan_computable hE
  have hy : Computable (fun q : (ℚ × BitString) × ℕ => q.1.2) :=
    Computable.snd.comp Computable.fst
  have hr : Computable (fun q : (ℚ × BitString) × ℕ => q.1.1) :=
    Computable.fst.comp Computable.fst
  have c1 : Computable (fun q : (ℚ × BitString) × ℕ => decide (q.1.1 < 0)) :=
    computable₂_ratLt.comp hr (Computable.const 0)
  have cS : Computable (fun q : (ℚ × BitString) × ℕ =>
      GC_scan E q.1.2 q.2 q.1.2.length) := hF.comp (Computable.pair hy Computable.snd)
  have cpow : Computable (fun r : ((ℚ × BitString) × ℕ) × (ℚ × ℕ) =>
      ((2 ^ r.2.2 : ℕ) : ℚ)) :=
    computable_nat_to_rat.comp
      (nat_pow_primrec₂.to_comp.comp (Computable.const 2) (Computable.snd.comp Computable.snd))
  have cB : Computable (fun q : (ℚ × BitString) × ℕ =>
      ((GC_scan E q.1.2 q.2 q.1.2.length).map
        (fun p => decide (q.1.1 < ((2 ^ p.2 : ℕ) : ℚ)))).getD false) := by
    refine Primrec.option_getD.to_comp.comp ?_ (Computable.const false)
    refine Computable.option_map cS ?_
    exact computable₂_ratLt.comp (hr.comp Computable.fst) cpow
  unfold GC_test
  exact Primrec.or.to_comp.comp c1 cB

private lemma GC_test_iff {m : BitString →. ℚ} {E : BitString → ℕ → Option ℚ}
    (hEm : ∀ (a : BitString) (s t : ℕ) (v : ℚ), s ≤ t → E a s = some v → E a t = some v)
    (hEs : ∀ (a : BitString) (v : ℚ), v ∈ m a ↔ ∃ s, E a s = some v)
    (r : ℚ) (y : BitString) :
    (r : ℝ) < GC_cap m y ↔ ∃ s, GC_test E ((r, y), s) = true := by
  classical
  constructor
  · intro h
    by_cases hr : r < 0
    · exact ⟨0, by simp [GC_test, hr]⟩
    have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast not_lt.1 hr
    by_cases ha : GC_alive m y
    · have hcap : GC_cap m y = (2 : ℝ) ^ GC_count m y y.length := by
        unfold GC_cap; rw [ite_eq_left ha]
      rw [hcap] at h
      obtain ⟨s, hs⟩ := GC_stage_exists hEs hEm y ha
      obtain ⟨v, c, hvc⟩ := GC_scan_some (E := E) y s y.length hs
      obtain ⟨-, -, hc⟩ := GC_scan_sound hEs y s y.length le_rfl v c hvc
      refine ⟨s, ?_⟩
      have hlt : r < ((2 ^ c : ℕ) : ℚ) := by
        rw [hc]
        have : (r : ℝ) < ((2 ^ GC_count m y y.length : ℕ) : ℝ) := by
          push_cast; exact h
        exact_mod_cast this
      simp only [GC_test, hvc, Option.map_some, Option.getD_some, Bool.or_eq_true,
        decide_eq_true_eq]
      exact Or.inr hlt
    · have hcap : GC_cap m y = 0 := by
        unfold GC_cap; rw [ite_eq_right ha]
      rw [hcap] at h
      exact absurd h (not_lt.2 hr0)
  · rintro ⟨s, hs⟩
    unfold GC_test at hs
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hs
    rcases hs with h1 | h2
    · exact lt_of_lt_of_le (by exact_mod_cast h1) (GC_cap_nonneg m y)
    · rcases hsc : GC_scan E y s y.length with _ | ⟨v, c⟩
      · rw [hsc] at h2; simp at h2
      · rw [hsc] at h2
        simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at h2
        obtain ⟨hal, -, hc⟩ := GC_scan_sound hEs y s y.length le_rfl v c hsc
        have ha : GC_alive m y := hal
        unfold GC_cap
        rw [ite_eq_left ha, ← hc]
        have : (r : ℝ) < (((2 ^ c : ℕ) : ℚ) : ℝ) := by exact_mod_cast h2
        simpa using this

private lemma GC_cap_lsc {m : BitString →. ℚ} (hm : Partrec m) :
    IsLowerSemicomputableOnStrings (GC_cap m) := by
  obtain ⟨E, hEc, hEm, hEs⟩ :=
    isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_stepEval hm
  have hRE : IsRE (fun q : (ℚ × BitString) × ℕ => GC_test E q = true) :=
    isRE_of_computable_bool _ (GC_test E) (fun _ => Iff.rfl) (GC_test_computable hEc)
  have hex := IsRE.exists_encodable
    (R := fun (p : ℚ × BitString) (s : ℕ) => GC_test E (p, s) = true) hRE
  exact hex.of_iff (fun p => (GC_test_iff hEm hEs p.1 p.2).symm)

end isKLRandom_of_isMartinLofRandom_step1_partialComputablyRandom_step1_gainCapital_aux

/-- Step 1 of the proof of
`isKLRandom_of_isMartinLofRandom_partialComputablyRandom`:
the gain-counting capital.  For a partial computable partial martingale `m` there is a lower
semicomputable superfair capital `P` (for the uniform measure) that wins on every sequence along
which `m` is defined on all prefixes and has infinitely many gain steps.  Take `P(y) = 2^{g(y)}` if
`m` is defined on every prefix of `y` (`y` alive), where `g(y)` is the number of gain steps along
`y`, and `P(y) = 0` otherwise. A gain child `xb` of an alive `x` has no alive sibling (the sibling's
value would be `2 m(x) - m(xb) < 0` by fairness), and so `(P(x0) + P(x1))/2 ≤ P(x)`.
Lower semicomputability uses a stage-bounded evaluation of `m`. -/
private lemma isKLRandom_of_isMartinLofRandom_gainCapital
    (m : BitString →. ℚ) (hm : Partrec m) (hmart : IsPartialMartingale m) :
    ∃ P : BitString → ℝ, IsLowerSemicomputableOnStrings P ∧ IsSuperfairCapital uniformMeasure P ∧
      ∀ w : CantorSeq, (∀ n, (m (cantorPrefix w n)).Dom) →
        (∀ N, ∃ n ≥ N,
          isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m
            (cantorPrefix w n) (w n)) → Wins P w := by
  open isKLRandom_of_isMartinLofRandom_step1_partialComputablyRandom_step1_gainCapital_aux in
  exact ⟨GC_cap m, GC_cap_lsc hm, GC_cap_isSuperfair hmart,
    fun w hdom hinf => GC_cap_wins hdom hinf⟩

namespace isKLRandom_of_isMartinLofRandom_step1_partialComputablyRandom_step2_noGainCapital_aux

/-- `y` is alive: `m` is defined on every prefix of `y`. -/
private def NGC_alive (m : BitString →. ℚ) (y : BitString) : Prop :=
  ∀ k, k ≤ y.length → (m (y.take k)).Dom

/-- No gain step of `m` along `y` at positions `≥ |σ|`. -/
private def NGC_noGain (m : BitString →. ℚ) (σ y : BitString) : Prop :=
  ∀ k, σ.length ≤ k → k < y.length →
    ¬ isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m (y.take k)
      (y.getD k false)

open Classical in
private noncomputable def NGC_mv (m : BitString →. ℚ) (y : BitString) : ℚ :=
  if h : (m y).Dom then (m y).get h else 0

open Classical in
/-- The capital of the proof. -/
private noncomputable def NGC_cap (m : BitString →. ℚ) (σ y : BitString) : ℝ :=
  if σ <+: y then (if NGC_alive m y ∧ NGC_noGain m σ y then (NGC_mv m y : ℝ) else 0)
  else if y <+: σ ∧ NGC_alive m σ then (NGC_mv m σ : ℝ) / 2 ^ (σ.length - y.length) else 0

private lemma NGC_alive_append (m : BitString →. ℚ) (x : BitString) (b : Bool) :
    NGC_alive m (x ++ [b]) ↔ NGC_alive m x ∧ (m (x ++ [b])).Dom := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · have := h k (by simp; omega)
      rwa [List.take_append_of_le_length hk] at this
    · have := h (x.length + 1) (by simp)
      rwa [List.take_of_length_le (by simp)] at this
  · rintro ⟨h1, h2⟩ k hk
    by_cases hk' : k ≤ x.length
    · rw [List.take_append_of_le_length hk']
      exact h1 k hk'
    · have : k = x.length + 1 := by simp at hk; omega
      subst this
      rwa [List.take_of_length_le (by simp)]

private lemma NGC_alive_dom {m : BitString →. ℚ} {y : BitString} (h : NGC_alive m y) :
    (m y).Dom := by
  simpa using h y.length le_rfl

private lemma NGC_noGain_append (m : BitString →. ℚ) (σ x : BitString) (b : Bool) :
    NGC_noGain m σ (x ++ [b]) ↔
      NGC_noGain m σ x ∧ (σ.length ≤ x.length →
        ¬ isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m x b) := by
  constructor
  · intro h
    refine ⟨fun k hk hk' => ?_, fun hs => ?_⟩
    · have := h k hk (by simp; omega)
      rwa [List.take_append_of_le_length hk'.le, List.getD_append _ _ _ _ hk'] at this
    · have := h x.length hs (by simp)
      simpa using this
  · rintro ⟨h1, h2⟩ k hk hk'
    by_cases hlt : k < x.length
    · rw [List.take_append_of_le_length hlt.le, List.getD_append _ _ _ _ hlt]
      exact h1 k hk hlt
    · have : k = x.length := by simp at hk'; omega
      subst this
      simpa using h2 hk

private lemma NGC_noGain_self (m : BitString →. ℚ) (σ : BitString) : NGC_noGain m σ σ :=
  fun k hk hk' => absurd hk' (by omega)

private lemma NGC_mv_nonneg {m : BitString →. ℚ} (hmart : IsPartialMartingale m) {y : BitString}
    (h : (m y).Dom) : 0 ≤ NGC_mv m y := by
  unfold NGC_mv
  rw [dite_eq_left h]
  exact hmart.nonneg y _ (Part.get_mem h)

private lemma NGC_mv_mem {m : BitString →. ℚ} {y : BitString}
    (h : (m y).Dom) : NGC_mv m y ∈ m y := by
  unfold NGC_mv
  rw [dite_eq_left h]
  exact Part.get_mem h

open Classical in
private lemma NGC_cap_of_ext {m : BitString →. ℚ} {σ y : BitString} (h : σ <+: y) :
    NGC_cap m σ y = if NGC_alive m y ∧ NGC_noGain m σ y then (NGC_mv m y : ℝ) else 0 := by
  unfold NGC_cap; rw [ite_eq_left h]

open Classical in
private lemma NGC_cap_of_prefix {m : BitString →. ℚ} {σ y : BitString} (h : y <+: σ) :
    NGC_cap m σ y = if NGC_alive m σ then (NGC_mv m σ : ℝ) / 2 ^ (σ.length - y.length) else 0 := by
  by_cases hs : σ <+: y
  · have : y = σ := h.eq_of_length (le_antisymm h.length_le hs.length_le)
    subst this
    rw [NGC_cap_of_ext hs]
    simp only [Nat.sub_self, pow_zero, div_one]
    by_cases ha : NGC_alive m y
    · rw [ite_eq_left ⟨ha, NGC_noGain_self m y⟩, ite_eq_left ha]
    · rw [ite_eq_right (fun h => ha h.1), ite_eq_right ha]
  · unfold NGC_cap
    rw [ite_eq_right hs]
    by_cases ha : NGC_alive m σ
    · rw [ite_eq_left ⟨h, ha⟩, ite_eq_left ha]
    · rw [ite_eq_right (fun h => ha h.2), ite_eq_right ha]

private lemma NGC_cap_of_incomp {m : BitString →. ℚ} {σ y : BitString} (h1 : ¬ σ <+: y)
    (h2 : ¬ y <+: σ) : NGC_cap m σ y = 0 := by
  unfold NGC_cap
  rw [ite_eq_right h1, ite_eq_right (fun h => h2 h.1)]

private lemma NGC_cap_nonneg {m : BitString →. ℚ} (hmart : IsPartialMartingale m) (σ y : BitString)
    :
    0 ≤ NGC_cap m σ y := by
  unfold NGC_cap
  split_ifs with h1 h2 h3
  · exact_mod_cast NGC_mv_nonneg hmart (NGC_alive_dom h2.1)
  · exact le_rfl
  · exact div_nonneg (by exact_mod_cast NGC_mv_nonneg hmart (NGC_alive_dom h3.2)) (by positivity)
  · exact le_rfl

private lemma NGC_incomp_child {σ x : BitString} {r : Bool} {t : BitString}
    (ht : x ++ r :: t = σ) (hx : ¬ σ <+: x) (b : Bool) (hb : b ≠ r) :
    ¬ σ <+: x ++ [b] ∧ ¬ x ++ [b] <+: σ := by
  constructor
  · intro h
    rcases List.prefix_concat_iff.1 h with h | h
    · apply hb
      rw [← ht] at h
      have := List.append_cancel_left h
      simp only [List.cons.injEq] at this
      exact this.1.symm
    · exact hx h
  · rintro ⟨u, hu⟩
    apply hb
    rw [← ht] at hu
    exact (by simpa [List.append_assoc] using hu : b = r ∧ u = t).1

private lemma NGC_cap_superfair_ext {m : BitString →. ℚ} (hmart : IsPartialMartingale m)
    {σ x : BitString} (hx : σ <+: x) :
    NGC_cap m σ (x ++ [false]) + NGC_cap m σ (x ++ [true]) ≤ 2 * NGC_cap m σ x := by
  classical
  have hc : ∀ b, σ <+: x ++ [b] := fun b => hx.trans (List.prefix_append _ _)
  by_cases hq : NGC_alive m x ∧ NGC_noGain m σ x
  · have hxd := NGC_alive_dom hq.1
    have hv0 : 0 ≤ NGC_mv m x := NGC_mv_nonneg hmart hxd
    have hvmem := NGC_mv_mem hxd
    have hgain : ∀ b,
        isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m x b ↔
        (m (x ++ [b])).Dom ∧ 2 * NGC_mv m x < NGC_mv m (x ++ [b]) := by
      intro b
      constructor
      · rintro ⟨q, hq, q', hq', hlt⟩
        have e1 : q = NGC_mv m x := Part.mem_unique hq hvmem
        have hd : (m (x ++ [b])).Dom := Part.dom_iff_mem.2 ⟨q', hq'⟩
        have e2 : q' = NGC_mv m (x ++ [b]) := Part.mem_unique hq' (NGC_mv_mem hd)
        exact ⟨hd, by rw [← e1, ← e2]; exact hlt⟩
      · rintro ⟨hd, hlt⟩
        exact ⟨_, hvmem, _, NGC_mv_mem hd, hlt⟩
    have hchild : ∀ b, NGC_cap m σ (x ++ [b]) =
        if (m (x ++ [b])).Dom ∧ ¬ (2 * NGC_mv m x < NGC_mv m (x ++ [b]))
          then (NGC_mv m (x ++ [b]) : ℝ) else 0 := by
      intro b
      rw [NGC_cap_of_ext (hc b)]
      refine if_congr ?_ rfl rfl
      rw [NGC_alive_append, NGC_noGain_append]
      constructor
      · rintro ⟨⟨_, hd⟩, _, hng⟩
        exact ⟨hd, fun hlt => hng hx.length_le ((hgain b).2 ⟨hd, hlt⟩)⟩
      · rintro ⟨hd, hn⟩
        exact ⟨⟨hq.1, hd⟩, hq.2, fun _ hg => hn ((hgain b).1 hg).2⟩
    have hv0' : (0 : ℝ) ≤ (NGC_mv m x : ℝ) := by exact_mod_cast hv0
    have hbound : ∀ b, NGC_cap m σ (x ++ [b]) ≤ 2 * (NGC_mv m x : ℝ) := by
      intro b
      rw [hchild b]
      split_ifs with h
      · have h2 := h.2
        push Not at h2
        have : (NGC_mv m (x ++ [b]) : ℝ) ≤ 2 * (NGC_mv m x : ℝ) := by exact_mod_cast h2
        exact this
      · linarith
    have hzero : ∀ b, ¬ (m (x ++ [b])).Dom → NGC_cap m σ (x ++ [b]) = 0 := by
      intro b hd
      rw [hchild b, ite_eq_right (fun h => hd h.1)]
    rw [NGC_cap_of_ext hx, ite_eq_left hq]
    by_cases d0 : (m (x ++ [false])).Dom <;> by_cases d1 : (m (x ++ [true])).Dom
    · have hf := hmart.fair x _ _ _ hvmem (NGC_mv_mem d0) (NGC_mv_mem d1)
      have n0 := NGC_mv_nonneg hmart d0
      have n1 := NGC_mv_nonneg hmart d1
      have h0 : ¬ 2 * NGC_mv m x < NGC_mv m (x ++ [false]) := by
        intro h; rw [hf] at h; linarith
      have h1 : ¬ 2 * NGC_mv m x < NGC_mv m (x ++ [true]) := by
        intro h; rw [hf] at h; linarith
      rw [hchild false, hchild true, ite_eq_left ⟨d0, h0⟩, ite_eq_left ⟨d1, h1⟩]
      have : (NGC_mv m x : ℝ) = ((NGC_mv m (x ++ [false]) : ℝ) + (NGC_mv m (x ++ [true]) : ℝ)) /
          2 := by
        exact_mod_cast hf
      linarith
    · rw [hzero true d1]
      have := hbound false
      linarith
    · rw [hzero false d0]
      have := hbound true
      linarith
    · rw [hzero false d0, hzero true d1]
      linarith
  · rw [NGC_cap_of_ext hx, ite_eq_right hq]
    have : ∀ b, NGC_cap m σ (x ++ [b]) = 0 := by
      intro b
      rw [NGC_cap_of_ext (hc b), ite_eq_right]
      rintro ⟨h1, h2⟩
      exact hq ⟨((NGC_alive_append m x b).1 h1).1, ((NGC_noGain_append m σ x b).1 h2).1⟩
    rw [this, this]
    simp

private lemma NGC_cap_superfair {m : BitString →. ℚ} (hmart : IsPartialMartingale m)
    (σ x : BitString) :
    NGC_cap m σ (x ++ [false]) + NGC_cap m σ (x ++ [true]) ≤ 2 * NGC_cap m σ x := by
  by_cases hx : σ <+: x
  · exact NGC_cap_superfair_ext hmart hx
  by_cases hxp : x <+: σ
  · obtain ⟨t, ht⟩ := hxp
    cases t with
    | nil => exact absurd (by rw [List.append_nil] at ht; rw [← ht]) hx
    | cons r t' =>
      have hr : x ++ [r] <+: σ := ⟨t', by rw [← ht]; simp⟩
      have hother : ∀ b, b ≠ r → NGC_cap m σ (x ++ [b]) = 0 := fun b hb =>
        NGC_cap_of_incomp (NGC_incomp_child ht hx b hb).1 (NGC_incomp_child ht hx b hb).2
      have hlen : σ.length = x.length + (t'.length + 1) := by rw [← ht]; simp
      have hkey : NGC_cap m σ (x ++ [r]) = 2 * NGC_cap m σ x := by
        rw [NGC_cap_of_prefix hr, NGC_cap_of_prefix ⟨_, ht⟩]
        classical
        by_cases ha : NGC_alive m σ
        · rw [ite_eq_left ha, ite_eq_left ha]
          have e1 : σ.length - x.length = t'.length + 1 := by omega
          have e2 : σ.length - (x ++ [r]).length = t'.length := by simp; omega
          rw [e1, e2, pow_succ]
          field_simp
        · rw [ite_eq_right ha, ite_eq_right ha]; simp
      cases r
      · rw [hkey, hother true (by simp)]; linarith
      · rw [hkey, hother false (by simp)]; linarith
  · have h0 : ∀ b, NGC_cap m σ (x ++ [b]) = 0 := by
      intro b
      refine NGC_cap_of_incomp ?_ ?_
      · intro h
        rcases List.prefix_concat_iff.1 h with h | h
        · exact hxp (by rw [h]; exact List.prefix_append _ _)
        · exact hx h
      · intro h
        exact hxp ((List.prefix_append _ _).trans h)
    rw [h0, h0, NGC_cap_of_incomp hx hxp]
    simp

private lemma NGC_cap_isSuperfair {m : BitString →. ℚ} (hmart : IsPartialMartingale m)
    (σ : BitString) : IsSuperfairCapital uniformMeasure (NGC_cap m σ) := by
  refine ⟨NGC_cap_nonneg hmart σ, fun x => ?_⟩
  rw [massR_uniformMeasure, massR_uniformMeasure, massR_uniformMeasure]
  simp only [List.length_append, List.length_singleton, pow_succ]
  have h := NGC_cap_superfair hmart σ x
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ x.length := by positivity
  nlinarith

private lemma NGC_cap_wins {m : BitString →. ℚ} {σ : BitString} {w : CantorSeq}
    (hw : PartialWins m w) (hσ : cantorPrefix w σ.length = σ)
    (hng : ∀ n ≥ σ.length,
      ¬ isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m
        (cantorPrefix w n) (w n)) :
    Wins (NGC_cap m σ) w := by
  have hval : ∀ n ≥ σ.length,
      NGC_cap m σ (cantorPrefix w n) = (NGC_mv m (cantorPrefix w n) : ℝ) := by
    intro n hn
    have hpre : σ <+: cantorPrefix w n := by
      rw [← hσ]; exact cantorPrefix_mono w hn
    rw [NGC_cap_of_ext hpre, ite_eq_left]
    refine ⟨fun k hk => ?_, fun k hk hk' => ?_⟩
    · rw [cantorPrefix_take w k n (by simpa using hk)]
      exact hw.1 k
    · rw [cantorPrefix_length] at hk'
      rw [cantorPrefix_take w k n hk'.le]
      have : (cantorPrefix w n).getD k false = w k := by
        rw [List.getD_eq_getElem _ _ (by simpa using hk')]
        exact cantorPrefix_getElem w n k _
      rw [this]
      exact hng k hk
  intro hB
  obtain ⟨B, hB⟩ := hB
  obtain ⟨C, hC⟩ := ((Set.finite_lt_nat σ.length).image
    (fun n => ((NGC_mv m (cantorPrefix w n) : ℚ) : ℝ))).bddAbove
  apply hw.2
  refine ⟨max B C, ?_⟩
  rintro r ⟨n, q, hq, rfl⟩
  have hqv : q = NGC_mv m (cantorPrefix w n) :=
    Part.mem_unique hq (NGC_mv_mem (hw.1 n))
  rw [hqv]
  by_cases hn : σ.length ≤ n
  · rw [← hval n hn]
    exact le_max_of_le_left (hB ⟨n, rfl⟩)
  · exact le_max_of_le_right (hC ⟨n, by simpa using hn, rfl⟩)

private def NGC_scan (E : BitString → ℕ → Option ℚ) (σ y : BitString) (s : ℕ) (n : ℕ) :
    Option (ℚ × Bool) :=
  Nat.rec ((E [] s).map (fun v => (v, true)))
    (fun k IH => IH.bind (fun p => (E (y.take (k + 1)) s).map
      (fun v' => (v', p.2 && (decide (k < σ.length) || !decide (2 * p.1 < v'))))))
    n

private lemma NGC_scan_zero (E : BitString → ℕ → Option ℚ) (σ y : BitString) (s : ℕ) :
    NGC_scan E σ y s 0 = (E [] s).map (fun v => (v, true)) := rfl

private lemma NGC_scan_succ (E : BitString → ℕ → Option ℚ) (σ y : BitString) (s k : ℕ) :
    NGC_scan E σ y s (k + 1) = (NGC_scan E σ y s k).bind (fun p => (E (y.take (k + 1)) s).map
      (fun v' => (v', p.2 && (decide (k < σ.length) || !decide (2 * p.1 < v'))))) := rfl

private lemma NGC_scan_sound {m : BitString →. ℚ} {E : BitString → ℕ → Option ℚ}
    (hEs : ∀ (a : BitString) (v : ℚ), v ∈ m a ↔ ∃ s, E a s = some v)
    (σ y : BitString) (s : ℕ) :
    ∀ n, n ≤ y.length → ∀ v g, NGC_scan E σ y s n = some (v, g) →
      (∀ k, k ≤ n → (m (y.take k)).Dom) ∧ v ∈ m (y.take n) ∧
      (g = true ↔ ∀ k, σ.length ≤ k → k < n →
        ¬ isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m (y.take k)
          (y.getD k false)) := by
  intro n
  induction n with
  | zero =>
    intro _ v g h
    rw [NGC_scan_zero] at h
    rcases hE : E [] s with _ | v0
    · rw [hE] at h; simp at h
    · rw [hE] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h2
      have hmem : v ∈ m [] := (hEs [] v).2 ⟨s, by rw [hE, h1]⟩
      refine ⟨fun k hk => ?_, by simpa using hmem, by simp⟩
      have : k = 0 := by omega
      subst this
      simpa using Part.dom_iff_mem.2 ⟨v, hmem⟩
  | succ n ih =>
    intro hn v g h
    rw [NGC_scan_succ] at h
    rcases hp : NGC_scan E σ y s n with _ | ⟨v0, g0⟩
    · rw [hp] at h; simp at h
    · rw [hp] at h
      rcases hE : E (y.take (n + 1)) s with _ | v1
      · rw [hE] at h; simp at h
      · rw [hE] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hal, hv0, hg0⟩ := ih (by omega) v0 g0 hp
        have hmem1 : v1 ∈ m (y.take (n + 1)) := (hEs _ v1).2 ⟨s, hE⟩
        have htake : y.take (n + 1) = y.take n ++ [y.getD n false] := by
          have hn' : n < y.length := by omega
          rw [List.take_add_one]
          simp [List.getElem?_eq_getElem hn']
        have hgain : isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m
            (y.take n) (y.getD n false) ↔ 2 * v0 < v1 := by
          unfold isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep
          rw [← htake]
          constructor
          · rintro ⟨q, hq, q', hq', hlt⟩
            rw [Part.mem_unique hq hv0, Part.mem_unique hq' hmem1] at hlt
            exact hlt
          · intro hlt
            exact ⟨v0, hv0, v1, hmem1, hlt⟩
        refine ⟨fun k hk => ?_, hmem1, ?_⟩
        · by_cases hkn : k ≤ n
          · exact hal k hkn
          · have : k = n + 1 := by omega
            subst this
            exact Part.dom_iff_mem.2 ⟨v1, hmem1⟩
        · constructor
          · intro hg k hk1 hk2
            simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
              decide_eq_false_iff_not] at hg
            by_cases hkn : k < n
            · exact (hg0.1 hg.1) k hk1 hkn
            · have : k = n := by omega
              subst this
              rw [hgain]
              rcases hg.2 with h | h
              · omega
              · exact h
          · intro hg
            simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
              decide_eq_false_iff_not]
            refine ⟨hg0.2 (fun k hk1 hk2 => hg k hk1 (by omega)), ?_⟩
            by_cases hs : n < σ.length
            · exact Or.inl hs
            · exact Or.inr ((hgain.not).1 (hg n (by omega) (by omega)))

private lemma NGC_scan_some {E : BitString → ℕ → Option ℚ} (σ y : BitString) (s : ℕ) :
    ∀ n, (∀ k, k ≤ n → (E (y.take k) s).isSome) → ∃ v g, NGC_scan E σ y s n = some (v, g) := by
  intro n
  induction n with
  | zero =>
    intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (by simpa using h 0 le_rfl)
    exact ⟨v, true, by rw [NGC_scan_zero, hv]; rfl⟩
  | succ n ih =>
    intro h
    obtain ⟨v, g, hvg⟩ := ih (fun k hk => h k (by omega))
    obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.1 (h (n + 1) le_rfl)
    exact ⟨v', _, by rw [NGC_scan_succ, hvg, hv']; rfl⟩

private lemma NGC_stage_exists {m : BitString →. ℚ} {E : BitString → ℕ → Option ℚ}
    (hEs : ∀ (a : BitString) (v : ℚ), v ∈ m a ↔ ∃ s, E a s = some v)
    (hEm : ∀ (a : BitString) (s t : ℕ) (v : ℚ), s ≤ t → E a s = some v → E a t = some v)
    (y : BitString) (hy : NGC_alive m y) :
    ∃ s, ∀ k, k ≤ y.length → (E (y.take k) s).isSome := by
  have : ∀ n, n ≤ y.length → ∃ s, ∀ k, k ≤ n → (E (y.take k) s).isSome := by
    intro n
    induction n with
    | zero =>
      intro _
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 (hy 0 (by omega))
      obtain ⟨s, hs⟩ := (hEs _ v).1 hv
      refine ⟨s, fun k hk => ?_⟩
      have : k = 0 := by omega
      subst this
      rw [hs]; rfl
    | succ n ih =>
      intro hn
      obtain ⟨s, hs⟩ := ih (by omega)
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 (hy (n + 1) hn)
      obtain ⟨s', hs'⟩ := (hEs _ v).1 hv
      refine ⟨max s s', fun k hk => ?_⟩
      by_cases hkn : k ≤ n
      · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hs k hkn)
        rw [hEm _ _ _ u (le_max_left _ _) hu]; rfl
      · have : k = n + 1 := by omega
        subst this
        rw [hEm _ _ _ v (le_max_right _ _) hs']; rfl
  exact this y.length le_rfl

private lemma NGC_scan_computable {E : BitString → ℕ → Option ℚ} (hE : Computable₂ E)
    (σ : BitString) :
    Computable (fun p : BitString × ℕ => NGC_scan E σ p.1 p.2 p.1.length) := by
  have hlen : Computable (fun p : BitString × ℕ => p.1.length) :=
    Primrec.list_length.to_comp.comp Computable.fst
  have hg : Computable (fun p : BitString × ℕ => (E [] p.2).map (fun v => (v, true))) :=
    Computable.option_map (hE.comp (Computable.const []) Computable.snd)
      (Computable.pair Computable.snd (Computable.const true)).to₂
  have hstep : Computable₂ (fun (a : BitString × ℕ) (z : ℕ × Option (ℚ × Bool)) =>
      z.2.bind (fun p => (E (a.1.take (z.1 + 1)) a.2).map
        (fun v' => (v', p.2 && (decide (z.1 < σ.length) || !decide (2 * p.1 < v')))))) := by
    refine Computable.option_bind (Computable.snd.comp Computable.snd) ?_
    refine Computable.option_map ?_ ?_
    · have h1 : Computable (fun r : ((BitString × ℕ) × (ℕ × Option (ℚ × Bool))) × (ℚ × Bool) =>
          r.1.2.1 + 1) := Primrec.succ.to_comp.comp (Computable.fst.comp (Computable.snd.comp
              Computable.fst))
      have h2 : Computable (fun r : ((BitString × ℕ) × (ℕ × Option (ℚ × Bool))) × (ℚ × Bool) =>
          r.1.1.1.take (r.1.2.1 + 1)) :=
        Primrec.list_take.to_comp.comp h1 (Computable.fst.comp (Computable.fst.comp Computable.fst))
      exact hE.comp h2 (Computable.snd.comp (Computable.fst.comp Computable.fst))
    · have hlt : Computable (fun r : (((BitString × ℕ) × (ℕ × Option (ℚ × Bool))) × (ℚ × Bool)) ×
        ℚ =>
          decide (r.1.1.2.1 < σ.length)) :=
        Primrec.nat_lt.decide.to_comp.comp (Computable.fst.comp (Computable.snd.comp
            (Computable.fst.comp Computable.fst)))
          (Computable.const σ.length)
      have hmul : Computable (fun r : (((BitString × ℕ) × (ℕ × Option (ℚ × Bool))) × (ℚ × Bool)) ×
          ℚ =>
          decide (2 * r.1.2.1 < r.2)) :=
        computable₂_ratLt.comp
          (computable₂_ratMul.comp (Computable.const 2)
            (Computable.fst.comp (Computable.snd.comp Computable.fst))) Computable.snd
      have hor : Computable (fun r : (((BitString × ℕ) × (ℕ × Option (ℚ × Bool))) × (ℚ × Bool)) ×
          ℚ =>
          (decide (r.1.1.2.1 < σ.length) || !decide (2 * r.1.2.1 < r.2))) :=
        Primrec.or.to_comp.comp hlt (Primrec.not.to_comp.comp hmul)
      have hand : Computable (fun r : (((BitString × ℕ) × (ℕ × Option (ℚ × Bool))) × (ℚ × Bool)) ×
          ℚ =>
          (r.1.2.2 && (decide (r.1.1.2.1 < σ.length) || !decide (2 * r.1.2.1 < r.2)))) :=
        Primrec.and.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)) hor
      exact (Computable.pair Computable.snd hand).to₂
  exact (Computable.nat_rec hlen hg hstep).of_eq (fun p => rfl)

private def NGC_test (E : BitString → ℕ → Option ℚ) (σ : BitString)
    (q : (ℚ × BitString) × ℕ) : Bool :=
  decide (q.1.1 < 0) ||
  (decide (q.1.2.take σ.length = σ) &&
    ((NGC_scan E σ q.1.2 q.2 q.1.2.length).map (fun p => p.2 && decide (q.1.1 < p.1))).getD false)
        ||
  (decide (q.1.2 = σ.take q.1.2.length) && decide (q.1.2.length < σ.length) &&
    ((NGC_scan E σ σ q.2 σ.length).map
      (fun p => decide (q.1.1 * ((2 ^ (σ.length - q.1.2.length) : ℕ) : ℚ) < p.1))).getD false)

private lemma NGC_test_computable {E : BitString → ℕ → Option ℚ} (hE : Computable₂ E)
    (σ : BitString) : Computable (NGC_test E σ) := by
  have hF := NGC_scan_computable hE σ
  have hy : Computable (fun q : (ℚ × BitString) × ℕ => q.1.2) :=
    Computable.snd.comp Computable.fst
  have hr : Computable (fun q : (ℚ × BitString) × ℕ => q.1.1) :=
    Computable.fst.comp Computable.fst
  have c1 : Computable (fun q : (ℚ × BitString) × ℕ => decide (q.1.1 < 0)) :=
    computable₂_ratLt.comp hr (Computable.const 0)
  have cA : Computable (fun q : (ℚ × BitString) × ℕ => decide (q.1.2.take σ.length = σ)) :=
    (Primrec.eq (α := BitString)).decide.to_comp.comp
      (Primrec.list_take.to_comp.comp (Computable.const σ.length) hy) (Computable.const σ)
  have cS1 : Computable (fun q : (ℚ × BitString) × ℕ =>
      NGC_scan E σ q.1.2 q.2 q.1.2.length) := hF.comp (Computable.pair hy Computable.snd)
  have cB : Computable (fun q : (ℚ × BitString) × ℕ =>
      ((NGC_scan E σ q.1.2 q.2 q.1.2.length).map
        (fun p => p.2 && decide (q.1.1 < p.1))).getD false) := by
    refine Primrec.option_getD.to_comp.comp ?_ (Computable.const false)
    refine Computable.option_map cS1 ?_
    exact Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd)
      (computable₂_ratLt.comp (hr.comp Computable.fst) (Computable.fst.comp Computable.snd))
  have cC : Computable (fun q : (ℚ × BitString) × ℕ => decide (q.1.2 = σ.take q.1.2.length)) :=
    (Primrec.eq (α := BitString)).decide.to_comp.comp hy
      (Primrec.list_take.to_comp.comp (Primrec.list_length.to_comp.comp hy) (Computable.const σ))
  have cD : Computable (fun q : (ℚ × BitString) × ℕ => decide (q.1.2.length < σ.length)) :=
    Primrec.nat_lt.decide.to_comp.comp (Primrec.list_length.to_comp.comp hy)
      (Computable.const σ.length)
  have cS2 : Computable (fun q : (ℚ × BitString) × ℕ => NGC_scan E σ σ q.2 σ.length) :=
    hF.comp (Computable.pair (Computable.const σ) Computable.snd)
  have cpow : Computable (fun q : (ℚ × BitString) × ℕ =>
      ((2 ^ (σ.length - q.1.2.length) : ℕ) : ℚ)) :=
    computable_nat_to_rat.comp
      (nat_pow_primrec₂.to_comp.comp (Computable.const 2)
        (Primrec.nat_sub.to_comp.comp (Computable.const σ.length)
          (Primrec.list_length.to_comp.comp hy)))
  have cE : Computable (fun q : (ℚ × BitString) × ℕ =>
      ((NGC_scan E σ σ q.2 σ.length).map
        (fun p => decide (q.1.1 * ((2 ^ (σ.length - q.1.2.length) : ℕ) : ℚ) < p.1))).getD false) :=
            by
    refine Primrec.option_getD.to_comp.comp ?_ (Computable.const false)
    refine Computable.option_map cS2 ?_
    exact computable₂_ratLt.comp
      (computable₂_ratMul.comp (hr.comp Computable.fst) (cpow.comp Computable.fst))
      (Computable.fst.comp Computable.snd)
  unfold NGC_test
  exact Primrec.or.to_comp.comp
    (Primrec.or.to_comp.comp c1 (Primrec.and.to_comp.comp cA cB))
    (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp cC cD) cE)

private lemma NGC_test_iff {m : BitString →. ℚ} (hmart : IsPartialMartingale m)
    {E : BitString → ℕ → Option ℚ}
    (hEm : ∀ (a : BitString) (s t : ℕ) (v : ℚ), s ≤ t → E a s = some v → E a t = some v)
    (hEs : ∀ (a : BitString) (v : ℚ), v ∈ m a ↔ ∃ s, E a s = some v)
    (σ : BitString) (r : ℚ) (y : BitString) :
    (r : ℝ) < NGC_cap m σ y ↔ ∃ s, NGC_test E σ ((r, y), s) = true := by
  classical
  constructor
  · intro h
    by_cases hr : r < 0
    · exact ⟨0, by simp [NGC_test, hr]⟩
    have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast not_lt.1 hr
    by_cases hx : σ <+: y
    · rw [NGC_cap_of_ext hx] at h
      by_cases hq : NGC_alive m y ∧ NGC_noGain m σ y
      · rw [ite_eq_left hq] at h
        obtain ⟨s, hs⟩ := NGC_stage_exists hEs hEm y hq.1
        obtain ⟨v, g, hvg⟩ := NGC_scan_some (E := E) σ y s y.length hs
        obtain ⟨-, hvm, hg⟩ := NGC_scan_sound hEs σ y s y.length le_rfl v g hvg
        rw [List.take_length] at hvm
        have hv : v = NGC_mv m y := Part.mem_unique hvm (NGC_mv_mem (NGC_alive_dom hq.1))
        have hgt : g = true := hg.2 hq.2
        refine ⟨s, ?_⟩
        have hlt : r < v := by rw [hv]; exact_mod_cast h
        have hpre : y.take σ.length = σ := (List.prefix_iff_eq_take.1 hx).symm
        simp [NGC_test, hvg, hgt, hlt, hpre]
      · rw [ite_eq_right hq] at h
        exact absurd h (not_lt.2 hr0)
    · by_cases hyp : y <+: σ ∧ NGC_alive m σ
      · rw [NGC_cap_of_prefix hyp.1, ite_eq_left hyp.2] at h
        have hlen : y.length < σ.length := by
          rcases Nat.lt_or_ge y.length σ.length with h1 | h1
          · exact h1
          · exact absurd (by rw [hyp.1.eq_of_length (le_antisymm hyp.1.length_le h1)]) hx
        obtain ⟨s, hs⟩ := NGC_stage_exists hEs hEm σ hyp.2
        obtain ⟨v, g, hvg⟩ := NGC_scan_some (E := E) σ σ s σ.length hs
        obtain ⟨-, hvm, -⟩ := NGC_scan_sound hEs σ σ s σ.length le_rfl v g hvg
        rw [List.take_length] at hvm
        have hv : v = NGC_mv m σ := Part.mem_unique hvm (NGC_mv_mem (NGC_alive_dom hyp.2))
        refine ⟨s, ?_⟩
        have hpos : (0 : ℝ) < 2 ^ (σ.length - y.length) := by positivity
        have hlt' : (r : ℝ) * 2 ^ (σ.length - y.length) < NGC_mv m σ := by
          rwa [lt_div_iff₀ hpos] at h
        have hlt : r * ((2 ^ (σ.length - y.length) : ℕ) : ℚ) < v := by
          rw [hv]; exact_mod_cast hlt'
        have hpre : y = σ.take y.length := List.prefix_iff_eq_take.1 hyp.1
        simp only [NGC_test, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, hvg,
          Option.map_some, Option.getD_some]
        exact Or.inr ⟨⟨hpre, hlen⟩, hlt⟩
      · have : NGC_cap m σ y = 0 := by
          unfold NGC_cap; rw [ite_eq_right hx, ite_eq_right hyp]
        rw [this] at h
        exact absurd h (not_lt.2 hr0)
  · rintro ⟨s, hs⟩
    unfold NGC_test at hs
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hs
    rcases hs with (h1 | ⟨h2, h3⟩) | ⟨⟨h4, h5⟩, h6⟩
    · exact lt_of_lt_of_le (by exact_mod_cast h1) (NGC_cap_nonneg hmart σ y)
    · have hx : σ <+: y := List.prefix_iff_eq_take.2 h2.symm
      rcases hsc : NGC_scan E σ y s y.length with _ | ⟨v, g⟩
      · rw [hsc] at h3; simp at h3
      · rw [hsc] at h3
        simp only [Option.map_some, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq] at h3
        obtain ⟨hal, hvm, hg⟩ := NGC_scan_sound hEs σ y s y.length le_rfl v g hsc
        rw [List.take_length] at hvm
        have hv : NGC_mv m y = v := (Part.mem_unique (NGC_mv_mem (NGC_alive_dom hal)) hvm)
        rw [NGC_cap_of_ext hx, ite_eq_left ⟨hal, hg.1 h3.1⟩, hv]
        exact_mod_cast h3.2
    · have hy : y <+: σ := List.prefix_iff_eq_take.2 h4
      have hx : ¬ σ <+: y := fun hh => absurd (hh.length_le) (by omega)
      rcases hsc : NGC_scan E σ σ s σ.length with _ | ⟨v, g⟩
      · rw [hsc] at h6; simp at h6
      · rw [hsc] at h6
        simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at h6
        obtain ⟨hal, hvm, -⟩ := NGC_scan_sound hEs σ σ s σ.length le_rfl v g hsc
        rw [List.take_length] at hvm
        have hv : NGC_mv m σ = v := (Part.mem_unique (NGC_mv_mem (NGC_alive_dom hal)) hvm)
        have hal' : NGC_alive m σ := hal
        rw [NGC_cap_of_prefix hy, ite_eq_left hal', hv]
        have hpos : (0 : ℝ) < 2 ^ (σ.length - y.length) := by positivity
        rw [lt_div_iff₀ hpos]
        exact_mod_cast h6

private lemma NGC_cap_lsc {m : BitString →. ℚ} (hm : Partrec m) (hmart : IsPartialMartingale m)
    (σ : BitString) : IsLowerSemicomputableOnStrings (NGC_cap m σ) := by
  obtain ⟨E, hEc, hEm, hEs⟩ :=
    isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_stepEval hm
  have hRE : IsRE (fun q : (ℚ × BitString) × ℕ => NGC_test E σ q = true) :=
    isRE_of_computable_bool _ (NGC_test E σ) (fun _ => Iff.rfl) (NGC_test_computable hEc σ)
  have hex := IsRE.exists_encodable
    (R := fun (p : ℚ × BitString) (s : ℕ) => NGC_test E σ (p, s) = true) hRE
  exact hex.of_iff (fun p => (NGC_test_iff hmart hEm hEs σ p.1 p.2).symm)

end isKLRandom_of_isMartinLofRandom_step1_partialComputablyRandom_step2_noGainCapital_aux

/-- Step 2 of the proof of
`isKLRandom_of_isMartinLofRandom_partialComputablyRandom`:
the capital after the last gain step.  For a partial computable partial martingale `m` and a string
`σ` there is a lower semicomputable superfair capital `M` (for the uniform measure) that wins on
every `w` through `σ` on which `m` partially wins and which has no gain step at positions `≥ |σ|`.
Take `M(y) = m(y)` if `σ ⊑ y`, `y` is alive (`m` defined on every prefix of `y`) and there is no
gain
step between `σ` and `y`; `M(y) = 2^{|y| - |σ|} m(σ)` if `y` is a proper prefix of an alive `σ`;
and `M(y) = 0` otherwise (`M = 0` if `σ` is not alive).  Superfairness: the alive non-gain children
of an alive `x` carry total value at most `2 m(x)` (equality by fairness when there are two, since a
gain child has no alive sibling; `m(c) ≤ 2 m(x)` when there is one), and the capital doubles along
`σ`.  Lower semicomputability uses a stage-bounded evaluation of `m`. -/
private lemma isKLRandom_of_isMartinLofRandom_noGainCapital
    (m : BitString →. ℚ) (hm : Partrec m) (hmart : IsPartialMartingale m) (σ : BitString) :
    ∃ M : BitString → ℝ, IsLowerSemicomputableOnStrings M ∧ IsSuperfairCapital uniformMeasure M ∧
      ∀ w : CantorSeq, PartialWins m w → cantorPrefix w σ.length = σ →
        (∀ n ≥ σ.length,
          ¬ isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m
            (cantorPrefix w n) (w n)) → Wins M w := by
  open isKLRandom_of_isMartinLofRandom_step1_partialComputablyRandom_step2_noGainCapital_aux in
  exact ⟨NGC_cap m σ, NGC_cap_lsc hm hmart σ, NGC_cap_isSuperfair hmart σ,
    fun w hw hσ hng => NGC_cap_wins hw hσ hng⟩

/-- Step 1 of the proof of `isKLRandom_of_isMartinLofRandom`: The monotone core.
Any Martin-Löf random sequence is partial-computably random. -/
private lemma isKLRandom_of_isMartinLofRandom_partialComputablyRandom {w : CantorSeq}
    (hw : IsMartinLofRandom uniformMeasure w) : IsPartialComputablyRandom w := by
  intro m hm hmart hwins
  have hnull : ∀ M : BitString → ℝ, IsLowerSemicomputableOnStrings M →
      IsSuperfairCapital uniformMeasure M → ¬ Wins M w := fun M hlsc hsf hW =>
    ((isEffectivelyNull_iff_forall_not_random isComputableMeasure_uniform _).1
      (isEffectivelyNull_wins_of_superfair isComputableMeasure_uniform hsf hlsc) w hW) hw
  obtain ⟨P, hPl, hPs, hPw⟩ :=
    isKLRandom_of_isMartinLofRandom_gainCapital m hm hmart
  by_cases hinf : ∀ N, ∃ n ≥ N,
      isKLRandom_of_isMartinLofRandom_partialComputablyRandom_GainStep m (cantorPrefix w n)
          (w n)
  · exact hnull P hPl hPs (hPw w hwins.1 hinf)
  · push Not at hinf
    obtain ⟨N, hN⟩ := hinf
    obtain ⟨M, hMl, hMs, hMw⟩ :=
      isKLRandom_of_isMartinLofRandom_noGainCapital m hm hmart
        (cantorPrefix w N)
    exact hnull M hMl hMs (hMw w hwins (by simp) (by simpa using hN))

/-- Step 1 of the proof of
`isKLRandom_of_isMartinLofRandom_revealed_isMartinLofRandom`:
selecting by the whole set of strings returns the string itself. -/
private lemma isKLRandom_of_isMartinLofRandom_revealed_isMartinLofRandom_selectedAux_univ
    (pre x : BitString) : selectedAux Set.univ pre x = x := by
  induction x generalizing pre with
  | nil => simp [selectedAux]
  | cons b x ih => simp [selectedAux, ih]

private lemma isKLRandom_of_isMartinLofRandom_revealed_isMartinLofRandom_selectedBits_univ
    (x : BitString) : selectedBits Set.univ x = x :=
  isKLRandom_of_isMartinLofRandom_revealed_isMartinLofRandom_selectedAux_univ [] x

/-- Step 2 of the proof of `isKLRandom_of_isMartinLofRandom`: If the run of a Martin-Löf
random sequence under a KL betting strategy is infinite, the revealed sequence is Martin-Löf random.
-/
private lemma isKLRandom_of_isMartinLofRandom_revealed_isMartinLofRandom {w : CantorSeq}
    (hw : IsMartinLofRandom uniformMeasure w) (β : KLBetting)
    (hnext : Partrec β.next) (hinf : ∀ t, t ≤ (β.toRule.revealed w t).length) :
    ∃ u : CantorSeq, β.toRule.revealedStream w = BitStream.infinite u ∧ IsMartinLofRandom
        uniformMeasure u := by
  classical
  set c : ℕ → BitString := β.toRule.revealed w with hcdef
  have hc : ∀ t, c t <+: c (t + 1) := β.toRule.revealed_prefix w
  have hlen_le : ∀ t, (c t).length ≤ t := by
    intro t
    induction t with
    | zero => simp [hcdef, KLRule.revealed]
    | succ t ih =>
      have : c (t + 1) = if h : (β.next (c t)).Dom then c t ++ [w ((β.next (c t)).get h)] else
        c t := rfl
      rw [this]
      split_ifs <;> simp <;> omega
  have hlen : ∀ t, (c t).length = t := fun t => le_antisymm (hlen_le t) (hinf t)
  have hprefix (t : ℕ) : BitStream.finite (c t) ≤ streamOfChain c hc :=
    (BitStream.finite_le_ofPrefixSet_iff (isStreamPrefixSet_chainPrefixSet hc) _).mpr
      ⟨t, List.prefix_rfl⟩
  have hstream : β.toRule.revealedStream w = streamOfChain c hc := rfl
  cases hs : streamOfChain c hc with
  | finite x =>
    exfalso
    have hp := hprefix (x.length + 1)
    rw [hs] at hp
    have := List.IsPrefix.length_le hp
    rw [hlen] at this
    omega
  | infinite u =>
    refine ⟨u, by rw [hstream, hs], ?_⟩
    have hcu : ∀ t, cantorPrefix u t = c t := by
      intro t
      have hp := hprefix t
      rw [hs] at hp
      have heq : cantorPrefix u (c t).length = c t :=
        (isCantorPrefix_iff_cantorPrefix_eq _ _).mp hp
      rwa [hlen] at heq
    let ρ : KLRule := ⟨β.next, fun _ => Part.some true, β.noRepeat⟩
    have hρ : ρ.IsAdmissible := ⟨hnext, Computable.partrec (Computable.const true)⟩
    have hrev : ∀ t, ρ.revealed w t = c t := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih =>
        have h1 : ρ.revealed w (t + 1) = if h : (β.next (ρ.revealed w t)).Dom then
            ρ.revealed w t ++ [w ((β.next (ρ.revealed w t)).get h)] else ρ.revealed w t := rfl
        have h2 : c (t + 1) = if h : (β.next (c t)).Dom then c t ++ [w ((β.next (c t)).get h)] else
          c t := rfl
        rw [h1, h2, ih]
    have hout : ∀ t, ρ.outputChain w t = c t := by
      intro t
      unfold KLRule.outputChain
      have hset : partialRuleSet ρ.sel = Set.univ := by
        ext x
        simp [partialRuleSet, ρ]
      rw [hset, hrev t]
      exact isKLRandom_of_isMartinLofRandom_revealed_isMartinLofRandom_selectedBits_univ _
    obtain ⟨f, hf, hfeq⟩ := isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_effopen hρ
    intro U hU hmem
    obtain ⟨g, hg, hUeq⟩ := hU.1
    have hD : Computable₂ (fun n i => disjEnum (g n) i) := computable_disjEnum hg
    have hG : Computable₂ (fun n k : ℕ => (disjEnum (g n) (Nat.unpair k).1).bind
        (fun x => f x (Nat.unpair k).2)) := by
      have h1 : Computable (fun p : ℕ × ℕ => disjEnum (g p.1) (Nat.unpair p.2).1) :=
        Computable₂.comp (f := fun n i => disjEnum (g n) i) hD Computable.fst
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
      have h2 : Computable (fun q : (ℕ × ℕ) × BitString => f q.2 (Nat.unpair q.1.2).2) :=
        Computable₂.comp (f := f) hf Computable.snd
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))).to_comp
      exact Computable.option_bind h1 h2
    set V : ℕ → Set CantorSeq := fun n => ⋃ k, ((disjEnum (g n) (Nat.unpair k).1).bind
        (fun x => f x (Nat.unpair k).2)).elim ∅ cantorCylinder with hVdef
    have hV : ∀ n, V n = ⋃ i, (disjEnum (g n) i).elim ∅
        (fun x => {w : CantorSeq | ∃ t, x <+: ρ.outputChain w t}) := by
      intro n
      ext v
      simp only [hVdef, Set.mem_iUnion]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨(Nat.unpair k).1, ?_⟩
        cases hd : disjEnum (g n) (Nat.unpair k).1 with
        | none => rw [hd] at hk; simp at hk
        | some x =>
          rw [hd] at hk
          simp only [Option.bind_some, Option.elim_some] at hk ⊢
          rw [hfeq x]
          exact Set.mem_iUnion.2 ⟨_, hk⟩
      · rintro ⟨i, hi⟩
        cases hd : disjEnum (g n) i with
        | none => rw [hd] at hi; simp at hi
        | some x =>
          rw [hd] at hi
          simp only [Option.elim_some] at hi
          rw [hfeq x] at hi
          obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hi
          refine ⟨Nat.pair i j, ?_⟩
          rw [Nat.unpair_pair]
          simp only [hd, Option.bind_some]
          exact hj
    have hVtest : IsMartinLofTest uniformMeasure V := by
      refine ⟨⟨_, hG, fun n => rfl⟩, fun n => ?_⟩
      rw [hV n]
      refine le_trans (measure_iUnion_le _) ?_
      have hterm : ∀ i, uniformMeasure ((disjEnum (g n) i).elim ∅
          (fun x => {w : CantorSeq | ∃ t, x <+: ρ.outputChain w t})) ≤
          (disjEnum (g n) i).elim 0 (cantorMass uniformMeasure) := by
        intro i
        cases hd : disjEnum (g n) i with
        | none => simp
        | some x =>
          simp only [Option.elim_some]
          exact isMisesKLRandomAt_of_isMartinLofRandom_bernoulli_selection
            (p := 1 / 2) (by norm_num) ρ x
      refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
      rw [tsum_measure_disjEnum uniformMeasure (g n)]
      have hset : (⋃ j, coverSet (g n) j) = U n := (hUeq n).symm
      rw [hset]
      exact hU.2 n
    apply hw V hVtest
    refine Set.mem_iInter.2 fun n => ?_
    rw [hV n]
    have hu : u ∈ ⋃ i, coverSet (disjEnum (g n)) i := by
      rw [coverSet_disjEnum_iUnion]
      have := Set.mem_iInter.1 hmem n
      rw [hUeq n] at this
      exact this
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hu
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    cases hd : disjEnum (g n) i with
    | none => rw [coverSet, hd] at hi; simp at hi
    | some x =>
      rw [coverSet, hd] at hi
      simp only [Option.elim_some] at hi ⊢
      refine ⟨x.length, ?_⟩
      have h1 : cantorPrefix u x.length = x := (isCantorPrefix_iff_cantorPrefix_eq _ _).mp hi
      rw [hout, ← hcu, h1]

/-- Step 3 of the proof of `isKLRandom_of_isMartinLofRandom`: The capital of a winning
KL betting strategy wins as a partial martingale on the revealed sequence. -/
private lemma isKLRandom_of_isMartinLofRandom_partialWins {w : CantorSeq} (β : KLBetting)
    {u : CantorSeq} (hwins : β.Wins w) (hu : β.toRule.revealedStream w = BitStream.infinite u) :
    PartialWins β.capital u := by
  have hle : ∀ t, (β.toRule.revealed w t).length ≤ t := by
    intro t
    induction t with
    | zero => simp [KLRule.revealed]
    | succ t ih =>
      rw [KLRule.revealed]
      split_ifs
      · simp only [List.length_append, List.length_singleton]
        omega
      · omega
  have hpre : ∀ t, cantorPrefix u t = β.toRule.revealed w t := by
    intro t
    have hlen : (β.toRule.revealed w t).length = t := le_antisymm (hle t) (hwins.1 t)
    have hT := isStreamPrefixSet_chainPrefixSet (β.toRule.revealed_prefix w)
    have hmem : β.toRule.revealed w t ∈ chainPrefixSet (β.toRule.revealed w) :=
      ⟨t, List.prefix_rfl⟩
    have h1 : BitStream.finite (β.toRule.revealed w t) ≤ β.toRule.revealedStream w :=
      (BitStream.finite_le_ofPrefixSet_iff hT _).2 hmem
    rw [hu] at h1
    have h2 : IsCantorPrefix (β.toRule.revealed w t) u := BitStream.finite_le_infinite_iff.1 h1
    have h3 := (isCantorPrefix_iff_cantorPrefix_eq _ _).1 h2
    rw [hlen] at h3
    exact h3
  refine ⟨fun n => ?_, ?_⟩
  · rw [hpre]; exact hwins.2.1 n
  · simpa only [hpre] using hwins.2.2

/-- **SUV p. 309.**  "It is easy to prove that all Martin-Löf random sequences have this
property". -/
theorem isKLRandom_of_isMartinLofRandom {w : CantorSeq}
    (hw : IsMartinLofRandom uniformMeasure w) : IsKLRandom w := by
  intro β hnext hcap hwins
  obtain ⟨u, hu_eq, hu_ml⟩ := isKLRandom_of_isMartinLofRandom_revealed_isMartinLofRandom hw β
      hnext hwins.1
  have hpcr := isKLRandom_of_isMartinLofRandom_partialComputablyRandom hu_ml
  have hmart : IsPartialMartingale β.capital := ⟨β.nonneg, β.fair⟩
  have hpwins := isKLRandom_of_isMartinLofRandom_partialWins β hwins hu_eq
  exact hpcr β.capital hcap hmart hpwins

end Kolmogorov.FrequencyGames
