/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.IndependentTrials

/-!
# Bookmaker Game

The bookmaker game attached to a pair of measures `μ`, `μ'` on Cantor space: the capital
`bookmakerCapital μ μ'` is a `μ`-martingale, and if the conditional probabilities along a sequence
`w` are separated from `0` and `1` while the squared differences are not summable, one of the two
capitals is unbounded on `w`.

## Main declarations

* `summable_sq_condOne_sub_of_isComputablyRandom`: computable randomness with respect to both
  measures forces summability of the squared differences of conditional probabilities.
* `isMartingale_bookmakerCapital`: the bookmaker capital is a `μ`-martingale.
* `wins_bookmaker_of_not_summable`: non-summability makes one of the two capitals win.

This formalizes the game argument for Theorem 197 of Shen, Uspensky and Vereshchagin,
"Kolmogorov complexity and algorithmic randomness" (see Problem 278, p. 301).
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped ENNReal

/-- uniformly computable real function. -/
private def ssc_UC {α : Type*} [Primcodable α]
    (g : α → ℝ) : Prop :=
  ∃ q : α × ℕ → ℚ, Computable q ∧ ∀ a s, |(q (a, s) : ℝ) - g a| ≤ (2 : ℝ)⁻¹ ^ s

private theorem ssc_UC_comp {α β : Type*}
    [Primcodable α] [Primcodable β] {g : α → ℝ}
    (hg : ssc_UC g)
    {f : β → α} (hf : Computable f) : ssc_UC
        (fun b => g (f b)) := by
  obtain ⟨q, hq, h⟩ := hg
  exact ⟨fun p => q (f p.1, p.2), hq.comp ((hf.comp Computable.fst).pair Computable.snd),
    fun b s => h (f b) s⟩

private theorem ssc_UC_rat {α : Type*}
    [Primcodable α] {r : α → ℚ} (hr : Computable r) :
    ssc_UC (fun a => (r a : ℝ)) :=
  ⟨fun p => r p.1, hr.comp Computable.fst, fun a s => by simp⟩

private theorem ssc_UC_add {α : Type*}
    [Primcodable α] {g h : α → ℝ} (hg : ssc_UC
    g) (hh : ssc_UC h) :
    ssc_UC (fun a => g a + h a) := by
  obtain ⟨q1, h1c, h1⟩ := hg
  obtain ⟨q2, h2c, h2⟩ := hh
  have hs : Computable (fun p : α × ℕ => p.2 + 1) :=
    Primrec.succ.to_comp.comp Computable.snd
  refine ⟨fun p => q1 (p.1, p.2 + 1) + q2 (p.1, p.2 + 1), ?_, fun a s => ?_⟩
  · exact computable₂_ratAdd.comp (h1c.comp (Computable.fst.pair hs))
      (h2c.comp (Computable.fst.pair hs))
  · have e1 := h1 a (s + 1)
    have e2 := h2 a (s + 1)
    push_cast
    have : (2 : ℝ)⁻¹ ^ (s + 1) + (2 : ℝ)⁻¹ ^ (s + 1) = (2 : ℝ)⁻¹ ^ s := by
      rw [pow_succ]; ring
    calc |(q1 (a, s + 1) : ℝ) + q2 (a, s + 1) - (g a + h a)|
        = |((q1 (a, s + 1) : ℝ) - g a) + ((q2 (a, s + 1) : ℝ) - h a)| := by ring_nf
      _ ≤ |(q1 (a, s + 1) : ℝ) - g a| + |(q2 (a, s + 1) : ℝ) - h a| := abs_add_le _ _
      _ ≤ _ := by linarith

/-- natural bound for a rational. -/
private def ssc_qb (r : ℚ) : ℕ :=
    r.num.toNat + (-r.num).toNat

private lemma ssc_qb_comp : Computable
    ssc_qb :=
  Computable₂.comp Primrec.nat_add.to_comp
    (ComputableReals.primrec_intToNat.to_comp.comp computable_ratNum)
    (ComputableReals.primrec_intToNat.to_comp.comp (primrec_intNeg.to_comp.comp computable_ratNum))

private lemma ssc_abs_le_qb (r : ℚ) : |(r : ℝ)|
    ≤ (ssc_qb r : ℝ) := by
  have h1 : (ssc_qb r : ℤ) = |r.num| := by
    rw [Int.abs_eq_natAbs]; unfold ssc_qb;
    omega
  have h2 : |(r : ℝ)| ≤ |(r.num : ℝ)| := by
    have hd : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
    have : (r : ℝ) = (r.num : ℝ) / r.den := by
      rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
    rw [this, abs_div, abs_of_pos (by linarith : (0 : ℝ) < r.den)]
    apply div_le_self (abs_nonneg _) hd
  have h3 : ((ssc_qb r : ℕ) : ℝ) =
      |(r.num : ℝ)| := by
    have : ((ssc_qb r : ℤ) : ℝ) =
        ((|r.num| : ℤ) : ℝ) := by rw [h1]
    rw [← Int.cast_abs]; exact_mod_cast this
  rw [h3]; exact h2

private lemma ssc_nat_mul_half_pow_le (k : ℕ) :
    (k : ℝ) * (2 : ℝ)⁻¹ ^ k ≤ 1 := by
  rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
  exact_mod_cast (Nat.lt_two_pow_self (n := k)).le

private theorem ssc_UC_mul {α : Type*}
    [Primcodable α] {g h : α → ℝ} (hg : ssc_UC
    g) (hh : ssc_UC h) :
    ssc_UC (fun a => g a * h a) := by
  obtain ⟨q1, h1c, h1⟩ := hg
  obtain ⟨q2, h2c, h2⟩ := hh
  let k : α → ℕ := fun a => ssc_qb (q1 (a, 0))
                              + ssc_qb (q2
                              (a, 0)) + 3
  have hk : Computable k := by
    have c1 : Computable (fun a : α => ssc_qb
                                         (q1 (a, 0))) :=
      ssc_qb_comp.comp (h1c.comp (Computable.id.pair
          (Computable.const 0)))
    have c2 : Computable (fun a : α => ssc_qb
                                         (q2 (a, 0))) :=
      ssc_qb_comp.comp (h2c.comp (Computable.id.pair
          (Computable.const 0)))
    exact Computable₂.comp Primrec.nat_add.to_comp (Computable₂.comp Primrec.nat_add.to_comp c1 c2)
      (Computable.const 3)
  have hs : Computable (fun p : α × ℕ => p.2 + k p.1) :=
    Computable₂.comp Primrec.nat_add.to_comp Computable.snd (hk.comp Computable.fst)
  refine ⟨fun p => q1 (p.1, p.2 + k p.1) * q2 (p.1, p.2 + k p.1), ?_, fun a s => ?_⟩
  · exact computable₂_ratMul.comp (h1c.comp (Computable.fst.pair hs))
      (h2c.comp (Computable.fst.pair hs))
  · have e1 := h1 a (s + k a)
    have e2 := h2 a (s + k a)
    have e10 := h1 a 0
    have e20 := h2 a 0
    have b1 := ssc_abs_le_qb (q1 (a, 0))
    have b2 := ssc_abs_le_qb (q2 (a, 0))
    set e : ℝ := (2 : ℝ)⁻¹ ^ (s + k a) with he
    have he1 : e ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have he0 : 0 ≤ e := by positivity
    have hkk := ssc_nat_mul_half_pow_le (k a)
    have hes : e = (2 : ℝ)⁻¹ ^ s * (2 : ℝ)⁻¹ ^ (k a) := by rw [he, pow_add]
    simp only [pow_zero] at e10 e20
    have hg1 : |g a| ≤ (ssc_qb (q1 (a, 0)) : ℝ)
        + 1 := by
      have : |g a| ≤ |(q1 (a, 0) : ℝ)| + |(q1 (a, 0) : ℝ) - g a| := by
        calc |g a| = |(q1 (a, 0) : ℝ) - ((q1 (a, 0) : ℝ) - g a)| := by ring_nf
          _ ≤ _ := abs_sub _ _
      linarith
    have hh2 : |h a| ≤ (ssc_qb (q2 (a, 0)) : ℝ)
        + 1 := by
      have : |h a| ≤ |(q2 (a, 0) : ℝ)| + |(q2 (a, 0) : ℝ) - h a| := by
        calc |h a| = |(q2 (a, 0) : ℝ) - ((q2 (a, 0) : ℝ) - h a)| := by ring_nf
          _ ≤ _ := abs_sub _ _
      linarith
    have hx1 : |(q1 (a, s + k a) : ℝ)| ≤
        (ssc_qb (q1 (a, 0)) : ℝ) + 2 := by
      have : |(q1 (a, s + k a) : ℝ)| ≤ |g a| + |(q1 (a, s + k a) : ℝ) - g a| := by
        calc |(q1 (a, s + k a) : ℝ)| = |g a + ((q1 (a, s + k a) : ℝ) - g a)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      linarith
    push_cast
    have hdec : (q1 (a, s + k a) : ℝ) * q2 (a, s + k a) - g a * h a =
        (q1 (a, s + k a) : ℝ) * ((q2 (a, s + k a) : ℝ) - h a) +
          h a * ((q1 (a, s + k a) : ℝ) - g a) := by ring
    rw [hdec]
    calc _ ≤ |(q1 (a, s + k a) : ℝ) * ((q2 (a, s + k a) : ℝ) - h a)| +
          |h a * ((q1 (a, s + k a) : ℝ) - g a)| := abs_add_le _ _
      _ = |(q1 (a, s + k a) : ℝ)| * |(q2 (a, s + k a) : ℝ) - h a| +
          |h a| * |(q1 (a, s + k a) : ℝ) - g a| := by rw [abs_mul, abs_mul]
      _ ≤ ((ssc_qb (q1 (a, 0)) : ℝ) + 2) * e +
          ((ssc_qb (q2 (a, 0)) : ℝ) + 1) * e :=
          by
          gcongr
      _ = (k a : ℝ) * e := by
          simp only [k]; push_cast; ring
      _ ≤ (2 : ℝ)⁻¹ ^ s := by
          rw [hes]
          calc (k a : ℝ) * ((2 : ℝ)⁻¹ ^ s * (2 : ℝ)⁻¹ ^ (k a))
              = (2 : ℝ)⁻¹ ^ s * ((k a : ℝ) * (2 : ℝ)⁻¹ ^ (k a)) := by ring
            _ ≤ (2 : ℝ)⁻¹ ^ s * 1 := by gcongr
            _ = _ := mul_one _

/-- inverse of a positive rational (junk otherwise). -/
private def ssc_ratInv (q : ℚ) : ℚ :=
    ((q.den : ℤ) : ℚ) / ((max 1 q.num.toNat : ℕ) : ℚ)

private lemma ssc_ratInv_comp : Computable
    ssc_ratInv :=
  computable_of_num_den (N := fun q : ℚ => (q.den : ℤ)) (D := fun q : ℚ => max 1 q.num.toNat)
    (ComputableReals.primrec_natCastInt.to_comp.comp computable_ratDen)
    (Computable₂.comp Primrec.nat_max.to_comp (Computable.const 1)
      (ComputableReals.primrec_intToNat.to_comp.comp computable_ratNum))
    (fun _ => lt_max_of_lt_left Nat.one_pos) (fun _ => rfl)

private lemma ssc_ratInv_eq {q : ℚ}
    (hq : 0 < q) : ssc_ratInv q = q⁻¹ := by
  have hn : 0 < q.num := Rat.num_pos.mpr hq
  have h1 : max 1 q.num.toNat = q.num.toNat := max_eq_right (by omega)
  have h2 : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
    have : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg hn.le
    exact_mod_cast this
  unfold ssc_ratInv
  rw [h1, h2]
  have hq' := Rat.num_div_den q
  calc ((q.den : ℤ) : ℚ) / (q.num : ℚ) = ((q.num : ℚ) / (q.den : ℚ))⁻¹ := by
        rw [inv_div]; simp
    _ = q⁻¹ := by rw [hq']

private theorem ssc_UC_inv_pos {α : Type*}
    [Primcodable α] {g : α → ℝ} (hg : ssc_UC g)
    (hpos : ∀ a, 0 < g a) : ssc_UC
        (fun a => (g a)⁻¹) := by
  classical
  obtain ⟨q, hc, hq⟩ := hg
  have hP : Computable (fun p : α × ℕ =>
      decide (¬ (q (p.1, p.2) * ((2 ^ p.2 : ℕ) : ℚ) < 3))) := by
    have h1 : Computable (fun p : α × ℕ => q (p.1, p.2) * ((2 ^ p.2 : ℕ) : ℚ)) :=
      computable₂_ratMul.comp (hc.comp (Computable.fst.pair Computable.snd))
        (computable_nat_to_rat.comp (comp_pow.comp Computable.snd))
    have h2 := (computable_ratLtConst 3).comp h1
    exact (Primrec.not.to_comp.comp h2).of_eq (fun p => by simp only [decide_not])
  have hex : ∀ a, ∃ t, ¬ (q (a, t) * ((2 ^ t : ℕ) : ℚ) < 3) := by
    intro a
    obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one
      (show 0 < g a / 4 by have := hpos a; positivity) (show (2 : ℝ)⁻¹ < 1 by norm_num)
    refine ⟨t, fun hlt => ?_⟩
    have hlt' : (q (a, t) : ℝ) * 2 ^ t < 3 := by exact_mod_cast hlt
    have h1 := hq a t
    have hq3 : 3 * (2 : ℝ)⁻¹ ^ t < q (a, t) := by
      have := (abs_le.mp h1).1
      linarith
    have hmul : (2 : ℝ)⁻¹ ^ t * 2 ^ t = 1 := by rw [← mul_pow]; norm_num
    have := mul_lt_mul_of_pos_right hq3 (pow_pos (two_pos : (0 : ℝ) < 2) t)
    nlinarith
  let t : α → ℕ := fun a => Nat.find (hex a)
  have ht : Computable t := Computable.natFind hP hex
  have hspec : ∀ a, ¬ (q (a, t a) * ((2 ^ t a : ℕ) : ℚ) < 3) := fun a => Nat.find_spec (hex a)
  have hidx : Computable (fun p : α × ℕ => p.2 + 2 * t p.1 + 1) :=
    Computable₂.comp Primrec.nat_add.to_comp
      (Computable₂.comp Primrec.nat_add.to_comp Computable.snd
        (Computable₂.comp Primrec.nat_mul.to_comp (Computable.const 2) (ht.comp Computable.fst)))
      (Computable.const 1)
  refine ⟨fun p => ssc_ratInv
                     (q (p.1, p.2 + 2 * t p.1 + 1)),
    ssc_ratInv_comp.comp (hc.comp (Computable.fst.pair hidx)), fun a s => ?_⟩
  set T := t a with hT
  have hsp := hspec a
  have hsp' : 3 ≤ (q (a, T) : ℝ) * 2 ^ T := by
    have : (3 : ℚ) ≤ q (a, T) * ((2 ^ T : ℕ) : ℚ) := not_lt.mp hsp
    exact_mod_cast this
  set et : ℝ := (2 : ℝ)⁻¹ ^ T with het
  have het0 : 0 < et := by positivity
  have hmul : et * 2 ^ T = 1 := by rw [het, ← mul_pow]; norm_num
  have hq3 : 3 * et ≤ q (a, T) := by
    have := mul_le_mul_of_nonneg_left hsp' het0.le
    nlinarith
  have hgl : 2 * et ≤ g a := by
    have := (abs_le.mp (hq a T)).2
    linarith
  set u := s + 2 * T + 1 with hu
  have heu : (2 : ℝ)⁻¹ ^ u = (2 : ℝ)⁻¹ ^ s * et ^ 2 * 2⁻¹ := by
    rw [hu, pow_succ, pow_add, het, ← pow_mul]; ring_nf
  have heut : (2 : ℝ)⁻¹ ^ u ≤ et := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hxu := hq a u
  set x : ℝ := (q (a, u) : ℝ) with hx
  have hxl : et ≤ x := by
    have := (abs_le.mp hxu).2
    have h2 := (abs_le.mp hxu).1
    linarith
  have hx0 : 0 < x := lt_of_lt_of_le het0 hxl
  have hqx : 0 < q (a, u) := by
    have : (0 : ℝ) < (q (a, u) : ℝ) := hx0
    exact_mod_cast this
  have hg0 := hpos a
  change |((ssc_ratInv (q (a, u)) : ℚ) : ℝ) -
      (g a)⁻¹| ≤ _
  rw [ssc_ratInv_eq hqx]
  push_cast
  rw [← hx, inv_sub_inv hx0.ne' hg0.ne', abs_div, abs_of_pos (mul_pos hx0 hg0),
    div_le_iff₀ (mul_pos hx0 hg0)]
  have hxg : 2 * et ^ 2 ≤ x * g a := by nlinarith
  have hs0 : 0 ≤ (2 : ℝ)⁻¹ ^ s := by positivity
  have habs : |g a - x| ≤ (2 : ℝ)⁻¹ ^ s * et ^ 2 * 2⁻¹ := by
    rw [abs_sub_comm, ← heu]; exact hxu
  calc |g a - x| ≤ (2 : ℝ)⁻¹ ^ s * et ^ 2 * 2⁻¹ := habs
    _ ≤ (2 : ℝ)⁻¹ ^ s * (2 * et ^ 2) := by
        have : 0 ≤ (2 : ℝ)⁻¹ ^ s * et ^ 2 := by positivity
        nlinarith
    _ ≤ _ := by gcongr

private theorem ssc_comp_rangeProd
    {γ β : Type*} [Primcodable γ] [Primcodable β] [CommMonoid β]
    (hmul : Computable₂ (fun a b : β => a * b)) {f : γ → ℕ → β} (hf : Computable₂ f) :
    Computable (fun p : γ × ℕ => ∏ i ∈ Finset.range p.2, f p.1 i) := by
  have h := Computable.nat_rec (f := fun p : γ × ℕ => p.2) (g := fun _ => (1 : β))
    (h := fun (p : γ × ℕ) (yi : ℕ × β) => yi.2 * f p.1 yi.1) Computable.snd (Computable.const 1)
    (hmul.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)))
  refine h.of_eq fun p => ?_
  obtain ⟨a, n⟩ := p
  change Nat.rec (motive := fun _ => β) 1 (fun y IH => IH * f a y) n = _
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ]; exact congrArg (· * f a n) ih

private theorem ssc_prod_err (r F B : ℕ → ℝ)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hB : ∀ i, 0 ≤ B i) (hr : ∀ i, |r i - F i| ≤ δ) (hF : ∀ i, |F i| ≤ B i) (n : ℕ) :
    |∏ i ∈ Finset.range n, r i - ∏ i ∈ Finset.range n, F i| ≤
      δ * n * ∏ i ∈ Finset.range n, (B i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
    set Pr := ∏ i ∈ Finset.range n, r i
    set PF := ∏ i ∈ Finset.range n, F i
    set T := ∏ i ∈ Finset.range n, (B i + 1) with hT
    have hT1 : 0 ≤ T := Finset.prod_nonneg (fun i _ => by linarith [hB i])
    have hPF : |PF| ≤ T := by
      rw [Finset.abs_prod]
      calc ∏ i ∈ Finset.range n, |F i| ≤ ∏ i ∈ Finset.range n, (B i + 1) :=
            Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => by linarith [hF i])
        _ = T := rfl
    have hrn : |r n| ≤ B n + 1 := by
      have := abs_sub_abs_le_abs_sub (r n) (F n)
      have := hr n; have := hF n
      linarith [abs_sub_comm (r n) (F n)]
    have heq : Pr * r n - PF * F n = (Pr - PF) * r n + PF * (r n - F n) := by ring
    rw [heq]
    have h1 : |(Pr - PF) * r n| ≤ (δ * n * T) * (B n + 1) := by
      rw [abs_mul]
      exact mul_le_mul ih hrn (abs_nonneg _) (by positivity)
    have h2 : |PF * (r n - F n)| ≤ T * δ := by
      rw [abs_mul]
      exact mul_le_mul hPF (hr n) (abs_nonneg _) (by linarith)
    have hBn := hB n
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc |(Pr - PF) * r n + PF * (r n - F n)| ≤ |(Pr - PF) * r n| + |PF * (r n - F n)| :=
          abs_add_le _ _
      _ ≤ (δ * n * T) * (B n + 1) + T * δ := add_le_add h1 h2
      _ ≤ δ * ((n + 1 : ℕ) : ℝ) * (T * (B n + 1)) := by
          push_cast
          have : T * δ ≤ δ * T * (B n + 1) := by
            nlinarith [mul_nonneg hδ0 (by linarith : (0 : ℝ) ≤ T)]
          nlinarith

private theorem ssc_UC_prod_range {α : Type*}
    [Primcodable α] {G : α × ℕ → ℝ} (hG :
    ssc_UC G) :
    ssc_UC (fun p : α ×
        ℕ => ∏ i ∈ Finset.range p.2, G (p.1, i)) := by
  obtain ⟨q, hq, hb⟩ := hG
  let K : α × ℕ → ℕ := fun p => p.2 * ∏ i ∈ Finset.range p.2,
                                  (ssc_qb (q ((p.1,
                                  i), 0)) + 2)
  have hf1 : Computable₂ (fun (a : α) (i : ℕ) =>
    ssc_qb (q ((a, i), 0)) + 2) := by
    have : Computable (fun x : α × ℕ => ssc_qb
                                          (q ((x.1, x.2), 0)) + 2) :=
      Primrec.nat_add.to_comp.comp
        (ssc_qb_comp.comp (hq.comp (Computable.pair
            Computable.id (Computable.const 0))))
        (Computable.const 2)
    exact this
  have hK : Computable K :=
    Primrec.nat_mul.to_comp.comp Computable.snd
      (ssc_comp_rangeProd (β := ℕ)
          Primrec.nat_mul.to_comp hf1)
  have hf2 : Computable₂ (fun (ps : (α × ℕ) × ℕ) (i : ℕ) => q ((ps.1.1, i), ps.2 + K ps.1)) := by
    have : Computable (fun x : ((α × ℕ) × ℕ) × ℕ => q ((x.1.1.1, x.2), x.1.2 + K x.1.1)) :=
      hq.comp (Computable.pair (Computable.pair (Computable.fst.comp (Computable.fst.comp
          Computable.fst))
        Computable.snd)
        (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.fst)
          (hK.comp (Computable.fst.comp Computable.fst))))
    exact this
  have hP := ssc_comp_rangeProd (β := ℚ)
      computable₂_ratMul hf2
  refine ⟨fun x : (α × ℕ) × ℕ => ∏ i ∈ Finset.range x.1.2, q ((x.1.1, i), x.2 + K x.1), ?_, ?_⟩
  · exact (hP.comp (Computable.pair Computable.id (Computable.snd.comp Computable.fst))).of_eq
      fun x => rfl
  · intro p s
    obtain ⟨a, n⟩ := p
    change |((∏ i ∈ Finset.range n, q ((a, i), s + K (a, n)) : ℚ) : ℝ) -
        ∏ i ∈ Finset.range n, G (a, i)| ≤ _
    push_cast
    set k := K (a, n) with hk
    have herr := ssc_prod_err
        (fun i => (q ((a, i), s + k) : ℝ)) (fun i => G (a, i))
      (fun i => (ssc_qb (q ((a, i), 0)) : ℝ) +
                  1) ((2 : ℝ)⁻¹ ^ (s + k)) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))
      (fun i => by positivity) (fun i => hb _ _)
      (fun i => by
        have h0 := hb (a, i) 0
        have h1 := ssc_abs_le_qb
            (q ((a, i), 0))
        simp only [pow_zero] at h0
        have := abs_sub_abs_le_abs_sub (G (a, i)) (q ((a, i), 0) : ℝ)
        rw [abs_sub_comm] at this
        linarith) n
    refine herr.trans ?_
    have hprod : ∏ i ∈ Finset.range n,
        (((ssc_qb (q ((a, i), 0)) : ℝ) + 1) +
        1) =
        ∏ i ∈ Finset.range n, ((ssc_qb (q ((a,
            i), 0)) + 2 : ℕ) : ℝ) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      push_cast; ring
    rw [hprod]
    have hkc : ((k : ℕ) : ℝ) = (n : ℝ) * ∏ i ∈ Finset.range n,
        ((ssc_qb (q ((a, i), 0)) + 2 : ℕ) : ℝ)
        := by
      simp only [hk, K]; push_cast; rfl
    rw [mul_assoc, ← hkc, pow_add]
    have hk2 : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ s := by positivity
    have : (2 : ℝ)⁻¹ ^ k * (k : ℝ) ≤ 1 := by
      rw [inv_pow]
      rw [inv_mul_le_iff₀ (by positivity)]
      simpa using hk2
    calc (2 : ℝ)⁻¹ ^ s * (2 : ℝ)⁻¹ ^ k * (k : ℝ) = (2 : ℝ)⁻¹ ^ s * ((2 : ℝ)⁻¹ ^ k * k) := by ring
      _ ≤ (2 : ℝ)⁻¹ ^ s * 1 := mul_le_mul_of_nonneg_left this hpos.le
      _ = _ := mul_one _

-- B
private lemma ssc_dyadicValue_toReal (n s : ℕ)
    :
    (dyadicValue n s).toReal = (n : ℝ) / 2 ^ s := by
  simp [dyadicValue, ENNReal.toReal_div]

private lemma ssc_cantorMass_ne_top
    (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (y : BitString) :
    cantorMass μ y ≠ ⊤ := by
  unfold cantorMass
  exact measure_ne_top _ _

private theorem ssc_UC_mass
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) :
    ssc_UC (fun y : BitString =>
      (cantorMass μ y).toReal) := by
  obtain ⟨a, ha, hb⟩ := hμ
  refine ⟨fun p => ((a p.1 p.2 : ℕ) : ℚ) / ((2 ^ p.2 : ℕ) : ℚ), ?_, ?_⟩
  · refine computable_of_num_den (N := fun p : BitString × ℕ => ((a p.1 p.2 : ℕ) : ℤ))
      (D := fun p : BitString × ℕ => 2 ^ p.2) ?_ ?_ (fun p => by positivity)
          (fun p => by push_cast; rfl)
    · exact (ComputableReals.primrec_natCastInt.to_comp).comp (ha : Computable₂ a)
    · exact comp_pow.comp Computable.snd
  · intro y s
    obtain ⟨h1, h2⟩ := hb y s
    have hne := ssc_cantorMass_ne_top μ y
    have hne1 : dyadicValue 1 s ≠ ⊤ := by simp [dyadicValue]
    have hne2 : dyadicValue (a y s) s ≠ ⊤ := by
      unfold dyadicValue
      exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ (by norm_num))
    have h1' := (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hne, hne1⟩) h1)
    have h2' := (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hne2, hne1⟩) h2)
    rw [ENNReal.toReal_add hne hne1, ssc_dyadicValue_toReal, ssc_dyadicValue_toReal] at h1'
    rw [ENNReal.toReal_add hne2 hne1, ssc_dyadicValue_toReal, ssc_dyadicValue_toReal] at h2'
    have hpow : ((2 : ℝ)⁻¹) ^ s = (1 : ℝ) / 2 ^ s := by rw [inv_pow]; simp
    rw [hpow, abs_le]
    push_cast
    constructor <;> linarith

-- C
private lemma ssc_condProb_eq
    (μ : Measure CantorSeq) (y : BitString) (b : Bool) :
    condProb (cantorMass μ) y b =
      (cantorMass μ (y ++ [b])).toReal * ((cantorMass μ y).toReal)⁻¹ := div_eq_mul_inv _ _

private lemma ssc_condProb_pos
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ]
    (hpos : ∀ x, 0 < cantorMass μ x) (y : BitString) (b : Bool) :
    0 < condProb (cantorMass μ) y b := by
  unfold condProb
  exact div_pos (ENNReal.toReal_pos (hpos _).ne'
      (ssc_cantorMass_ne_top μ _))
    (ENNReal.toReal_pos (hpos _).ne'
        (ssc_cantorMass_ne_top μ _))

private lemma ssc_UC_condProb
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ]
    (hμ : IsComputableMeasure μ) (hpos : ∀ x, 0 < cantorMass μ x) :
    ssc_UC (fun p : BitString × Bool =>
      condProb (cantorMass μ) p.1 p.2) := by
  have hm := ssc_UC_mass hμ
  have h1 : ssc_UC (fun p : BitString × Bool =>
    (cantorMass μ (p.1 ++ [p.2])).toReal) :=
    ssc_UC_comp hm (f := fun p : BitString ×
        Bool => p.1 ++ [p.2])
      (Computable.list_append.comp Computable.fst
        ((Computable.list_cons.comp Computable.snd (Computable.const [])) ))
  have h2 : ssc_UC (fun p : BitString × Bool =>
    (cantorMass μ p.1).toReal) :=
    ssc_UC_comp hm (f := fun p : BitString ×
        Bool => p.1) Computable.fst
  have h3 := ssc_UC_inv_pos h2
      (fun p => ENNReal.toReal_pos (hpos _).ne'
                  (ssc_cantorMass_ne_top μ _))
  have := ssc_UC_mul h1 h3
  simpa only [ssc_condProb_eq] using this

private theorem ssc_main
    {μ μ' : Measure CantorSeq} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hμ : IsComputableMeasure μ) (hμ' : IsComputableMeasure μ')
    (hpos : ∀ x, 0 < cantorMass μ x) (hpos' : ∀ x, 0 < cantorMass μ' x) :
    IsComputableOnStrings (fun x : BitString =>
      ∏ i : Fin x.length,
        (condProb (cantorMass μ) (x.take i) x[i] +
          condProb (cantorMass μ') (x.take i) x[i]) /
          (2 * condProb (cantorMass μ) (x.take i) x[i])) := by
  have hP := ssc_UC_condProb hμ hpos
  have hP' := ssc_UC_condProb hμ' hpos'
  have hinv := ssc_UC_inv_pos hP
      (fun p => ssc_condProb_pos hpos p.1 p.2)
  have hhalf : ssc_UC (fun _ : BitString ×
      Bool => ((1 / 2 : ℚ) : ℝ)) :=
    ssc_UC_rat (r := fun _ : BitString ×
        Bool => (1 / 2 : ℚ)) (Computable.const _)
  have hFac := ssc_UC_mul
      (ssc_UC_add hP hP')
      (ssc_UC_mul hhalf hinv)
  have hG : ssc_UC (fun p : BitString × ℕ =>
      (fun q : BitString × Bool => (condProb (cantorMass μ) q.1 q.2 + condProb (cantorMass μ') q.1
                                     q.2) *
        (((1 / 2 : ℚ) : ℝ) * (condProb (cantorMass μ) q.1 q.2)⁻¹)) (p.1.take p.2, p.1.getD p.2
            false)) :=
    ssc_UC_comp hFac (f := fun p : BitString ×
        ℕ => (p.1.take p.2, p.1.getD p.2 false))
      (Computable.pair
        ((Primrec.list_take.to_comp).comp Computable.snd Computable.fst)
        (((Primrec.list_getD false).to_comp).comp Computable.fst Computable.snd))
  have hprod := ssc_UC_comp
      (ssc_UC_prod_range hG)
    (f := fun x : BitString => (x, x.length)) (Computable.pair Computable.id Computable.list_length)
  have heq : (fun x : BitString =>
      ∏ i : Fin x.length,
        (condProb (cantorMass μ) (x.take i) x[i] +
          condProb (cantorMass μ') (x.take i) x[i]) /
          (2 * condProb (cantorMass μ) (x.take i) x[i])) =
      fun x : BitString => ∏ i ∈ Finset.range (x, x.length).2,
        (fun p : BitString × ℕ =>
      (fun q : BitString × Bool => (condProb (cantorMass μ) q.1 q.2 + condProb (cantorMass μ') q.1
                                     q.2) *
        (((1 / 2 : ℚ) : ℝ) * (condProb (cantorMass μ) q.1 q.2)⁻¹)) (p.1.take p.2, p.1.getD p.2
            false)) ((x, x.length).1, i) := by
    funext x
    simp only
    rw [← Fin.prod_univ_eq_prod_range (fun i => (condProb (cantorMass μ) (x.take i) (x.getD i false)
                                                  +
      condProb (cantorMass μ') (x.take i) (x.getD i false)) *
        (((1 / 2 : ℚ) : ℝ) * (condProb (cantorMass μ) (x.take i) (x.getD i false))⁻¹)) x.length]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [List.getD_eq_getElem _ _ i.2, div_eq_mul_inv, mul_inv]
    push_cast
    simp [one_div]
  rw [heq]
  exact hprod
/-- Step 1 of the proof of `summable_sq_condOne_sub_of_isComputablyRandom`: both inline
bookmaker capitals are computable on strings. -/
theorem summable_sq_condOne_sub_of_isComputablyRandom_comp
    {μ μ' : Measure CantorSeq} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hμ : IsComputableMeasure μ) (hμ' : IsComputableMeasure μ')
    (hpos : ∀ x, 0 < cantorMass μ x) (hpos' : ∀ x, 0 < cantorMass μ' x) :
    IsComputableOnStrings (fun x : BitString =>
      ∏ i : Fin x.length,
        (condProb (cantorMass μ) (x.take i) x[i] +
          condProb (cantorMass μ') (x.take i) x[i]) /
          (2 * condProb (cantorMass μ) (x.take i) x[i])) ∧
    IsComputableOnStrings (fun x : BitString =>
      ∏ i : Fin x.length,
        (condProb (cantorMass μ') (x.take i) x[i] +
          condProb (cantorMass μ) (x.take i) x[i]) /
          (2 * condProb (cantorMass μ') (x.take i) x[i])) :=
  ⟨ssc_main hμ hμ' hpos hpos',
    ssc_main hμ' hμ hpos' hpos⟩

/-- The `Fin`-indexed product as a product over `Finset.range` with the letter read by `getD`. -/
private lemma summable_sq_condOne_sub_of_isComputablyRandom_fair_aux_prod
    (g : BitString → Bool → ℝ) (x : BitString) :
    ∏ i : Fin x.length, g (x.take i) x[i] =
      ∏ i ∈ Finset.range x.length, g (x.take i) (x.getD i false) := by
  rw [← Fin.prod_univ_eq_prod_range (fun i => g (x.take i) (x.getD i false)) x.length]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [List.getD_eq_getElem?_getD]

/-- Appending a bit multiplies the product by one new factor. -/
private lemma summable_sq_condOne_sub_of_isComputablyRandom_fair_aux_snoc
    (g : BitString → Bool → ℝ) (x : BitString) (b : Bool) :
    ∏ i : Fin (x ++ [b]).length, g ((x ++ [b]).take i) (x ++ [b])[i] =
      (∏ i : Fin x.length, g (x.take i) x[i]) * g x b := by
  rw [summable_sq_condOne_sub_of_isComputablyRandom_fair_aux_prod,
    summable_sq_condOne_sub_of_isComputablyRandom_fair_aux_prod,
    List.length_append, List.length_singleton, Finset.prod_range_succ]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < x.length := Finset.mem_range.1 hi
    rw [List.take_append_of_le_length hi'.le, List.getD_append _ _ _ _ hi']
  · simp

/-- General fairness of the inline bookmaker capital. -/
private lemma summable_sq_condOne_sub_of_isComputablyRandom_fair_aux_fair
    {μ μ' : Measure CantorSeq} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hpos : ∀ x, 0 < cantorMass μ x) (hpos' : ∀ x, 0 < cantorMass μ' x) :
    IsFairCapital μ (fun x : BitString => ∏ i : Fin x.length,
      (condProb (cantorMass μ) (x.take i) x[i] +
        condProb (cantorMass μ') (x.take i) x[i]) /
        (2 * condProb (cantorMass μ) (x.take i) x[i])) := by
  have hsnoc := summable_sq_condOne_sub_of_isComputablyRandom_fair_aux_snoc
    (fun y b => (condProb (cantorMass μ) y b + condProb (cantorMass μ') y b) /
      (2 * condProb (cantorMass μ) y b))
  refine ⟨fun x => ?_, fun x => ?_⟩
  · exact Finset.prod_nonneg fun i _ => div_nonneg
      (add_nonneg (condProb_nonneg _ _ _) (condProb_nonneg _ _ _))
      (mul_nonneg (by norm_num) (condProb_nonneg _ _ _))
  · rw [hsnoc x false, hsnoc x true]
    generalize (∏ i : Fin x.length, (condProb (cantorMass μ) (x.take i) x[i] +
        condProb (cantorMass μ') (x.take i) x[i]) /
        (2 * condProb (cantorMass μ) (x.take i) x[i])) = P
    have hM : 0 < massR μ x := ENNReal.toReal_pos (hpos x).ne' (measure_ne_top _ _)
    have hmass : ∀ b, massR μ (x ++ [b]) = condProb (cantorMass μ) x b * massR μ x := by
      intro b
      unfold condProb massR
      exact (div_mul_cancel₀ _ hM.ne').symm
    have hMb : ∀ b, 0 < massR μ (x ++ [b]) := fun b =>
      ENNReal.toReal_pos (hpos _).ne' (measure_ne_top _ _)
    have hc : ∀ b, 0 < condProb (cantorMass μ) x b := by
      intro b
      have := hMb b
      rw [hmass b] at this
      exact pos_of_mul_pos_left this hM.le
    have h1 := condProb_cantorMass_add_eq_one μ (hpos x).ne'
    have h2 := condProb_cantorMass_add_eq_one μ' (hpos' x).ne'
    rw [hmass false, hmass true]
    have e : ∀ b, (condProb (cantorMass μ) x b + condProb (cantorMass μ') x b) /
        (2 * condProb (cantorMass μ) x b) * condProb (cantorMass μ) x b =
        (condProb (cantorMass μ) x b + condProb (cantorMass μ') x b) / 2 := by
      intro b
      have := (hc b).ne'
      field_simp
    linear_combination (-(P * massR μ x)) * e false + (-(P * massR μ x)) * e true +
      (-(P * massR μ x / 2)) * (h1 + h2)

/-- Step 2 of the proof of `summable_sq_condOne_sub_of_isComputablyRandom`: each inline
bookmaker capital is fair for its measure. -/
private theorem summable_sq_condOne_sub_of_isComputablyRandom_fair
    {μ μ' : Measure CantorSeq} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hpos : ∀ x, 0 < cantorMass μ x) (hpos' : ∀ x, 0 < cantorMass μ' x) :
    IsFairCapital μ (fun x : BitString => ∏ i : Fin x.length,
      (condProb (cantorMass μ) (x.take i) x[i] +
        condProb (cantorMass μ') (x.take i) x[i]) /
        (2 * condProb (cantorMass μ) (x.take i) x[i])) ∧
    IsFairCapital μ' (fun x : BitString => ∏ i : Fin x.length,
      (condProb (cantorMass μ') (x.take i) x[i] +
        condProb (cantorMass μ) (x.take i) x[i]) /
        (2 * condProb (cantorMass μ') (x.take i) x[i])) :=
  ⟨summable_sq_condOne_sub_of_isComputablyRandom_fair_aux_fair hpos hpos',
    summable_sq_condOne_sub_of_isComputablyRandom_fair_aux_fair hpos' hpos⟩

/-- Step 3 of the proof of `ssc_wins`:
reindexing a `Fin`-product over a prefix as a `range` product. -/
private lemma ssc_wins_aux1_prod
    (F : BitString → Bool → ℝ) (w : CantorSeq) (n : ℕ) :
    ∏ i : Fin (cantorPrefix w n).length, F ((cantorPrefix w n).take i) (cantorPrefix w n)[i] =
      ∏ i ∈ Finset.range n, F (cantorPrefix w i) (w i) := by
  have h1 : ∏ i : Fin (cantorPrefix w n).length,
      F ((cantorPrefix w n).take i) (cantorPrefix w n)[i] =
      ∏ i : Fin (cantorPrefix w n).length, F (cantorPrefix w i.1) (w i.1) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hi : (i : ℕ) ≤ n := by
      have : (i : ℕ) < n := by simpa using i.2
      omega
    rw [cantorPrefix_take w i n hi]
    simp
  rw [h1]
  have h := cantorPrefix_length w n
  generalize (cantorPrefix w n).length = m at h ⊢
  subst h
  exact Fin.prod_univ_eq_prod_range (fun i => F (cantorPrefix w i) (w i)) _

/-- Step 4 of the proof of `ssc_wins`: `1
+ ∑ t ≤ ∏ (1 + t)` for nonnegative `t`. -/
private lemma ssc_wins_aux2_prod_ge
    (t : ℕ → ℝ) (ht : ∀ i, 0 ≤ t i) (n : ℕ) :
    1 + ∑ i ∈ Finset.range n, t i ≤ ∏ i ∈ Finset.range n, (1 + t i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hS : 0 ≤ ∑ i ∈ Finset.range n, t i := Finset.sum_nonneg (fun i _ => ht i)
    have := ht n
    nlinarith

/-- Step 5 of the proof of `ssc_wins`: the
product of the two factors is at least `1 + (a - a')^2 / 4`. -/
private lemma ssc_wins_aux3_factor
    {a a' : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (ha' : 0 < a') (ha1' : a' ≤ 1) :
    1 + (a - a') ^ 2 / 4 ≤ ((a + a') / (2 * a)) * ((a' + a) / (2 * a')) := by
  have hprod : a * a' ≤ 1 := by nlinarith
  have hpos : 0 < a * a' := mul_pos ha ha'
  have h : ((a + a') / (2 * a)) * ((a' + a) / (2 * a')) = 1 + (a - a') ^ 2 / (4 * (a * a')) := by
    field_simp
    ring
  rw [h]
  have : (a - a') ^ 2 / 4 ≤ (a - a') ^ 2 / (4 * (a * a')) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    nlinarith
  linarith

/-- Step 6 of the proof of `ssc_wins`:
conditional probabilities of the actual bit lie in `(0, 1]` and are `condOne` or `1 - condOne`. -/
private lemma ssc_wins_aux4_cond
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ] (hpos : ∀ x, 0 < cantorMass μ x)
    (x : BitString) (b : Bool) :
    0 < condProb (cantorMass μ) x b ∧ condProb (cantorMass μ) x b ≤ 1 ∧
      (condProb (cantorMass μ) x b = if b then condOne μ x else 1 - condOne μ x) := by
  have h1 := condProb_cantorMass_add_eq_one μ (hpos x).ne'
  have hnn0 := condProb_nonneg (cantorMass μ) x false
  have hnn1 := condProb_nonneg (cantorMass μ) x true
  have hp : 0 < condProb (cantorMass μ) x b := by
    unfold condProb
    apply div_pos
    · exact ENNReal.toReal_pos (hpos _).ne' (ne_top_of_lt (measure_lt_top μ _))
    · exact ENNReal.toReal_pos (hpos _).ne' (ne_top_of_lt (measure_lt_top μ _))
  refine ⟨hp, ?_, ?_⟩
  · cases b <;> linarith
  · cases b
    · simp only [condOne]; simp; linarith
    · simp [condOne]

/-- Step 3 of the proof of `summable_sq_condOne_sub_of_isComputablyRandom`: nonsummability
makes one inline bookmaker capital win. -/
private theorem ssc_wins
    {μ μ' : Measure CantorSeq} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hpos : ∀ x, 0 < cantorMass μ x) (hpos' : ∀ x, 0 < cantorMass μ' x)
    {w : CantorSeq}
    (hsum : ¬ Summable fun n =>
      (condOne μ (cantorPrefix w n) - condOne μ' (cantorPrefix w n)) ^ 2) :
    Wins (fun x : BitString => ∏ i : Fin x.length,
      (condProb (cantorMass μ) (x.take i) x[i] +
        condProb (cantorMass μ') (x.take i) x[i]) /
        (2 * condProb (cantorMass μ) (x.take i) x[i])) w ∨
    Wins (fun x : BitString => ∏ i : Fin x.length,
      (condProb (cantorMass μ') (x.take i) x[i] +
        condProb (cantorMass μ) (x.take i) x[i]) /
        (2 * condProb (cantorMass μ') (x.take i) x[i])) w := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  unfold Wins at h1 h2
  rw [not_not] at h1 h2
  obtain ⟨B, hB⟩ := h1
  obtain ⟨B', hB'⟩ := h2
  apply hsum
  set a : ℕ → ℝ := fun i => condProb (cantorMass μ) (cantorPrefix w i) (w i) with ha_def
  set a' : ℕ → ℝ := fun i => condProb (cantorMass μ') (cantorPrefix w i) (w i) with ha'_def
  have hP : ∀ n, (∏ i : Fin (cantorPrefix w n).length,
      (condProb (cantorMass μ) ((cantorPrefix w n).take i) (cantorPrefix w n)[i] +
        condProb (cantorMass μ') ((cantorPrefix w n).take i) (cantorPrefix w n)[i]) /
        (2 * condProb (cantorMass μ) ((cantorPrefix w n).take i) (cantorPrefix w n)[i])) =
      ∏ i ∈ Finset.range n, (a i + a' i) / (2 * a i) := fun n =>
    ssc_wins_aux1_prod
      (fun x b => (condProb (cantorMass μ) x b + condProb (cantorMass μ') x b) /
        (2 * condProb (cantorMass μ) x b)) w n
  have hP' : ∀ n, (∏ i : Fin (cantorPrefix w n).length,
      (condProb (cantorMass μ') ((cantorPrefix w n).take i) (cantorPrefix w n)[i] +
        condProb (cantorMass μ) ((cantorPrefix w n).take i) (cantorPrefix w n)[i]) /
        (2 * condProb (cantorMass μ') ((cantorPrefix w n).take i) (cantorPrefix w n)[i])) =
      ∏ i ∈ Finset.range n, (a' i + a i) / (2 * a' i) := fun n =>
    ssc_wins_aux1_prod
      (fun x b => (condProb (cantorMass μ') x b + condProb (cantorMass μ) x b) /
        (2 * condProb (cantorMass μ') x b)) w n
  have hB1 : ∀ n, ∏ i ∈ Finset.range n, (a i + a' i) / (2 * a i) ≤ B := fun n => by
    rw [← hP]; exact hB ⟨n, rfl⟩
  have hB2 : ∀ n, ∏ i ∈ Finset.range n, (a' i + a i) / (2 * a' i) ≤ B' := fun n => by
    rw [← hP']; exact hB' ⟨n, rfl⟩
  have hapos : ∀ i, 0 < a i := fun i =>
    (ssc_wins_aux4_cond hpos _ _).1
  have ha1 : ∀ i, a i ≤ 1 := fun i =>
    (ssc_wins_aux4_cond hpos _ _).2.1
  have hapos' : ∀ i, 0 < a' i := fun i =>
    (ssc_wins_aux4_cond hpos' _ _).1
  have ha1' : ∀ i, a' i ≤ 1 := fun i =>
    (ssc_wins_aux4_cond hpos' _ _).2.1
  have hdiff : ∀ i, (a i - a' i) ^ 2 =
      (condOne μ (cantorPrefix w i) - condOne μ' (cantorPrefix w i)) ^ 2 := by
    intro i
    have e1 := (ssc_wins_aux4_cond hpos
      (cantorPrefix w i) (w i)).2.2
    have e2 := (ssc_wins_aux4_cond hpos'
      (cantorPrefix w i) (w i)).2.2
    simp only [ha_def, ha'_def]
    rw [e1, e2]
    cases w i <;> simp
    ring
  have hB0 : 1 ≤ B := by simpa using hB1 0
  have hmain : ∀ n, 1 + (∑ i ∈ Finset.range n,
      (condOne μ (cantorPrefix w i) - condOne μ' (cantorPrefix w i)) ^ 2) / 4 ≤ B * B' := by
    intro n
    have e1 : 1 + (∑ i ∈ Finset.range n,
        (condOne μ (cantorPrefix w i) - condOne μ' (cantorPrefix w i)) ^ 2) / 4 =
        1 + ∑ i ∈ Finset.range n, (a i - a' i) ^ 2 / 4 := by
      rw [Finset.sum_div]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by rw [hdiff i])
    rw [e1]
    refine (ssc_wins_aux2_prod_ge
      (fun i => (a i - a' i) ^ 2 / 4) (fun i => by positivity) n).trans ?_
    calc ∏ i ∈ Finset.range n, (1 + (a i - a' i) ^ 2 / 4)
        ≤ ∏ i ∈ Finset.range n, (((a i + a' i) / (2 * a i)) * ((a' i + a i) / (2 * a' i))) := by
          refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => ?_)
          exact ssc_wins_aux3_factor
            (hapos i) (ha1 i) (hapos' i) (ha1' i)
      _ = (∏ i ∈ Finset.range n, (a i + a' i) / (2 * a i)) *
            ∏ i ∈ Finset.range n, (a' i + a i) / (2 * a' i) := Finset.prod_mul_distrib
      _ ≤ B * B' := by
          refine mul_le_mul (hB1 n) (hB2 n)
            (Finset.prod_nonneg (fun i _ => by have := hapos i; have := hapos' i; positivity))
            (by linarith)
  refine summable_of_sum_range_le (c := 4 * (B * B')) (fun n => sq_nonneg _) (fun n => ?_)
  have := hmain n
  linarith

/-- **SUV Problem 278, p. 301.**  For Theorem 197 computable randomness with respect to both
measures is enough, assuming all masses positive.  Here the conditional probabilities must be
separated from `0` and `1`, as in the book: the argument of Theorem 197 uses it. -/
theorem summable_sq_condOne_sub_of_isComputablyRandom {μ μ' : Measure CantorSeq}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hμ : IsComputableMeasure μ)
    (hμ' : IsComputableMeasure μ') (hpos : ∀ x, 0 < cantorMass μ x)
    (hpos' : ∀ x, 0 < cantorMass μ' x) {w : CantorSeq} (hw : IsComputablyRandom μ w)
    (hw' : IsComputablyRandom μ' w) {ε : ℝ} (_hε : 0 < ε)
    (_hsep : ∀ n, ε < condOne μ (cantorPrefix w n) ∧ condOne μ (cantorPrefix w n) < 1 - ε)
    (_hsep' : ∀ n, ε < condOne μ' (cantorPrefix w n) ∧ condOne μ' (cantorPrefix w n) < 1 - ε) :
    Summable fun n => (condOne μ (cantorPrefix w n) - condOne μ' (cantorPrefix w n)) ^ 2 := by
  by_contra hsum
  obtain ⟨hcomp, hcomp'⟩ := summable_sq_condOne_sub_of_isComputablyRandom_comp hμ hμ' hpos
      hpos'
  obtain ⟨hfair, hfair'⟩ := summable_sq_condOne_sub_of_isComputablyRandom_fair hpos hpos'
  have hwins := ssc_wins hpos hpos'
      hsum
  rcases hwins with hwins_left | hwins_right
  · exact hw _ hfair hcomp hwins_left
  · exact hw' _ hfair' hcomp' hwins_right

/-- The factor by which the first of two bookmakers' capitals changes on outcome `b` after `x`: the
capital split in the proportion of the average of the two conditional probabilities. -/
noncomputable def bookmakerFactor (μ μ' : Measure CantorSeq) (x : BitString) (b : Bool) : ℝ :=
  (condProb (cantorMass μ) x b + condProb (cantorMass μ') x b) / (2 * condProb (cantorMass μ) x b)

/-- The capital against the bookmaker `μ`, when the other bookmaker is `μ'`, SUV p. 301. -/
noncomputable def bookmakerCapital (μ μ' : Measure CantorSeq) (x : BitString) : ℝ :=
  ∏ i : Fin x.length, bookmakerFactor μ μ' (x.take i) x[i]


/-- Step 1 of the proof of `isMartingale_bookmakerCapital`: the initial capital is 1. -/
lemma isMartingale_bookmakerCapital_nil (μ μ' : Measure CantorSeq) :
    bookmakerCapital μ μ' [] = 1 := by
  rfl

/-- Step 2 of the proof of `isMartingale_bookmakerCapital`: the capital is non-negative.
-/
lemma isMartingale_bookmakerCapital_nonneg (μ μ' : Measure CantorSeq) (x : BitString)
    :
    0 ≤ bookmakerCapital μ μ' x := by
  dsimp [bookmakerCapital]
  apply Finset.prod_nonneg
  intro i _
  apply div_nonneg
  · apply add_nonneg <;> apply div_nonneg <;> exact ENNReal.toReal_nonneg
  · apply mul_nonneg (by norm_num) (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

/-- Step 3 of the proof of `isMartingale_bookmakerCapital`: bookmakerCapital recursive
step -/
private lemma isMartingale_bookmakerCapital_rec (μ μ' : Measure CantorSeq) (x : BitString)
    (b : Bool) :
    bookmakerCapital μ μ' (x ++ [b]) = bookmakerCapital μ μ' x * bookmakerFactor μ μ' x b := by
  have key : ∀ y : BitString, bookmakerCapital μ μ' y =
      ∏ i ∈ Finset.range y.length, bookmakerFactor μ μ' (y.take i) (y.getD i false) := by
    intro y
    unfold bookmakerCapital
    rw [← Fin.prod_univ_eq_prod_range
      (fun i => bookmakerFactor μ μ' (y.take i) (y.getD i false)) y.length]
    apply Finset.prod_congr rfl
    intro i _
    simp [List.getD_eq_getElem?_getD]
  rw [key, key, List.length_append, List.length_singleton, Finset.prod_range_succ]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    have hi' : i < x.length := Finset.mem_range.mp hi
    rw [List.take_append_of_le_length hi'.le, List.getD_append _ _ _ _ hi']
  · simp

/-- Step 4 of the proof of `isMartingale_bookmakerCapital`: condition probabilities sum to
1. -/
private lemma isMartingale_bookmakerCapital_sum (μ : Measure CantorSeq) [IsProbabilityMeasure
    μ]
    (hpos : ∀ x, 0 < cantorMass μ x) (x : BitString) :
    condProb (cantorMass μ) x false + condProb (cantorMass μ) x true = 1 :=
  condProb_cantorMass_add_eq_one μ (hpos x).ne'

/-- Step 5 of the proof of `isMartingale_bookmakerCapital`: factor mass step -/
private lemma isMartingale_bookmakerCapital_mass (μ μ' : Measure CantorSeq)
    [IsProbabilityMeasure μ]
    (hpos : ∀ x, 0 < cantorMass μ x) (x : BitString) (b : Bool) :
    bookmakerFactor μ μ' x b * massR μ (x ++ [b]) =
    (condProb (cantorMass μ) x b + condProb (cantorMass μ') x b) / 2 * massR μ x := by
  have hA : massR μ x ≠ 0 := by
    unfold massR
    exact (ENNReal.toReal_pos (hpos x).ne' (measure_ne_top μ _)).ne'
  have hB : massR μ (x ++ [b]) ≠ 0 := by
    unfold massR
    exact (ENNReal.toReal_pos (hpos (x ++ [b])).ne' (measure_ne_top μ _)).ne'
  have hp : condProb (cantorMass μ) x b ≠ 0 := by
    unfold condProb
    exact div_ne_zero hB hA
  have hmass : massR μ (x ++ [b]) = condProb (cantorMass μ) x b * massR μ x := by
    unfold condProb
    unfold massR at hA ⊢
    field_simp
  unfold bookmakerFactor
  rw [hmass]
  field_simp

/-- **SUV p. 301.**  For measures with all conditional probabilities positive,
`bookmakerCapital μ μ'` is a `μ`-martingale. -/
theorem isMartingale_bookmakerCapital {μ μ' : Measure CantorSeq} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (hpos : ∀ x, 0 < cantorMass μ x) (hpos' : ∀ x, 0 < cantorMass μ' x) :
    IsMartingale μ (bookmakerCapital μ μ') := by
  apply IsMartingale.mk (IsFairCapital.mk (isMartingale_bookmakerCapital_nonneg μ μ') _)
      (isMartingale_bookmakerCapital_nil μ μ')
  intro x
  rw [isMartingale_bookmakerCapital_rec μ μ' x false, isMartingale_bookmakerCapital_rec
      μ μ' x true]
  rw [mul_assoc, isMartingale_bookmakerCapital_mass μ μ' hpos x false]
  rw [mul_assoc, isMartingale_bookmakerCapital_mass μ μ' hpos x true]
  have h1 := isMartingale_bookmakerCapital_sum μ hpos x
  have h2 := isMartingale_bookmakerCapital_sum μ' hpos' x
  have hm : (condProb (cantorMass μ) x false + condProb (cantorMass μ') x false) / 2 * massR μ x +
            (condProb (cantorMass μ) x true + condProb (cantorMass μ') x true) / 2 * massR μ x =
                massR μ x := by
    calc
      _ = ((condProb (cantorMass μ) x false + condProb (cantorMass μ') x false) / 2 +
           (condProb (cantorMass μ) x true + condProb (cantorMass μ') x true) / 2) * massR μ x := by
             ring
      _ = ((condProb (cantorMass μ) x false + condProb (cantorMass μ) x true +
            (condProb (cantorMass μ') x false + condProb (cantorMass μ') x true)) / 2) * massR μ
                x := by ring
      _ = ((1 + 1) / 2) * massR μ x := by rw [h1, h2]
      _ = massR μ x := by ring
  calc
    bookmakerCapital μ μ' x * massR μ x = bookmakerCapital μ μ' x *
        ((condProb (cantorMass μ) x false + condProb (cantorMass μ') x false) / 2 * massR μ x +
        (condProb (cantorMass μ) x true + condProb (cantorMass μ') x true) / 2 * massR μ x) := by
          rw [hm]
    _ = bookmakerCapital μ μ' x * ((condProb (cantorMass μ) x false + condProb (cantorMass μ') x
        false) / 2 * massR μ x) +
        bookmakerCapital μ μ' x * ((condProb (cantorMass μ) x true + condProb (cantorMass μ') x
            true) / 2 * massR μ x) := by ring

/-- **SUV p. 301.**  The game reading of Theorem 197: for every sequence where the conditional
probabilities for both measures are separated from `0` and `1` and the squares of their differences
have infinite sum, at least one of the two capitals is unbounded. -/
theorem wins_bookmaker_of_not_summable {μ μ' : Measure CantorSeq} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (hpos : ∀ x, 0 < cantorMass μ x) (hpos' : ∀ x, 0 < cantorMass μ' x)
    {w : CantorSeq} {ε : ℝ} (_hε : 0 < ε)
    (_hsep : ∀ n, ε < condOne μ (cantorPrefix w n) ∧ condOne μ (cantorPrefix w n) < 1 - ε)
    (_hsep' : ∀ n, ε < condOne μ' (cantorPrefix w n) ∧ condOne μ' (cantorPrefix w n) < 1 - ε)
    (hsum : ¬ Summable fun n =>
      (condOne μ (cantorPrefix w n) - condOne μ' (cantorPrefix w n)) ^ 2) :
    Wins (bookmakerCapital μ μ') w ∨ Wins (bookmakerCapital μ' μ) w := by
  have hwins := ssc_wins hpos hpos'
      hsum
  have h_eq :
    (fun x : BitString => ∏ i : Fin x.length,
      (condProb (cantorMass μ) (x.take i) x[i] +
        condProb (cantorMass μ') (x.take i) x[i]) /
        (2 * condProb (cantorMass μ) (x.take i) x[i])) =
    bookmakerCapital μ μ' := by rfl
  have h_eq' :
    (fun x : BitString => ∏ i : Fin x.length,
      (condProb (cantorMass μ') (x.take i) x[i] +
        condProb (cantorMass μ) (x.take i) x[i]) /
        (2 * condProb (cantorMass μ') (x.take i) x[i])) =
    bookmakerCapital μ' μ := by rfl
  rw [h_eq, h_eq'] at hwins
  exact hwins

end Kolmogorov.FrequencyGames
