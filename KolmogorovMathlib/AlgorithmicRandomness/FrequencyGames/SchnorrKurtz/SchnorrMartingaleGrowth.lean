/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz.GrowthMartingales

/-!
# Schnorr Martingale Growth

Characterizations of Schnorr randomness for a computable measure on Cantor space whose
cylinders all have positive measure.

The main results are:
* `not_isSchnorrRandom_iff_exists_growth`: a sequence is not Schnorr random iff some computable
  fair capital `m` and some computable non-decreasing unbounded `g` satisfy
  `g n ≤ m (ω_0 … ω_{n-1})` for infinitely many `n` (SUV Theorem 183);
* `isSchnorrRandom_of_isComputablyRandom`: computable randomness implies Schnorr randomness;
* `isSchnorrRandom_iff_forall_computable_bound`: Schnorr randomness expressed through computable
  upper bounds of prefix complexity (SUV Problem 270).

This formalizes the part of the book by Shen, Uspensky and Vereshchagin, "Kolmogorov complexity
and algorithmic randomness", on Schnorr randomness and martingales with a computable growth rate.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped ENNReal

/-- Step 1 of the proof of `not_isSchnorrRandom_iff_exists_growth_rtl`: construct
computable
triggers with capital bounds and a computable length threshold for the tail bound. -/
private theorem not_isSchnorrRandom_iff_exists_growth_trigger {m : BitString → ℝ}
    (hcomp : IsComputableOnStrings m) {g : ℕ → ℕ}
    (hgrowth : IsComputableGrowth g) (c : ℕ) :
    ∃ (T : ℕ → BitString → Bool) (L : ℕ → ℕ), Computable₂ T ∧ Computable L ∧
      (∀ n x, T n x = true → ((c * 2 ^ n : ℕ) : ℝ) ≤ m x) ∧
      (∀ s n x, T n x = true → L s ≤ x.length → ((c * 2 ^ (s + 1) : ℕ) : ℝ) ≤ m x) ∧
      (∀ n (w : CantorSeq), (∃ᶠ l in atTop, (g l : ℝ) ≤ m (cantorPrefix w l)) →
        ∃ l, T n (cantorPrefix w l) = true) := by
  obtain ⟨q, hq, hqerr⟩ := hcomp
  -- the error of the stage-1 approximation is at most `1/2`
  have hq1 : ∀ x : BitString, |(q (x, 1) : ℝ) - m x| ≤ 2⁻¹ := by
    intro x
    simpa using hqerr x 1
  -- the trigger: `max (g |x|) (c 2^n + 1) ≤ q(x, 1) + 1/2`
  let T : ℕ → BitString → Bool := fun n x =>
    decide (((max (g x.length) (c * 2 ^ n + 1) : ℕ) : ℚ) ≤ q (x, 1) + 1 / 2)
  have hcast : ∀ (a : ℕ) (r : ℚ), ((a : ℚ) ≤ r + 1 / 2) ↔ ((a : ℝ) ≤ (r : ℝ) + 1 / 2) := by
    intro a r
    have h : ((a : ℚ) ≤ r + 1 / 2) ↔ (((a : ℚ) : ℝ) ≤ ((r + 1 / 2 : ℚ) : ℝ)) :=
      Rat.cast_le.symm
    rw [h]
    push_cast
    try exact Iff.rfl
  have hT_iff : ∀ n x, T n x = true ↔
      ((max (g x.length) (c * 2 ^ n + 1) : ℕ) : ℝ) ≤ (q (x, 1) : ℝ) + 1 / 2 := by
    intro n x
    simp only [T, decide_eq_true_eq]
    exact hcast _ _
  have hTc : Computable₂ T := by
    have hl : Computable fun p : ℕ × BitString => p.2.length :=
      Computable.list_length.comp Computable.snd
    have hgl : Computable fun p : ℕ × BitString => g p.2.length := hgrowth.computable.comp hl
    have hpow : Computable fun p : ℕ × BitString => c * 2 ^ p.1 + 1 :=
      Computable.succ.comp
        (Computable₂.comp Primrec.nat_mul.to_comp (Computable.const c)
          (comp_pow.comp Computable.fst))
    have hθ : Computable fun p : ℕ × BitString => max (g p.2.length) (c * 2 ^ p.1 + 1) :=
      Computable₂.comp Primrec.nat_max.to_comp hgl hpow
    have hθq : Computable fun p : ℕ × BitString =>
        ((max (g p.2.length) (c * 2 ^ p.1 + 1) : ℕ) : ℚ) := computable_nat_to_rat.comp hθ
    have hqx : Computable fun p : ℕ × BitString => q (p.2, 1) :=
      hq.comp (Computable.snd.pair (Computable.const 1))
    have hrhs : Computable fun p : ℕ × BitString => q (p.2, 1) + 1 / 2 :=
      Computable₂.comp (f := fun a b : ℚ => a + b) computable₂_ratAdd hqx
        (Computable.const (1 / 2 : ℚ))
    have hdec : Computable fun p : ℕ × BitString =>
        decide (((max (g p.2.length) (c * 2 ^ p.1 + 1) : ℕ) : ℚ) ≤ q (p.2, 1) + 1 / 2) :=
      Computable₂.comp (f := fun a b : ℚ => decide (a ≤ b))
        ComputableReals.primrec_ratLe.decide.to_comp hθq hrhs
    exact hdec
  -- the length threshold: least `L` with `c 2^(s+1) < g L`
  have hunb : ∀ s : ℕ, ∃ n, c * 2 ^ (s + 1) < g n := fun s => by
    obtain ⟨n, hn⟩ := hgrowth.unbounded (c * 2 ^ (s + 1) + 1)
    exact ⟨n, by omega⟩
  have hLc : Computable fun s => Nat.find (hunb s) :=
    Computable.searchCore (P := fun s n => c * 2 ^ (s + 1) < g n) g hgrowth.computable
      (fun s => c * 2 ^ (s + 1))
      (Computable₂.comp Primrec.nat_mul.to_comp (Computable.const c)
        (comp_pow.comp Computable.succ))
      (fun s n => Iff.rfl) hunb
  refine ⟨T, fun s => Nat.find (hunb s), hTc, hLc, ?_, ?_, ?_⟩
  · -- soundness: a triggered string has `m ≥ c 2^n`
    intro n x hx
    have h1 := (hT_iff n x).mp hx
    have h2 := hq1 x
    have h3 : c * 2 ^ n + 1 ≤ max (g x.length) (c * 2 ^ n + 1) := le_max_right _ _
    generalize max (g x.length) (c * 2 ^ n + 1) = M at h1 h3
    have h3' : ((c * 2 ^ n + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast h3
    rw [abs_le] at h2
    push_cast at h3' ⊢
    linarith [h2.1, h2.2]
  · -- tail: a triggered string of length `≥ L s` has `m ≥ c 2^(s+1)`
    intro s n x hx hlen
    have h1 := (hT_iff n x).mp hx
    have h2 := hq1 x
    have hLs : c * 2 ^ (s + 1) < g (Nat.find (hunb s)) := Nat.find_spec (hunb s)
    have hmono : g (Nat.find (hunb s)) ≤ g x.length := hgrowth.monotone hlen
    have h3 : g x.length ≤ max (g x.length) (c * 2 ^ n + 1) := le_max_left _ _
    generalize max (g x.length) (c * 2 ^ n + 1) = M at h1 h3
    have h4 : c * 2 ^ (s + 1) + 1 ≤ M := by omega
    have h4' : ((c * 2 ^ (s + 1) + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast h4
    rw [abs_le] at h2
    push_cast at h4' ⊢
    linarith [h2.1, h2.2]
  · -- completeness: along `w`, a large `l` with `g l ≤ m (w|l)` triggers
    intro n w hfreq
    obtain ⟨l0, hl0⟩ := hgrowth.unbounded (c * 2 ^ n + 1)
    obtain ⟨l, hl, hgl⟩ := Filter.frequently_atTop.mp hfreq l0
    have hmono : g l0 ≤ g l := hgrowth.monotone hl
    have hmax : max (g l) (c * 2 ^ n + 1) = g l := max_eq_left (by omega)
    refine ⟨l, (hT_iff n _).mpr ?_⟩
    rw [cantorPrefix_length, hmax]
    have h2 := hq1 (cantorPrefix w l)
    rw [abs_le] at h2
    linarith [h2.1, h2.2]

/-- Step 2 of the proof of `not_isSchnorrRandom_iff_exists_growth_rtl`: select the
triggered strings with no triggered proper prefix, uniformly computably. -/
private theorem not_isSchnorrRandom_iff_exists_growth_select (T : ℕ → BitString →
    Bool) (hT : Computable₂ T) :
    ∃ S : ℕ → BitString → Bool, Computable₂ S ∧
      ∀ n x, S n x = true ↔ (T n x = true ∧ ∀ y, y <+: x → y ≠ x → T n y = false) := by
  -- the accumulator `acc n x L` says that none of the first `L` prefixes `x.take k` is triggered
  have hacc : ∀ n (x : BitString) (L : ℕ),
      (Nat.rec (motive := fun _ => Bool) true
          (fun k IH => IH && !T n (x.take k)) L) = true ↔
        ∀ k < L, T n (x.take k) = false := by
    intro n x L
    induction L with
    | zero => simp
    | succ L ih =>
      change ((Nat.rec (motive := fun _ => Bool) true
          (fun k IH => IH && !T n (x.take k)) L) && !T n (x.take L)) = true ↔ _
      rw [Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h1, h2⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact h1 k hk
        · simpa using h2
      · intro h
        refine ⟨fun k hk => h k (by omega), ?_⟩
        simpa using h L (by omega)
  refine ⟨fun n x => T n x && Nat.rec (motive := fun _ => Bool) true
      (fun k IH => IH && !T n (x.take k)) x.length, ?_, ?_⟩
  · -- computability: a `Nat.rec` iteration over the length of `x`
    have hlen : Computable fun p : ℕ × BitString => p.2.length :=
      Primrec.list_length.to_comp.comp Computable.snd
    have hstep : Computable₂ (fun (p : ℕ × BitString) (r : ℕ × Bool) =>
        r.2 && !T p.1 (p.2.take r.1)) := by
      have h1 : Computable fun v : (ℕ × BitString) × (ℕ × Bool) => v.2.2 :=
        Computable.snd.comp Computable.snd
      have h2 : Computable fun v : (ℕ × BitString) × (ℕ × Bool) => v.1.2.take v.2.1 :=
        (Primrec.list_take.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.fst)).to_comp
      have h3 : Computable fun v : (ℕ × BitString) × (ℕ × Bool) =>
          T v.1.1 (v.1.2.take v.2.1) :=
        hT.comp (Computable.fst.comp Computable.fst) h2
      exact Computable₂.comp Primrec.and.to_comp h1 (Primrec.not.to_comp.comp h3)
    have hrec := Computable.nat_rec (σ := Bool) hlen (Computable.const true) hstep
    exact Computable₂.comp Primrec.and.to_comp hT hrec
  · intro n x
    rw [Bool.and_eq_true, hacc]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h y hy hne
      have hlt : y.length < x.length :=
        lt_of_le_of_ne hy.length_le (fun h' => hne (hy.eq_of_length h'))
      have h1 := h y.length hlt
      have e : x.take y.length = y := (List.prefix_iff_eq_take.mp hy).symm
      rw [e] at h1
      exact h1
    · intro h k hk
      refine h (x.take k) (List.take_prefix k x) ?_
      intro heq
      have := congrArg List.length heq
      simp only [List.length_take] at this
      omega

/-- Step 3 of the proof of `not_isSchnorrRandom_iff_exists_growth_rtl`: Ville
bounds the sum of masses of an injectively enumerated prefix-free family with capital at least `k`.
-/
private theorem not_isSchnorrRandom_iff_exists_growth_mass {π : Measure CantorSeq}
    [IsProbabilityMeasure π] {m : BitString → ℝ}
    (hm : IsFairCapital π m) {k : ℝ} (hk : 0 < k) (F : ℕ → Option BitString)
    (hmem : ∀ i x, F i = some x → k ≤ m x)
    (hinj : ∀ i j x, F i = some x → F j = some x → i = j)
    (hpf : ∀ i j x y, F i = some x → F j = some y → x <+: y → x = y) :
    ∑' i, coverMass π (F i) ≤ ENNReal.ofReal (m [] / k) := by
  set A : ℕ → Set CantorSeq := fun i => (F i).elim ∅ cantorCylinder with hA
  have hAm : ∀ i, MeasurableSet (A i) := by
    intro i
    cases h : F i with
    | none => simp [hA, h]
    | some x => simpa [hA, h] using measurableSet_cantorCylinder x
  have hAdisj : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    cases hi : F i with
    | none => simp [Function.onFun, hA, hi]
    | some x =>
      cases hj : F j with
      | none => simp [Function.onFun, hA, hj]
      | some y =>
        simp only [Function.onFun, hA, hi, hj, Option.elim]
        apply cantorCylinder_disjoint_of_incompatible
        · intro hxy
          have hxy' := hpf i j x y hi hj hxy
          subst hxy'
          exact hij (hinj i j x hi hj)
        · intro hyx
          have hyx' := hpf j i y x hj hi hyx
          subst hyx'
          exact hij (hinj i j y hi hj)
  have hcov : ∀ i, coverMass π (F i) = π (A i) := by
    intro i
    cases h : F i <;> simp [coverMass, hA, h, cantorMass]
  have hsum : ∑' i, coverMass π (F i) = π (⋃ i, A i) := by
    rw [measure_iUnion hAdisj hAm]
    exact tsum_congr hcov
  have hsub : (⋃ i, A i) ⊆ {w | ∃ n, k ≤ m (cantorPrefix w n)} := by
    intro w hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
    cases h : F i with
    | none => simp [hA, h] at hi
    | some x =>
      simp only [hA, h, Option.elim] at hi
      refine ⟨x.length, ?_⟩
      have := (isCantorPrefix_iff_cantorPrefix_eq x w).mp hi
      rw [this]
      exact hmem i x h
  calc ∑' i, coverMass π (F i) = π (⋃ i, A i) := hsum
    _ ≤ π {w | ∃ n, k ≤ m (cantorPrefix w n)} := measure_mono hsub
    _ ≤ ENNReal.ofReal (m [] / k) := measure_exists_ge_le hm hk

/-- The numerator of the stage-`t` dyadic approximation of the mass of an optional cylinder. -/
private def growth_rtl_massApprox (a : BitString → ℕ → ℕ)
    (o : Option BitString) (t : ℕ) : ℕ :=
  o.elim 0 (fun x => a x t)

-- (A) pure computability of the rational approximants
private theorem growth_rtl_massApprox_computable
    (a : BitString → ℕ → ℕ) (F : ℕ → ℕ → Option BitString) (B : ℕ → ℕ)
    (ha : Computable₂ a) (hF : Computable₂ F) (hB : Computable B) :
    Computable fun p : ℕ × ℕ =>
      ((∑ i ∈ Finset.range (B p.2), growth_rtl_massApprox a
          (F p.1 i) (p.2 + 1 + B p.2) : ℕ) : ℚ) /
        2 ^ (p.2 + 1 + B p.2) := by
  have hs1 : Computable fun p : ℕ × ℕ => p.2 + 1 :=
    Computable₂.comp Primrec.nat_add.to_comp Computable.snd (Computable.const 1)
  have hL : Computable fun p : ℕ × ℕ => B p.2 := hB.comp Computable.snd
  have hs' : Computable fun p : ℕ × ℕ => p.2 + 1 + B p.2 :=
    Computable₂.comp Primrec.nat_add.to_comp hs1 hL
  have hterm : Computable fun q : (ℕ × ℕ) × (ℕ × ℕ) =>
      growth_rtl_massApprox a (F q.1.1 q.2.1) (q.1.2 + 1 +
          B q.1.2) := by
    have ho : Computable fun q : (ℕ × ℕ) × (ℕ × ℕ) => F q.1.1 q.2.1 :=
      Computable₂.comp hF (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd)
    have hst : Computable fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.1.2 + 1 + B q.1.2 :=
      hs'.comp Computable.fst
    have hg : Computable₂ fun (q : (ℕ × ℕ) × (ℕ × ℕ)) (x : BitString) =>
        a x (q.1.2 + 1 + B q.1.2) :=
      Computable₂.comp ha Computable.snd (hst.comp Computable.fst)
    have hcases := Computable.option_casesOn (σ := ℕ) ho (Computable.const 0) hg
    refine hcases.of_eq fun q => ?_
    cases F q.1.1 q.2.1 <;> rfl
  have hsum : Computable fun p : ℕ × ℕ =>
      ∑ i ∈ Finset.range (B p.2), growth_rtl_massApprox a
          (F p.1 i) (p.2 + 1 + B p.2) := by
    have hrec := Computable.nat_rec (σ := ℕ) hL (Computable.const 0)
      (h := fun (p : ℕ × ℕ) (r : ℕ × ℕ) =>
        r.2 + growth_rtl_massApprox a (F p.1 r.1) (p.2 + 1 + B p.2))
      (Computable₂.comp Primrec.nat_add.to_comp (Computable.snd.comp Computable.snd) hterm)
    refine hrec.of_eq fun p => ?_
    have key : ∀ (S L : ℕ), Nat.rec (motive := fun _ => ℕ) 0
        (fun y IH => (y, IH).2 + growth_rtl_massApprox a
                       (F p.1 (y, IH).1) S) L
        = ∑ i ∈ Finset.range L, growth_rtl_massApprox a
            (F p.1 i) S := by
      intro S L
      induction L with
      | zero => simp
      | succ k ih => simp [Finset.sum_range_succ, ih]
    exact key _ _
  have hnum : Computable fun p : ℕ × ℕ =>
      ((∑ i ∈ Finset.range (B p.2), growth_rtl_massApprox a
          (F p.1 i) (p.2 + 1 + B p.2) : ℕ) : ℤ) :=
    ComputableReals.primrec_natCastInt.to_comp.comp hsum
  have hden : Computable fun p : ℕ × ℕ => 2 ^ (p.2 + 1 + B p.2) := comp_pow.comp hs'
  refine computable_of_num_den hnum hden (fun p => by positivity) (fun p => ?_)
  push_cast
  rfl

-- (B) pieces
/-- The real value of a finite dyadic mass. -/
private theorem not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_toReal (m t : ℕ) :
    (dyadicValue m t).toReal = (m : ℝ) / 2 ^ t := by
  unfold dyadicValue
  rw [ENNReal.toReal_div, ENNReal.toReal_pow]
  simp

/-- A dyadic mass is finite. -/
private theorem not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_ne_top (m t : ℕ) :
    dyadicValue m t ≠ ⊤ := by
  unfold dyadicValue
  exact (ENNReal.div_lt_top (by simp) (by simp)).ne

/-- The dyadic approximation of a cylinder mass has the prescribed real error. -/
private theorem growth_rtl_massApprox_error
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (a : BitString → ℕ → ℕ)
    (ha : ∀ y s, dyadicValue (a y s) s ≤ cantorMass π y + dyadicValue 1 s ∧
      cantorMass π y ≤ dyadicValue (a y s) s + dyadicValue 1 s)
    (y : BitString) (t : ℕ) :
    |(a y t : ℝ) / 2 ^ t - (cantorMass π y).toReal| ≤ (2 : ℝ)⁻¹ ^ t := by
  have hfin : cantorMass π y ≠ ⊤ := measure_ne_top π _
  have hd : dyadicValue 1 t ≠ ⊤ := not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_ne_top 1 t
  have hd' : dyadicValue (a y t) t ≠ ⊤ :=
      not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_ne_top _ t
  obtain ⟨h1, h2⟩ := ha y t
  have h1' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin, hd⟩) h1
  have h2' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hd', hd⟩) h2
  rw [ENNReal.toReal_add hfin hd, not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_toReal,
      not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_toReal] at h1'
  rw [ENNReal.toReal_add hd' hd, not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_toReal,
      not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_toReal] at h2'
  have h3 : (2 : ℝ)⁻¹ ^ t = 1 / 2 ^ t := by rw [inv_pow, one_div]
  rw [h3, abs_le]
  simp only [Nat.cast_one] at h1' h2'
  constructor <;> linarith

/-- The same error estimate holds for an optional cylinder. -/
private theorem growth_rtl_massApprox_option_error
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (a : BitString → ℕ → ℕ)
    (ha : ∀ y s, dyadicValue (a y s) s ≤ cantorMass π y + dyadicValue 1 s ∧
      cantorMass π y ≤ dyadicValue (a y s) s + dyadicValue 1 s)
    (o : Option BitString) (t : ℕ) :
    |(growth_rtl_massApprox a o t : ℝ) / 2 ^ t -
        (coverMass π o).toReal| ≤ (2 : ℝ)⁻¹ ^ t := by
  cases o with
  | none =>
    have h0 : (growth_rtl_massApprox a none t : ℝ) / 2 ^ t -
        (coverMass π none).toReal = 0 := by
      simp [growth_rtl_massApprox, coverMass]
    rw [h0, abs_zero]
    positivity
  | some y => exact growth_rtl_massApprox_error a ha y t

/-- Every optional cylinder has finite mass for a probability measure. -/
private theorem not_isSchnorrRandom_iff_exists_growth_rtl_coverMass_ne_top
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (o : Option BitString) : coverMass π o ≠ ⊤ := by
  cases o with
  | none => simp [coverMass]
  | some y => exact measure_ne_top π _

/-- Increasing precision by the number of summands bounds the total error. -/
private theorem not_isSchnorrRandom_iff_exists_growth_rtl_finite_sum_error_bound (s L : ℕ) :
    (L : ℝ) * (2 : ℝ)⁻¹ ^ (s + 1 + L) ≤ (2 : ℝ)⁻¹ ^ (s + 1) := by
  have h : (L : ℝ) ≤ 2 ^ L := by exact_mod_cast (Nat.lt_two_pow_self (n := L)).le
  have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (s + 1) := by positivity
  have h1 : (L : ℝ) * (2 : ℝ)⁻¹ ^ L ≤ 1 := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact h
  calc (L : ℝ) * (2 : ℝ)⁻¹ ^ (s + 1 + L)
      = (2 : ℝ)⁻¹ ^ (s + 1) * ((L : ℝ) * (2 : ℝ)⁻¹ ^ L) := by rw [pow_add]; ring
    _ ≤ (2 : ℝ)⁻¹ ^ (s + 1) * 1 := mul_le_mul_of_nonneg_left h1 hpos.le
    _ = _ := mul_one _

/-- The error of a finite dyadic approximation plus the uniformly small tail. -/
private theorem not_isSchnorrRandom_iff_exists_growth_rtl_coverMass_sum_error
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (a : BitString → ℕ → ℕ)
    (ha : ∀ y s, dyadicValue (a y s) s ≤ cantorMass π y + dyadicValue 1 s ∧
      cantorMass π y ≤ dyadicValue (a y s) s + dyadicValue 1 s)
    (F : ℕ → ℕ → Option BitString) (B : ℕ → ℕ)
    (htail : ∀ n s, ∑' j, coverMass π (F n (B s + j)) ≤ dyadicValue 1 (s + 1)) (n s : ℕ) :
    |((((∑ i ∈ Finset.range (B s), growth_rtl_massApprox a (F n
        i) (s + 1 + B s) : ℕ) : ℚ) /
        2 ^ (s + 1 + B s) : ℚ) : ℝ) -
      (∑' i, coverMass π (F n i)).toReal| ≤ (2 : ℝ)⁻¹ ^ s := by
  obtain ⟨L, hLdef⟩ : ∃ L, L = B s := ⟨_, rfl⟩
  rw [← hLdef]
  obtain ⟨t, htdef⟩ : ∃ t, t = s + 1 + L := ⟨_, rfl⟩
  rw [← htdef]
  have hpfin : ∀ i, coverMass π (F n i) ≠ ⊤ :=
      fun i => not_isSchnorrRandom_iff_exists_growth_rtl_coverMass_ne_top _
  have hsplit : ∑' i, coverMass π (F n i) =
      ∑ i ∈ Finset.range L, coverMass π (F n i) +
        ∑' i, coverMass π (F n (i + L)) := by
    have := Summable.sum_add_tsum_nat_add' (f := fun i => coverMass π (F n i))
      (k := L) ENNReal.summable
    exact this.symm
  have htail' : ∑' i, coverMass π (F n (i + L)) ≤ dyadicValue 1 (s + 1) := by
    have h := htail n s
    rw [← hLdef] at h
    calc ∑' i, coverMass π (F n (i + L)) = ∑' j, coverMass π (F n (L + j)) :=
          tsum_congr fun i => by rw [Nat.add_comm]
      _ ≤ _ := h
  have hhead_fin : ∑ i ∈ Finset.range L, coverMass π (F n i) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => hpfin i)
  have htail_fin : ∑' i, coverMass π (F n (i + L)) ≠ ⊤ :=
    ne_top_of_le_ne_top (not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_ne_top 1 (s + 1))
        htail'
  have hS : (∑' i, coverMass π (F n i)).toReal =
      (∑ i ∈ Finset.range L, (coverMass π (F n i)).toReal) +
        (∑' i, coverMass π (F n (i + L))).toReal := by
    rw [hsplit, ENNReal.toReal_add hhead_fin htail_fin,
      ENNReal.toReal_sum (fun i _ => hpfin i)]
  have htail_real : (∑' i, coverMass π (F n (i + L))).toReal ≤ (2 : ℝ)⁻¹ ^ (s + 1) := by
    have := ENNReal.toReal_mono (not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_ne_top 1
        (s + 1)) htail'
    rw [not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_toReal] at this
    simpa [inv_pow] using this
  have htail_nonneg : 0 ≤ (∑' i, coverMass π (F n (i + L))).toReal :=
    ENNReal.toReal_nonneg
  have hhead : |(∑ i ∈ Finset.range L, (growth_rtl_massApprox a
      (F n i) t : ℝ) / 2 ^ t) -
      ∑ i ∈ Finset.range L, (coverMass π (F n i)).toReal| ≤ (2 : ℝ)⁻¹ ^ (s + 1) := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ i ∈ Finset.range L,
          |(growth_rtl_massApprox a (F n i) t : ℝ) / 2 ^ t -
              (coverMass π (F n i)).toReal| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range L, (2 : ℝ)⁻¹ ^ t :=
          Finset.sum_le_sum fun i _ =>
            growth_rtl_massApprox_option_error a ha _ t
      _ = L * (2 : ℝ)⁻¹ ^ t := by simp
      _ ≤ _ := by rw [htdef]; exact
                    not_isSchnorrRandom_iff_exists_growth_rtl_finite_sum_error_bound s L
  have hq : ((((∑ i ∈ Finset.range L, growth_rtl_massApprox a
      (F n i) t : ℕ) : ℚ) / 2 ^ t : ℚ) : ℝ) =
      ∑ i ∈ Finset.range L, (growth_rtl_massApprox a (F n i) t
          : ℝ) / 2 ^ t := by
    push_cast
    rw [Finset.sum_div]
  rw [hq, hS]
  have h2 : (2 : ℝ)⁻¹ ^ s = (2 : ℝ)⁻¹ ^ (s + 1) + (2 : ℝ)⁻¹ ^ (s + 1) := by
    rw [pow_succ]; ring
  rw [h2]
  rw [abs_le] at hhead ⊢
  constructor <;> linarith [hhead.1, hhead.2]

/-- Step 4 of the proof of `not_isSchnorrRandom_iff_exists_growth_rtl`: a series of
cylinder masses with a computable uniform tail bound is a computable real sequence. -/
private theorem not_isSchnorrRandom_iff_exists_growth_computable_sum
    {π : Measure CantorSeq} [IsProbabilityMeasure π] (hπ : IsComputableMeasure π)
    (F : ℕ → ℕ → Option BitString) (hF : Computable₂ F) (B : ℕ → ℕ) (hB : Computable B)
    (htail : ∀ n s, ∑' j, coverMass π (F n (B s + j)) ≤ dyadicValue 1 (s + 1)) :
    IsComputableRealSeq fun n => (∑' i, coverMass π (F n i)).toReal := by
  obtain ⟨a, ha_comp, ha⟩ := hπ
  refine ⟨fun p => ((∑ i ∈ Finset.range (B p.2),
      growth_rtl_massApprox a (F p.1 i) (p.2 + 1 + B p.2) :
          ℕ) : ℚ) / 2 ^ (p.2 + 1 + B p.2), ?_, ?_⟩
  · exact growth_rtl_massApprox_computable a F B ha_comp hF hB
  · intro n s
    exact not_isSchnorrRandom_iff_exists_growth_rtl_coverMass_sum_error (π := π) a ha F B
        htail n s

/-- Step 2 of the proof of `not_isSchnorrRandom_iff_exists_growth`: the reverse direction,
showing that such a martingale and growth function imply the sequence is not Schnorr random. -/
private theorem not_isSchnorrRandom_iff_exists_growth_rtl {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (w : CantorSeq) :
    (∃ m g, IsFairCapital π m ∧ IsComputableOnStrings m ∧
      IsComputableGrowth g ∧ ∃ᶠ n in atTop, (g n : ℝ) ≤ m (cantorPrefix w n)) →
        ¬ IsSchnorrRandom π w := by
  rintro ⟨m, g, hfair, hcomp, hgrowth, hfreq⟩ hschnorr
  apply hschnorr
  obtain ⟨c, hc, hinit⟩ : ∃ c : ℕ, 0 < c ∧ m [] ≤ c :=
    ⟨⌈m []⌉₊ + 1, Nat.succ_pos _, by have := Nat.le_ceil (m []); push_cast; linarith⟩
  obtain ⟨T, L, hTc, hLc, hT1, hT2, hT3⟩ :=
      not_isSchnorrRandom_iff_exists_growth_trigger hcomp hgrowth c
  obtain ⟨S, hSc, hS⟩ := not_isSchnorrRandom_iff_exists_growth_select T hTc
  let f : ℕ → ℕ → Option BitString := fun n i =>
    cond (S n (natToBitString i)) (some (natToBitString i)) none
  have hf_some : ∀ n i x, f n i = some x → x = natToBitString i ∧ S n x = true := by
    intro n i x h
    by_cases hs : S n (natToBitString i) = true
    · simp only [f, hs, Bool.cond_true, Option.some.injEq] at h
      subst h
      exact ⟨rfl, hs⟩
    · simp [f, hs] at h
  have hville : ∀ n a (k : ℝ), 0 < k → (∀ i, a ≤ i → ∀ x, f n i = some x → k ≤ m x) →
      ∑' j, coverMass π (f n (a + j)) ≤ ENNReal.ofReal (m [] / k) := by
    intro n a k hk hmem
    refine not_isSchnorrRandom_iff_exists_growth_mass hfair hk
        (fun j => f n (a + j))
      (fun j x hj => hmem (a + j) (Nat.le_add_right a j) x hj) ?_ ?_
    · intro i j x hi hj
      have h1 := (hf_some n (a + i) x hi).1.symm.trans (hf_some n (a + j) x hj).1
      exact Nat.add_left_cancel (natToBitString_injective h1)
    · intro i j x y hi hj hxy
      obtain ⟨hx, hSx⟩ := hf_some n _ x hi
      obtain ⟨hy, hSy⟩ := hf_some n _ y hj
      by_contra hne
      have h1 := ((hS n y).mp hSy).2 x hxy hne
      have h2 := ((hS n x).mp hSx).1
      rw [h1] at h2
      exact Bool.false_ne_true h2
  have hf_trig : ∀ n i x, f n i = some x → T n x = true :=
    fun n i x h => ((hS n x).mp (hf_some n i x h).2).1
  have hnat : Computable fun p : ℕ × ℕ => natToBitString p.2 :=
    computable_natToBitString.comp Computable.snd
  have hfc : Computable₂ f :=
    Computable.cond (Computable₂.comp hSc Computable.fst hnat)
      (Computable.option_some.comp hnat) (Computable.const none)
  -- Ville numerics: `m(Λ) / (c 2^n) ≤ 2^{-n}`
  have hnum : ∀ n : ℕ, ENNReal.ofReal (m [] / ((c * 2 ^ n : ℕ) : ℝ)) ≤ dyadicValue 1 n := by
    intro n
    have hK : (0 : ℝ) < ((c * 2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos hc (by positivity)
    have h1 : m [] / ((c * 2 ^ n : ℕ) : ℝ) ≤ (2 : ℝ)⁻¹ ^ n := by
      rw [div_le_iff₀ hK]
      have h2 : (2 : ℝ)⁻¹ ^ n * ((c * 2 ^ n : ℕ) : ℝ) = c := by
        push_cast
        rw [inv_pow]
        field_simp
      rw [h2]
      exact hinit
    have h3 : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n) = (2 : ENNReal)⁻¹ ^ n := by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
      simp
    refine (ENNReal.ofReal_le_ofReal h1).trans ?_
    rw [h3]
    unfold dyadicValue
    rw [Nat.cast_one, div_eq_mul_inv, one_mul]
    exact ENNReal.inv_pow.symm.le
  -- length of the `i`-th string
  have hlen : ∀ L i : ℕ, 2 ^ L ≤ i → L ≤ (natToBitString i).length := by
    intro L i hi
    have h1 : L < Nat.size (i + 1) := Nat.lt_size.mpr (by omega)
    have h2 : (natToBitString i).length = Nat.size (i + 1) - 1 := by
      rw [natToBitString, List.length_dropLast, Nat.size_eq_bits_len]
    omega
  refine ⟨f, hfc, ?_, ?_, ?_⟩
  · -- cover: the shortest triggered prefix of `w` is selected
    intro n v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    classical
    have hex : ∃ l, T n (cantorPrefix v l) = true := hT3 n v hfreq
    have hl : T n (cantorPrefix v (Nat.find hex)) = true := Nat.find_spec hex
    have hmin : ∀ k < Nat.find hex, T n (cantorPrefix v k) = false := fun k hk => by
      simpa using Nat.find_min hex hk
    have hSx : S n (cantorPrefix v (Nat.find hex)) = true := by
      rw [hS]
      refine ⟨hl, fun y hy hne => ?_⟩
      have hlen_le : y.length ≤ Nat.find hex := by
        simpa using hy.length_le
      have hlt : y.length < Nat.find hex := by
        rcases lt_or_eq_of_le hlen_le with h | h
        · exact h
        · exact absurd (hy.eq_of_length (by simpa using h)) hne
      have hy' : y = cantorPrefix v y.length := by
        have := List.prefix_iff_eq_take.mp hy
        rw [this, cantorPrefix_take v y.length (Nat.find hex) hlen_le]
        simp
      rw [hy']
      exact hmin _ hlt
    refine Set.mem_iUnion.mpr ⟨bitStringToNat (cantorPrefix v (Nat.find hex)), ?_⟩
    have hfx : f n (bitStringToNat (cantorPrefix v (Nat.find hex))) =
        some (cantorPrefix v (Nat.find hex)) := by
      simp [f, hSx]
    rw [hfx]
    change v ∈ cantorCylinder (cantorPrefix v (Nat.find hex))
    exact (isCantorPrefix_iff_cantorPrefix_eq _ v).mpr (by simp)
  · -- mass: Ville at level `c 2^n`
    intro n
    have hk : (0 : ℝ) < ((c * 2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos hc (by positivity)
    have h := hville n 0 ((c * 2 ^ n : ℕ) : ℝ) hk
      (fun i _ x hx => hT1 n x (hf_trig n i x hx))
    simp only [zero_add] at h
    exact h.trans (hnum n)
  · -- computable real sequence: the tail beyond index `2 ^ L s` has length `≥ L s`
    refine not_isSchnorrRandom_iff_exists_growth_computable_sum hπ f hfc
        (fun s => 2 ^ L s) (comp_pow.comp hLc) ?_
    intro n s
    have hk : (0 : ℝ) < ((c * 2 ^ (s + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos hc (by positivity)
    have h := hville n (2 ^ L s) ((c * 2 ^ (s + 1) : ℕ) : ℝ) hk (fun i hi x hx => by
      obtain ⟨hx1, _⟩ := hf_some n i x hx
      exact hT2 s n x (hf_trig n i x hx) (by rw [hx1]; exact hlen _ _ hi))
    exact h.trans (hnum (s + 1))

/-- **SUV Theorem 183, p. 282 (Schnorr).**  Let `π` be computable with all intervals of positive
measure.  A sequence `ω` is not Schnorr random exactly when there are a computable `π`-martingale
`m` and a computable non-decreasing unbounded `g` with `m(ω_0 … ω_{n-1}) ≥ g(n)` for infinitely many
`n`. -/
theorem not_isSchnorrRandom_iff_exists_growth {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) (w : CantorSeq) :
    ¬ IsSchnorrRandom π w ↔ ∃ m g, IsFairCapital π m ∧ IsComputableOnStrings m ∧
      IsComputableGrowth g ∧ ∃ᶠ n in atTop, (g n : ℝ) ≤ m (cantorPrefix w n) := by
  exact ⟨not_isSchnorrRandom_iff_exists_growth_ltr hπ hpos w,
      not_isSchnorrRandom_iff_exists_growth_rtl hπ w⟩

/-- **SUV p. 282, after Theorem 183.**  A computably random sequence is Schnorr random. -/
theorem isSchnorrRandom_of_isComputablyRandom {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) {w : CantorSeq}
    (hw : IsComputablyRandom π w) : IsSchnorrRandom π w := by
  intro h_not_schnorr
  have h_not : ¬IsSchnorrRandom π w := by
    change ¬ ¬ IsSchnorrNull π {w}
    intro h_not_not
    exact h_not_not h_not_schnorr
  have ⟨m, g, h_fair, h_comp, h_growth, h_freq⟩ := (not_isSchnorrRandom_iff_exists_growth hπ hpos
      w).mp h_not
  have hwins : Wins m w := by
    intro hbdd
    obtain ⟨B, hB⟩ := hbdd
    have hbdd2 : ∀ n, m (cantorPrefix w n) ≤ B := fun n => hB (Set.mem_range_self n)
    obtain ⟨B_nat, hB_nat⟩ := exists_nat_gt B
    have ⟨n0, hn0⟩ := h_growth.unbounded B_nat
    have h_freq2 : ∃ n ≥ n0, (g n : ℝ) ≤ m (cantorPrefix w n) := by
      exact Filter.frequently_atTop.mp h_freq n0
    obtain ⟨n, hn_ge, hn_le⟩ := h_freq2
    have h1 : (B_nat : ℝ) ≤ (g n0 : ℝ) := by exact Nat.cast_le.mpr hn0
    have h2 : (g n0 : ℝ) ≤ (g n : ℝ) := by exact Nat.cast_le.mpr (h_growth.monotone hn_ge)
    have h3 : (B_nat : ℝ) ≤ m (cantorPrefix w n) := le_trans (le_trans h1 h2) hn_le
    have h4 : m (cantorPrefix w n) ≤ B := hbdd2 n
    have h5 : (B_nat : ℝ) ≤ B := le_trans h3 h4
    have h6 : B < (B_nat : ℝ) := hB_nat
    exact lt_irrefl _ (lt_of_le_of_lt h5 h6)
  have h_not_wins : ¬ Wins m w := hw m h_fair h_comp
  exact h_not_wins hwins

/-- Step 1 of the proof of `isSchnorrRandom_iff_forall_computable_bound_ltr`:
negation implies small mass -/
private lemma isSchnorrRandom_iff_forall_computable_bound_n
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ]
    (hpos : ∀ x, 0 < cantorMass μ x) (w : CantorSeq) (k : BitString → ℕ) (h : ℕ → ℕ) :
    (¬ ∃ c : ℝ, ∀ n : ℕ, -Real.logb 2 (massR μ (cantorPrefix w n)) - h n - c ≤ k (cantorPrefix w n))
        →
    ∀ m : ℕ, ∃ n : ℕ, cantorMass μ (cantorPrefix w n) < dyadicValue 1 (k (cantorPrefix w n) +
        h (cantorPrefix w n).length + m + 1) := by
  intro h_not m
  push Not at h_not
  obtain ⟨n, hn⟩ := h_not (m + 1)
  use n
  have h1 : ((k (cantorPrefix w n) : ℝ) + (h n : ℝ) + (m : ℝ) + 1) < - Real.logb 2
      (massR μ (cantorPrefix w n)) := by linarith
  have h2 : (massR μ (cantorPrefix w n)) < (2 : ℝ) ^ (- ((k (cantorPrefix w n) : ℝ) + (h n : ℝ) +
      (m : ℝ) + 1)) := by
    have hp := hpos (cantorPrefix w n)
    have hp_real : 0 < massR μ (cantorPrefix w n) := by
      exact ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top μ _)
    have hl1 : Real.logb 2 (massR μ (cantorPrefix w n)) < - ((k (cantorPrefix w n) : ℝ) + (h n : ℝ)
        + (m : ℝ) + 1) := by linarith
    have h_rpow_mono := Real.rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) hl1
    have h_rpow_logb : (2 : ℝ) ^ Real.logb 2 (massR μ (cantorPrefix w n)) =
        (massR μ (cantorPrefix w n)) := by
      apply Real.rpow_logb (by norm_num) (by norm_num) hp_real
    rw [h_rpow_logb] at h_rpow_mono
    exact h_rpow_mono
  have h3 : cantorMass μ (cantorPrefix w n) < ENNReal.ofReal
      ((2 : ℝ) ^ (- ((k (cantorPrefix w n) : ℝ) + (h (cantorPrefix w n).length : ℝ) + (m : ℝ) + 1)))
      := by
    have h_massR_def : massR μ (cantorPrefix w n) = (cantorMass μ (cantorPrefix w n)).toReal := rfl
    have h_ennreal_eq : ENNReal.ofReal (massR μ (cantorPrefix w n)) = cantorMass μ
        (cantorPrefix w n) := by
      rw [h_massR_def]
      exact ENNReal.ofReal_toReal (measure_ne_top μ _)
    rw [← h_ennreal_eq]
    rw [cantorPrefix_length]
    rw [ENNReal.ofReal_lt_ofReal_iff]
    · exact h2
    · positivity
  rw [dyadicValue_one_eq_inv_two_pow']
  have h4 : ENNReal.ofReal ((2 : ℝ) ^ (- ((k (cantorPrefix w n) : ℝ) + (h (cantorPrefix w n).length
      : ℝ) + (m : ℝ) + 1))) = (2 : ENNReal)⁻¹ ^ (k (cantorPrefix w n) + h (cantorPrefix w n).length
      + m + 1) := by
    rw [Real.rpow_neg (by norm_num)]
    have h_pow : (2 : ℝ) ^ ((k (cantorPrefix w n) : ℝ) + (h (cantorPrefix w n).length : ℝ) + (m : ℝ)
        + 1) = (2 : ℝ) ^ ((k (cantorPrefix w n) + h (cantorPrefix w n).length + m + 1 : ℕ) : ℝ) :=
        by
      push_cast
      rfl
    rw [h_pow]
    rw [Real.rpow_natCast]
    rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    rw [ENNReal.ofReal_pow (by norm_num)]
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    rw [ENNReal.inv_pow]
  rwa [h4] at h3


private lemma isSchnorrRandom_iff_forall_computable_bound_Bm_computable
    (a : BitString → ℕ → ℕ) (ha : Computable₂ a)
    (k : BitString → ℕ) (hk : Computable k) (h : ℕ → ℕ) (hh : Computable h) :
    Computable₂ (fun (m : ℕ) (x : BitString) => decide (a x (k x + h x.length + m + 2) ≤ 3)) := by
  have hs1 : Computable₂ fun (m : ℕ) (x : BitString) => x := Computable.snd
  have hs2 : Computable₂ fun (m : ℕ) (x : BitString) => k x := hk.comp hs1
  have hs3 : Computable₂ fun (m : ℕ) (x : BitString) => h x.length :=
    hh.comp (Computable.list_length.comp hs1)
  have hs4 : Computable₂ fun (m : ℕ) (x : BitString) => m := Computable.fst
  have hs5 : Computable₂ fun (m : ℕ) (x : BitString) => k x + h x.length + m + 2 :=
    (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp hs2
        hs3) hs4) (Computable.const 2))
  have hs6 : Computable₂ fun (m : ℕ) (x : BitString) => a x (k x + h x.length + m + 2) :=
    ha.comp hs1 hs5
  exact (PrimrecRel.decide Primrec.nat_le).to_comp.comp hs6 (Computable.const 3)

private lemma isSchnorrRandom_iff_forall_computable_bound_Bm_lower
    {μ : Measure CantorSeq}
    (k : BitString → ℕ) (h : ℕ → ℕ)
    (a : BitString → ℕ → ℕ)
    (h_lower : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s)
    (m : ℕ) (x : BitString) :
    cantorMass μ x ≤ dyadicValue 1 (k x + h x.length + m + 1) → a x (k x + h x.length + m + 2) ≤
        3 := by
  intro h_le
  let s := k x + h x.length + m + 2
  have h1 : dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s := h_lower x s
  have h2 : cantorMass μ x + dyadicValue 1 s ≤ dyadicValue 1 (k x + h x.length + m + 1) +
      dyadicValue 1 s := by gcongr
  have h3 : dyadicValue 1 (k x + h x.length + m + 1) = dyadicValue 2 s := by
    unfold dyadicValue
    have h_pow : (2 : ℝ≥0∞) ^ s = (2 : ℝ≥0∞) ^ (k x + h x.length + m + 1) * 2 := by
      change (2 : ℝ≥0∞) ^ (k x + h x.length + m + 1 + 1) = _
      rw [pow_add]
      congr
      norm_num
    rw [h_pow]
    have h_two_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have h_two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    rw [mul_comm]
    have h_rw : ((2 : ℕ) : ℝ≥0∞) = 2 * 1 := by norm_num
    have h_rw2 : ((1 : ℕ) : ℝ≥0∞) = 1 := by norm_num
    rw [h_rw, h_rw2]
    exact (ENNReal.mul_div_mul_left 1 _ h_two_ne_zero h_two_ne_top).symm
  have h4 : dyadicValue 1 (k x + h x.length + m + 1) + dyadicValue 1 s = dyadicValue 3 s := by
    rw [h3]
    unfold dyadicValue
    rw [← ENNReal.add_div]
    congr
    norm_cast
  have h5 : dyadicValue (a x s) s ≤ dyadicValue 3 s := le_trans h1 (le_trans h2 (le_of_eq h4))
  unfold dyadicValue at h5
  have h_mul : ((a x s : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s * (2 : ℝ≥0∞) ^ s ≤ ((3 : ℕ) : ℝ≥0∞) /
      (2 : ℝ≥0∞) ^ s * (2 : ℝ≥0∞) ^ s := by gcongr
  have h_ne_zero : (2 : ℝ≥0∞) ^ s ≠ 0 := by
    apply ENNReal.pow_ne_zero
    norm_num
  have h_ne_top : (2 : ℝ≥0∞) ^ s ≠ ⊤ := by
    apply ENNReal.pow_ne_top
    exact ENNReal.coe_ne_top
  have h_canc : ∀ n : ℕ, (n : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s * (2 : ℝ≥0∞) ^ s = n := by
    intro n
    rw [ENNReal.div_mul_cancel h_ne_zero h_ne_top]
  rw [h_canc (a x s), h_canc 3] at h_mul
  exact_mod_cast h_mul

private lemma isSchnorrRandom_iff_forall_computable_bound_Bm_upper
    {μ : Measure CantorSeq}
    (k : BitString → ℕ) (h : ℕ → ℕ)
    (a : BitString → ℕ → ℕ)
    (h_upper : ∀ x s, cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (m : ℕ) (x : BitString) :
    (a x (k x + h x.length + m + 2) ≤ 3) → cantorMass μ x ≤ dyadicValue 1 (k x + h x.length + m) :=
        by
  intro h_le
  let s := k x + h x.length + m + 2
  have h1 : cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s := h_upper x s
  have h2 : dyadicValue (a x s) s ≤ dyadicValue 3 s := by
    unfold dyadicValue
    have h_le_cast : ((a x s : ℝ≥0∞) : ℝ≥0∞) ≤ ((3 : ℝ≥0∞) : ℝ≥0∞) := by exact_mod_cast h_le
    gcongr
  have h3 : dyadicValue (a x s) s + dyadicValue 1 s ≤ dyadicValue 3 s + dyadicValue 1 s := by gcongr
  have h4 : dyadicValue 3 s + dyadicValue 1 s = dyadicValue 4 s := by
    unfold dyadicValue
    rw [← ENNReal.add_div]
    congr
    norm_cast
  have h5 : dyadicValue 4 s = dyadicValue 1 (k x + h x.length + m) := by
    unfold dyadicValue
    have h_pow : (2 : ℝ≥0∞) ^ s = (2 : ℝ≥0∞) ^ (k x + h x.length + m) * 4 := by
      change (2 : ℝ≥0∞) ^ (k x + h x.length + m + 2) = _
      rw [pow_add]
      congr
      norm_num
    rw [h_pow]
    have h_four_ne_zero : (4 : ℝ≥0∞) ≠ 0 := by norm_num
    have h_four_ne_top : (4 : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    rw [mul_comm]
    have h_rw : ((4 : ℕ) : ℝ≥0∞) = 4 * 1 := by norm_num
    have h_rw2 : ((1 : ℕ) : ℝ≥0∞) = 1 := by norm_num
    rw [h_rw, h_rw2]
    exact ENNReal.mul_div_mul_left 1 _ h_four_ne_zero h_four_ne_top
  exact le_trans h1 (le_trans h3 (by rw [h4, h5]))

/-- Step 2 of the proof of `isSchnorrRandom_iff_forall_computable_bound_ltr`: set
B_m and coverage -/
private lemma isSchnorrRandom_iff_forall_computable_bound_Bm
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ)
    (k : BitString → ℕ) (hk : Computable k) (h : ℕ → ℕ) (hh : IsComputableGrowth h) :
    ∃ B : ℕ → BitString → Bool, Computable₂ B ∧
      (∀ m x, B m x = true → cantorMass μ x ≤ dyadicValue 1 (k x + h x.length + m)) ∧
      (∀ m x, cantorMass μ x ≤ dyadicValue 1 (k x + h x.length + m + 1) → B m x = true) := by
  rcases hμ with ⟨a, h_comp_a, h_bounds⟩
  let B := fun m x => decide (a x (k x + h x.length + m + 2) ≤ 3)
  use B
  refine ⟨?_, ?_, ?_⟩
  · exact isSchnorrRandom_iff_forall_computable_bound_Bm_computable a h_comp_a k hk
      h hh.computable
  · intro m x hB
    have h_le : a x (k x + h x.length + m + 2) ≤ 3 := decide_eq_true_iff.mp hB
    exact isSchnorrRandom_iff_forall_computable_bound_Bm_upper k h a
        (fun x s => (h_bounds x s).2) m x h_le
  · intro m x h_le
    have h_le_a : a x (k x + h x.length + m + 2) ≤ 3 :=
      isSchnorrRandom_iff_forall_computable_bound_Bm_lower k h a
          (fun x s => (h_bounds x s).1) m x h_le
    exact decide_eq_true_iff.mpr h_le_a

/-- Step 3 of the proof of `isSchnorrRandom_iff_forall_computable_bound_ltr`: Kraft
bounds -/
private lemma isSchnorrRandom_iff_forall_computable_bound_kraft
    (U : Map) (hU : IsOptimalPrefixConditional U)
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ]
    (k : BitString → ℕ) (h : ℕ → ℕ) (hh : IsComputableGrowth h)
    (c_0 : ℕ) (hk_bound : ∀ x, KPPlain U x ≤ ((k x + c_0 : ℕ) : ℕ∞))
    (B : ℕ → BitString → Bool)
    (hB_upper : ∀ m x, B m x = true → cantorMass μ x ≤ dyadicValue 1 (k x + h x.length + m)) :
    (∀ m, ∑' x : {x // B (m + c_0) x = true}, cantorMass μ x ≤ dyadicValue 1 m) ∧
    (∀ m N, ∑' x : {x // B (m + c_0) x = true ∧ (x : BitString).length ≥ N}, cantorMass μ x ≤
        dyadicValue 1 (m + h N)) := by
  have h_dv (s : ℕ) : dyadicValue 1 s = (2 : ENNReal)⁻¹ ^ s := by
    unfold dyadicValue
    rw [ENNReal.div_eq_inv_mul, Nat.cast_one, mul_one, ENNReal.inv_pow]
  have hk_weight_bound : ∀ x, complexityWeight (KPPlain U x) ≥ (2 : ENNReal)⁻¹ ^ (k x + c_0) := by
    intro x
    exact complexityWeight_antitone (hk_bound x)
  have hkraft := KPPlain_kraft_sum_le_one U hU.isPrefixDecompressor
  constructor
  · intro m
    have h1 : ∀ x : {x // B (m + c_0) x = true}, cantorMass μ x ≤ (2 : ENNReal)⁻¹ ^ m *
        (2 : ENNReal)⁻¹ ^ (k x.1 + c_0) := by
      intro ⟨x, hx⟩
      have h2 := hB_upper (m + c_0) x hx
      rw [h_dv] at h2
      have h3 : m + (k x + c_0) ≤ k x + h x.length + (m + c_0) := by omega
      have h4 : (2 : ENNReal)⁻¹ ^ (k x + h x.length + (m + c_0)) ≤ (2 : ENNReal)⁻¹ ^
          (m + (k x + c_0)) := by
        exact pow_le_pow_of_le_one (by positivity) (by norm_num) h3
      exact h2.trans (by
        have h5 : (2 : ENNReal)⁻¹ ^ (m + (k x + c_0)) = (2 : ENNReal)⁻¹ ^ m * (2 : ENNReal)⁻¹ ^
            (k x + c_0) := by
          rw [pow_add]
        rwa [h5] at h4)
    have h2 : ∑' x : {x // B (m + c_0) x = true}, cantorMass μ x ≤ (2 : ENNReal)⁻¹ ^ m * ∑' x :
        {x // B (m + c_0) x = true}, (2 : ENNReal)⁻¹ ^ (k x.1 + c_0) := by
      calc ∑' x : {x // B (m + c_0) x = true}, cantorMass μ x
        _ ≤ ∑' x : {x // B (m + c_0) x = true}, (2 : ENNReal)⁻¹ ^ m * (2 : ENNReal)⁻¹ ^
            (k x.1 + c_0) := ENNReal.tsum_le_tsum h1
        _ = (2 : ENNReal)⁻¹ ^ m * ∑' x : {x // B (m + c_0) x = true}, (2 : ENNReal)⁻¹ ^
            (k x.1 + c_0) := ENNReal.tsum_mul_left
    have h3 : ∑' x : {x // B (m + c_0) x = true}, (2 : ENNReal)⁻¹ ^ (k x.1 + c_0) ≤ 1 := by
      calc ∑' x : {x // B (m + c_0) x = true}, (2 : ENNReal)⁻¹ ^ (k x.1 + c_0)
        _ ≤ ∑' x : {x // B (m + c_0) x = true}, complexityWeight (KPPlain U x.1) :=
            ENNReal.tsum_le_tsum (fun x => hk_weight_bound x.1)
        _ ≤ ∑' x : BitString, complexityWeight (KPPlain U x) :=
            ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun x =>
              complexityWeight (KPPlain U x))
        _ ≤ 1 := hkraft
    calc ∑' x : {x // B (m + c_0) x = true}, cantorMass μ x
      _ ≤ (2 : ENNReal)⁻¹ ^ m * ∑' x : {x // B (m + c_0) x = true}, (2 : ENNReal)⁻¹ ^ (k x.1 + c_0)
          := h2
      _ ≤ (2 : ENNReal)⁻¹ ^ m * 1 := mul_le_mul_right h3 _
      _ = (2 : ENNReal)⁻¹ ^ m := mul_one _
      _ = dyadicValue 1 m := (h_dv m).symm
  · intro m N
    have h1 : ∀ x : {x // B (m + c_0) x = true ∧ (x : BitString).length ≥ N}, cantorMass μ x ≤
        (2 : ENNReal)⁻¹ ^ (m + h N) * (2 : ENNReal)⁻¹ ^ (k x.1 + c_0) := by
      intro ⟨x, hx, hxN⟩
      have h2 := hB_upper (m + c_0) x hx
      rw [h_dv] at h2
      have h3 : m + h N + (k x + c_0) ≤ k x + h x.length + (m + c_0) := by
        have h_growth := hh.monotone hxN
        omega
      have h4 : (2 : ENNReal)⁻¹ ^ (k x + h x.length + (m + c_0)) ≤ (2 : ENNReal)⁻¹ ^
          (m + h N + (k x + c_0)) := by
        exact pow_le_pow_of_le_one (by positivity) (by norm_num) h3
      exact h2.trans (by
        have h5 : (2 : ENNReal)⁻¹ ^ (m + h N + (k x + c_0)) = (2 : ENNReal)⁻¹ ^ (m + h N) *
            (2 : ENNReal)⁻¹ ^ (k x + c_0) := by
          rw [pow_add]
        rwa [h5] at h4)
    have h2 : ∑' x : {x // B (m + c_0) x = true ∧ (x : BitString).length ≥ N}, cantorMass μ x ≤
        (2 : ENNReal)⁻¹ ^ (m + h N) * ∑' x : {x // B (m + c_0) x = true ∧ (x : BitString).length ≥
        N}, (2 : ENNReal)⁻¹ ^ (k x.1 + c_0) := by
      calc ∑' x : {x // B (m + c_0) x = true ∧ (x : BitString).length ≥ N}, cantorMass μ x
        _ ≤ ∑' x : {x // B (m + c_0) x = true ∧ (x : BitString).length ≥ N}, (2 : ENNReal)⁻¹ ^
            (m + h N) * (2 : ENNReal)⁻¹ ^ (k x.1 + c_0) := ENNReal.tsum_le_tsum h1
        _ = (2 : ENNReal)⁻¹ ^ (m + h N) * ∑' x : {x // B (m + c_0) x = true ∧ (x : BitString).length
            ≥ N}, (2 : ENNReal)⁻¹ ^ (k x.1 + c_0) := ENNReal.tsum_mul_left
    have h3 : ∑' x : {x // B (m + c_0) x = true ∧ (x : BitString).length ≥ N}, (2 : ENNReal)⁻¹ ^
        (k x.1 + c_0) ≤ 1 := by
      calc ∑' x : {x // B (m + c_0) x = true ∧ (x : BitString).length ≥ N}, (2 : ENNReal)⁻¹ ^
          (k x.1 + c_0)
        _ ≤ ∑' x : {x // B (m + c_0) x = true ∧ (x : BitString).length ≥ N}, complexityWeight
            (KPPlain U x.1) := ENNReal.tsum_le_tsum (fun x => hk_weight_bound x.1)
        _ ≤ ∑' x : BitString, complexityWeight (KPPlain U x) :=
            ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun x =>
              complexityWeight (KPPlain U x))
        _ ≤ 1 := hkraft
    calc ∑' x : {x // B (m + c_0) x = true ∧ (x : BitString).length ≥ N}, cantorMass μ x
      _ ≤ (2 : ENNReal)⁻¹ ^ (m + h N) * ∑' x : {x // B (m + c_0) x = true ∧ (x : BitString).length ≥
          N}, (2 : ENNReal)⁻¹ ^ (k x.1 + c_0) := h2
      _ ≤ (2 : ENNReal)⁻¹ ^ (m + h N) * 1 := mul_le_mul_right h3 _
      _ = (2 : ENNReal)⁻¹ ^ (m + h N) := mul_one _
      _ = dyadicValue 1 (m + h N) := (h_dv (m + h N)).symm

/-- Enumeration of all bit strings, each exactly once: index `Nat.pair l j` is the `j`-th string of
length `l`. -/
private def isSchnorrRandom_iff_forall_computable_bound_test_enum (i : ℕ) :
    Option BitString := (levelList i.unpair.1)[i.unpair.2]?

private lemma isSchnorrRandom_iff_forall_computable_bound_test_computable_enum :
    Computable isSchnorrRandom_iff_forall_computable_bound_test_enum := by
  unfold isSchnorrRandom_iff_forall_computable_bound_test_enum
  have h1 : Computable (fun i : ℕ => levelList i.unpair.1) :=
    primrec_levelList.to_comp.comp ((Primrec.fst.comp Primrec.unpair).to_comp)
  have h2 : Computable (fun i : ℕ => i.unpair.2) := (Primrec.snd.comp Primrec.unpair).to_comp
  exact Primrec.list_getElem?.to_comp.comp h1 h2

/-- The code of a string in the enumeration. -/
private def isSchnorrRandom_iff_forall_computable_bound_test_code (x : BitString) :
    ℕ := Nat.pair x.length ((levelList x.length).idxOf x)

private lemma isSchnorrRandom_iff_forall_computable_bound_test_enum_code
    (x : BitString) :
    isSchnorrRandom_iff_forall_computable_bound_test_enum
      (isSchnorrRandom_iff_forall_computable_bound_test_code x) = some x := by
  have hm : x ∈ levelList x.length := mem_levelList.2 rfl
  unfold isSchnorrRandom_iff_forall_computable_bound_test_enum
    isSchnorrRandom_iff_forall_computable_bound_test_code
  rw [Nat.unpair_pair]
  simp only
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.2 hm), List.getElem_idxOf]

private lemma isSchnorrRandom_iff_forall_computable_bound_test_eq_code
    (i : ℕ) (x : BitString)
    (h : isSchnorrRandom_iff_forall_computable_bound_test_enum i = some x) :
    i = isSchnorrRandom_iff_forall_computable_bound_test_code x := by
  have h' := isSchnorrRandom_iff_forall_computable_bound_test_enum_code x
  unfold isSchnorrRandom_iff_forall_computable_bound_test_enum at h h'
  unfold isSchnorrRandom_iff_forall_computable_bound_test_code at h' ⊢
  rw [Nat.unpair_pair] at h'
  simp only at h'
  have hmem : x ∈ levelList i.unpair.1 := List.mem_of_getElem? h
  have hlen : x.length = i.unpair.1 := mem_levelList.1 hmem
  rw [hlen] at h' ⊢
  have hlt : i.unpair.2 < (levelList i.unpair.1).length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)
  have hj := (List.Nodup.getElem?_inj hlt (nodup_levelList _)).1 (h.trans h'.symm)
  rw [← hj, Nat.pair_unpair]

/-- Step 4 of the proof of `isSchnorrRandom_iff_forall_computable_bound_ltr`: build
test -/
private lemma isSchnorrRandom_iff_forall_computable_bound_test
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ]
    (B : ℕ → BitString → Bool) (hB_comp : Computable₂ B)
    (w : CantorSeq) (c_0 : ℕ)
    (hw_cov : ∀ m, ∃ n, B m (cantorPrefix w n) = true)
    (h_mass : ∀ m, ∑' x : {x // B (m + c_0) x = true}, cantorMass μ x ≤ dyadicValue 1 m) :
    ∃ f : ℕ → ℕ → Option BitString, Computable₂ f ∧
      (∀ n, {w} ⊆ ⋃ i, (f n i).elim ∅ cantorCylinder) ∧
      (∀ n, ∑' i, coverMass μ (f n i) ≤ dyadicValue 1 n) ∧
      (∀ n, ∑' i, coverMass μ (f n i) = ∑' x : {x // B (n + c_0) x = true}, cantorMass μ x) := by
  classical
  set E := isSchnorrRandom_iff_forall_computable_bound_test_enum with hE
  set G := isSchnorrRandom_iff_forall_computable_bound_test_code with hG
  have hEG : ∀ x, E (G x) = some x :=
    isSchnorrRandom_iff_forall_computable_bound_test_enum_code
  have hGE : ∀ i x, E i = some x → i = G x :=
    isSchnorrRandom_iff_forall_computable_bound_test_eq_code
  have hGinj : Function.Injective G := by
    intro x y hxy
    have := hEG x
    rw [hxy, hEG y] at this
    exact (Option.some.inj this).symm
  let f : ℕ → ℕ → Option BitString := fun n i =>
    (E i).bind (fun x => if B (n + c_0) x = true then some x else none)
  have hf_comp : Computable₂ f := by
    have hE' : Computable (fun p : ℕ × ℕ => E p.2) :=
      isSchnorrRandom_iff_forall_computable_bound_test_computable_enum.comp
        Computable.snd
    have hinner : Computable₂ (fun (p : ℕ × ℕ) (x : BitString) =>
        if B (p.1 + c_0) x = true then some x else none) := by
      have hBc : Computable (fun r : (ℕ × ℕ) × BitString => B (r.1.1 + c_0) r.2) :=
        hB_comp.comp
          (Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.fst)
            (Computable.const c_0)) Computable.snd
      refine (Computable.cond hBc (Computable.option_some.comp Computable.snd)
        (Computable.const none)).to₂.of_eq ?_
      rintro ⟨p, x⟩
      cases h : B (p.1 + c_0) x <;> simp [h]
    exact Computable.option_bind hE' hinner
  have hcov_mass : ∀ n, ∑' i, coverMass μ (f n i) =
      ∑' x : {x // B (n + c_0) x = true}, cantorMass μ x := by
    intro n
    rw [← (hGinj.comp Subtype.val_injective : Function.Injective
      (fun x : {x // B (n + c_0) x = true} => G x.1)).tsum_eq]
    · refine tsum_congr fun x => ?_
      have : f n (G x.1) = some x.1 := by
        simp [f, hEG, x.2]
      simp [this, coverMass]
    · intro i hi
      simp only [Function.mem_support] at hi
      by_cases hn : E i = none
      · exact absurd (by simp [f, hn, coverMass]) hi
      · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hn
        by_cases hB : B (n + c_0) x = true
        · exact ⟨⟨x, hB⟩, (hGE i x hx).symm⟩
        · exact absurd (by simp [f, hx, hB, coverMass]) hi
  refine ⟨f, hf_comp, ?_, ?_, hcov_mass⟩
  · intro n v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    obtain ⟨m, hm⟩ := hw_cov (n + c_0)
    refine Set.mem_iUnion.2 ⟨G (cantorPrefix v m), ?_⟩
    have : f n (G (cantorPrefix v m)) = some (cantorPrefix v m) := by
      simp [f, hEG, hm]
    rw [this, Option.elim_some]
    change IsCantorPrefix (cantorPrefix v m) v
    rw [isCantorPrefix_iff_cantorPrefix_eq, cantorPrefix_length]
  · intro n
    rw [hcov_mass n]
    simpa using h_mass n

/-- Step 1 of the proof of
`isSchnorrRandom_iff_forall_computable_bound_computable_sum`: bounding N. -/
private lemma isSchnorrRandom_iff_forall_computable_bound_computable_sum_n
    (h : ℕ → ℕ) (hh : IsComputableGrowth h) :
    ∃ N : ℕ → ℕ, Computable N ∧ ∀ s, s + 1 ≤ h (N s) := by
  have hunb : ∀ s, ∃ n, s + 1 ≤ h n := fun s => hh.unbounded (s + 1)
  refine ⟨fun s => Nat.find (hunb s), ?_, fun s => Nat.find_spec (hunb s)⟩
  have hP : Computable (fun p : ℕ × ℕ => decide ((fun s n => s + 1 ≤ h n) p.1 p.2)) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp.comp
      (Primrec.succ.to_comp.comp Computable.fst) (hh.computable.comp Computable.snd)
  exact Computable.natFind (P := fun s n => s + 1 ≤ h n) hP hunb

/-- Step 2 of the proof of
`isSchnorrRandom_iff_forall_computable_bound_computable_sum`: sequence definition.
-/
private lemma isSchnorrRandom_iff_forall_computable_bound_q
    (a : BitString → ℕ → ℕ) (ha_comp : Computable₂ a)
    (B : ℕ → BitString → Bool) (hB_comp : Computable₂ B) (c_0 : ℕ)
    (N : ℕ → ℕ) (hN_comp : Computable N) :
    ∃ q : ℕ × ℕ → ℚ, Computable q ∧ ∀ n s,
      q (n, s) = ((((List.range (N s)).flatMap (fun l => levelList l)).filter
          (fun x => B (n + c_0) x = true)).map (fun x => (a x (s + 1 + N s) : ℚ))).sum /
          2 ^ (s + 1 + N s) := by
  refine ⟨fun p => ((((List.range (N p.2)).flatMap (fun l => levelList l)).filter
      (fun x => B (p.1 + c_0) x = true)).map (fun x => (a x (p.2 + 1 + N p.2) : ℚ))).sum /
      2 ^ (p.2 + 1 + N p.2), ?_, fun n s => rfl⟩
  have ht : Computable fun p : ℕ × ℕ => p.2 + 1 + N p.2 :=
    Primrec.nat_add.to_comp.comp (Primrec.succ.to_comp.comp Computable.snd)
      (hN_comp.comp Computable.snd)
  have hlev : Computable fun p : ℕ × ℕ => (List.range (N p.2)).flatMap (fun l => levelList l) :=
    (Primrec.list_flatMap Primrec.list_range (primrec_levelList.comp Primrec.snd).to₂).to_comp.comp
      (hN_comp.comp Computable.snd)
  have hpred : Computable₂ fun (p : ℕ × ℕ) (x : BitString) => decide (B (p.1 + c_0) x = true) := by
    refine (hB_comp.comp (Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.fst)
      (Computable.const c_0)) Computable.snd).to₂.of_eq ?_
    intro p
    simp
  have hL : Computable fun p : ℕ × ℕ => ((List.range (N p.2)).flatMap (fun l => levelList l)).filter
      (fun x => B (p.1 + c_0) x = true) :=
    computable_list_filter hlev hpred
  have hf : Computable₂ fun (p : ℕ × ℕ) (x : BitString) => a x (p.2 + 1 + N p.2) :=
    (ha_comp.comp Computable.snd (ht.comp Computable.fst)).to₂
  have hnum : Computable fun p : ℕ × ℕ =>
    (((((List.range (N p.2)).flatMap (fun l => levelList l)).filter
      (fun x => B (p.1 + c_0) x = true)).map (fun x => a x (p.2 + 1 + N p.2))).sum : ℤ) :=
    ComputableReals.primrec_natCastInt.to_comp.comp (computable_list_sum_map hL hf)
  have hden : Computable fun p : ℕ × ℕ => 2 ^ (p.2 + 1 + N p.2) := comp_pow.comp ht
  refine computable_of_num_den hnum hden (fun p => by positivity) (fun p => ?_)
  push_cast
  simp [List.map_map, Function.comp_def]

private lemma isSchnorrRandom_iff_forall_computable_bound_finite_err_aux_elem
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ] (x : BitString) (t m : ℕ)
    (h : dyadicValue m t ≤ cantorMass μ x + dyadicValue 1 t ∧ cantorMass μ x ≤ dyadicValue m t +
        dyadicValue 1 t) :
    |(m : ℝ) / 2 ^ t - (cantorMass μ x).toReal| ≤ (2 : ℝ)⁻¹ ^ t := by
  have hfin : cantorMass μ x ≠ ⊤ := by
    unfold cantorMass; exact measure_ne_top _ _
  have hd : ∀ k : ℕ, dyadicValue k t = ENNReal.ofReal ((k : ℝ) / 2 ^ t) := by
    intro k
    unfold dyadicValue
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    simp
  have h1 : (1 : ℝ) / 2 ^ t = (2 : ℝ)⁻¹ ^ t := by rw [inv_pow]; simp
  obtain ⟨h1', h2'⟩ := h
  rw [hd, hd] at h1' h2'
  push_cast at h1' h2'
  have hm0 : (0 : ℝ) ≤ (m : ℝ) / 2 ^ t := by positivity
  have hne : (cantorMass μ x).toReal ≥ 0 := ENNReal.toReal_nonneg
  have e1 : ENNReal.ofReal ((m : ℝ) / 2 ^ t) ≤ ENNReal.ofReal ((cantorMass μ x).toReal + (1 : ℝ) /
      2 ^ t) := by
    rw [ENNReal.ofReal_add hne (by positivity), ENNReal.ofReal_toReal hfin]; exact h1'
  have e2 : cantorMass μ x ≤ ENNReal.ofReal ((m : ℝ) / 2 ^ t + (1 : ℝ) / 2 ^ t) := by
    rw [ENNReal.ofReal_add hm0 (by positivity)]; exact h2'
  have f1 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 e1
  have f2 : (cantorMass μ x).toReal ≤ (m : ℝ) / 2 ^ t + (1 : ℝ) / 2 ^ t := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top e2
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  rw [abs_le]; rw [h1] at f1 f2
  constructor <;> linarith

private lemma isSchnorrRandom_iff_forall_computable_bound_finite_err_aux_list
    (a : BitString → ℕ) (g : BitString → ℝ) (t : ℕ) (ε : ℝ)
    (hε : ∀ x, |(a x : ℝ) / 2 ^ t - g x| ≤ ε) :
    ∀ L : List BitString,
      |(((L.map (fun x => (a x : ℚ))).sum : ℚ) : ℝ) / 2 ^ t - (L.map g).sum| ≤ L.length * ε := by
  intro L
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Rat.cast_add, Rat.cast_natCast]
    have : ((a x : ℝ) + ((L.map (fun x => (a x : ℚ))).sum : ℚ)) / 2 ^ t - (g x + (L.map g).sum)
        = ((a x : ℝ) / 2 ^ t - g x) + (((L.map (fun x => (a x : ℚ))).sum : ℚ) / 2 ^ t -
            (L.map g).sum) := by
      ring
    rw [this]
    calc _ ≤ |(a x : ℝ) / 2 ^ t - g x| + |(((L.map (fun x => (a x : ℚ))).sum : ℚ) : ℝ) / 2 ^ t -
        (L.map g).sum| := abs_add_le _ _
      _ ≤ ε + L.length * ε := add_le_add (hε x) ih
      _ = ((L.length + 1 : ℕ) : ℝ) * ε := by push_cast; ring

private lemma isSchnorrRandom_iff_forall_computable_bound_finite_err_aux_len
    (N : ℕ) : ((List.range N).flatMap (fun l => levelList l)).length ≤ 2 ^ N := by
  have : ∀ N : ℕ, ((List.range N).flatMap (fun l => levelList l)).length + 1 = 2 ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append]
      have hl : (levelList N).length = 2 ^ N := by
        have := card_levelFinset N
        rw [levelFinset, List.toFinset_card_of_nodup (nodup_levelList N)] at this
        exact this
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hl]
      rw [pow_succ]; omega
  have := this N
  omega

/-- Step 3 of the proof of
`isSchnorrRandom_iff_forall_computable_bound_computable_sum`: finite error. -/
private lemma isSchnorrRandom_iff_forall_computable_bound_finite_err
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ]
    (a : BitString → ℕ → ℕ) (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
        cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (B : ℕ → BitString → Bool) (c_0 : ℕ)
    (N : ℕ → ℕ) (q : ℕ × ℕ → ℚ)
    (hq : ∀ n s, q (n, s) = ((((List.range (N s)).flatMap (fun l => levelList l)).filter (fun x =>
      B (n + c_0) x = true)).map (fun x => (a x (s + 1 + N s) : ℚ))).sum / 2 ^ (s + 1 + N s)) :
    ∀ n s, |(q (n, s) : ℝ) - ((((List.range (N s)).flatMap (fun l => levelList l)).filter
        (fun x => B (n + c_0) x = true)).map (fun x => (cantorMass μ x).toReal)).sum| ≤ (2 : ℝ)⁻¹ ^
        (s + 1) := by
  intro n s
  set t := s + 1 + N s with ht
  set L := ((List.range (N s)).flatMap (fun l => levelList l)).filter
      (fun x => B (n + c_0) x = true) with hL
  have hlen : L.length ≤ 2 ^ N s :=
    le_trans (List.length_filter_le _ _)
      (isSchnorrRandom_iff_forall_computable_bound_finite_err_aux_len (N s))
  have key := isSchnorrRandom_iff_forall_computable_bound_finite_err_aux_list
    (fun x => a x t) (fun x => (cantorMass μ x).toReal) t ((2 : ℝ)⁻¹ ^ t)
    (fun x => isSchnorrRandom_iff_forall_computable_bound_finite_err_aux_elem x t (a x t) (ha x t))
        L
  have hq' : (q (n, s) : ℝ) = (((L.map (fun x => (a x t : ℚ))).sum : ℚ) : ℝ) / 2 ^ t := by
    rw [hq n s]; push_cast; rfl
  rw [hq']
  refine key.trans ?_
  have h2 : ((L.length : ℕ) : ℝ) ≤ 2 ^ N s := by exact_mod_cast hlen
  have hpos : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ t := by positivity
  calc (L.length : ℝ) * (2 : ℝ)⁻¹ ^ t ≤ 2 ^ N s * (2 : ℝ)⁻¹ ^ t :=
        mul_le_mul_of_nonneg_right h2 hpos
    _ = (2 : ℝ)⁻¹ ^ (s + 1) := by
      have h3 : (2 : ℝ) ^ N s * (2 : ℝ)⁻¹ ^ N s = 1 := by rw [← mul_pow]; simp
      rw [ht, pow_add (2 : ℝ)⁻¹ (s + 1) (N s), mul_left_comm, h3, mul_one]

/-- Step 4 of the proof of
`isSchnorrRandom_iff_forall_computable_bound_computable_sum`: tail error. -/
private lemma isSchnorrRandom_iff_forall_computable_bound_tail_err
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ]
    (B : ℕ → BitString → Bool) (c_0 : ℕ)
    (h : ℕ → ℕ) (N : ℕ → ℕ) (hN : ∀ s, s + 1 ≤ h (N s))
    (f : ℕ → ℕ → Option BitString) (hf_eq : ∀ n, ∑' i, coverMass μ (f n i) = ∑' x :
        {x // B (n + c_0) x = true}, cantorMass μ x)
    (h_tail : ∀ m N_len, ∑' x : {x // B (m + c_0) x = true ∧ (x : BitString).length ≥ N_len},
        cantorMass μ x ≤ dyadicValue 1 (m + h N_len)) :
    ∀ n s, |((((List.range (N s)).flatMap (fun l => levelList l)).filter
        (fun x => B (n + c_0) x = true)).map (fun x => (cantorMass μ x).toReal)).sum -
        (∑' i, coverMass μ (f n i)).toReal| ≤ (2 : ℝ)⁻¹ ^ (s + 1) := by
  intro n s
  set L := ((List.range (N s)).flatMap (fun l => levelList l)).filter
      (fun x => B (n + c_0) x = true) with hL
  have hnd : L.Nodup := by
    apply List.Nodup.filter
    rw [List.nodup_flatMap]
    refine ⟨fun l _ => nodup_levelList l, ?_⟩
    refine (List.nodup_range).imp ?_
    intro a b hab
    change List.Disjoint (levelList a) (levelList b)
    rw [List.disjoint_left]
    intro x hxa hxb
    rw [mem_levelList] at hxa hxb
    exact hab (hxa.symm.trans hxb)
  have hmem : ∀ x, x ∈ L ↔ B (n + c_0) x = true ∧ x.length < N s := by
    intro x
    simp only [hL, List.mem_filter, List.mem_flatMap, List.mem_range, mem_levelList,
        decide_eq_true_eq]
    constructor
    · rintro ⟨⟨l, hl, hx⟩, hb⟩
      exact ⟨hb, hx ▸ hl⟩
    · rintro ⟨hb, hx⟩
      exact ⟨⟨x.length, hx, rfl⟩, hb⟩
  set g : BitString → ℝ≥0∞ := cantorMass μ with hg
  have hgtop : ∀ x, g x ≠ ⊤ := fun x => measure_ne_top μ _
  classical
  have hF : (L.map (fun x => (cantorMass μ x).toReal)).sum = (∑ x ∈ L.toFinset, g x).toReal := by
    rw [ENNReal.toReal_sum (fun x _ => hgtop x), List.sum_toFinset _ hnd]
  have hsplit : ∑' i, coverMass μ (f n i) = ∑ x ∈ L.toFinset, g x + ∑' x : {x // B (n + c_0) x =
      true ∧ (x : BitString).length ≥ N s}, g x := by
    have e1 : ∑' x : {x // B (n + c_0) x = true}, g x
        = ∑' x, {x | B (n + c_0) x = true}.indicator g x :=
      tsum_subtype {x | B (n + c_0) x = true} g
    have e2 : ∑' x : {x // B (n + c_0) x = true ∧ (x : BitString).length ≥ N s}, g x
        = ∑' x, {x | B (n + c_0) x = true ∧ x.length ≥ N s}.indicator g x :=
      tsum_subtype {x | B (n + c_0) x = true ∧ x.length ≥ N s} g
    rw [hf_eq n, e1, e2, sum_eq_tsum_indicator, ← ENNReal.tsum_add]
    congr 1
    funext x
    by_cases hb : B (n + c_0) x = true
    · by_cases hl : x.length < N s
      · have : x ∈ (L.toFinset : Set BitString) := by
          simp only [Finset.mem_coe, List.mem_toFinset, hmem]; exact ⟨hb, hl⟩
        rw [Set.indicator_of_mem this, Set.indicator_of_mem (show x ∈ {x | B (n + c_0) x = true}
            from hb),
          Set.indicator_of_notMem (show x ∉ {x | B (n + c_0) x = true ∧ x.length ≥ N s} from fun h
              => absurd h.2 (not_le.mpr hl)), add_zero]
      · have : x ∉ (L.toFinset : Set BitString) := by
          simp only [Finset.mem_coe, List.mem_toFinset, hmem]; exact fun h => hl h.2
        rw [Set.indicator_of_notMem this, Set.indicator_of_mem (show x ∈ {x | B (n + c_0) x = true}
            from hb),
          Set.indicator_of_mem (show x ∈ {x | B (n + c_0) x = true ∧ x.length ≥ N s} from
              ⟨hb, not_lt.mp hl⟩), zero_add]
    · have h1 : x ∉ (L.toFinset : Set BitString) := by
        simp only [Finset.mem_coe, List.mem_toFinset, hmem]; exact fun h => hb h.1
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (show x ∉ {x | B (n + c_0) x = true}
          from hb),
          Set.indicator_of_notMem (show x ∉ {x | B (n + c_0) x = true ∧ x.length ≥ N s} from fun h
              => hb h.1), add_zero]
  set Tl := ∑' x : {x // B (n + c_0) x = true ∧ (x : BitString).length ≥ N s}, g x with hTl
  have hTl_le : Tl ≤ dyadicValue 1 (n + h (N s)) := h_tail n (N s)
  have hTl_top : Tl ≠ ⊤ := ne_top_of_le_ne_top (dyadicValue_ne_top 1 _) hTl_le
  have hFin_top : ∑ x ∈ L.toFinset, g x ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun x _ => hgtop x)
  have hdiff : (∑ x ∈ L.toFinset, g x).toReal - (∑' i, coverMass μ (f n i)).toReal = - Tl.toReal :=
      by
    rw [hsplit, ENNReal.toReal_add hFin_top hTl_top]; ring
  rw [hF, hdiff, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg]
  have h1 : Tl.toReal ≤ (dyadicValue 1 (n + h (N s))).toReal :=
      ENNReal.toReal_mono (dyadicValue_ne_top 1 _) hTl_le
  have h2 : (dyadicValue 1 (n + h (N s))).toReal = (2 : ℝ)⁻¹ ^ (n + h (N s)) := by
    rw [dyadicValue_one_eq_inv_two_pow', ENNReal.toReal_pow, ENNReal.toReal_inv]; simp
  refine h1.trans (h2.le.trans ?_)
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  have := hN s
  omega

/-- Step 5 of the proof of
`isSchnorrRandom_iff_forall_computable_bound_computable_sum`: triangle inequality.
-/
private lemma isSchnorrRandom_iff_forall_computable_bound_triangle
    (q : ℕ × ℕ → ℚ) (v : ℕ → ℝ) (u : ℕ × ℕ → ℝ)
    (h1 : ∀ n s, |(q (n, s) : ℝ) - u (n, s)| ≤ (2 : ℝ)⁻¹ ^ (s + 1))
    (h2 : ∀ n s, |u (n, s) - v n| ≤ (2 : ℝ)⁻¹ ^ (s + 1)) :
    ∀ n s, |(q (n, s) : ℝ) - v n| ≤ (2 : ℝ)⁻¹ ^ s := by
  intro n s
  calc |(q (n, s) : ℝ) - v n|
      ≤ |(q (n, s) : ℝ) - u (n, s)| + |u (n, s) - v n| := abs_sub_le _ _ _
    _ ≤ (2 : ℝ)⁻¹ ^ (s + 1) + (2 : ℝ)⁻¹ ^ (s + 1) := add_le_add (h1 n s) (h2 n s)
    _ = (2 : ℝ)⁻¹ ^ s := by rw [pow_succ]; ring

/-- Step 5 of the proof of `isSchnorrRandom_iff_forall_computable_bound_ltr`:
computable sequence -/
private lemma isSchnorrRandom_iff_forall_computable_bound_computable_sum
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ)
    (B : ℕ → BitString → Bool) (hB_comp : Computable₂ B) (c_0 : ℕ)
    (h : ℕ → ℕ) (hh : IsComputableGrowth h)
    (f : ℕ → ℕ → Option BitString) (hf_eq : ∀ n, ∑' i, coverMass μ (f n i) = ∑' x :
        {x // B (n + c_0) x = true}, cantorMass μ x)
    (h_tail : ∀ m N, ∑' x : {x // B (m + c_0) x = true ∧ (x : BitString).length ≥ N}, cantorMass μ x
        ≤ dyadicValue 1 (m + h N)) :
    IsComputableRealSeq fun n => (∑' i, coverMass μ (f n i)).toReal := by
  obtain ⟨a, ha_comp, ha_bounds⟩ := hμ
  obtain ⟨N, hN_comp, hN_bound⟩ :=
      isSchnorrRandom_iff_forall_computable_bound_computable_sum_n h hh
  obtain ⟨q, hq_comp, hq_eq⟩ :=
      isSchnorrRandom_iff_forall_computable_bound_q a ha_comp B
      hB_comp c_0 N hN_comp
  use q, hq_comp
  intro n s
  have h_fin := isSchnorrRandom_iff_forall_computable_bound_finite_err a ha_bounds B c_0 N q hq_eq
  have h_tail_err := isSchnorrRandom_iff_forall_computable_bound_tail_err B c_0 h N hN_bound f hf_eq
      h_tail
  exact isSchnorrRandom_iff_forall_computable_bound_triangle q
    (fun n => (∑' i, coverMass μ (f n i)).toReal)
    (fun p => ((((List.range (N p.2)).flatMap (fun l => levelList l)).filter (fun x =>
                B (p.1 + c_0) x = true)).map (fun x => (cantorMass μ x).toReal)).sum)
    (fun n s => h_fin n s) (fun n s => h_tail_err n s) n s

/-- Step 1 of the proof of `isSchnorrRandom_iff_forall_computable_bound`: the forward
direction. -/
private theorem isSchnorrRandom_iff_forall_computable_bound_ltr (U : Map)
    (hU : IsOptimalPrefixConditional U)
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ)
    (hpos : ∀ x, 0 < cantorMass μ x) (w : CantorSeq) :
    IsSchnorrRandom μ w → ∀ k : BitString → ℕ, Computable k →
      (∃ c : ℕ, ∀ x, KPPlain U x ≤ ((k x + c : ℕ) : ℕ∞)) →
      ∀ h : ℕ → ℕ, IsComputableGrowth h → ∃ c : ℝ, ∀ n : ℕ,
        -Real.logb 2 (massR μ (cantorPrefix w n)) - h n - c ≤ k (cantorPrefix w n) := by
  intro hw k hk ⟨c_0, hk_bound⟩ h hh
  by_contra h_not
  have h_not' := isSchnorrRandom_iff_forall_computable_bound_n hpos w k h h_not
  obtain ⟨B, hB_comp, hB_upper, hB_lower⟩ :=
      isSchnorrRandom_iff_forall_computable_bound_Bm hμ k hk h hh
  have ⟨h_mass, h_tail⟩ := isSchnorrRandom_iff_forall_computable_bound_kraft U hU k
      h hh c_0 hk_bound B hB_upper
  have hw_cov : ∀ m, ∃ n, B m (cantorPrefix w n) = true := by
    intro m
    obtain ⟨n, hn⟩ := h_not' m
    use n
    exact hB_lower m (cantorPrefix w n) (le_of_lt hn)
  obtain ⟨f, hf_comp, hf_cov, hf_mass, hf_eq⟩ :=
      isSchnorrRandom_iff_forall_computable_bound_test B hB_comp w c_0 hw_cov h_mass
  have h_seq := isSchnorrRandom_iff_forall_computable_bound_computable_sum hμ B
      hB_comp c_0 h hh f hf_eq h_tail
  have hw_null : IsSchnorrNull μ {w} := ⟨f, hf_comp, hf_cov, hf_mass, h_seq⟩
  exact hw hw_null

/-- Step 1 of the proof of
`isSchnorrRandom_iff_forall_computable_bound_rtl`: search for the first approximation
numerator at least two. Positivity makes the search terminate, and minimality gives a dyadic
sandwich for every cylinder mass. -/
private lemma isSchnorrRandom_iff_forall_computable_bound_dyadic_approx
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ)
    (hpos : ∀ y, 0 < cantorMass μ y) :
    ∃ lam : BitString → ℕ, Computable lam ∧ ∀ y,
      dyadicValue 1 (lam y + 2) ≤ cantorMass μ y ∧
        cantorMass μ y ≤ dyadicValue 1 (lam y) := by
  obtain ⟨a, hac, ha⟩ := hμ
  have herr := growth_rtl_massApprox_error a ha
  have hposR : ∀ y, 0 < (cantorMass μ y).toReal := fun y =>
    ENNReal.toReal_pos (ne_of_gt (hpos y)) (measure_ne_top μ _)
  have hex : ∀ y, ∃ m, 2 ≤ a y (m + 2) := by
    intro y
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
      (div_pos (hposR y) (by norm_num : (0 : ℝ) < 4))
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    refine ⟨m, ?_⟩
    by_contra hlt
    have hsmall : (a y (m + 2) : ℝ) ≤ 1 := by exact_mod_cast (show a y (m + 2) ≤ 1 by omega)
    have heps : (2 : ℝ)⁻¹ ^ (m + 2) ≤ (2 : ℝ)⁻¹ ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hfrac : (a y (m + 2) : ℝ) / 2 ^ (m + 2) ≤ (2 : ℝ)⁻¹ ^ (m + 2) := by
      rw [inv_pow, ← one_div]
      exact div_le_div_of_nonneg_right hsmall (by positivity)
    have he := (abs_le.mp (herr y (m + 2))).1
    nlinarith [hposR y]
  let lam : BitString → ℕ := fun y => Nat.find (hex y)
  have hlamc : Computable lam := by
    apply Computable.natFind (P := fun y m => 2 ≤ a y (m + 2)) ?_ hex
    exact (PrimrecRel.decide Primrec.nat_le).to_comp.comp (Computable.const 2)
      (hac.comp Computable.fst
        (Primrec.nat_add.to_comp.comp Computable.snd (Computable.const 2)))
  refine ⟨lam, hlamc, fun y => ?_⟩
  have hlowerR : (2 : ℝ)⁻¹ ^ (lam y + 2) ≤ (cantorMass μ y).toReal := by
    have htwo : (2 : ℝ) ≤ a y (lam y + 2) := by exact_mod_cast Nat.find_spec (hex y)
    have hfrac : 2 * (2 : ℝ)⁻¹ ^ (lam y + 2) ≤
        (a y (lam y + 2) : ℝ) / 2 ^ (lam y + 2) := by
      rw [inv_pow, ← one_div, mul_one_div]
      exact div_le_div_of_nonneg_right htwo (by positivity)
    have he := (abs_le.mp (herr y (lam y + 2))).2
    linarith
  have hupperR : (cantorMass μ y).toReal ≤ (2 : ℝ)⁻¹ ^ lam y := by
    by_cases hz : lam y = 0
    · rw [hz, pow_zero]
      exact MeasureTheory.measureReal_le_one
    · have hp : a y (lam y - 1 + 2) ≤ 1 := by
        have := Nat.find_min (hex y) (show lam y - 1 < lam y by omega)
        omega
      have hstage : lam y - 1 + 2 = lam y + 1 := by omega
      rw [hstage] at hp
      have hsmall : (a y (lam y + 1) : ℝ) ≤ 1 := by exact_mod_cast hp
      have hfrac : (a y (lam y + 1) : ℝ) / 2 ^ (lam y + 1) ≤ (2 : ℝ)⁻¹ ^ (lam y + 1) := by
        rw [inv_pow, ← one_div]
        exact div_le_div_of_nonneg_right hsmall (by positivity)
      have he := (abs_le.mp (herr y (lam y + 1))).1
      have hid : 2 * (2 : ℝ)⁻¹ ^ (lam y + 1) = (2 : ℝ)⁻¹ ^ lam y := by
        rw [pow_succ]
        ring
      linarith
  constructor
  · apply (ENNReal.toReal_le_toReal
      (not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_ne_top _ _)
      (measure_ne_top μ _)).mp
    rw [not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_toReal]
    simpa [cantorMass, inv_pow, one_div] using hlowerR
  · apply (ENNReal.toReal_le_toReal (measure_ne_top μ _)
      (not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_ne_top _ _)).mp
    rw [not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_toReal]
    simpa [cantorMass, inv_pow, one_div] using hupperR

/-- Step 2 of the proof of
`isSchnorrRandom_iff_forall_computable_bound_rtl`: a strictly increasing computable
sequence of group lengths has a computable monotone inverse that takes value `j` at the length
of group `j`. -/
private lemma isSchnorrRandom_iff_forall_computable_bound_inverse
    (L : ℕ → ℕ) (hLc : Computable L) (hLm : StrictMono L) :
    ∃ g : ℕ → ℕ, Computable g ∧ Monotone g ∧ ∀ j, g (L j) = j := by
  have hex : ∀ n, ∃ j, n < L j := fun n =>
    ⟨n + 1, lt_of_lt_of_le (Nat.lt_succ_self n) (hLm.id_le _)⟩
  let g : ℕ → ℕ := fun n => Nat.find (hex n) - 1
  have ht : Computable (fun n => Nat.find (hex n)) := by
    apply Computable.natFind (P := fun n j => n < L j) ?_ hex
    exact (PrimrecRel.decide Primrec.nat_lt).to_comp.comp Computable.fst
      (hLc.comp Computable.snd)
  refine ⟨g, Primrec.nat_sub.to_comp.comp ht (Computable.const 1), ?_, ?_⟩
  · intro m n hmn
    apply Nat.sub_le_sub_right
    exact Nat.find_mono (fun j hj => lt_of_le_of_lt hmn hj)
  · intro j
    have hfind : Nat.find (hex (L j)) = j + 1 := by
      apply (Nat.find_eq_iff _).mpr
      refine ⟨hLm (Nat.lt_succ_self j), ?_⟩
      intro k hk
      exact not_lt_of_ge (hLm.monotone (by omega))
    simp only [g, hfind, Nat.add_sub_cancel]

/-- Step 3 of the proof of
`isSchnorrRandom_iff_forall_computable_bound_rtl`: the code length uses the boosted mass
code in the selected group and the ordinary length code elsewhere; this choice is computable. -/
private lemma isSchnorrRandom_iff_forall_computable_bound_code_computable
    (S : ℕ → List BitString) (hS : Computable S)
    (lam : BitString → ℕ) (hlam : Computable lam)
    (g : ℕ → ℕ) (hg : Computable g) :
    Computable (fun y : BitString => if y ∈ S (g y.length)
      then lam y + 2 - g y.length else 1 + 2 * y.length) := by
  have hidx : Computable (fun y : BitString => g y.length) := hg.comp Computable.list_length
  have hP : Computable (fun y : BitString => decide (y ∈ S (g y.length))) := by
    have hc := computable_list_any (hS.comp hidx)
      (primrec_decideEq.to_comp : Computable₂ (fun y z : BitString => decide (y = z)))
    exact hc.of_eq (fun y => Bool.eq_iff_iff.mpr (by
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨z, hz, hzy⟩; rwa [← hzy] at hz
      · intro hy; exact ⟨y, hy, rfl⟩))
  have hc1 : Computable (fun y : BitString => lam y + 2 - g y.length) :=
    Primrec.nat_sub.to_comp.comp
      (Primrec.nat_add.to_comp.comp hlam (Computable.const 2)) hidx
  have hc2 : Computable (fun y : BitString => 1 + 2 * y.length) :=
    Primrec.nat_add.to_comp.comp (Computable.const 1)
      (Primrec.nat_mul.to_comp.comp (Computable.const 2) Computable.list_length)
  exact (Computable.cond hP hc1 hc2).of_eq (fun y => by simp)

/-- Step 4 of the proof of
`isSchnorrRandom_iff_forall_computable_bound_rtl`: the ordinary length codes have Kraft
sum at most one. The codes in group `j` have weight at most `2^j` times its mass, so their total
contribution is at most two. -/
private lemma isSchnorrRandom_iff_forall_computable_bound_rtl_kraft
    (μ : Measure CantorSeq) (S : ℕ → List BitString)
    (hSn : ∀ j, (S j).Nodup)
    (hbudget : ∀ j, ((S j).map (cantorMass μ)).sum ≤ dyadicValue 1 (2 * j))
    (lam : BitString → ℕ)
    (hlam : ∀ y, dyadicValue 1 (lam y + 2) ≤ cantorMass μ y)
    (g : ℕ → ℕ) :
    (∑' y : BitString, (2 : ℝ≥0∞)⁻¹ ^
      (if y ∈ S (g y.length) then lam y + 2 - g y.length else 1 + 2 * y.length)) ≤ 3 := by
  classical
  have hcancel : ∀ j : ℕ, (2 : ℝ≥0∞) ^ j * (2 : ℝ≥0∞)⁻¹ ^ j = 1 := by
    intro j
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  have hsub : ∀ a j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (a - j) ≤
      (2 : ℝ≥0∞) ^ j * (2 : ℝ≥0∞)⁻¹ ^ a := by
    intro a j
    calc (2 : ℝ≥0∞)⁻¹ ^ (a - j)
        = ((2 : ℝ≥0∞) ^ j * (2 : ℝ≥0∞)⁻¹ ^ j) * (2 : ℝ≥0∞)⁻¹ ^ (a - j) := by
            rw [hcancel, one_mul]
      _ = (2 : ℝ≥0∞) ^ j * (2 : ℝ≥0∞)⁻¹ ^ (a - j + j) := by
            rw [pow_add]; ac_rfl
      _ ≤ (2 : ℝ≥0∞) ^ j * (2 : ℝ≥0∞)⁻¹ ^ a := by
            simpa only [mul_comm] using mul_le_mul_left
              (pow_le_pow_of_le_one (by positivity : 0 ≤ (2 : ℝ≥0∞)⁻¹)
                (by norm_num : (2 : ℝ≥0∞)⁻¹ ≤ 1) (by omega : a ≤ a - j + j))
              ((2 : ℝ≥0∞) ^ j)
  let F : ℕ → BitString → ℝ≥0∞ := fun j y =>
    if y ∈ S j then (2 : ℝ≥0∞) ^ j * cantorMass μ y else 0
  have hpoint : ∀ y : BitString, (2 : ℝ≥0∞)⁻¹ ^
      (if y ∈ S (g y.length) then lam y + 2 - g y.length else 1 + 2 * y.length)
        ≤ lengthWeight y + ∑' j, F j y := by
    intro y
    by_cases hy : y ∈ S (g y.length)
    · rw [ite_eq_left hy]
      have hmass : (2 : ℝ≥0∞)⁻¹ ^ (lam y + 2) ≤ cantorMass μ y := by
        simpa only [dyadicValue_one_eq_inv_two_pow'] using hlam y
      have hweight : (2 : ℝ≥0∞)⁻¹ ^ (lam y + 2 - g y.length) ≤ F (g y.length) y := by
        simp only [F, ite_eq_left hy]
        exact (hsub _ _).trans (by
          simpa only [mul_comm] using mul_le_mul_left hmass ((2 : ℝ≥0∞) ^ g y.length))
      exact hweight.trans
        ((ENNReal.le_tsum (f := fun j => F j y) (g y.length)).trans (le_add_left le_rfl))
    · simp only [ite_eq_right hy]
      exact le_add_right (le_refl (lengthWeight y))
  have hrow : ∀ j, ∑' y, F j y ≤ (2 : ℝ≥0∞)⁻¹ ^ j := by
    intro j
    have hfinite : ∑' y, F j y = ∑ y ∈ (S j).toFinset, (2 : ℝ≥0∞) ^ j * cantorMass μ y := by
      rw [tsum_eq_sum (s := (S j).toFinset)]
      · exact Finset.sum_congr rfl (fun y hy => by simp [F, List.mem_toFinset.mp hy])
      · intro y hy
        simp [F, show y ∉ S j from fun h => hy (List.mem_toFinset.mpr h)]
    rw [hfinite, ← Finset.mul_sum, List.sum_toFinset _ (hSn j)]
    calc (2 : ℝ≥0∞) ^ j * ((S j).map (cantorMass μ)).sum
        ≤ (2 : ℝ≥0∞) ^ j * dyadicValue 1 (2 * j) := by
          simpa only [mul_comm] using mul_le_mul_left (hbudget j) ((2 : ℝ≥0∞) ^ j)
      _ = (2 : ℝ≥0∞)⁻¹ ^ j := by
        rw [dyadicValue_one_eq_inv_two_pow', show 2 * j = j + j by omega, pow_add,
          ← mul_assoc, hcancel, one_mul]
  calc _ ≤ ∑' y : BitString, (lengthWeight y + ∑' j, F j y) := ENNReal.tsum_le_tsum hpoint
    _ = (∑' y, lengthWeight y) + ∑' j, ∑' y, F j y := by
      rw [ENNReal.tsum_add, ENNReal.tsum_comm]
    _ ≤ 1 + ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ j :=
      add_le_add tsum_lengthWeight (ENNReal.tsum_le_tsum hrow)
    _ = 3 := by
      rw [ENNReal.tsum_geometric]
      norm_num

/-- Step 5 of the proof of
`isSchnorrRandom_iff_forall_computable_bound_rtl`: transfer Kraft–Chaitin coding along
the computable bijection between naturals and strings, using the constant upper semicomputable
approximation of a computable code length. -/
private lemma isSchnorrRandom_iff_forall_computable_bound_complexity_bound
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (q : BitString → ℕ) (hq : Computable q)
    (hsum : (∑' y : BitString, (2 : ℝ≥0∞)⁻¹ ^ q y) ≠ ⊤) :
    ∃ c : ℕ, ∀ y, KPPlain U y ≤ ((q y + c : ℕ) : ℕ∞) := by
  have hc : Computable (fun n => q (natToBitString n)) := hq.comp computable_natToBitString
  have hupper : IsUpperSemicomputableNat (fun n => q (natToBitString n)) :=
    ⟨fun _ n => q (natToBitString n), hc.comp Computable.snd,
      fun _ _ => le_rfl, fun _ => ⟨0, fun _ _ => rfl⟩⟩
  obtain ⟨c, hc⟩ := KPPlain_le_of_tsum_two_pow_neg_ne_top hU computable_natToBitString
    hupper (by
      have heq := tsum_comp_natToBitString (fun y => (2 : ℝ≥0∞)⁻¹ ^ q y)
      rw [heq]
      exact hsum)
  refine ⟨c, fun y => ?_⟩
  have hh := hc (bitStringToNat y)
  simpa only [natToBitString_bitStringToNat, Nat.cast_add] using hh

/-- Step 6 of the proof of
`isSchnorrRandom_iff_forall_computable_bound_rtl`: a positive cylinder of mass at most
`2^-m` has negative base-two logarithm at least `m`. -/
private lemma isSchnorrRandom_iff_forall_computable_bound_log_lower
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ]
    (hpos : ∀ y, 0 < cantorMass μ y) (y : BitString) (m : ℕ)
    (hbound : cantorMass μ y ≤ dyadicValue 1 m) :
    (m : ℝ) ≤ -Real.logb 2 (massR μ y) := by
  have hp : 0 < massR μ y :=
    ENNReal.toReal_pos (ne_of_gt (hpos y)) (measure_ne_top μ _)
  have hreal : massR μ y ≤ (2 : ℝ)⁻¹ ^ m := by
    have hh := ENNReal.toReal_mono
      (not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_ne_top 1 m) hbound
    rw [not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_toReal] at hh
    simpa [massR, inv_pow, one_div] using hh
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp hreal
  rw [Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hh
  linarith

/-- Step 7 of the proof of
`isSchnorrRandom_iff_forall_computable_bound_rtl`: infinitely many hits in groups of
arbitrarily large index contradict every additive constant. The dyadic lower estimate and the
group budget justify removing truncated subtraction. -/
private lemma isSchnorrRandom_iff_forall_computable_bound_conclusion
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ]
    (hpos : ∀ y, 0 < cantorMass μ y)
    (w : CantorSeq) (L : ℕ → ℕ) (S : ℕ → List BitString)
    (hbudget : ∀ j, ((S j).map (cantorMass μ)).sum ≤ dyadicValue 1 (2 * j))
    (hhit : ∃ᶠ j in atTop, cantorPrefix w (L j) ∈ S j)
    (lam : BitString → ℕ)
    (hlam : ∀ y, dyadicValue 1 (lam y + 2) ≤ cantorMass μ y ∧
      cantorMass μ y ≤ dyadicValue 1 (lam y))
    (q : BitString → ℕ) (hq : ∀ j y, y ∈ S j → q y ≤ lam y + 2 - j)
    (h : ℕ → ℕ) (hh : ∀ j, h (L j) ≤ j / 2) :
    ¬ ∃ c : ℝ, ∀ n,
      -Real.logb 2 (massR μ (cantorPrefix w n)) - h n - c ≤ q (cantorPrefix w n) := by
  rintro ⟨c, hc⟩
  obtain ⟨J, hJ⟩ := exists_nat_gt (2 * (c + 2))
  obtain ⟨j, hj, hmem⟩ := Filter.frequently_atTop.mp hhit J
  let y := cantorPrefix w (L j)
  have hy : y ∈ S j := hmem
  have hmass : cantorMass μ y ≤ dyadicValue 1 (2 * j) :=
    (List.le_sum_of_mem (List.mem_map.mpr ⟨y, hy, rfl⟩)).trans (hbudget j)
  have hpow : (2 : ℝ)⁻¹ ^ (lam y + 2) ≤ (2 : ℝ)⁻¹ ^ (2 * j) := by
    have hh := ENNReal.toReal_mono
      (not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_ne_top 1 (2 * j))
      ((hlam y).1.trans hmass)
    rw [not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_toReal,
      not_isSchnorrRandom_iff_exists_growth_rtl_dyadic_toReal] at hh
    simpa [inv_pow, one_div] using hh
  have hlarge : 2 * j ≤ lam y + 2 :=
    (pow_le_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)).mp hpow
  have htrunc : j ≤ lam y + 2 := by omega
  have hqR : (q y : ℝ) ≤ (lam y : ℝ) + 2 - j := by
    have hh : (q y : ℝ) ≤ ((lam y + 2 - j : ℕ) : ℝ) := by exact_mod_cast hq j y hy
    rw [Nat.cast_sub htrunc, Nat.cast_add, Nat.cast_ofNat] at hh
    exact hh
  have hhalf : (2 : ℝ) * h (L j) ≤ j := by
    have hnat : 2 * h (L j) ≤ j := by
      have hhj := hh j
      omega
    exact_mod_cast hnat
  have hlog := isSchnorrRandom_iff_forall_computable_bound_log_lower
    hpos y (lam y) (hlam y).2
  have hb := hc (L j)
  change -Real.logb 2 (massR μ y) - (h (L j) : ℝ) - c ≤ q y at hb
  have hjR : (J : ℝ) ≤ j := by exact_mod_cast hj
  linarith

/-- Step 2 of the proof of `isSchnorrRandom_iff_forall_computable_bound`: the reverse
direction. -/
theorem isSchnorrRandom_iff_forall_computable_bound_rtl (U : Map)
    (hU : IsOptimalPrefixConditional U)
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ)
    (hpos : ∀ x, 0 < cantorMass μ x) (w : CantorSeq) :
    (∀ k : BitString → ℕ, Computable k →
      (∃ c : ℕ, ∀ x, KPPlain U x ≤ ((k x + c : ℕ) : ℕ∞)) →
      ∀ h : ℕ → ℕ, IsComputableGrowth h → ∃ c : ℝ, ∀ n : ℕ,
        -Real.logb 2 (massR μ (cantorPrefix w n)) - h n - c ≤ k (cantorPrefix w n)) →
            IsSchnorrRandom μ w := by
  intro H
  by_contra hw
  obtain ⟨x, hx, ⟨N, hN, hTail⟩, hHit⟩ :=
    (not_isSchnorrRandom_iff_exists_series hμ w).mp hw
  obtain ⟨L, hLc, hLm, S, hSc, hS, hFreq⟩ :=
    not_isSchnorrRandom_iff_exists_growth_group_and_extend
      w x hx N hN hTail hHit
  obtain ⟨lam, hlamc, hlam⟩ :=
    isSchnorrRandom_iff_forall_computable_bound_dyadic_approx hμ hpos
  obtain ⟨g, hgc, hgm, hgL⟩ :=
    isSchnorrRandom_iff_forall_computable_bound_inverse L hLc hLm
  let q : BitString → ℕ := fun y => if y ∈ S (g y.length)
    then lam y + 2 - g y.length else 1 + 2 * y.length
  have hqc : Computable q :=
    isSchnorrRandom_iff_forall_computable_bound_code_computable S hSc lam hlamc g
        hgc
  have hbudget := fun j => (hS j).2.2
  have hsum : (∑' y : BitString, (2 : ℝ≥0∞)⁻¹ ^ q y) ≤ 3 :=
    isSchnorrRandom_iff_forall_computable_bound_rtl_kraft μ S (fun j => (hS j).1)
      hbudget lam (fun y => (hlam y).1) g
  have hqbound := isSchnorrRandom_iff_forall_computable_bound_complexity_bound
    U hU q hqc (ne_top_of_le_ne_top (by norm_num) hsum)
  let h : ℕ → ℕ := fun n => g n / 2
  have hh : IsComputableGrowth h := by
    refine ⟨Primrec.nat_div.to_comp.comp hgc (Computable.const 2), ?_, ?_⟩
    · intro m n hmn
      exact Nat.div_le_div_right (hgm hmn)
    · intro B
      refine ⟨L (2 * B), ?_⟩
      simp [h, hgL]
  have hqS : ∀ j y, y ∈ S j → q y ≤ lam y + 2 - j := by
    intro j y hy
    have hlen := (hS j).2.1 y hy
    simp [q, hlen, hgL, hy]
  exact isSchnorrRandom_iff_forall_computable_bound_conclusion
    hpos w L S hbudget hFreq lam hlam q hqS h (fun j => by simp [h, hgL])
    (H q hqc hqbound h hh)

/-- **SUV Problem 270, p. 283.**  `ω` is Schnorr random with respect to a computable `μ` exactly
when for every computable total upper bound `k` of prefix complexity and every computable
non-decreasing unbounded `h`, one has `k((ω)_n) ≥ -log₂ μ(Ω_{(ω)_n}) - h(n) - O(1)` for all `n`.
"Upper bound" is understood up to an additive constant, as prefix complexity itself is.  Positivity
of the cylinders is needed for `-log₂ μ` to be finite; the book leaves it implicit. -/
theorem isSchnorrRandom_iff_forall_computable_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ)
    (hpos : ∀ x, 0 < cantorMass μ x) (w : CantorSeq) :
    IsSchnorrRandom μ w ↔ ∀ k : BitString → ℕ, Computable k →
      (∃ c : ℕ, ∀ x, KPPlain U x ≤ ((k x + c : ℕ) : ℕ∞)) →
      ∀ h : ℕ → ℕ, IsComputableGrowth h → ∃ c : ℝ, ∀ n : ℕ,
        -Real.logb 2 (massR μ (cantorPrefix w n)) - h n - c ≤ k (cantorPrefix w n) := by
  exact ⟨isSchnorrRandom_iff_forall_computable_bound_ltr U hU hμ hpos w,
      isSchnorrRandom_iff_forall_computable_bound_rtl U hU hμ hpos w⟩

end Kolmogorov.FrequencyGames
