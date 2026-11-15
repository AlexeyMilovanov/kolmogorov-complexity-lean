/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale.RandomnessBasics

/-!
# Mises Church Separation

This module separates Mises-Church randomness from computable randomness for the uniform
measure.  A computable sequence of non-negative uniform martingales, each winning on every
zero-dominated sequence, is combined with weights `2 ^ (-(j + 1))` into one computable
martingale.  The main declaration is `exists_isMisesChurchRandom_not_isComputablyRandom`,
which formalizes Theorem 182(d) of Shen, Uspensky and Vereshchagin.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology ComputableReals

private def exists_isMisesChurchRandom_not_isComputablyRandom_A_natStep (cap : ℕ) (b : Bool) :
    ℕ :=
  if cap > 0 then (bif (b == false) then cap + 1 else cap - 1) else 0

private def exists_isMisesChurchRandom_not_isComputablyRandom_A_M0 (x : BitString) : ℕ :=
  x.foldl exists_isMisesChurchRandom_not_isComputablyRandom_A_natStep 1

private def exists_isMisesChurchRandom_not_isComputablyRandom_A_stepTl (t l : ℕ)
    (s : ℕ × ℕ × ℕ) (b : Bool) : ℕ × ℕ × ℕ :=
  (bif (decide (t ≤ s.2.1 + s.2.2) && (s.2.1 - s.2.2 == l)) then
      (bif b then 0 else 2 * s.1) else s.1,
   bif b then s.2.1 else s.2.1 + 1, bif b then s.2.2 + 1 else s.2.2)

private def exists_isMisesChurchRandom_not_isComputablyRandom_A_state (t l : ℕ)
    (x : BitString) : ℕ × ℕ × ℕ :=
  x.foldl (exists_isMisesChurchRandom_not_isComputablyRandom_A_stepTl t l) (1, 0, 0)

private def exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl (t l : ℕ)
    (x : BitString) : ℕ :=
  (exists_isMisesChurchRandom_not_isComputablyRandom_A_state t l x).1

private def exists_isMisesChurchRandom_not_isComputablyRandom_A_A (j : ℕ)
    (x : BitString) : ℕ :=
  if j = 0 then exists_isMisesChurchRandom_not_isComputablyRandom_A_M0 x
  else exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl
    (Nat.unpair (j - 1)).1 (Nat.unpair (j - 1)).2 x

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_M0_snoc
    (x : BitString) (b : Bool) :
    exists_isMisesChurchRandom_not_isComputablyRandom_A_M0 (x ++ [b]) =
      exists_isMisesChurchRandom_not_isComputablyRandom_A_natStep
        (exists_isMisesChurchRandom_not_isComputablyRandom_A_M0 x) b := by
  simp [exists_isMisesChurchRandom_not_isComputablyRandom_A_M0, List.foldl_append]

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_M0_pair (x : BitString) :
    exists_isMisesChurchRandom_not_isComputablyRandom_A_M0 (x ++ [false]) +
      exists_isMisesChurchRandom_not_isComputablyRandom_A_M0 (x ++ [true]) =
      2 * exists_isMisesChurchRandom_not_isComputablyRandom_A_M0 x := by
  rw [exists_isMisesChurchRandom_not_isComputablyRandom_A_M0_snoc,
    exists_isMisesChurchRandom_not_isComputablyRandom_A_M0_snoc]
  unfold exists_isMisesChurchRandom_not_isComputablyRandom_A_natStep
  split_ifs <;> simp <;> omega

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_M0_le (x : BitString) :
    exists_isMisesChurchRandom_not_isComputablyRandom_A_M0 x ≤ x.length + 1 := by
  induction x using List.reverseRecOn with
  | nil => simp [exists_isMisesChurchRandom_not_isComputablyRandom_A_M0]
  | append_singleton x b ih =>
    rw [exists_isMisesChurchRandom_not_isComputablyRandom_A_M0_snoc]
    unfold exists_isMisesChurchRandom_not_isComputablyRandom_A_natStep
    split_ifs <;> cases b <;> simp <;> omega

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_state_snoc
    (t l : ℕ) (x : BitString) (b : Bool) :
    exists_isMisesChurchRandom_not_isComputablyRandom_A_state t l (x ++ [b]) =
      exists_isMisesChurchRandom_not_isComputablyRandom_A_stepTl t l
        (exists_isMisesChurchRandom_not_isComputablyRandom_A_state t l x) b := by
  simp [exists_isMisesChurchRandom_not_isComputablyRandom_A_state, List.foldl_append]

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_state_counts
    (t l : ℕ) (x : BitString) :
    (exists_isMisesChurchRandom_not_isComputablyRandom_A_state t l x).2.1 =
        x.count false ∧
      (exists_isMisesChurchRandom_not_isComputablyRandom_A_state t l x).2.2 =
        x.count true := by
  induction x using List.reverseRecOn with
  | nil => simp [exists_isMisesChurchRandom_not_isComputablyRandom_A_state]
  | append_singleton x b ih =>
    rw [exists_isMisesChurchRandom_not_isComputablyRandom_A_state_snoc]
    unfold exists_isMisesChurchRandom_not_isComputablyRandom_A_stepTl
    cases b <;> simp [List.count_append, ih.1, ih.2]

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl_snoc
    (t l : ℕ) (x : BitString) (b : Bool) :
    exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl t l (x ++ [b]) =
      bif (decide (t ≤ x.length) && (x.count false - x.count true == l)) then
        (bif b then 0 else 2 * exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl t l x)
      else exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl t l x := by
  have h := exists_isMisesChurchRandom_not_isComputablyRandom_A_state_counts t l x
  have hl := List.count_false_add_count_true x
  unfold exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl
  rw [exists_isMisesChurchRandom_not_isComputablyRandom_A_state_snoc]
  unfold exists_isMisesChurchRandom_not_isComputablyRandom_A_stepTl
  simp only [h.1, h.2]
  have : x.count false + x.count true = x.length := hl
  have e : decide (t ≤ x.count false + x.count true) = decide (t ≤ x.length) := by rw [this]
  rw [e]

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl_pair
    (t l : ℕ) (x : BitString) :
    exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl t l (x ++ [false]) +
      exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl t l (x ++ [true]) =
      2 * exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl t l x := by
  rw [exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl_snoc,
    exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl_snoc]
  cases h : (decide (t ≤ x.length) && (x.count false - x.count true == l)) <;> simp; omega

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl_le
    (t l : ℕ) (x : BitString) :
    exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl t l x ≤ 2 ^ x.length := by
  induction x using List.reverseRecOn with
  | nil =>
    simp [exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl,
      exists_isMisesChurchRandom_not_isComputablyRandom_A_state]
  | append_singleton x b ih =>
    rw [exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl_snoc]
    simp only [List.length_append, List.length_singleton, pow_succ]
    cases h : (decide (t ≤ x.length) && (x.count false - x.count true == l)) <;> cases b <;>
      simp <;> omega

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_A_pair
    (j : ℕ) (x : BitString) :
    exists_isMisesChurchRandom_not_isComputablyRandom_A_A j (x ++ [false]) +
      exists_isMisesChurchRandom_not_isComputablyRandom_A_A j (x ++ [true]) =
      2 * exists_isMisesChurchRandom_not_isComputablyRandom_A_A j x := by
  unfold exists_isMisesChurchRandom_not_isComputablyRandom_A_A
  split_ifs
  · exact exists_isMisesChurchRandom_not_isComputablyRandom_A_M0_pair x
  · exact exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl_pair _ _ x

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_A_le
    (j : ℕ) (x : BitString) :
    exists_isMisesChurchRandom_not_isComputablyRandom_A_A j x ≤ 2 ^ x.length := by
  unfold exists_isMisesChurchRandom_not_isComputablyRandom_A_A
  split_ifs
  · exact (exists_isMisesChurchRandom_not_isComputablyRandom_A_M0_le x).trans
      (Nat.succ_le_of_lt Nat.lt_two_pow_self)
  · exact exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl_le _ _ x

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_A_fair (j : ℕ) :
    IsFairCapital uniformMeasure
      (fun x => (exists_isMisesChurchRandom_not_isComputablyRandom_A_A j x : ℝ)) := by
  rw [isFairCapital_uniform_iff]
  refine ⟨fun x => Nat.cast_nonneg _, fun x => ?_⟩
  have h : ((exists_isMisesChurchRandom_not_isComputablyRandom_A_A j (x ++ [false]) : ℕ) : ℝ)
      +
      (exists_isMisesChurchRandom_not_isComputablyRandom_A_A j (x ++ [true]) : ℕ) =
      2 * (exists_isMisesChurchRandom_not_isComputablyRandom_A_A j x : ℕ) := by
    exact_mod_cast exists_isMisesChurchRandom_not_isComputablyRandom_A_A_pair j x
  linarith

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_primrec_M0 :
    Primrec exists_isMisesChurchRandom_not_isComputablyRandom_A_M0 := by
  refine Primrec.list_foldl (f := fun x : BitString => x) (g := fun _ => (1:ℕ))
    (h := fun (_ : BitString) (p : ℕ × Bool) =>
      exists_isMisesChurchRandom_not_isComputablyRandom_A_natStep p.1 p.2)
    Primrec.id (Primrec.const 1) ?_
  unfold exists_isMisesChurchRandom_not_isComputablyRandom_A_natStep
  have key : Primrec (fun a : BitString × (ℕ × Bool) =>
      if a.2.1 > 0 then (bif (a.2.2 == false) then a.2.1 + 1 else a.2.1 - 1) else 0) := by
    refine Primrec.ite (c := fun a : BitString × (ℕ × Bool) => a.2.1 > 0) ?_ ?_ (Primrec.const 0)
    · exact Primrec.nat_lt.comp (Primrec.const 0) (Primrec.fst.comp Primrec.snd)
    · refine Primrec.cond ?_ ?_ ?_
      · exact (Primrec.beq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const false))
      · exact Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
      · exact Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
  exact key.to₂

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_primrec_Mtl :
    Primrec (fun a : ℕ × ℕ × BitString =>
      exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl a.1 a.2.1 a.2.2) := by
  have hx : Primrec (fun a : ℕ × ℕ × BitString => a.2.2) := Primrec.snd.comp Primrec.snd
  have hstep : Primrec₂ (fun (a : ℕ × ℕ × BitString) (q : (ℕ × ℕ × ℕ) × Bool) =>
      exists_isMisesChurchRandom_not_isComputablyRandom_A_stepTl a.1 a.2.1 q.1 q.2) := by
    unfold exists_isMisesChurchRandom_not_isComputablyRandom_A_stepTl
    have hs : Primrec (fun r : (ℕ × ℕ × BitString) × ((ℕ × ℕ × ℕ) × Bool) => r.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hb : Primrec (fun r : (ℕ × ℕ × BitString) × ((ℕ × ℕ × ℕ) × Bool) => r.2.2) :=
      Primrec.snd.comp Primrec.snd
    have hc : Primrec (fun r : (ℕ × ℕ × BitString) × ((ℕ × ℕ × ℕ) × Bool) => r.2.1.1) :=
      Primrec.fst.comp hs
    have hz : Primrec (fun r : (ℕ × ℕ × BitString) × ((ℕ × ℕ × ℕ) × Bool) => r.2.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp hs)
    have ho : Primrec (fun r : (ℕ × ℕ × BitString) × ((ℕ × ℕ × ℕ) × Bool) => r.2.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp hs)
    have ht : Primrec (fun r : (ℕ × ℕ × BitString) × ((ℕ × ℕ × ℕ) × Bool) => r.1.1) :=
      Primrec.fst.comp Primrec.fst
    have hl : Primrec (fun r : (ℕ × ℕ × BitString) × ((ℕ × ℕ × ℕ) × Bool) => r.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    refine Primrec.pair (Primrec.cond ?_ (Primrec.cond hb (Primrec.const 0)
        (Primrec.nat_mul.comp (Primrec.const 2) hc)) hc) (Primrec.pair
        (Primrec.cond hb hz (Primrec.succ.comp hz))
        (Primrec.cond hb (Primrec.succ.comp ho) ho))
    exact Primrec.and.comp (Primrec.nat_le.comp ht (Primrec.nat_add.comp hz ho)).decide
      (Primrec.beq.comp (Primrec.nat_sub.comp hz ho) hl)
  have := Primrec.list_foldl (f := fun a : ℕ × ℕ × BitString => a.2.2)
    (g := fun _ => ((1, 0, 0) : ℕ × ℕ × ℕ)) hx (Primrec.const _) hstep
  exact Primrec.fst.comp this

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_primrec_A :
    Primrec (fun p : ℕ × BitString =>
      exists_isMisesChurchRandom_not_isComputablyRandom_A_A p.1 p.2) := by
  unfold exists_isMisesChurchRandom_not_isComputablyRandom_A_A
  refine Primrec.ite (c := fun p : ℕ × BitString => p.1 = 0)
    (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (exists_isMisesChurchRandom_not_isComputablyRandom_A_primrec_M0.comp Primrec.snd) ?_
  have hu : Primrec (fun p : ℕ × BitString => Nat.unpair (p.1 - 1)) :=
    Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))
  exact exists_isMisesChurchRandom_not_isComputablyRandom_A_primrec_Mtl.comp
    (Primrec.pair (Primrec.fst.comp hu) (Primrec.pair (Primrec.snd.comp hu) Primrec.snd))

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_counts_false
    (w : CantorSeq) (i : ℕ) (h : w i = false) :
    zerosCount w (i + 1) = zerosCount w i + 1 ∧ onesCount w (i + 1) = onesCount w i := by
  simp [zerosCount, onesCount, cantorPrefix_succ, h, List.count_append]

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_counts_true
    (w : CantorSeq) (i : ℕ) (h : w i = true) :
    zerosCount w (i + 1) = zerosCount w i ∧ onesCount w (i + 1) = onesCount w i + 1 := by
  simp [zerosCount, onesCount, cantorPrefix_succ, h, List.count_append]

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_M0_prefix
    (w : CantorSeq) (hw : ZerosDominate w) (n : ℕ) :
    exists_isMisesChurchRandom_not_isComputablyRandom_A_M0 (cantorPrefix w n) =
      1 + zerosCount w n - onesCount w n := by
  induction n with
  | zero =>
    simp [exists_isMisesChurchRandom_not_isComputablyRandom_A_M0, cantorPrefix,
      zerosCount, onesCount]
  | succ n ih =>
    rw [cantorPrefix_succ, exists_isMisesChurchRandom_not_isComputablyRandom_A_M0_snoc, ih]
    have h1 := hw n
    have hpos : 1 + zerosCount w n - onesCount w n > 0 := by omega
    unfold exists_isMisesChurchRandom_not_isComputablyRandom_A_natStep
    rw [ite_eq_left hpos]
    cases h : w n
    · obtain ⟨a, b⟩ := exists_isMisesChurchRandom_not_isComputablyRandom_A_counts_false w n h
      rw [a, b]
      simp; omega
    · obtain ⟨a, b⟩ := exists_isMisesChurchRandom_not_isComputablyRandom_A_counts_true w n h
      rw [a, b]
      simp; omega

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl_prefix_succ
    (w : CantorSeq) (t l n : ℕ)
    (hb : ∀ i, t ≤ i → zerosCount w i - onesCount w i = l → w i = false) :
    exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl t l (cantorPrefix w (n + 1)) =
      if t ≤ n ∧ zerosCount w n - onesCount w n = l then
        2 * exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl t l (cantorPrefix w n)
      else exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl t l (cantorPrefix w n) :=
             by
  rw [cantorPrefix_succ, exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl_snoc,
    cantorPrefix_length]
  have hcond : (decide (t ≤ n) &&
      ((cantorPrefix w n).count false - (cantorPrefix w n).count true == l))
      = decide (t ≤ n ∧ zerosCount w n - onesCount w n = l) := by
    simp only [zerosCount, onesCount]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact decide_eq_true_iff.symm
  rw [hcond]
  by_cases hc : t ≤ n ∧ zerosCount w n - onesCount w n = l
  · have := hb n hc.1 hc.2
    simp [hc, this]
  · simp [hc]

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl_unbounded
    (w : CantorSeq) (t l : ℕ)
    (hb : ∀ i, t ≤ i → zerosCount w i - onesCount w i = l → w i = false)
    (hinf : {i | t ≤ i ∧ zerosCount w i - onesCount w i = l}.Infinite) (K : ℕ) :
    ∃ n, 2 ^ K ≤
      exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl t l (cantorPrefix w n) := by
  have mono : ∀ m n, m ≤ n →
      exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl t l (cantorPrefix w m) ≤
        exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl t l (cantorPrefix w n) := by
    intro m n hmn
    induction hmn with
    | refl => exact le_rfl
    | step h ih =>
      refine ih.trans ?_
      rw [exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl_prefix_succ w t l _ hb]
      split_ifs <;> omega
  induction K with
  | zero =>
    exact ⟨0, by
      simp [exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl,
        exists_isMisesChurchRandom_not_isComputablyRandom_A_state, cantorPrefix]⟩
  | succ K ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨i, hi, hni⟩ := hinf.exists_gt n
    refine ⟨i + 1, ?_⟩
    have hi' : t ≤ i ∧ zerosCount w i - onesCount w i = l := hi
    rw [exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl_prefix_succ w t l _ hb,
      ite_eq_left hi']
    have := mono n i hni.le
    rw [pow_succ]
    omega

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A_wins
    (w : CantorSeq) (hw : ZerosDominate w) :
    ∃ j, Wins (fun x => (exists_isMisesChurchRandom_not_isComputablyRandom_A_A j x : ℝ)) w :=
        by
  suffices h : ∃ j, ∀ K : ℕ, ∃ n,
      K ≤ exists_isMisesChurchRandom_not_isComputablyRandom_A_A j (cantorPrefix w n) by
    obtain ⟨j, hj⟩ := h
    refine ⟨j, ?_⟩
    rintro ⟨C, hC⟩
    obtain ⟨K, hK⟩ := exists_nat_gt C
    obtain ⟨n, hn⟩ := hj K
    have h1 := hC ⟨n, rfl⟩
    have h2 : (K : ℝ) ≤
        (exists_isMisesChurchRandom_not_isComputablyRandom_A_A j (cantorPrefix w n) : ℝ) := by
      exact_mod_cast hn
    simp only at h1
    linarith
  classical
  by_cases h : ∀ l, {i | zerosCount w i - onesCount w i = l}.Finite
  · refine ⟨0, fun K => ?_⟩
    by_contra hcon
    push Not at hcon
    have hfin : {i | zerosCount w i - onesCount w i < K}.Finite := by
      have : {i | zerosCount w i - onesCount w i < K} =
          ⋃ l ∈ Set.Iio K, {i | zerosCount w i - onesCount w i = l} := by ext i; simp
      rw [this]
      exact (Set.finite_Iio K).biUnion fun l _ => h l
    have huniv : {i | zerosCount w i - onesCount w i < K} = Set.univ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have h1 := hcon i
      have h2 := exists_isMisesChurchRandom_not_isComputablyRandom_A_M0_prefix w hw i
      have h3 := hw i
      simp only [exists_isMisesChurchRandom_not_isComputablyRandom_A_A, ite_true] at h1
      omega
    rw [huniv] at hfin
    exact Set.infinite_univ hfin
  · push Not at h
    have hinf : {i | zerosCount w i - onesCount w i = Nat.find h}.Infinite := Nat.find_spec h
    have hfinlt : ∀ l' < Nat.find h, {i | zerosCount w i - onesCount w i = l'}.Finite :=
      fun l' hl' => not_not.mp (Nat.find_min h hl')
    have hfin : {i | zerosCount w i - onesCount w i < Nat.find h}.Finite := by
      have : {i | zerosCount w i - onesCount w i < Nat.find h} =
          ⋃ l ∈ Set.Iio (Nat.find h), {i | zerosCount w i - onesCount w i = l} := by
        ext i; simp
      rw [this]
      exact (Set.finite_Iio _).biUnion fun l hl => hfinlt l hl
    obtain ⟨t, ht⟩ : ∃ t, ∀ i, t ≤ i → Nat.find h ≤ zerosCount w i - onesCount w i := by
      obtain ⟨N, hN⟩ := hfin.bddAbove
      refine ⟨N + 1, fun i hi => ?_⟩
      by_contra hlt
      push Not at hlt
      have := hN (show i ∈ {i | zerosCount w i - onesCount w i < Nat.find h} from hlt)
      omega
    have hb : ∀ i, t ≤ i → zerosCount w i - onesCount w i = Nat.find h → w i = false := by
      intro i hi hDi
      by_contra hwi
      have hwi' : w i = true := by simpa using hwi
      obtain ⟨a, b⟩ := exists_isMisesChurchRandom_not_isComputablyRandom_A_counts_true w i
          hwi'
      have h1 := hw (i + 1)
      have h2 := ht (i + 1) (by omega)
      have h3 := hw i
      omega
    have hT : {i | t ≤ i ∧ zerosCount w i - onesCount w i = Nat.find h}.Infinite :=
      (hinf.sdiff (Set.finite_Iio t)).mono (fun i hi => ⟨by simpa using hi.2, hi.1⟩)
    refine ⟨1 + Nat.pair t (Nat.find h), fun K => ?_⟩
    obtain ⟨n, hn⟩ :=
      exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl_unbounded w t (Nat.find h) hb hT
          K
    refine ⟨n, ?_⟩
    have hA : exists_isMisesChurchRandom_not_isComputablyRandom_A_A
        (1 + Nat.pair t (Nat.find h)) (cantorPrefix w n) =
        exists_isMisesChurchRandom_not_isComputablyRandom_A_Mtl t (Nat.find h)
          (cantorPrefix w n) := by
      simp [exists_isMisesChurchRandom_not_isComputablyRandom_A_A, Nat.unpair_pair]
    rw [hA]
    exact (Nat.lt_two_pow_self.le).trans hn

/-- Step 1 of the proof of `exists_isMisesChurchRandom_not_isComputablyRandom`: there is a
computable sequence of non-negative uniform martingales bounded by $2^n$ that win on all
zero-dominated sequences. -/
private lemma exists_isMisesChurchRandom_not_isComputablyRandom_A :
    ∃ A : ℕ → BitString → ℕ,
      Computable (fun p : ℕ × BitString => A p.1 p.2) ∧
      (∀ j, IsFairCapital uniformMeasure (fun x => (A j x : ℝ))) ∧
      (∀ j x, A j x ≤ 2 ^ x.length) ∧
      ∀ w, ZerosDominate w → ∃ j, Wins (fun x => (A j x : ℝ)) w :=
  ⟨exists_isMisesChurchRandom_not_isComputablyRandom_A_A,
    exists_isMisesChurchRandom_not_isComputablyRandom_A_primrec_A.to_comp,
    exists_isMisesChurchRandom_not_isComputablyRandom_A_A_fair,
    exists_isMisesChurchRandom_not_isComputablyRandom_A_A_le,
    fun w hw => exists_isMisesChurchRandom_not_isComputablyRandom_A_wins w hw⟩

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_m_summable
    (A : ℕ → BitString → ℕ) (hbound : ∀ j x, A j x ≤ 2 ^ x.length) (x : BitString) :
    Summable (fun j => (1 / 2 : ℝ) ^ (j + 1) * (A j x : ℝ)) := by
  have hg : Summable (fun j : ℕ => (2 : ℝ) ^ x.length * (1 / 2 : ℝ) ^ (j + 1)) := by
    have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left
      ((2 : ℝ) ^ x.length * (1 / 2))
    refine this.congr (fun j => ?_)
    rw [pow_succ]; ring
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hg
  have h : (A j x : ℝ) ≤ 2 ^ x.length := by exact_mod_cast hbound j x
  calc (1 / 2 : ℝ) ^ (j + 1) * (A j x : ℝ) ≤ (1 / 2 : ℝ) ^ (j + 1) * 2 ^ x.length :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_m_rec_eq
    (a : ℕ → ℚ) (N : ℕ) :
    (Nat.rec (0 : ℚ) (fun n IH => IH + a n) N : ℚ) = ∑ n ∈ Finset.range N, a n := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ← ih]

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_m_computable
    (A : ℕ → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString => A p.1 p.2))
    (hbound : ∀ j x, A j x ≤ 2 ^ x.length) :
    IsComputableOnStrings (fun x => ∑' j, (1 / 2 : ℝ) ^ (j + 1) * (A j x : ℝ)) := by
  have hhalf : Computable (fun k : ℕ => (1 / 2 : ℚ) ^ k) := by
    refine computable_of_num_den (N := fun _ : ℕ => (1 : ℤ)) (D := fun k : ℕ => 2 ^ k)
      (Computable.const 1) comp_pow (fun k => by positivity) (fun k => ?_)
    simp
  have hQ : Computable (fun p : BitString × ℕ =>
      (Nat.rec (0 : ℚ) (fun n IH => IH + (1 / 2 : ℚ) ^ (n + 1) * (A n p.1 : ℚ))
        (p.1.length + p.2) : ℚ)) := by
    refine Computable.nat_rec (f := fun p : BitString × ℕ => p.1.length + p.2)
      (g := fun _ => (0 : ℚ))
      (h := fun (p : BitString × ℕ) (r : ℕ × ℚ) =>
        r.2 + (1 / 2 : ℚ) ^ (r.1 + 1) * (A r.1 p.1 : ℚ)) ?_ ?_ ?_
    · exact Computable₂.comp Primrec.nat_add.to_comp
        (Primrec.list_length.to_comp.comp Computable.fst) Computable.snd
    · exact Computable.const 0
    · have h1 : Computable (fun x : (BitString × ℕ) × (ℕ × ℚ) => x.2.2) :=
        Computable.snd.comp Computable.snd
      have h2 : Computable (fun x : (BitString × ℕ) × (ℕ × ℚ) => x.2.1 + 1) :=
        Computable₂.comp Primrec.nat_add.to_comp (Computable.fst.comp Computable.snd)
          (Computable.const 1)
      have h3 : Computable (fun x : (BitString × ℕ) × (ℕ × ℚ) =>
          (A x.2.1 x.1.1 : ℚ)) :=
        computable_nat_to_rat.comp (hcomp.comp (Computable.pair
          (Computable.fst.comp Computable.snd) (Computable.fst.comp Computable.fst)))
      exact Computable₂.comp computable₂_ratAdd h1
        (Computable₂.comp computable₂_ratMul (hhalf.comp h2) h3)
  refine ⟨_, hQ, fun y s => ?_⟩
  have hq1 : ((Nat.rec (0 : ℚ) (fun n IH => IH + (1 / 2 : ℚ) ^ (n + 1) * (A n y : ℚ))
      (y.length + s) : ℚ)) =
      ∑ n ∈ Finset.range (y.length + s), (1 / 2 : ℚ) ^ (n + 1) * (A n y : ℚ) :=
    exists_isMisesChurchRandom_not_isComputablyRandom_m_rec_eq
      (fun n => (1 / 2 : ℚ) ^ (n + 1) * (A n y : ℚ)) _
  change |((Nat.rec (0 : ℚ) (fun n IH => IH + (1 / 2 : ℚ) ^ (n + 1) * (A n y : ℚ))
      (y.length + s) : ℚ) : ℝ) - ∑' j, (1 / 2 : ℝ) ^ (j + 1) * (A j y : ℝ)| ≤ (2 : ℝ)⁻¹ ^ s
  rw [hq1]
  push_cast
  have hsumm := exists_isMisesChurchRandom_not_isComputablyRandom_m_summable A hbound y
  have hsplit := hsumm.sum_add_tsum_nat_add (y.length + s)
  have htail_nn : 0 ≤ ∑' n, (1 / 2 : ℝ) ^ (n + (y.length + s) + 1) *
      (A (n + (y.length + s)) y : ℝ) :=
    tsum_nonneg fun n => by positivity
  have htail_le : ∑' n, (1 / 2 : ℝ) ^ (n + (y.length + s) + 1) * (A (n + (y.length + s)) y : ℝ)
      ≤ (2 : ℝ)⁻¹ ^ s := by
    have hgeo : Summable (fun n : ℕ =>
        (2 : ℝ) ^ y.length * (1 / 2 : ℝ) ^ (n + (y.length + s) + 1)) := by
      have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left
        ((2 : ℝ) ^ y.length * (1 / 2) ^ (y.length + s + 1))
      refine this.congr (fun n => ?_)
      rw [show n + (y.length + s) + 1 = n + (y.length + s + 1) by ring, pow_add]; ring
    calc ∑' n, (1 / 2 : ℝ) ^ (n + (y.length + s) + 1) * (A (n + (y.length + s)) y : ℝ)
        ≤ ∑' n : ℕ, (2 : ℝ) ^ y.length * (1 / 2 : ℝ) ^ (n + (y.length + s) + 1) := by
          refine Summable.tsum_le_tsum (fun n => ?_)
            (hsumm.comp_injective (add_left_injective _)) hgeo
          have h : (A (n + (y.length + s)) y : ℝ) ≤ 2 ^ y.length := by
            exact_mod_cast hbound _ y
          calc (1 / 2 : ℝ) ^ (n + (y.length + s) + 1) * (A (n + (y.length + s)) y : ℝ)
              ≤ (1 / 2 : ℝ) ^ (n + (y.length + s) + 1) * 2 ^ y.length :=
                mul_le_mul_of_nonneg_left h (by positivity)
            _ = _ := by ring
      _ = (2 : ℝ)⁻¹ ^ s := by
          have : ∀ n : ℕ, (2 : ℝ) ^ y.length * (1 / 2 : ℝ) ^ (n + (y.length + s) + 1) =
              ((1 / 2 : ℝ) ^ s * (1 / 2)) * (1 / 2 : ℝ) ^ n := fun n => by
            have h2 : (2 : ℝ) ^ y.length * (1 / 2 : ℝ) ^ y.length = 1 := by
              rw [← mul_pow]; norm_num
            calc (2 : ℝ) ^ y.length * (1 / 2 : ℝ) ^ (n + (y.length + s) + 1)
                = ((2 : ℝ) ^ y.length * (1 / 2 : ℝ) ^ y.length) * ((1 / 2 : ℝ) ^ s * (1 / 2) *
                    (1 / 2 : ℝ) ^ n) := by
                  rw [show n + (y.length + s) + 1 = n + s + y.length + 1 by ring]
                  simp only [pow_add, pow_succ]; ring
              _ = _ := by rw [h2]; ring
          simp_rw [this]
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          rw [one_div, inv_pow]; norm_num; ring
  rw [abs_le]
  constructor <;> linarith

private lemma exists_isMisesChurchRandom_not_isComputablyRandom_m_fair
    (A : ℕ → BitString → ℕ)
    (hfair : ∀ j, IsFairCapital uniformMeasure (fun x => (A j x : ℝ)))
    (hbound : ∀ j x, A j x ≤ 2 ^ x.length) :
    IsFairCapital uniformMeasure (fun x => ∑' j, (1 / 2 : ℝ) ^ (j + 1) * (A j x : ℝ)) := by
  rw [isFairCapital_uniform_iff]
  have hS := exists_isMisesChurchRandom_not_isComputablyRandom_m_summable A hbound
  refine ⟨fun x => tsum_nonneg fun j => by positivity, fun x => ?_⟩
  rw [← (hS (x ++ [false])).tsum_add (hS (x ++ [true])), ← tsum_div_const]
  refine tsum_congr (fun j => ?_)
  have h : (A j x : ℝ) = ((A j (x ++ [false]) : ℝ) + (A j (x ++ [true]) : ℝ)) / 2 :=
    ((isFairCapital_uniform_iff _).1 (hfair j)).2 x
  change (1 / 2 : ℝ) ^ (j + 1) * (A j x : ℝ) = _
  rw [h]; ring

/-- Step 2 of the proof of `exists_isMisesChurchRandom_not_isComputablyRandom`: combining
the sequence of martingales $A_j$ with weights $2^{-(j+1)}$ yields a computable martingale $m$
bounded below by each component. -/
private lemma exists_isMisesChurchRandom_not_isComputablyRandom_m
    (A : ℕ → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString => A p.1 p.2))
    (hfair : ∀ j, IsFairCapital uniformMeasure (fun x => (A j x : ℝ)))
    (hbound : ∀ j x, A j x ≤ 2 ^ x.length) :
    ∃ m : BitString → ℝ,
      IsFairCapital uniformMeasure m ∧
      IsComputableOnStrings m ∧
      ∀ j x, (1 / 2 : ℝ) ^ (j + 1) * (A j x : ℝ) ≤ m x := by
  refine ⟨fun x => ∑' j, (1 / 2 : ℝ) ^ (j + 1) * (A j x : ℝ),
    exists_isMisesChurchRandom_not_isComputablyRandom_m_fair A hfair hbound,
    exists_isMisesChurchRandom_not_isComputablyRandom_m_computable A hcomp hbound,
    fun j x => ?_⟩
  exact (exists_isMisesChurchRandom_not_isComputablyRandom_m_summable A hbound x).le_tsum j
    (fun i _ => by positivity)

/-- **SUV Theorem 182(d), p. 280.**  Not every Mises-Church random sequence is computably random,
for the uniform measure. -/
theorem exists_isMisesChurchRandom_not_isComputablyRandom :
    ∃ w, IsMisesChurchRandom w ∧ ¬ IsComputablyRandom uniformMeasure w := by
  obtain ⟨w, hw1, hw2⟩ := exists_isMisesChurchRandom_zerosDominate
  obtain ⟨A, hcomp, hfair, hbound, hwins_A⟩ :=
      exists_isMisesChurchRandom_not_isComputablyRandom_A
  obtain ⟨m, hfair_m, hcomp_m, hm_bound⟩ :=
      exists_isMisesChurchRandom_not_isComputablyRandom_m A hcomp hfair hbound
  use w
  refine ⟨hw1, ?_⟩
  intro h
  obtain ⟨j, hj⟩ := hwins_A w hw2
  have hwins_m : Wins m w := by
    dsimp [Wins] at hj ⊢
    intro h_bdd
    apply hj
    rcases h_bdd with ⟨c, hc⟩
    use c / ((1 / 2 : ℝ) ^ (j + 1))
    rintro _ ⟨n, rfl⟩
    have h1 := hc ⟨n, rfl⟩
    have h2 := hm_bound j (cantorPrefix w n)
    have h3 : (1 / 2 : ℝ) ^ (j + 1) * (A j (cantorPrefix w n) : ℝ) ≤ c := le_trans h2 h1
    rw [le_div_iff₀ (by positivity)]
    rw [mul_comm]
    exact h3
  exact h m hfair_m hcomp_m hwins_m

end Kolmogorov.FrequencyGames
