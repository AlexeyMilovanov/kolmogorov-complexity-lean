/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.LowerSemicomputable.Theorem181

/-!
# Computable Martingales

A lower semicomputable martingale `m` with `m(Λ) = 1` with respect to a computable measure `π`
with positive cylinders is computable (SUV Problem 265, p. 278).

The proof has three steps: the rational lower approximations of `m` are computed by folding over
the enumeration of the set `{(r, x) | r < m(x)}`; upper approximations are obtained from the
martingale identity, since the weighted values `m(y) π(y)` over the strings `y` of a fixed length
sum to `1`; the lower and upper approximations are then combined into approximations with
prescribed error.

Main declaration:
* `isComputableOnStrings_of_isMartingale`: lower semicomputable martingales are computable.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-- One step of the fold in `isComputableOnStrings_of_isMartingale_lower`: at stage `j`,
decode
`j = ⟨k, t⟩`; if the stage test accepts the `k`-th rational for `x` at time `t`, raise the
accumulator to it. -/
private def isComputableOnStrings_of_isMartingale_lower_stepFn
    (chk : ℚ × BitString → ℕ → Bool) (x : BitString) (acc : ℚ) (j : ℕ) : ℚ :=
  if chk (Denumerable.ofNat ℚ j.unpair.1, x) j.unpair.2 = true then
    max acc (Denumerable.ofNat ℚ j.unpair.1) else acc

/-- The fold over `j < s` of the step function from the base value `r0`. -/
private def isComputableOnStrings_of_isMartingale_lower_foldQ
    (chk : ℚ × BitString → ℕ → Bool) (r0 : ℚ) (x : BitString) (s : ℕ) : ℚ :=
  (List.range s).foldl (isComputableOnStrings_of_isMartingale_lower_stepFn chk x) r0

private lemma isComputableOnStrings_of_isMartingale_lower_foldQ_succ
    (chk : ℚ × BitString → ℕ → Bool) (r0 : ℚ) (x : BitString) (s : ℕ) :
    isComputableOnStrings_of_isMartingale_lower_foldQ chk r0 x (s + 1) =
      isComputableOnStrings_of_isMartingale_lower_stepFn chk x
        (isComputableOnStrings_of_isMartingale_lower_foldQ chk r0 x s) s := by
  unfold isComputableOnStrings_of_isMartingale_lower_foldQ
  rw [List.range_succ, List.foldl_append]
  rfl

private lemma isComputableOnStrings_of_isMartingale_lower_stepFn_ge
    (chk : ℚ × BitString → ℕ → Bool) (x : BitString) (acc : ℚ) (j : ℕ) :
    acc ≤ isComputableOnStrings_of_isMartingale_lower_stepFn chk x acc j := by
  unfold isComputableOnStrings_of_isMartingale_lower_stepFn
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

private lemma isComputableOnStrings_of_isMartingale_lower_foldQ_mono
    (chk : ℚ × BitString → ℕ → Bool) (r0 : ℚ) (x : BitString) :
    Monotone (isComputableOnStrings_of_isMartingale_lower_foldQ chk r0 x) := by
  refine monotone_nat_of_le_succ (fun s => ?_)
  rw [isComputableOnStrings_of_isMartingale_lower_foldQ_succ]
  exact isComputableOnStrings_of_isMartingale_lower_stepFn_ge chk x _ s

private lemma isComputableOnStrings_of_isMartingale_lower_foldQ_le
    (chk : ℚ × BitString → ℕ → Bool) (r0 : ℚ) (x : BitString) (b : ℝ) (hr0 : (r0 : ℝ) ≤ b)
    (hchk : ∀ k t, chk (Denumerable.ofNat ℚ k, x) t = true → ((Denumerable.ofNat ℚ k : ℚ) : ℝ) ≤ b)
    (s : ℕ) :
    (isComputableOnStrings_of_isMartingale_lower_foldQ chk r0 x s : ℝ) ≤ b := by
  induction s with
  | zero => simpa [isComputableOnStrings_of_isMartingale_lower_foldQ] using hr0
  | succ s ih =>
    rw [isComputableOnStrings_of_isMartingale_lower_foldQ_succ]
    unfold isComputableOnStrings_of_isMartingale_lower_stepFn
    split_ifs with h
    · push_cast
      exact max_le ih (hchk _ _ h)
    · exact ih

private lemma isComputableOnStrings_of_isMartingale_lower_foldQ_ge
    (chk : ℚ × BitString → ℕ → Bool) (r0 : ℚ) (x : BitString) (j s : ℕ) (hj : j < s)
    (h : chk (Denumerable.ofNat ℚ j.unpair.1, x) j.unpair.2 = true) :
    Denumerable.ofNat ℚ j.unpair.1 ≤
      isComputableOnStrings_of_isMartingale_lower_foldQ chk r0 x s := by
  induction s with
  | zero => omega
  | succ s ih =>
    rw [isComputableOnStrings_of_isMartingale_lower_foldQ_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · exact (ih hj').trans
        (isComputableOnStrings_of_isMartingale_lower_stepFn_ge chk x _ s)
    · unfold isComputableOnStrings_of_isMartingale_lower_stepFn
      rw [ite_eq_left h]
      exact le_max_right _ _

private lemma isComputableOnStrings_of_isMartingale_lower_foldQ_computable
    {chk : ℚ × BitString → ℕ → Bool} (hchk : Computable₂ chk) {r0 : BitString → ℚ}
    (hr0 : Computable r0) :
    Computable (fun p : BitString × ℕ =>
      isComputableOnStrings_of_isMartingale_lower_foldQ chk (r0 p.1) p.1 p.2) := by
  have hmax : Computable₂ (max : ℚ → ℚ → ℚ) := ComputableReals.primrec_ratMax.to_comp
  have hf : Computable (fun p : BitString × ℕ => List.range p.2) :=
    (Primrec.list_range.to_comp).comp Computable.snd
  have hg : Computable (fun p : BitString × ℕ => r0 p.1) := hr0.comp Computable.fst
  have hh : Computable₂ (fun (p : BitString × ℕ) (z : ℚ × ℕ) =>
      isComputableOnStrings_of_isMartingale_lower_stepFn chk p.1 z.1 z.2) := by
    have hk : Computable (fun z : (BitString × ℕ) × ℚ × ℕ => z.2.2.unpair.1) :=
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))).to_comp
    have ht : Computable (fun z : (BitString × ℕ) × ℚ × ℕ => z.2.2.unpair.2) :=
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))).to_comp
    have hq : Computable (fun z : (BitString × ℕ) × ℚ × ℕ => Denumerable.ofNat ℚ z.2.2.unpair.1) :=
      (Computable.ofNat ℚ).comp hk
    have hx : Computable (fun z : (BitString × ℕ) × ℚ × ℕ => z.1.1) :=
      Computable.fst.comp Computable.fst
    have hacc : Computable (fun z : (BitString × ℕ) × ℚ × ℕ => z.2.1) :=
      Computable.fst.comp Computable.snd
    have hb : Computable (fun z : (BitString × ℕ) × ℚ × ℕ =>
        chk (Denumerable.ofNat ℚ z.2.2.unpair.1, z.1.1) z.2.2.unpair.2) :=
      hchk.comp (hq.pair hx) ht
    have hm : Computable (fun z : (BitString × ℕ) × ℚ × ℕ =>
        max z.2.1 (Denumerable.ofNat ℚ z.2.2.unpair.1)) := hmax.comp hacc hq
    have := Computable.cond hb hm hacc
    refine this.of_eq (fun z => ?_)
    unfold isComputableOnStrings_of_isMartingale_lower_stepFn
    simp only [Bool.cond_eq_ite]
  have hfold := Computable.list_foldl
    (l := fun p : BitString × ℕ => List.range p.2) (g := fun p : BitString × ℕ => r0 p.1)
    (h := fun (p : BitString × ℕ) (z : ℚ × ℕ) =>
      isComputableOnStrings_of_isMartingale_lower_stepFn chk p.1 z.1 z.2) hf hg hh
  refine hfold.of_eq (fun p => ?_)
  unfold isComputableOnStrings_of_isMartingale_lower_foldQ
  rfl

/-- Step 1 of the proof of `isComputableOnStrings_of_isMartingale`: a lower semicomputable
function has a computable, non-decreasing rational approximation from below that converges to it. -/
private lemma isComputableOnStrings_of_isMartingale_lower {m : BitString → ℝ}
    (hlsc : IsLowerSemicomputableOnStrings m) :
    ∃ qL : BitString × ℕ → ℚ, Computable qL ∧ ∀ x, Tendsto (fun s => (qL (x, s) : ℝ)) atTop (𝓝 (m
        x)) ∧
      ∀ s, qL (x, s) ≤ qL (x, s + 1) ∧ (qL (x, s) : ℝ) ≤ m x := by
  classical
  obtain ⟨chk, hchkc, -, hiff⟩ := hlsc.exists_stageApprox
  have hex : ∀ x : BitString, ∃ j : ℕ, chk (Denumerable.ofNat ℚ j.unpair.1, x) j.unpair.2 = true :=
      by
    intro x
    obtain ⟨q, hq⟩ := exists_rat_lt (m x)
    obtain ⟨t, ht⟩ := (hiff (q, x)).1 hq
    refine ⟨Nat.pair (Kolmogorov.ComputableReals.ratIndex q) t, ?_⟩
    rw [Nat.unpair_pair, Kolmogorov.ComputableReals.ofNat_ratIndex]
    exact ht
  have hP : Computable (fun p : BitString × ℕ =>
      decide (chk (Denumerable.ofNat ℚ p.2.unpair.1, p.1) p.2.unpair.2 = true)) := by
    have hk : Computable (fun p : BitString × ℕ => p.2.unpair.1) :=
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have ht : Computable (fun p : BitString × ℕ => p.2.unpair.2) :=
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have hq : Computable (fun p : BitString × ℕ => Denumerable.ofNat ℚ p.2.unpair.1) :=
      (Computable.ofNat ℚ).comp hk
    have := hchkc.comp (hq.pair Computable.fst) ht
    exact this.of_eq (fun p => Bool.decide_eq_true.symm)
  have hfind := Computable.natFind
    (P := fun (x : BitString) (j : ℕ) =>
      chk (Denumerable.ofNat ℚ j.unpair.1, x) j.unpair.2 = true) hP hex
  have hr0c : Computable (fun x : BitString =>
      Denumerable.ofNat ℚ (Nat.find (hex x)).unpair.1) :=
    (Computable.ofNat ℚ).comp
      ((Primrec.fst.comp Primrec.unpair).to_comp.comp hfind)
  have hlt : ∀ x k t, chk (Denumerable.ofNat ℚ k, x) t = true →
      ((Denumerable.ofNat ℚ k : ℚ) : ℝ) < m x := by
    intro x k t h
    exact (hiff (Denumerable.ofNat ℚ k, x)).2 ⟨t, h⟩
  have hr0lt : ∀ x, ((Denumerable.ofNat ℚ (Nat.find (hex x)).unpair.1 : ℚ) : ℝ) < m x := by
    intro x
    exact hlt x _ _ (Nat.find_spec (hex x))
  have hcomp := isComputableOnStrings_of_isMartingale_lower_foldQ_computable
    (r0 := fun x : BitString => Denumerable.ofNat ℚ (Nat.find (hex x)).unpair.1) hchkc hr0c
  refine ⟨_, hcomp, fun x => ?_⟩
  have hle : ∀ s, ((isComputableOnStrings_of_isMartingale_lower_foldQ chk
      (Denumerable.ofNat ℚ (Nat.find (hex x)).unpair.1) x s : ℚ) : ℝ) ≤ m x := by
    intro s
    exact isComputableOnStrings_of_isMartingale_lower_foldQ_le chk _ x (m x) (hr0lt x).le
      (fun k t h => (hlt x k t h).le) s
  have hmono := isComputableOnStrings_of_isMartingale_lower_foldQ_mono chk
    (Denumerable.ofNat ℚ (Nat.find (hex x)).unpair.1) x
  refine ⟨?_, fun s => ⟨hmono (Nat.le_succ s), hle s⟩⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨q, haq, hqm⟩ := exists_rat_btwn ha
    obtain ⟨t, ht⟩ := (hiff (q, x)).1 hqm
    set j := Nat.pair (Kolmogorov.ComputableReals.ratIndex q) t with hj
    have hjc : chk (Denumerable.ofNat ℚ j.unpair.1, x) j.unpair.2 = true := by
      rw [hj, Nat.unpair_pair, Kolmogorov.ComputableReals.ofNat_ratIndex]
      exact ht
    filter_upwards [eventually_gt_atTop j] with s hs
    have h1 := isComputableOnStrings_of_isMartingale_lower_foldQ_ge chk
      (Denumerable.ofNat ℚ (Nat.find (hex x)).unpair.1) x j s hs hjc
    rw [hj, Nat.unpair_pair, Kolmogorov.ComputableReals.ofNat_ratIndex] at h1
    exact lt_of_lt_of_le haq (by exact_mod_cast h1)
  · exact Eventually.of_forall (fun s => lt_of_le_of_lt (hle s) hb)

private lemma isComputableOnStrings_of_isMartingale_upper_massR_nil
    (π : Measure CantorSeq) [IsProbabilityMeasure π] : massR π [] = 1 := by
  have hcyl : cantorCylinder [] = Set.univ := by
    ext w
    simp [cantorCylinder, IsCantorPrefix]
  simp [massR, cantorMass, hcyl]

private lemma isComputableOnStrings_of_isMartingale_upper_levelAux {f : BitString → ℝ}
    (hf : ∀ x, f x = f (x ++ [false]) + f (x ++ [true])) :
    ∀ (n : ℕ) (p : BitString), ((allStrings n).map (fun y => f (p ++ y))).sum = f p := by
  intro n
  induction n with
  | zero => intro p; simp [allStrings]
  | succ n ih =>
    intro p
    have h1 := ih (p ++ [false])
    have h2 := ih (p ++ [true])
    have e1 : ((fun y => f (p ++ y)) ∘ fun x => false :: x) = fun y => f ((p ++ [false]) ++ y) := by
      funext y; simp
    have e2 : ((fun y => f (p ++ y)) ∘ fun x => true :: x) = fun y => f ((p ++ [true]) ++ y) := by
      funext y; simp
    simp only [allStrings, List.map_append, List.map_map, List.sum_append]
    rw [e1, e2, h1, h2]
    exact (hf p).symm

private lemma isComputableOnStrings_of_isMartingale_upper_level
    {π : Measure CantorSeq} [IsProbabilityMeasure π] {m : BitString → ℝ}
    (hm : IsMartingale π m) (n : ℕ) :
    ((allStrings n).map (fun y => m y * massR π y)).sum = 1 := by
  have := isComputableOnStrings_of_isMartingale_upper_levelAux
    (f := fun y => m y * massR π y) (fun x => hm.fair x) n []
  simpa [hm.init, isComputableOnStrings_of_isMartingale_upper_massR_nil] using this

private lemma isComputableOnStrings_of_isMartingale_upper_tendstoSum {ι : Type*}
    (l : List ι) (F : ι → ℕ → ℝ) (G : ι → ℝ)
    (h : ∀ y ∈ l, Tendsto (F y) atTop (𝓝 (G y))) :
    Tendsto (fun s => (l.map (fun y => F y s)).sum) atTop (𝓝 (l.map G).sum) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih (fun y hy => h y (by simp [hy])))

private lemma isComputableOnStrings_of_isMartingale_upper_sumLe {ι : Type*} (l : List ι)
    (f g : ι → ℝ) (h : ∀ y ∈ l, f y ≤ g y) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih (fun y hy => h y (by simp [hy])))

private lemma isComputableOnStrings_of_isMartingale_upper_castSum {ι : Type*} (l : List ι)
    (f : ι → ℚ) :
    (((l.map f).sum : ℚ) : ℝ) = (l.map (fun y => (f y : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

private lemma isComputableOnStrings_of_isMartingale_upper_sumSplit :
    ∀ {L : List BitString}, L.Nodup → ∀ {x : BitString}, x ∈ L →
    ∀ (g : BitString → ℝ),
    (L.map g).sum = g x + ((L.filter (fun y => y ≠ x)).map g).sum
  | [], _, x, hx, g => absurd hx (by simp)
  | a :: t, hnd, x, hx, g => by
    rw [List.nodup_cons] at hnd
    by_cases hax : a = x
    · subst hax
      have hfilt : t.filter (fun y => y ≠ a) = t := by
        apply List.filter_eq_self.mpr
        intro y hy
        have : y ≠ a := fun h => hnd.1 (h ▸ hy)
        simpa using this
      have hfa : decide (a ≠ a) = false := by simp
      simp only [List.filter_cons, hfa, Bool.false_eq_true, ite_false, hfilt, List.map_cons,
        List.sum_cons]
    · have hxt : x ∈ t := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hax
        · exact h
      have ih := isComputableOnStrings_of_isMartingale_upper_sumSplit hnd.2 hxt g
      simp only [List.filter_cons, List.map_cons, List.sum_cons]
      have hax' : decide (a ≠ x) = true := by simpa using hax
      rw [hax']
      simp only [ite_true, List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-- Stage `s` of the upper bound for `m x`:
`(1 - Σ_{y ≠ x, |y| = |x|} qL(y,s) pl(y,s)) / max(ℓ x, pl(x,s))`. -/
private def isComputableOnStrings_of_isMartingale_upper_U
    (qL pl : BitString × ℕ → ℚ) (ℓ : BitString → ℚ) (x : BitString) (s : ℕ) : ℚ :=
  (1 - (((allStrings x.length).filter (fun y => y ≠ x)).map
      (fun y => qL (y, s) * pl (y, s))).sum) / max (ℓ x) (pl (x, s))

private lemma isComputableOnStrings_of_isMartingale_upper_upperAn
    {π : Measure CantorSeq} [IsProbabilityMeasure π] {m : BitString → ℝ}
    (hm : IsMartingale π m) {qL pl : BitString × ℕ → ℚ} {ℓ : BitString → ℚ}
    (hqL : ∀ x, Tendsto (fun s => (qL (x, s) : ℝ)) atTop (𝓝 (m x)) ∧
      ∀ s, (qL (x, s) : ℝ) ≤ m x)
    (hpl0 : ∀ y s, 0 ≤ pl (y, s) ∧ (pl (y, s) : ℝ) ≤ massR π y)
    (hpl : ∀ y, Tendsto (fun s => (pl (y, s) : ℝ)) atTop (𝓝 (massR π y)))
    (hℓ : ∀ y, 0 < ℓ y ∧ (ℓ y : ℝ) ≤ massR π y) (x : BitString) :
    (∀ s, m x ≤ (isComputableOnStrings_of_isMartingale_upper_U qL pl ℓ x s : ℝ)) ∧
      Tendsto (fun s => (isComputableOnStrings_of_isMartingale_upper_U qL pl ℓ x s : ℝ))
        atTop (𝓝 (m x)) := by
  classical
  set L := allStrings x.length with hL
  have hxL : x ∈ L := (mem_allStrings _ _).mpr rfl
  have hnd : L.Nodup := allStrings_nodup _
  have hsplit := isComputableOnStrings_of_isMartingale_upper_sumSplit hnd hxL
    (fun y => m y * massR π y)
  have hlev : (L.map (fun y => m y * massR π y)).sum = 1 :=
    isComputableOnStrings_of_isMartingale_upper_level hm x.length
  have hsx : ((L.filter (fun y => y ≠ x)).map (fun y => m y * massR π y)).sum
      = 1 - m x * massR π x := by linarith
  have hmx : 0 ≤ m x := hm.nonneg x
  have hℓx : (0 : ℝ) < (ℓ x : ℝ) := by exact_mod_cast (hℓ x).1
  have hpx : 0 < massR π x := lt_of_lt_of_le hℓx (hℓ x).2
  have hcast : ∀ s, (isComputableOnStrings_of_isMartingale_upper_U qL pl ℓ x s : ℝ) =
      (1 - ((L.filter (fun y => y ≠ x)).map
        (fun y => (qL (y, s) : ℝ) * (pl (y, s) : ℝ))).sum) /
        max (ℓ x : ℝ) (pl (x, s) : ℝ) := by
    intro s
    unfold isComputableOnStrings_of_isMartingale_upper_U
    rw [Rat.cast_div, Rat.cast_sub, Rat.cast_one,
      isComputableOnStrings_of_isMartingale_upper_castSum, Rat.cast_max]
    simp only [Rat.cast_mul]
    rfl
  have hS_le : ∀ s, ((L.filter (fun y => y ≠ x)).map
      (fun y => (qL (y, s) : ℝ) * (pl (y, s) : ℝ))).sum ≤
      ((L.filter (fun y => y ≠ x)).map (fun y => m y * massR π y)).sum := by
    intro s
    apply isComputableOnStrings_of_isMartingale_upper_sumLe
    intro y _
    have h1 := (hqL y).2 s
    have h2 := hpl0 y s
    have h3 := hm.nonneg y
    have h2a : (0 : ℝ) ≤ (pl (y, s) : ℝ) := by exact_mod_cast h2.1
    have e1 : (qL (y, s) : ℝ) * pl (y, s) ≤ m y * pl (y, s) :=
      mul_le_mul_of_nonneg_right h1 h2a
    have e2 : m y * (pl (y, s) : ℝ) ≤ m y * massR π y :=
      mul_le_mul_of_nonneg_left h2.2 h3
    linarith
  constructor
  · intro s
    rw [hcast s]
    have hd_pos : 0 < max (ℓ x : ℝ) (pl (x, s) : ℝ) :=
      lt_of_lt_of_le hℓx (le_max_left _ _)
    rw [le_div_iff₀ hd_pos]
    have hd_le : max (ℓ x : ℝ) (pl (x, s) : ℝ) ≤ massR π x :=
      max_le (hℓ x).2 (hpl0 x s).2
    linarith [mul_le_mul_of_nonneg_left hd_le hmx, hS_le s, hsx]
  · have hS : Tendsto (fun s => ((L.filter (fun y => y ≠ x)).map
        (fun y => (qL (y, s) : ℝ) * (pl (y, s) : ℝ))).sum) atTop
        (𝓝 (((L.filter (fun y => y ≠ x)).map (fun y => m y * massR π y)).sum)) :=
      isComputableOnStrings_of_isMartingale_upper_tendstoSum _
        (fun y s => (qL (y, s) : ℝ) * (pl (y, s) : ℝ))
        (fun y => m y * massR π y) (fun y _ => ((hqL y).1).mul (hpl y))
    have hd : Tendsto (fun s => max (ℓ x : ℝ) (pl (x, s) : ℝ)) atTop (𝓝 (massR π x)) := by
      have := (tendsto_const_nhds (x := (ℓ x : ℝ))).max (hpl x)
      rwa [max_eq_right (hℓ x).2] at this
    have hnum := (tendsto_const_nhds (x := (1 : ℝ))).sub hS
    have hq := hnum.div hd hpx.ne'
    have hlim : (1 - ((L.filter (fun y => y ≠ x)).map
        (fun y => m y * massR π y)).sum) / massR π x = m x := by
      rw [hsx]; field_simp; ring
    rw [hlim] at hq
    exact hq.congr (fun s => (hcast s).symm)

private def isComputableOnStrings_of_isMartingale_upper_runMin (U : ℕ → ℚ) : ℕ → ℚ
  | 0 => U 0
  | s + 1 => min (isComputableOnStrings_of_isMartingale_upper_runMin U s) (U (s + 1))

private lemma isComputableOnStrings_of_isMartingale_upper_runMin_anti (U : ℕ → ℚ) (s : ℕ) :
    isComputableOnStrings_of_isMartingale_upper_runMin U (s + 1) ≤
      isComputableOnStrings_of_isMartingale_upper_runMin U s := by
  simp only [isComputableOnStrings_of_isMartingale_upper_runMin]; exact min_le_left _ _

private lemma isComputableOnStrings_of_isMartingale_upper_runMin_le (U : ℕ → ℚ) :
    ∀ s, isComputableOnStrings_of_isMartingale_upper_runMin U s ≤ U s
  | 0 => le_refl _
  | s + 1 => by
    simp only [isComputableOnStrings_of_isMartingale_upper_runMin]; exact min_le_right _ _

private lemma isComputableOnStrings_of_isMartingale_upper_le_runMin {U : ℕ → ℚ} {c : ℝ}
    (h : ∀ s, c ≤ (U s : ℝ)) :
    ∀ s, c ≤ (isComputableOnStrings_of_isMartingale_upper_runMin U s : ℝ)
  | 0 => h 0
  | s + 1 => by
    simp only [isComputableOnStrings_of_isMartingale_upper_runMin]
    rw [Rat.cast_min]
    exact le_min (isComputableOnStrings_of_isMartingale_upper_le_runMin h s) (h _)

private lemma isComputableOnStrings_of_isMartingale_upper_runMin_an {U : ℕ → ℚ} {c : ℝ}
    (hU : ∀ s, c ≤ (U s : ℝ)) (hT : Tendsto (fun s => (U s : ℝ)) atTop (𝓝 c)) :
    (∀ s, isComputableOnStrings_of_isMartingale_upper_runMin U (s + 1) ≤
        isComputableOnStrings_of_isMartingale_upper_runMin U s ∧
      c ≤ (isComputableOnStrings_of_isMartingale_upper_runMin U s : ℝ)) ∧
      Tendsto (fun s => (isComputableOnStrings_of_isMartingale_upper_runMin U s : ℝ))
        atTop (𝓝 c) :=
  ⟨fun s => ⟨isComputableOnStrings_of_isMartingale_upper_runMin_anti U s,
      isComputableOnStrings_of_isMartingale_upper_le_runMin hU s⟩,
   tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT
     (isComputableOnStrings_of_isMartingale_upper_le_runMin hU)
     (fun s => Rat.cast_le.mpr (isComputableOnStrings_of_isMartingale_upper_runMin_le U s))⟩

private lemma isComputableOnStrings_of_isMartingale_upper_analytic
    {π : Measure CantorSeq} [IsProbabilityMeasure π] {m : BitString → ℝ}
    (hm : IsMartingale π m) {qL pl : BitString × ℕ → ℚ} {ℓ : BitString → ℚ}
    (hqL : ∀ x, Tendsto (fun s => (qL (x, s) : ℝ)) atTop (𝓝 (m x)) ∧
      ∀ s, (qL (x, s) : ℝ) ≤ m x)
    (hpl0 : ∀ y s, 0 ≤ pl (y, s) ∧ (pl (y, s) : ℝ) ≤ massR π y)
    (hpl : ∀ y, Tendsto (fun s => (pl (y, s) : ℝ)) atTop (𝓝 (massR π y)))
    (hℓ : ∀ y, 0 < ℓ y ∧ (ℓ y : ℝ) ≤ massR π y) (x : BitString) :
    Tendsto (fun s => (isComputableOnStrings_of_isMartingale_upper_runMin
        (isComputableOnStrings_of_isMartingale_upper_U qL pl ℓ x) s : ℝ)) atTop
        (𝓝 (m x)) ∧
      ∀ s, isComputableOnStrings_of_isMartingale_upper_runMin
          (isComputableOnStrings_of_isMartingale_upper_U qL pl ℓ x) (s + 1) ≤
        isComputableOnStrings_of_isMartingale_upper_runMin
          (isComputableOnStrings_of_isMartingale_upper_U qL pl ℓ x) s ∧
        m x ≤ (isComputableOnStrings_of_isMartingale_upper_runMin
          (isComputableOnStrings_of_isMartingale_upper_U qL pl ℓ x) s : ℝ) := by
  obtain ⟨h1, h2⟩ := isComputableOnStrings_of_isMartingale_upper_upperAn
    hm hqL hpl0 hpl hℓ x
  obtain ⟨h3, h4⟩ := isComputableOnStrings_of_isMartingale_upper_runMin_an h1 h2
  exact ⟨h4, h3⟩

private lemma isComputableOnStrings_of_isMartingale_upper_dvNe (n s : ℕ) :
    dyadicValue n s ≠ ⊤ := by
  unfold dyadicValue
  exact ENNReal.div_ne_top (ENNReal.natCast_ne_top n) (pow_ne_zero _ (by norm_num))

private lemma isComputableOnStrings_of_isMartingale_upper_dvReal (n s : ℕ) :
    (dyadicValue n s).toReal = (n : ℝ) / 2 ^ s := by
  unfold dyadicValue
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow]
  norm_num

private lemma isComputableOnStrings_of_isMartingale_upper_massBounds
    {π : Measure CantorSeq} [IsProbabilityMeasure π] {a : BitString → ℕ → ℕ}
    (hbound : ∀ x s, dyadicValue (a x s) s ≤ cantorMass π x + dyadicValue 1 s ∧
      cantorMass π x ≤ dyadicValue (a x s) s + dyadicValue 1 s) (x : BitString) (s : ℕ) :
    (a x s : ℝ) / 2 ^ s ≤ massR π x + 1 / 2 ^ s ∧ massR π x ≤ (a x s : ℝ) / 2 ^ s + 1 / 2 ^ s := by
  have hne : cantorMass π x ≠ ⊤ := measure_ne_top π _
  obtain ⟨h1, h2⟩ := hbound x s
  have e1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨hne, isComputableOnStrings_of_isMartingale_upper_dvNe 1 s⟩) h1
  have e2 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨isComputableOnStrings_of_isMartingale_upper_dvNe _ s,
      isComputableOnStrings_of_isMartingale_upper_dvNe 1 s⟩) h2
  rw [ENNReal.toReal_add hne (isComputableOnStrings_of_isMartingale_upper_dvNe 1 s),
    isComputableOnStrings_of_isMartingale_upper_dvReal,
    isComputableOnStrings_of_isMartingale_upper_dvReal] at e1
  rw [ENNReal.toReal_add (isComputableOnStrings_of_isMartingale_upper_dvNe _ s)
    (isComputableOnStrings_of_isMartingale_upper_dvNe 1 s),
    isComputableOnStrings_of_isMartingale_upper_dvReal,
    isComputableOnStrings_of_isMartingale_upper_dvReal] at e2
  simp only [Nat.cast_one] at e1 e2
  exact ⟨e1, e2⟩

private lemma isComputableOnStrings_of_isMartingale_upper_massApprox
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) :
    ∃ pl : BitString × ℕ → ℚ, ∃ ℓ : BitString → ℚ, Computable pl ∧ Computable ℓ ∧
      (∀ y s, 0 ≤ pl (y, s) ∧ (pl (y, s) : ℝ) ≤ massR π y) ∧
      (∀ y, Tendsto (fun s => (pl (y, s) : ℝ)) atTop (𝓝 (massR π y))) ∧
      (∀ y, 0 < ℓ y ∧ (ℓ y : ℝ) ≤ massR π y) := by
  obtain ⟨a, ha, hbound⟩ := hπ
  obtain ⟨pl, hpl⟩ : ∃ pl : BitString × ℕ → ℚ,
      ∀ p, pl p = ((a p.1 p.2 - 1 : ℕ) : ℚ) / ((2 ^ p.2 : ℕ) : ℚ) := ⟨_, fun _ => rfl⟩
  have hplR : ∀ y s, (pl (y, s) : ℝ) = ((a y s - 1 : ℕ) : ℝ) / 2 ^ s := by
    intro y s
    rw [hpl]
    push_cast
    rfl
  have hpl_comp : Computable pl := by
    refine Kolmogorov.computable_of_num_den (N := fun p => ((a p.1 p.2 - 1 : ℕ) : ℤ))
      (D := fun p => 2 ^ p.2) ?_ ?_ (fun p => Nat.two_pow_pos _) (fun p => ?_)
    · exact ComputableReals.primrec_natCastInt.to_comp.comp
        (Computable₂.comp Primrec.nat_sub.to_comp ha (Computable.const 1))
    · exact Kolmogorov.comp_pow.comp Computable.snd
    · rw [hpl]; simp
  have hnn : ∀ y, 0 ≤ massR π y := fun y => ENNReal.toReal_nonneg
  have hle : ∀ y s, (pl (y, s) : ℝ) ≤ massR π y := by
    intro y s
    rw [hplR]
    rcases Nat.eq_zero_or_pos (a y s) with h0 | h0
    · rw [h0]; simpa using hnn y
    · have h1 := (isComputableOnStrings_of_isMartingale_upper_massBounds hbound y s).1
      have : ((a y s - 1 : ℕ) : ℝ) / 2 ^ s = (a y s : ℝ) / 2 ^ s - 1 / 2 ^ s := by
        rw [Nat.cast_sub (Nat.succ_le_of_lt h0), Nat.cast_one, sub_div]
      linarith
  have hge : ∀ y s, massR π y - 2 * (1 / 2 : ℝ) ^ s ≤ (pl (y, s) : ℝ) := by
    intro y s
    rw [hplR]
    have h2s : (0 : ℝ) < 2 ^ s := by positivity
    have h2 := (isComputableOnStrings_of_isMartingale_upper_massBounds hbound y s).2
    have hsub : ((a y s : ℝ) - 1) ≤ ((a y s - 1 : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos (a y s) with h0 | h0
      · rw [h0]; simp
      · rw [Nat.cast_sub (Nat.succ_le_of_lt h0), Nat.cast_one]
    have h3 : ((a y s : ℝ) - 1) / 2 ^ s ≤ ((a y s - 1 : ℕ) : ℝ) / 2 ^ s := by gcongr
    have e : ((a y s : ℝ) - 1) / 2 ^ s = (a y s : ℝ) / 2 ^ s - 1 / 2 ^ s := sub_div _ _ _
    have e2 : 2 * (1 / 2 : ℝ) ^ s = 2 / 2 ^ s := by rw [one_div_pow, mul_one_div]
    have e3 : (2 : ℝ) / 2 ^ s = 1 / 2 ^ s + 1 / 2 ^ s := by ring
    linarith
  have htend : ∀ y, Tendsto (fun s => (pl (y, s) : ℝ)) atTop (𝓝 (massR π y)) := by
    intro y
    have hlim : Tendsto (fun s : ℕ => massR π y - 2 * (1 / 2 : ℝ) ^ s) atTop (𝓝 (massR π y)) := by
      have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 2
      simpa using (tendsto_const_nhds (x := massR π y)).sub h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds (hge y) (hle y)
  have hmpos : ∀ y, 0 < massR π y := fun y =>
    ENNReal.toReal_pos (hpos y).ne' (measure_ne_top π _)
  have hex : ∀ y, ∃ s, 2 ≤ a y s := by
    intro y
    obtain ⟨s, hs⟩ := ((htend y).eventually_const_lt (hmpos y)).exists
    refine ⟨s, ?_⟩
    rw [hplR] at hs
    have h2s : (0 : ℝ) < 2 ^ s := by positivity
    have h4 : 0 < ((a y s - 1 : ℕ) : ℝ) := (div_pos_iff_of_pos_right h2s).mp hs
    have h5 : 0 < a y s - 1 := by exact_mod_cast h4
    omega
  have hP : Computable (fun p : BitString × ℕ => decide (2 ≤ a p.1 p.2)) :=
    Computable₂.comp Primrec.nat_le.decide.to_comp (Computable.const 2) ha
  refine ⟨pl, fun y => pl (y, Nat.find (hex y)), hpl_comp, ?_, fun y s => ⟨?_, hle y s⟩, htend,
    fun y => ⟨?_, hle y _⟩⟩
  · exact hpl_comp.comp (Computable.pair Computable.id
      (Computable.natFind (P := fun y s => 2 ≤ a y s) hP hex))
  · rw [hpl]; positivity
  · have h2 := Nat.find_spec (hex y)
    change 0 < pl (y, Nat.find (hex y))
    rw [hpl]
    dsimp only
    apply div_pos
    · exact_mod_cast (by omega : 0 < a y (Nat.find (hex y)) - 1)
    · exact_mod_cast Nat.two_pow_pos _

private lemma isComputableOnStrings_of_isMartingale_upper_ratDiv {α : Type*}
    [Primcodable α] {f d : α → ℚ}
    (hf : Computable f) (hd : Computable d) (hdpos : ∀ a, 0 < d a) :
    Computable (fun a => f a / d a) := by
  refine Kolmogorov.computable_of_num_den
    (N := fun a => (f a).num * ((d a).den : ℤ))
    (D := fun a => (f a).den * (d a).num.toNat) ?_ ?_ ?_ (fun a => ?_)
  · exact Computable₂.comp Kolmogorov.primrec_intMul.to_comp
      (Kolmogorov.computable_ratNum.comp hf)
      (ComputableReals.primrec_natCastInt.to_comp.comp (Kolmogorov.computable_ratDen.comp hd))
  · exact Computable₂.comp Primrec.nat_mul.to_comp (Kolmogorov.computable_ratDen.comp hf)
      (ComputableReals.primrec_intToNat.to_comp.comp (Kolmogorov.computable_ratNum.comp hd))
  · intro a
    exact Nat.mul_pos (f a).pos (by have := Rat.num_pos.mpr (hdpos a); omega)
  · have hnpos : 0 < (d a).num := Rat.num_pos.mpr (hdpos a)
    have hn : (((d a).num.toNat : ℕ) : ℚ) = ((d a).num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hnpos.le
    have hdnum : ((d a).num : ℚ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have hfd : ((f a).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (f a).den_nz
    have hdd : ((d a).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (d a).den_nz
    push_cast
    rw [hn]
    rw [div_eq_div_iff (hdpos a).ne' (mul_ne_zero hfd hdnum)]
    have h1 : (f a) * ((f a).den : ℚ) = (f a).num := Rat.mul_den_eq_num (f a)
    have h2 : (d a) * ((d a).den : ℚ) = (d a).num := Rat.mul_den_eq_num (d a)
    rw [← h2, ← h1]
    ring

private lemma isComputableOnStrings_of_isMartingale_upper_foldlSkip (x : BitString)
    (f : BitString → ℚ) (l : List BitString) (c : ℚ) :
    l.foldl (fun acc y => bif decide (y = x) then acc else acc + f y) c
      = c + ((l.filter (fun y => decide (y ≠ x))).map f).sum := by
  induction l generalizing c with
  | nil => simp
  | cons y l ih =>
    by_cases hy : y = x
    · simpa [List.foldl_cons, List.filter_cons, hy] using ih c
    · simpa [List.foldl_cons, List.filter_cons, hy, add_assoc] using ih (c + f y)

private lemma isComputableOnStrings_of_isMartingale_upper_Ucomp
    {qL pl : BitString × ℕ → ℚ} {ℓ : BitString → ℚ}
    (hqL : Computable qL) (hpl : Computable pl) (hℓ : Computable ℓ) (hℓpos : ∀ x, 0 < ℓ x) :
    Computable (fun p : BitString × ℕ =>
      (1 - (((allStrings p.1.length).filter (fun y => decide (y ≠ p.1))).map
        (fun y => qL (y, p.2) * pl (y, p.2))).sum) /
        max (ℓ p.1) (pl (p.1, p.2))) := by
  have hsum : Computable (fun p : BitString × ℕ =>
      (((allStrings p.1.length).filter (fun y => decide (y ≠ p.1))).map
        (fun y => qL (y, p.2) * pl (y, p.2))).sum) := by
    have hfold : Computable (fun p : BitString × ℕ =>
        List.foldl (fun acc y => bif decide (y = p.1) then acc
            else acc + qL (y, p.2) * pl (y, p.2)) (0 : ℚ) (allStrings p.1.length)) := by
      refine Computable.list_foldl (l := fun p : BitString × ℕ => allStrings p.1.length)
        (g := fun _ => (0 : ℚ))
        (h := fun p (t : ℚ × BitString) => bif decide (t.2 = p.1) then t.1
          else t.1 + qL (t.2, p.2) * pl (t.2, p.2)) ?_ ?_ ?_
      · exact Kolmogorov.CodedFiniteDistribution.allStrings_primrec.to_comp.comp
          (Computable.list_length.comp Computable.fst)
      · exact Computable.const 0
      · have hc : Computable (fun q : (BitString × ℕ) × (ℚ × BitString) =>
            decide (q.2.2 = q.1.1)) :=
          Computable₂.comp (Primrec.eq (α := BitString)).decide.to_comp
            (Computable.snd.comp Computable.snd) (Computable.fst.comp Computable.fst)
        have hq : Computable (fun q : (BitString × ℕ) × (ℚ × BitString) =>
            (q.2.2, q.1.2)) :=
          Computable.pair (Computable.snd.comp Computable.snd) (Computable.snd.comp Computable.fst)
        exact Computable.cond hc (Computable.fst.comp Computable.snd)
          (Computable₂.comp Kolmogorov.computable₂_ratAdd (Computable.fst.comp Computable.snd)
            (Computable₂.comp Kolmogorov.computable₂_ratMul (hqL.comp hq) (hpl.comp hq)))
    refine hfold.of_eq (fun p => ?_)
    rw [isComputableOnStrings_of_isMartingale_upper_foldlSkip, zero_add]
  have hnum : Computable (fun p : BitString × ℕ =>
      1 - (((allStrings p.1.length).filter (fun y => decide (y ≠ p.1))).map
        (fun y => qL (y, p.2) * pl (y, p.2))).sum) :=
    Computable₂.comp Kolmogorov.computable₂_ratSub (Computable.const 1) hsum
  have hden : Computable (fun p : BitString × ℕ => max (ℓ p.1) (pl (p.1, p.2))) :=
    Computable₂.comp ComputableReals.primrec_ratMax.to_comp (hℓ.comp Computable.fst) hpl
  exact isComputableOnStrings_of_isMartingale_upper_ratDiv hnum hden
    (fun p => lt_of_lt_of_le (hℓpos p.1) (le_max_left _ _))

private def isComputableOnStrings_of_isMartingale_upper_runMinC
    (U : BitString × ℕ → ℚ) (p : BitString × ℕ) : ℚ :=
  Nat.rec (U (p.1, 0)) (fun t acc => min acc (U (p.1, t + 1))) p.2

private lemma isComputableOnStrings_of_isMartingale_upper_runMinC_succ
    (U : BitString × ℕ → ℚ) (x : BitString) (s : ℕ) :
    isComputableOnStrings_of_isMartingale_upper_runMinC U (x, s + 1) =
      min (isComputableOnStrings_of_isMartingale_upper_runMinC U (x, s)) (U (x, s + 1)) :=
  rfl

private lemma isComputableOnStrings_of_isMartingale_upper_runMinC_comp
    {U : BitString × ℕ → ℚ} (hU : Computable U) :
    Computable (isComputableOnStrings_of_isMartingale_upper_runMinC U) := by
  have h := Computable.nat_rec (α := BitString × ℕ) (σ := ℚ) (f := fun p => p.2)
    (g := fun p => U (p.1, 0)) (h := fun p (t : ℕ × ℚ) => min t.2 (U (p.1, t.1 + 1)))
    Computable.snd (hU.comp (Computable.pair Computable.fst (Computable.const 0)))
    (Computable₂.comp ComputableReals.primrec_ratMin.to_comp (Computable.snd.comp Computable.snd)
      (hU.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)))))
  exact h

/-- Step 2 of the proof of `isComputableOnStrings_of_isMartingale`: for a lower
semicomputable martingale with positive cylinders, one can compute a non-increasing rational
approximation from above that converges to it. -/
private lemma isComputableOnStrings_of_isMartingale_upper {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) {m : BitString → ℝ}
    (hm : IsMartingale π m) (hlsc : IsLowerSemicomputableOnStrings m) :
    ∃ qU : BitString × ℕ → ℚ, Computable qU ∧ ∀ x, Tendsto (fun s => (qU (x, s) : ℝ)) atTop (𝓝 (m
        x)) ∧
      ∀ s, qU (x, s + 1) ≤ qU (x, s) ∧ m x ≤ (qU (x, s) : ℝ) := by
  obtain ⟨qL, hqLc, hqL⟩ := isComputableOnStrings_of_isMartingale_lower hlsc
  obtain ⟨pl, ℓ, hplc, hℓc, hpl0, hpl, hℓ⟩ :=
    isComputableOnStrings_of_isMartingale_upper_massApprox hπ hpos
  have hqL' : ∀ x, Tendsto (fun s => (qL (x, s) : ℝ)) atTop (𝓝 (m x)) ∧
      ∀ s, (qL (x, s) : ℝ) ≤ m x :=
    fun x => ⟨(hqL x).1, fun s => ((hqL x).2 s).2⟩
  have hU : Computable (fun p : BitString × ℕ =>
      isComputableOnStrings_of_isMartingale_upper_U qL pl ℓ p.1 p.2) :=
    isComputableOnStrings_of_isMartingale_upper_Ucomp hqLc hplc hℓc (fun x => (hℓ x).1)
  have hrun : ∀ (x : BitString) (s : ℕ),
      isComputableOnStrings_of_isMartingale_upper_runMinC
        (fun p : BitString × ℕ => isComputableOnStrings_of_isMartingale_upper_U qL pl ℓ p.1
            p.2)
        (x, s) =
      isComputableOnStrings_of_isMartingale_upper_runMin
        (isComputableOnStrings_of_isMartingale_upper_U qL pl ℓ x) s := by
    intro x s
    induction s with
    | zero => rfl
    | succ s ih =>
      rw [isComputableOnStrings_of_isMartingale_upper_runMinC_succ, ih]
      rfl
  refine ⟨isComputableOnStrings_of_isMartingale_upper_runMinC
    (fun p : BitString × ℕ => isComputableOnStrings_of_isMartingale_upper_U qL pl ℓ p.1 p.2),
    isComputableOnStrings_of_isMartingale_upper_runMinC_comp hU, fun x => ?_⟩
  simpa only [hrun] using
    isComputableOnStrings_of_isMartingale_upper_analytic hm hqL' hpl0 hpl hℓ x

/-- Step 3 of the proof of `isComputableOnStrings_of_isMartingale`: a function with
computable lower and upper approximations that converge to it is computable on strings. -/
private lemma isComputableOnStrings_of_isMartingale_combine {m : BitString → ℝ}
    (h_lower : ∃ qL : BitString × ℕ → ℚ, Computable qL ∧ ∀ x, Tendsto (fun s => (qL (x, s) : ℝ))
        atTop (𝓝 (m x)) ∧ ∀ s, qL (x, s) ≤ qL (x, s + 1) ∧ (qL (x, s) : ℝ) ≤ m x)
    (h_upper : ∃ qU : BitString × ℕ → ℚ, Computable qU ∧ ∀ x, Tendsto (fun s => (qU (x, s) : ℝ))
        atTop (𝓝 (m x)) ∧ ∀ s, qU (x, s + 1) ≤ qU (x, s) ∧ m x ≤ (qU (x, s) : ℝ)) :
    IsComputableOnStrings m := by
  obtain ⟨qL, hqL, hL⟩ := h_lower
  obtain ⟨qU, hqU, hU⟩ := h_upper
  let P : (BitString × ℕ) → ℕ → Prop := fun a t =>
    (qU (a.1, t) - qL (a.1, t)) * (2 ^ a.2 : ℕ) ≤ (1 : ℚ)
  have hex : ∀ a : BitString × ℕ, ∃ t, P a t := by
    intro a
    have h1 : Tendsto (fun t => ((qU (a.1, t) : ℝ) - (qL (a.1, t) : ℝ))) atTop (𝓝 0) := by
      simpa using (hU a.1).1.sub (hL a.1).1
    have h2 : Tendsto (fun t => ((qU (a.1, t) : ℝ) - (qL (a.1, t) : ℝ)) * ((2 ^ a.2 : ℕ) : ℝ))
        atTop (𝓝 0) := by simpa using h1.mul_const ((2 ^ a.2 : ℕ) : ℝ)
    obtain ⟨t, ht⟩ := (h2.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
    refine ⟨t, ?_⟩
    have : ((((qU (a.1, t) - qL (a.1, t)) * (2 ^ a.2 : ℕ) : ℚ)) : ℝ) ≤ ((1 : ℚ) : ℝ) := by
      push_cast at ht ⊢; exact ht.le
    exact_mod_cast this
  have hP : Computable (fun p : (BitString × ℕ) × ℕ => decide (P p.1 p.2)) := by
    have hq : Computable fun p : (BitString × ℕ) × ℕ => (p.1.1, p.2) :=
      (Computable.fst.comp Computable.fst).pair Computable.snd
    have hpow : Computable fun p : (BitString × ℕ) × ℕ => ((2 ^ p.1.2 : ℕ) : ℚ) :=
      computable_nat_to_rat.comp (comp_pow.comp (Computable.snd.comp Computable.fst))
    have hcmp : Computable₂ (fun a b : ℚ => decide (a ≤ b)) :=
      (PrimrecRel.decide ComputableReals.primrec_ratLe).to_comp
    exact hcmp.comp
      (computable₂_ratMul.comp (computable₂_ratSub.comp (hqU.comp hq) (hqL.comp hq)) hpow)
      (Computable.const 1)
  have ht := Computable.natFind (P := P) hP hex
  refine ⟨fun a => qL (a.1, Nat.find (hex a)), ?_, ?_⟩
  · exact hqL.comp ((Computable.fst.pair ht))
  · intro x s
    have hfs := Nat.find_spec (hex (x, s))
    set t := Nat.find (hex (x, s))
    have hfs' : (((qU (x, t) : ℝ) - (qL (x, t) : ℝ))) * ((2 : ℝ) ^ s) ≤ 1 := by
      have : ((((qU (x, t) - qL (x, t)) * (2 ^ s : ℕ) : ℚ)) : ℝ) ≤ ((1 : ℚ) : ℝ) := by
        exact_mod_cast hfs
      push_cast at this; exact this
    have hlo := (hL x).2 t
    have hup := (hU x).2 t
    have hpos : (0 : ℝ) < 2 ^ s := by positivity
    have hle : (qU (x, t) : ℝ) - (qL (x, t) : ℝ) ≤ (2 : ℝ)⁻¹ ^ s := by
      rw [inv_pow]
      calc (qU (x, t) : ℝ) - (qL (x, t) : ℝ)
          = ((qU (x, t) : ℝ) - (qL (x, t) : ℝ)) * (2 : ℝ) ^ s * ((2 : ℝ) ^ s)⁻¹ := by
            field_simp
        _ ≤ 1 * ((2 : ℝ) ^ s)⁻¹ := by gcongr
        _ = ((2 : ℝ) ^ s)⁻¹ := one_mul _
    change |(qL (x, t) : ℝ) - m x| ≤ _
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hlo.2])]
    linarith [hlo.2, hup.2]

/-- **SUV Problem 265, p. 278.**  A lower semicomputable martingale with `m(Λ) = 1` is computable.
Stated for computable `π` with positive cylinders, the uniform measure being the case the book has
in mind.  Without positivity the claim is false: on a null cylinder a martingale can be any lower
semicomputable non-negative function. -/
theorem isComputableOnStrings_of_isMartingale {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) {m : BitString → ℝ}
    (hm : IsMartingale π m) (hlsc : IsLowerSemicomputableOnStrings m) :
    IsComputableOnStrings m := by
  have h_lower := isComputableOnStrings_of_isMartingale_lower hlsc
  have h_upper := isComputableOnStrings_of_isMartingale_upper hπ hpos hm hlsc
  exact isComputableOnStrings_of_isMartingale_combine h_lower h_upper

end Kolmogorov.FrequencyGames
