/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.FrequencyDeviation

/-!
# K L Randomness

Randomness with respect to Kolmogorov-Loveland selection rules.  The module shows that
Martin-Löf randomness implies randomness with respect to Kolmogorov-Loveland (non-monotone,
adaptive) selection rules: a rule that selects a biased set of bits would yield a
Martin-Löf test, via a Chernoff-type bound on the independent-trials measure.  It
formalizes a part of the chapter on frequency games of the book by Shen, Uspensky and
Vereshchagin, "Kolmogorov complexity and algorithmic randomness".
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped ENNReal

private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_length_le (ρ : KLRule)
    (w : CantorSeq) (t : ℕ) :
    (ρ.revealed w t).length ≤ t := by
  induction t with
  | zero => simp [KLRule.revealed]
  | succ t ih =>
    rw [KLRule.revealed]
    split_ifs
    · simp only [List.length_append, List.length_singleton]
      omega
    · omega

/-- Auxiliary: one step of `revealed` when `F` is defined. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_dom (ρ : KLRule)
    (w : CantorSeq) (t : ℕ)
    (hd : (ρ.next (ρ.revealed w t)).Dom) :
    ρ.revealed w (t + 1) = ρ.revealed w t ++ [w ((ρ.next (ρ.revealed w t)).get hd)] := by
  rw [KLRule.revealed]
  exact dite_eq_left hd

/-- Auxiliary: one step of `revealed` when `F` is undefined. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_not_dom (ρ : KLRule)
    (w : CantorSeq) (t : ℕ)
    (hd : ¬ (ρ.next (ρ.revealed w t)).Dom) :
    ρ.revealed w (t + 1) = ρ.revealed w t := by
  rw [KLRule.revealed]
  exact dite_eq_right hd

/-- Auxiliary: if `F` is defined on the string revealed at time `t`, its length is `t`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_length_eq (ρ : KLRule)
    (w : CantorSeq) (t : ℕ)
    (hd : (ρ.next (ρ.revealed w t)).Dom) : (ρ.revealed w t).length = t := by
  induction t with
  | zero => simp [KLRule.revealed]
  | succ t ih =>
    by_cases hdt : (ρ.next (ρ.revealed w t)).Dom
    · rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_dom ρ w t hdt]
      simp [ih hdt]
    · exfalso
      rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_not_dom ρ w t hdt] at hd
      exact hdt hd

/-- Auxiliary: a string `x` followed by a bit inside `h` is a proper prefix of `h`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_proper_prefix {x h : BitString}
    {c : Bool} (hxc : x ++ [c] <+: h) :
    x <+: h ∧ x ≠ h := by
  refine ⟨(List.prefix_append x [c]).trans hxc, ?_⟩
  rintro rfl
  have := hxc.length_le
  simp at this

/-- Auxiliary: path characterization of the scenario `{revealed w |h| = h}`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_path (ρ : KLRule) (w : CantorSeq)
    (h : BitString) :
    ρ.revealed w h.length = h ↔
      ∀ (x : BitString) (c : Bool), x ++ [c] <+: h → ∃ n ∈ ρ.next x, w n = c := by
  induction h using List.reverseRecOn with
  | nil =>
    simp only [List.length_nil]
    constructor
    · intro _ x c hx
      exfalso
      have := hx.length_le
      simp at this
    · intro _
      simp [KLRule.revealed]
  | append_singleton h' c0 ih =>
    have hlen : (h' ++ [c0]).length = h'.length + 1 := by simp
    rw [hlen]
    constructor
    · intro H
      by_cases hd : (ρ.next (ρ.revealed w h'.length)).Dom
      · rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_dom ρ w _ hd] at H
        obtain ⟨hrev, hc⟩ := List.append_inj' H rfl
        have hP := ih.mp hrev
        obtain ⟨n, hn, hnc⟩ : ∃ n, n ∈ ρ.next (ρ.revealed w h'.length) ∧ w n = c0 :=
          ⟨_, Part.get_mem hd, by simpa using hc⟩
        rw [hrev] at hn
        intro x c hx
        rw [List.prefix_concat_iff] at hx
        rcases hx with hx | hx
        · obtain ⟨hx1, hx2⟩ := List.append_inj' hx rfl
          have hcc : c = c0 := by simpa using hx2
          rw [hx1, hcc]
          exact ⟨n, hn, hnc⟩
        · exact hP x c hx
      · exfalso
        rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_not_dom ρ w _ hd] at H
        have h1 := isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_length_le ρ w
            h'.length
        rw [H] at h1
        simp at h1
    · intro P
      have hP' : ∀ (x : BitString) (c : Bool), x ++ [c] <+: h' → ∃ n ∈ ρ.next x, w n = c :=
        fun x c hx => P x c (hx.trans (List.prefix_append _ _))
      have hrev : ρ.revealed w h'.length = h' := ih.mpr hP'
      obtain ⟨n, hn, hnc⟩ := P h' c0 List.prefix_rfl
      have hn' : n ∈ ρ.next (ρ.revealed w h'.length) := by rw [hrev]; exact hn
      have hd : (ρ.next (ρ.revealed w h'.length)).Dom := Part.dom_iff_mem.mpr ⟨n, hn'⟩
      have hget : (ρ.next (ρ.revealed w h'.length)).get hd = n := Part.get_eq_of_mem hn' hd
      rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_dom ρ w _ hd, hget, hnc,
          hrev]

/-- Step 2b (dependence): the scenario `{revealed w |h| = h}` depends only on finitely many
coordinates, none of which is the coordinate `F h` revealed next. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_depends (ρ : KLRule) (h : BitString) :
    ∃ S : Finset ℕ, (∀ n ∈ ρ.next h, n ∉ S) ∧
      ∀ w w' : CantorSeq, (∀ i ∈ S, w i = w' i) →
        (ρ.revealed w h.length = h ↔ ρ.revealed w' h.length = h) := by
  classical
  have hfin : {n : ℕ | ∃ x : BitString, x <+: h ∧ x ≠ h ∧ n ∈ ρ.next x}.Finite := by
    have hsub : {n : ℕ | ∃ x : BitString, x <+: h ∧ x ≠ h ∧ n ∈ ρ.next x} ⊆
        ⋃ x ∈ (h.inits.toFinset : Set BitString), {n | n ∈ ρ.next x} := by
      rintro n ⟨x, hxh, hxne, hn⟩
      simp only [Set.mem_iUnion]
      refine ⟨x, ?_, hn⟩
      simpa [List.mem_inits] using hxh
    refine Set.Finite.subset ?_ hsub
    refine Set.Finite.biUnion (Finset.finite_toSet _) (fun x _ => ?_)
    exact (show ({n | n ∈ ρ.next x} : Set ℕ).Subsingleton from
      fun a ha b hb => Part.mem_unique ha hb).finite
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro n hn hnS
    rw [Set.Finite.mem_toFinset] at hnS
    obtain ⟨x, hxh, hxne, hnx⟩ := hnS
    exact ρ.noRepeat x h hxh hxne n hnx n hn rfl
  · have hdir : ∀ w w' : CantorSeq, (∀ i ∈ hfin.toFinset, w i = w' i) →
        ρ.revealed w h.length = h → ρ.revealed w' h.length = h := by
      intro w w' hww' hrev
      rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_path] at hrev ⊢
      intro x c hxc
      obtain ⟨n, hn, hwn⟩ := hrev x c hxc
      refine ⟨n, hn, ?_⟩
      have hmem : n ∈ hfin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact ⟨x, (isMisesKLRandomAt_of_isMartinLofRandom_aux_proper_prefix hxc).1,
            (isMisesKLRandomAt_of_isMartinLofRandom_aux_proper_prefix hxc).2, hn⟩
      rw [← hww' n hmem]
      exact hwn
    intro w w' hww'
    exact ⟨hdir w w' hww', hdir w' w (fun i hi => (hww' i hi).symm)⟩
/-- The restriction of a Cantor sequence to the coordinates in a finite set `S`. -/
private def isMisesKLRandomAt_of_isMartinLofRandom_aux_restrict (S : Finset ℕ) (w : CantorSeq)
    : S → Bool := fun i => w i

private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_measurable_restrict (S : Finset ℕ) :
    Measurable (isMisesKLRandomAt_of_isMartinLofRandom_aux_restrict S) :=
  measurable_pi_iff.2 (fun i => measurable_pi_apply (i : ℕ))

/-- An event depending only on the coordinates in `S` is the preimage of its image under the
restriction to `S`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_eq_preimage (S : Finset ℕ)
    (E : Set CantorSeq)
    (hE : ∀ w w' : CantorSeq, (∀ i ∈ S, w i = w' i) → (w ∈ E ↔ w' ∈ E)) :
    E = isMisesKLRandomAt_of_isMartinLofRandom_aux_restrict S ⁻¹'
        (isMisesKLRandomAt_of_isMartinLofRandom_aux_restrict S '' E) := by
  ext w
  constructor
  · intro hw
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w', hw', hww'⟩
    have hcoord : ∀ i ∈ S, w' i = w i := by
      intro i hi
      have := congrFun hww' ⟨i, hi⟩
      simpa [isMisesKLRandomAt_of_isMartinLofRandom_aux_restrict] using this
    exact (hE w' w hcoord).1 hw'

/-- Step 2a': an event that depends only on finitely many coordinates is measurable. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_measurable (S : Finset ℕ)
    (E : Set CantorSeq)
    (hE : ∀ w w' : CantorSeq, (∀ i ∈ S, w i = w' i) → (w ∈ E ↔ w' ∈ E)) :
    MeasurableSet E := by
  rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_eq_preimage S E hE]
  exact (isMisesKLRandomAt_of_isMartinLofRandom_aux_measurable_restrict S)
    (Set.toFinite (isMisesKLRandomAt_of_isMartinLofRandom_aux_restrict S '' E)).measurableSet

/-! ### Auxiliary material for `isMisesKLRandomAt_of_isMartinLofRandom` -/

open Classical in
/-- The coordinate that `F` reveals after the history `x` (`0` when `F x` is undefined). -/
private noncomputable def isMisesKLRandomAt_of_isMartinLofRandom_pos (ρ : KLRule) (x : BitString) :
    ℕ :=
  if h : (ρ.next x).Dom then (ρ.next x).get h else 0

open Classical in
/-- The factor of the exponential weight contributed by revealing the bit `c` after the history `x`:
`exp (lam * [c = b] - kap)` if the step is *active* (the revealed coordinate is `≥ N0`, the bit is
selected, and fewer than `n` bits have been selected before), and `1` otherwise. -/
private noncomputable def isMisesKLRandomAt_of_isMartinLofRandom_stepFac (ρ : KLRule) (b : Bool)
    (N0 n : ℕ) (lam kap : ℝ) (x : BitString) (c : Bool) : ℝ :=
  if N0 ≤ isMisesKLRandomAt_of_isMartinLofRandom_pos ρ x ∧ x ∈ partialRuleSet ρ.sel ∧
      (selectedBits (partialRuleSet ρ.sel) x).length < n then
    Real.exp (lam * (if c = b then 1 else 0) - kap)
  else 1

/-- The exponential weight of a history `h` of revealed bits: the product of the step factors of
the steps `i < |h|` (history `h.take i`, revealed bit `h[i]`). -/
private noncomputable def isMisesKLRandomAt_of_isMartinLofRandom_gz (ρ : KLRule) (b : Bool)
    (N0 n : ℕ) (lam kap : ℝ) (h : BitString) : ℝ :=
  ∏ i ∈ Finset.range h.length,
    isMisesKLRandomAt_of_isMartinLofRandom_stepFac ρ b N0 n lam kap (h.take i) (h.getD i false)

private lemma isMisesKLRandomAt_of_isMartinLofRandom_gz_nil (ρ : KLRule) (b : Bool)
    (N0 n : ℕ) (lam kap : ℝ) :
    isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap [] = 1 := by
  simp [isMisesKLRandomAt_of_isMartinLofRandom_gz]

private lemma isMisesKLRandomAt_of_isMartinLofRandom_gz_append_singleton (ρ : KLRule) (b : Bool)
    (N0 n : ℕ) (lam kap : ℝ) (x : BitString) (c : Bool) :
    isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap (x ++ [c]) =
      isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap x *
        isMisesKLRandomAt_of_isMartinLofRandom_stepFac ρ b N0 n lam kap x c := by
  unfold isMisesKLRandomAt_of_isMartinLofRandom_gz
  rw [List.length_append, List.length_singleton, Finset.prod_range_succ]
  congr 1
  · refine Finset.prod_congr rfl (fun i hi => ?_)
    have hi' : i < x.length := Finset.mem_range.1 hi
    rw [List.take_append_of_le_length hi'.le, List.getD_append _ _ _ _ hi']
  · simp

/-- Step 3 aux: one position of the certificate check.  `acc` is the list of bits selected so far,
`r1 = EF (h.take i) s`, `r2 = EG (h.take i) s`, `r3 = h[i]?`.  The check passes when the
evaluators have converged, and the queried coordinate `n` of `x` is the bit `h[i]`. -/
private def isMisesKLRandomAt_of_isMartinLofRandom_aux_fin (x : BitString)
    (acc : Option BitString) (r1 : Option ℕ)
    (r2 r3 : Option Bool) : Option BitString :=
  cond (acc.isSome && r1.isSome && r2.isSome && r3.isSome && decide (x[r1.getD 0]? = r3))
    (some (cond (r2.getD false) (acc.getD [] ++ [r3.getD false]) (acc.getD []))) none

/-- Unfolding of the successful case of the check. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_fin_eq_some {x : BitString}
    {acc : Option BitString} {r1 : Option ℕ}
    {r2 r3 : Option Bool} {L' : BitString} :
    isMisesKLRandomAt_of_isMartinLofRandom_aux_fin x acc r1 r2 r3 = some L' ↔
      ∃ (L : BitString) (n : ℕ) (v b : Bool), acc = some L ∧ r1 = some n ∧ r2 = some v ∧
        r3 = some b ∧ x[n]? = some b ∧ L' = cond v (L ++ [b]) L := by
  rcases acc with _ | L <;> rcases r1 with _ | n <;> rcases r2 with _ | v <;>
    rcases r3 with _ | b <;> simp [isMisesKLRandomAt_of_isMartinLofRandom_aux_fin]
  by_cases hxb : x[n]? = some b <;> simp [hxb, eq_comm]

/-- The certificate: runs the check along the positions `0, …, n-1` of `h`, accumulating the
selected bits (a position is selected when the evaluator of `G` answers `true`). -/
private def isMisesKLRandomAt_of_isMartinLofRandom_aux_cert (EF : BitString → ℕ → Option ℕ)
    (EG : BitString → ℕ → Option Bool)
    (s : ℕ) (x h : BitString) (n : ℕ) : Option BitString :=
  Nat.rec (motive := fun _ => Option BitString) (some [])
    (fun i acc => isMisesKLRandomAt_of_isMartinLofRandom_aux_fin x acc (EF (h.take i) s)
                    (EG (h.take i) s) h[i]?) n

private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_zero (EF : BitString → ℕ →
    Option ℕ)
    (EG : BitString → ℕ → Option Bool) (s : ℕ) (x h : BitString) :
    isMisesKLRandomAt_of_isMartinLofRandom_aux_cert EF EG s x h 0 = some [] := rfl

private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_succ (EF : BitString → ℕ →
    Option ℕ)
    (EG : BitString → ℕ → Option Bool) (s : ℕ) (x h : BitString) (i : ℕ) :
    isMisesKLRandomAt_of_isMartinLofRandom_aux_cert EF EG s x h (i + 1) =
      isMisesKLRandomAt_of_isMartinLofRandom_aux_fin x
        (isMisesKLRandomAt_of_isMartinLofRandom_aux_cert EF EG s x h i)
        (EF (h.take i) s) (EG (h.take i) s) h[i]? := rfl

private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_fin_primrec :
    Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool =>
      isMisesKLRandomAt_of_isMartinLofRandom_aux_fin z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) :=
          by
  have hx : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool =>
      z.1) := Primrec.fst
  have hacc : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      z.2.1) := Primrec.fst.comp Primrec.snd
  have hr1 : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool =>
      z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr2 : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool =>
      z.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hr3 : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool =>
      z.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hget : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      z.2.2.1.getD 0) := Primrec.option_getD.comp hr1 (Primrec.const 0)
  have hxn : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool =>
      z.1[z.2.2.1.getD 0]?) := Primrec.list_getElem?.comp hx hget
  have hdec : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      decide (z.1[z.2.2.1.getD 0]? = z.2.2.2.2)) :=
    (Primrec.dom_finite (fun p : Option Bool × Option Bool => decide (p.1 = p.2))).comp
      (Primrec.pair hxn hr3)
  have hc : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool =>
      (z.2.1.isSome && z.2.2.1.isSome && z.2.2.2.1.isSome && z.2.2.2.2.isSome &&
        decide (z.1[z.2.2.1.getD 0]? = z.2.2.2.2))) := by
    refine Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
      (Primrec.option_isSome.comp hacc) (Primrec.option_isSome.comp hr1))
      (Primrec.option_isSome.comp hr2)) (Primrec.option_isSome.comp hr3)) hdec
  have haccd : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      z.2.1.getD []) := Primrec.option_getD.comp hacc (Primrec.const [])
  have hr2d : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      z.2.2.2.1.getD false) := Primrec.option_getD.comp hr2 (Primrec.const false)
  have hr3d : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      z.2.2.2.2.getD false) := Primrec.option_getD.comp hr3 (Primrec.const false)
  have happ : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      z.2.1.getD [] ++ [z.2.2.2.2.getD false]) :=
    Primrec.list_append.comp haccd (Primrec.list_cons.comp hr3d (Primrec.const []))
  have hval : Primrec (fun z : BitString × Option BitString × Option ℕ × Option Bool × Option Bool
      =>
      cond (z.2.2.2.1.getD false) (z.2.1.getD [] ++ [z.2.2.2.2.getD false]) (z.2.1.getD [])) :=
    Primrec.cond hr2d happ haccd
  exact Primrec.cond hc (Primrec.option_some.comp hval) (Primrec.const none)

private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_primrec_decide_eq {α β : Type}
    [Primcodable α] [Primcodable β]
    [DecidableEq β] {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => decide (f a = g a)) :=
  (Primrec.eq.comp hf hg).decide

private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_computable {EF : BitString → ℕ →
    Option ℕ}
    {EG : BitString → ℕ → Option Bool} (hEF : Computable₂ EF) (hEG : Computable₂ EG) :
    Computable (fun c : BitString × ℕ × BitString =>
      isMisesKLRandomAt_of_isMartinLofRandom_aux_cert EF EG c.2.1 c.2.2 c.1 c.1.length) := by
  have hh : Computable (fun c : BitString × ℕ × BitString => c.1) := Computable.fst
  refine Computable.nat_rec (f := fun c : BitString × ℕ × BitString => c.1.length)
    (g := fun _ => some ([] : BitString))
    (h := fun (c : BitString × ℕ × BitString) (p : ℕ × Option BitString) =>
      isMisesKLRandomAt_of_isMartinLofRandom_aux_fin c.2.2 p.2 (EF (c.1.take p.1) c.2.1)
          (EG (c.1.take p.1) c.2.1) c.1[p.1]?)
    (Computable.list_length.comp hh) (Computable.const _) ?_
  -- the step function, as a function of `q = (c, (i, acc))`
  have hq1 : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString => q.1.1) :=
    Computable.fst.comp Computable.fst
  have hqs : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString => q.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hqx : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString => q.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hqi : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString => q.2.1) :=
    Computable.fst.comp Computable.snd
  have hqa : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString => q.2.2) :=
    Computable.snd.comp Computable.snd
  have htake : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString =>
      q.1.1.take q.2.1) :=
    (Primrec.list_take.to_comp : Computable₂ (List.take : ℕ → BitString → BitString)).comp hqi hq1
  have hr1 : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString =>
      EF (q.1.1.take q.2.1) q.1.2.1) := hEF.comp htake hqs
  have hr2 : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString =>
      EG (q.1.1.take q.2.1) q.1.2.1) := hEG.comp htake hqs
  have hr3 : Computable (fun q : (BitString × ℕ × BitString) × ℕ × Option BitString =>
      q.1.1[q.2.1]?) :=
    (Computable.list_getElem? : Computable₂ (fun (l : BitString) (n : ℕ) => l[n]?)).comp hq1 hqi
  have hfin := isMisesKLRandomAt_of_isMartinLofRandom_aux_fin_primrec.to_comp.comp
    (Computable.pair hqx (Computable.pair hqa (Computable.pair hr1 (Computable.pair hr2 hr3))))
  exact hfin

/-- The check of one candidate `c = (h, s, x)` for the string `u`: output `x` when the certificate
passes and `u` is a prefix of the selected bits. -/
private def isMisesKLRandomAt_of_isMartinLofRandom_aux_ok (EF : BitString → ℕ → Option ℕ)
    (EG : BitString → ℕ → Option Bool)
    (a : BitString × BitString × ℕ × BitString) : Option BitString :=
  (isMisesKLRandomAt_of_isMartinLofRandom_aux_cert EF EG a.2.2.1 a.2.2.2 a.2.1
      a.2.1.length).bind fun L =>
    cond (decide (a.1 = L.take a.1.length)) (some a.2.2.2) none

private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_ok_computable {EF : BitString → ℕ →
    Option ℕ}
    {EG : BitString → ℕ → Option Bool} (hEF : Computable₂ EF) (hEG : Computable₂ EG) :
    Computable (isMisesKLRandomAt_of_isMartinLofRandom_aux_ok EF EG) := by
  have hcert := isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_computable hEF hEG
  have hc : Computable (fun a : BitString × BitString × ℕ × BitString =>
      isMisesKLRandomAt_of_isMartinLofRandom_aux_cert EF EG a.2.2.1 a.2.2.2 a.2.1
          a.2.1.length) := hcert.comp Computable.snd
  refine Computable.option_bind hc ?_
  -- last step: a function of `r = (a, L)`
  have hu : Computable (fun r : (BitString × BitString × ℕ × BitString) × BitString => r.1.1) :=
    Computable.fst.comp Computable.fst
  have hL : Computable (fun r : (BitString × BitString × ℕ × BitString) × BitString => r.2) :=
    Computable.snd
  have hx : Computable (fun r : (BitString × BitString × ℕ × BitString) × BitString =>
      r.1.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hdecP : Primrec (fun p : BitString × BitString =>
      decide (p.1 = p.2.take p.1.length)) :=
    isMisesKLRandomAt_of_isMartinLofRandom_aux_primrec_decide_eq (f := fun p : BitString ×
        BitString => p.1)
      (g := fun p : BitString × BitString => p.2.take p.1.length) Primrec.fst
      (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd)
  have hdec : Computable (fun r : (BitString × BitString × ℕ × BitString) × BitString =>
      decide (r.1.1 = r.2.take r.1.1.length)) :=
    Computable.comp (f := fun p : BitString × BitString => decide (p.1 = p.2.take p.1.length))
      (g := fun r : (BitString × BitString × ℕ × BitString) × BitString => (r.1.1, r.2))
      hdecP.to_comp (Computable.pair hu hL)
  exact Computable.cond (c := fun r : (BitString × BitString × ℕ × BitString) × BitString =>
      decide (r.1.1 = r.2.take r.1.1.length))
    (f := fun r : (BitString × BitString × ℕ × BitString) × BitString => some r.1.2.2.2)
    (g := fun _ => none) hdec (Computable.option_some.comp hx) (Computable.const none)

/-- The enumeration of cylinders: decode a candidate `(h, s, x)`, run the certificate, and output
`x` when `u` is a prefix of the selected bits. -/
private def isMisesKLRandomAt_of_isMartinLofRandom_aux_f (EF : BitString → ℕ → Option ℕ)
    (EG : BitString → ℕ → Option Bool)
    (u : BitString) (j : ℕ) : Option BitString :=
  (Encodable.decode j : Option (BitString × ℕ × BitString)).bind fun c =>
    (isMisesKLRandomAt_of_isMartinLofRandom_aux_cert EF EG c.2.1 c.2.2 c.1 c.1.length).bind
        fun L =>
      cond (decide (u = L.take u.length)) (some c.2.2) none

private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_f_computable {EF : BitString → ℕ →
    Option ℕ}
    {EG : BitString → ℕ → Option Bool} (hEF : Computable₂ EF) (hEG : Computable₂ EG) :
    Computable₂ (isMisesKLRandomAt_of_isMartinLofRandom_aux_f EF EG) := by
  have hok := isMisesKLRandomAt_of_isMartinLofRandom_aux_ok_computable hEF hEG
  have hdec : Computable (fun a : BitString × ℕ =>
      (Encodable.decode a.2 : Option (BitString × ℕ × BitString))) :=
    Computable.decode.comp Computable.snd
  have hg : Computable₂ (fun (a : BitString × ℕ) (c : BitString × ℕ × BitString) =>
      isMisesKLRandomAt_of_isMartinLofRandom_aux_ok EF EG (a.1, c)) :=
    Computable.comp (f := isMisesKLRandomAt_of_isMartinLofRandom_aux_ok EF EG)
      (g := fun p : (BitString × ℕ) × (BitString × ℕ × BitString) => (p.1.1, p.2)) hok
      (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  exact Computable.option_bind (f := fun a : BitString × ℕ =>
      (Encodable.decode a.2 : Option (BitString × ℕ × BitString)))
    (g := fun (a : BitString × ℕ) (c : BitString × ℕ × BitString) =>
      isMisesKLRandomAt_of_isMartinLofRandom_aux_ok EF EG (a.1, c)) hdec hg

/-! ### Soundness of the certificate -/

/-- Unfolding of `cert (i+1) = some L'`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_succ_eq_some {EF : BitString →
    ℕ → Option ℕ}
    {EG : BitString → ℕ → Option Bool} {s : ℕ} {x h : BitString} {i : ℕ} {L' : BitString} :
    isMisesKLRandomAt_of_isMartinLofRandom_aux_cert EF EG s x h (i + 1) = some L' ↔
      ∃ (L : BitString) (n : ℕ) (v b : Bool), isMisesKLRandomAt_of_isMartinLofRandom_aux_cert
          EF EG s x h i = some L ∧
        EF (h.take i) s = some n ∧ EG (h.take i) s = some v ∧ h[i]? = some b ∧
        x[n]? = some b ∧ L' = cond v (L ++ [b]) L := by
  rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_succ,
    isMisesKLRandomAt_of_isMartinLofRandom_aux_fin_eq_some]

/-- If the certificate succeeds, each of the first `i` positions of `h` was checked: the evaluators
converged and the queried coordinate of `x` is the bit of `h`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_loc {EF : BitString → ℕ →
    Option ℕ}
    {EG : BitString → ℕ → Option Bool} {s : ℕ} {x h : BitString} :
    ∀ (i : ℕ) (L : BitString), isMisesKLRandomAt_of_isMartinLofRandom_aux_cert EF EG s x h i =
        some L →
      ∀ j, j < i → ∃ (n : ℕ) (v b : Bool), EF (h.take j) s = some n ∧ EG (h.take j) s = some v ∧
        h[j]? = some b ∧ x[n]? = some b := by
  intro i
  induction i with
  | zero => intro L _ j hj; omega
  | succ i ih =>
    intro L' hL' j hj
    obtain ⟨L, n, v, b, hL, hn, hv, hb, hxb, -⟩ :=
        isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_succ_eq_some.1 hL'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hji | hji
    · exact ih L hL j hji
    · subst hji
      exact ⟨n, v, b, hn, hv, hb, hxb⟩

/-- A prefix of a prefix. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_prefix_take {y h : BitString} {i : ℕ}
    (hy : y <+: h.take i) :
    y.length ≤ i ∧ y = h.take y.length := by
  have hle : y.length ≤ (h.take i).length := hy.length_le
  have hlen : y.length ≤ i := le_trans hle (List.length_take_le _ _)
  refine ⟨hlen, ?_⟩
  have hy' := List.prefix_iff_eq_take.1 hy
  rw [List.take_take, min_eq_left hlen] at hy'
  exact hy'

/-- The selected bits of a successful certificate are those of the rule `G`, and `G` is defined
on all the prefixes checked. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_selected (ρ : KLRule)
    {EF : BitString → ℕ → Option ℕ}
    {EG : BitString → ℕ → Option Bool}
    (hEGs : ∀ (a : BitString) (v : Bool), v ∈ ρ.sel a ↔ ∃ s, EG a s = some v)
    {s : ℕ} {x h : BitString} :
    ∀ (i : ℕ) (L : BitString), isMisesKLRandomAt_of_isMartinLofRandom_aux_cert EF EG s x h i =
        some L →
      (∀ j, j < i → (ρ.sel (h.take j)).Dom) ∧
        L = selectedBits (partialRuleSet ρ.sel) (h.take i) := by
  intro i
  induction i with
  | zero =>
    intro L hL
    refine ⟨fun j hj => by omega, ?_⟩
    have hL0 : L = [] := by
      have : isMisesKLRandomAt_of_isMartinLofRandom_aux_cert EF EG s x h 0 = some [] := rfl
      rw [this] at hL
      exact (Option.some.inj hL).symm
    simp [hL0, selectedBits, selectedAux]
  | succ i ih =>
    intro L' hL'
    obtain ⟨L, n, v, b, hL, hn, hv, hb, hxb, hL'eq⟩ :=
        isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_succ_eq_some.1 hL'
    obtain ⟨hdom, hLsel⟩ := ih L hL
    have hvmem : v ∈ ρ.sel (h.take i) := (hEGs _ _).2 ⟨s, hv⟩
    have hdomi : (ρ.sel (h.take i)).Dom := Part.dom_iff_mem.2 ⟨v, hvmem⟩
    refine ⟨?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hji | hji
      · exact hdom j hji
      · subst hji; exact hdomi
    · have htake : h.take (i + 1) = h.take i ++ [b] := by
        rw [List.take_add_one, hb]; rfl
      have hmem : h.take i ∈ partialRuleSet ρ.sel ↔ v = true := by
        constructor
        · rintro ⟨-, ht⟩
          exact Part.mem_unique hvmem ht
        · rintro rfl
          refine ⟨fun y hy => ?_, hvmem⟩
          obtain ⟨hyi, hyeq⟩ := isMisesKLRandomAt_of_isMartinLofRandom_aux_prefix_take hy
          rw [hyeq]
          rcases Nat.lt_or_ge y.length i with hlt | hge
          · exact hdom _ hlt
          · have : y.length = i := le_antisymm hyi hge
            rw [this]; exact hdomi
      rw [htake, selectedBits_append_singleton, hL'eq, hLsel]
      cases v
      · have : ¬ (h.take i ∈ partialRuleSet ρ.sel) := fun hh => by simpa using hmem.1 hh
        simp [this]
      · have : h.take i ∈ partialRuleSet ρ.sel := hmem.2 rfl
        simp [this]

open Classical in
/-- If `w` follows the path `h` (each revealed coordinate holds the next bit of `h`), then the
revealed string of `w` after `i ≤ |h|` steps is the prefix of `h` of length `i`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_of_path (ρ : KLRule)
    (w : CantorSeq) (h : BitString)
    (hpath : ∀ (i : ℕ) (hi : i < h.length), ∃ n ∈ ρ.next (h.take i), w n = h[i]) :
    ∀ i, i ≤ h.length → ρ.revealed w i = h.take i := by
  intro i
  induction i with
  | zero => intro _; simp [KLRule.revealed]
  | succ i ih =>
    intro hi
    have hi' : i < h.length := hi
    have h1 : ρ.revealed w i = h.take i := ih (Nat.le_of_lt hi')
    obtain ⟨n, hn, hwn⟩ := hpath i hi'
    have hdom : (ρ.next (h.take i)).Dom := Part.dom_iff_mem.2 ⟨n, hn⟩
    have hget : (ρ.next (h.take i)).get hdom = n := Part.get_eq_of_mem hn hdom
    have key : ∀ x : BitString, x = h.take i →
        (if hd : (ρ.next x).Dom then x ++ [w ((ρ.next x).get hd)] else x) =
          h.take i ++ [w n] := by
      intro x hx
      subst hx
      rw [dite_eq_left hdom, hget]
    have hstep : ρ.revealed w (i + 1) = h.take i ++ [w n] := by
      rw [KLRule.revealed]
      exact key _ h1
    rw [hstep, hwn, List.take_add_one, List.getElem?_eq_getElem hi']
    rfl

/-- **Soundness.**  If candidate `j` passes the check for `u` and outputs `x`, every `w` in the
cylinder of `x` has `u` as a prefix of its selected bits at some time. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_sound (ρ : KLRule) {EF : BitString →
    ℕ → Option ℕ}
    {EG : BitString → ℕ → Option Bool}
    (hEFs : ∀ (a : BitString) (v : ℕ), v ∈ ρ.next a ↔ ∃ s, EF a s = some v)
    (hEGs : ∀ (a : BitString) (v : Bool), v ∈ ρ.sel a ↔ ∃ s, EG a s = some v)
    (u : BitString) (j : ℕ) (x : BitString) (hj : isMisesKLRandomAt_of_isMartinLofRandom_aux_f
        EF EG u j = some x)
    (w : CantorSeq) (hw : w ∈ cantorCylinder x) : ∃ t, u <+: ρ.outputChain w t := by
  unfold isMisesKLRandomAt_of_isMartinLofRandom_aux_f at hj
  rw [Option.bind_eq_some_iff] at hj
  obtain ⟨c, hc, hj⟩ := hj
  rw [Option.bind_eq_some_iff] at hj
  obtain ⟨L, hL, hj⟩ := hj
  obtain ⟨h, s, x'⟩ := c
  simp only at hL hj
  have hdec : decide (u = L.take u.length) = true ∧ x' = x := by
    cases hd : decide (u = L.take u.length)
    · rw [hd] at hj; simp at hj
    · rw [hd, Bool.cond_true] at hj
      exact ⟨rfl, Option.some.inj hj⟩
  obtain ⟨hdec, rfl⟩ := hdec
  have hu : u <+: L := List.prefix_iff_eq_take.2 (of_decide_eq_true hdec)
  have hloc := isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_loc h.length L hL
  have hpath : ∀ (i : ℕ) (hi : i < h.length), ∃ n ∈ ρ.next (h.take i), w n = h[i] := by
    intro i hi
    obtain ⟨n, v, b, hn, -, hb, hxb⟩ := hloc i hi
    refine ⟨n, (hEFs _ _).2 ⟨s, hn⟩, ?_⟩
    have hb' : h[i] = b := by
      rw [List.getElem?_eq_getElem hi] at hb
      exact Option.some.inj hb
    have hnx : n < x'.length := by
      by_contra hcon
      rw [List.getElem?_eq_none (not_lt.1 hcon)] at hxb
      exact absurd hxb (by simp)
    rw [List.getElem?_eq_getElem hnx] at hxb
    have hxb' : x'[n] = b := Option.some.inj hxb
    rw [hb', ← hxb']
    exact hw n hnx
  have hrev := isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_of_path ρ w h hpath
      h.length le_rfl
  rw [List.take_length] at hrev
  obtain ⟨-, hLsel⟩ := isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_selected ρ hEGs
      h.length L hL
  rw [List.take_length] at hLsel
  refine ⟨h.length, ?_⟩
  have : ρ.outputChain w h.length = L := by
    unfold KLRule.outputChain
    rw [hrev, hLsel]
  rw [this]
  exact hu
/-- Step 3a: step-bounded evaluation of a partial computable function. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_stepEval {α σ : Type} [Primcodable α]
    [Primcodable σ] {f : α →. σ}
    (hf : Partrec f) :
    ∃ E : α → ℕ → Option σ, Computable₂ E ∧
      (∀ (a : α) (s t : ℕ) (v : σ), s ≤ t → E a s = some v → E a t = some v) ∧
      (∀ (a : α) (v : σ), v ∈ f a ↔ ∃ s, E a s = some v) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  have hevalr : ∀ a : α,
      Nat.Partrec.Code.eval c (Encodable.encode a) = Part.map Encodable.encode (f a) := by
    intro a
    simp only [hc]
    rw [Encodable.encodek]
    simp
  refine ⟨fun a s => (Nat.Partrec.Code.evaln s c (Encodable.encode a)).bind
    (fun m => Encodable.decode (α := σ) m), ?_, ?_, ?_⟩
  · have hsnd : Primrec (fun x : α × ℕ => x.2) := Primrec.snd
    have hfst : Primrec (fun x : α × ℕ => x.1) := Primrec.fst
    have h_prim := Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair hsnd (Primrec.const c)) (Primrec.encode.comp hfst))
    exact Computable.option_bind (Primrec.to_comp h_prim)
      (Computable.decode.comp Computable.snd)
  · intro a s t v hst h
    simp only at h ⊢
    rcases hev : Nat.Partrec.Code.evaln s c (Encodable.encode a) with _ | m
    · rw [hev] at h; simp at h
    · have hmono : Nat.Partrec.Code.evaln t c (Encodable.encode a) = some m :=
        Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hst (Option.mem_def.mpr hev))
      rw [hev] at h
      rw [hmono]
      exact h
  · intro a v
    simp only
    constructor
    · intro hv
      have hmem : (Encodable.encode v) ∈ Nat.Partrec.Code.eval c (Encodable.encode a) := by
        rw [hevalr a]
        exact Part.mem_map _ hv
      obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
      refine ⟨s, ?_⟩
      rw [Option.mem_def.mp hs]
      simp only [Option.bind]
      exact Encodable.encodek v
    · rintro ⟨s, hs⟩
      rcases hev : Nat.Partrec.Code.evaln s c (Encodable.encode a) with _ | m
      · rw [hev] at hs; simp at hs
      · rw [hev] at hs
        have hdec : (Encodable.decode (α := σ) m) = some v := hs
        have hmem : m ∈ Nat.Partrec.Code.eval c (Encodable.encode a) :=
          Nat.Partrec.Code.evaln_complete.mpr ⟨s, Option.mem_def.mpr hev⟩
        rw [hevalr a] at hmem
        obtain ⟨x, hx, hxm⟩ := (Part.mem_map_iff _).mp hmem
        have hxq : x = v := by
          have hd2 : (Encodable.decode (α := σ) (Encodable.encode x)) = some v := by
            rw [hxm]; exact hdec
          rw [Encodable.encodek] at hd2
          exact Option.some_injective _ hd2
        rwa [← hxq]

/-- Aux: at the time equal to the length of a revealed string, the revealed string is the same. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_fix (ρ : KLRule)
    (w : CantorSeq) (t : ℕ) :
    ρ.revealed w (ρ.revealed w t).length = ρ.revealed w t := by
  induction t with
  | zero => simp [KLRule.revealed]
  | succ t ih =>
    by_cases hd : (ρ.next (ρ.revealed w t)).Dom
    · have hlen := isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_length_eq ρ w t hd
      rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_dom ρ w t hd]
      simp only [List.length_append, List.length_singleton, hlen]
      exact isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_dom ρ w t hd
    · rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_not_dom ρ w t hd]
      exact ih

/-- Aux: membership in `partialRuleSet`, unfolded. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_mem_partialRuleSet
    {r : BitString →. Bool} {x : BitString} :
    x ∈ partialRuleSet r ↔ (∀ y, y <+: x → (r y).Dom) ∧ true ∈ r x := Iff.rfl

/-- Aux: a common stage for finitely many monotone requirements. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_common_stage (P : ℕ → ℕ → Prop)
    (hmono : ∀ k s t, s ≤ t → P k s → P k t) :
    ∀ m : ℕ, (∀ k, k < m → ∃ s, P k s) → ∃ s, ∀ k, k < m → P k s := by
  intro m
  induction m with
  | zero => intro _; exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro h
    obtain ⟨s1, hs1⟩ := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    obtain ⟨s2, hs2⟩ := h m (Nat.lt_succ_self m)
    refine ⟨max s1 s2, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact hmono _ _ _ (le_max_left _ _) (hs1 k hk)
    · exact hmono _ _ _ (le_max_right _ _) hs2

/-- Aux: the certificate computes the selected bits of the prefix. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_eq (ρ : KLRule)
    (EF : BitString → ℕ → Option ℕ) (EG : BitString → ℕ → Option Bool)
    (hGsound : ∀ (a : BitString) (s : ℕ) (v : Bool), EG a s = some v → v ∈ ρ.sel a)
    (s : ℕ) (x h : BitString)
    (hcond : ∀ k, (hk : k < h.length) → ∃ (n : ℕ) (v : Bool),
        EF (h.take k) s = some n ∧ x[n]? = some h[k] ∧ EG (h.take k) s = some v) :
    ∀ i, i ≤ h.length →
      isMisesKLRandomAt_of_isMartinLofRandom_aux_cert EF EG s x h i =
          some (selectedBits (partialRuleSet ρ.sel) (h.take i)) := by
  intro i
  induction i with
  | zero => intro _; simp [isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_zero, selectedBits,
              selectedAux]
  | succ i ih =>
    intro hi
    have hi' : i < h.length := hi
    have ih' := ih (Nat.le_of_lt hi')
    obtain ⟨n, v, hn, hx, hv⟩ := hcond i hi'
    have hvmem : v ∈ ρ.sel (h.take i) := hGsound _ _ _ hv
    have hmem : h.take i ∈ partialRuleSet ρ.sel ↔ v = true := by
      constructor
      · intro hh
        exact Part.mem_unique hvmem
            ((isMisesKLRandomAt_of_isMartinLofRandom_aux_mem_partialRuleSet.mp hh).2)
      · intro hvt
        refine isMisesKLRandomAt_of_isMartinLofRandom_aux_mem_partialRuleSet.mpr ⟨?_, hvt ▸
            hvmem⟩
        intro y hy
        have hy' : y = h.take (min y.length i) := by
          have h1 : y = (h.take i).take y.length := List.prefix_iff_eq_take.mp hy
          rw [List.take_take] at h1
          exact h1
        have hlt : min y.length i < h.length := lt_of_le_of_lt (min_le_right _ _) hi'
        obtain ⟨_, v', -, -, hv'⟩ := hcond _ hlt
        rw [hy']
        exact Part.dom_iff_mem.mpr ⟨v', hGsound _ _ _ hv'⟩
    have htk : h.take (i + 1) = h.take i ++ [h[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi']
      rfl
    rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_succ, ih', hn, hv,
        List.getElem?_eq_getElem hi',
      isMisesKLRandomAt_of_isMartinLofRandom_aux_fin_eq_some]
    refine ⟨selectedBits (partialRuleSet ρ.sel) (h.take i), n, v, h[i], rfl, rfl, rfl, rfl, hx, ?_⟩
    rw [htk, selectedBits_append_singleton]
    by_cases hvt : v = true
    · have hR : h.take i ∈ partialRuleSet ρ.sel := hmem.mpr hvt
      simp [hvt, hR]
    · have hR : h.take i ∉ partialRuleSet ρ.sel := fun hh => hvt (hmem.mp hh)
      have hvf : v = false := by simpa using hvt
      simp [hvf, hR]

/-- Step 3 aux (completeness): if `u` is a prefix of the selected bits of `w` after some time,
the enumeration `isMisesKLRandomAt_of_isMartinLofRandom_aux_f` produces a cylinder containing
`w`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_complete (ρ : KLRule)
    (EF : BitString → ℕ → Option ℕ) (EG : BitString → ℕ → Option Bool)
    (hFmono : ∀ (a : BitString) (s t : ℕ) (v : ℕ), s ≤ t → EF a s = some v → EF a t = some v)
    (hFspec : ∀ (a : BitString) (v : ℕ), v ∈ ρ.next a ↔ ∃ s, EF a s = some v)
    (hGmono : ∀ (a : BitString) (s t : ℕ) (v : Bool), s ≤ t → EG a s = some v → EG a t = some v)
    (hGspec : ∀ (a : BitString) (v : Bool), v ∈ ρ.sel a ↔ ∃ s, EG a s = some v)
    (u : BitString) (w : CantorSeq) (t : ℕ) (hu : u <+: ρ.outputChain w t) :
    ∃ (j : ℕ) (x : BitString), isMisesKLRandomAt_of_isMartinLofRandom_aux_f EF EG u j =
        some x ∧ w ∈ cantorCylinder x := by
  classical
  set R := partialRuleSet ρ.sel with hR
  set H := ρ.revealed w t with hH
  have hpath : ∀ (x : BitString) (c : Bool), x ++ [c] <+: H → ∃ n ∈ ρ.next x, w n = c :=
    (isMisesKLRandomAt_of_isMartinLofRandom_aux_path ρ w H).mp
        (isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_fix ρ w t)
  have hu' : u <+: selectedBits R H := hu
  have hex : ∃ m, u <+: selectedBits R (H.take m) :=
    ⟨H.length, by rwa [List.take_length]⟩
  set m := Nat.find hex with hm
  have hmspec : u <+: selectedBits R (H.take m) := Nat.find_spec hex
  have hmle : m ≤ H.length := Nat.find_min' hex (by rwa [List.take_length])
  have hmin : ∀ k, k < m → ¬ u <+: selectedBits R (H.take k) := fun k hk => Nat.find_min hex hk
  have hdomm : ∀ k, k < m → (ρ.sel (H.take k)).Dom := by
    intro k hk
    have hq : m - 1 < H.length := by omega
    have htm : H.take m = H.take (m - 1) ++ [H[m - 1]] := by
      have hm1 : m = (m - 1) + 1 := by omega
      conv_lhs => rw [hm1]
      rw [List.take_add_one, List.getElem?_eq_getElem hq]
      rfl
    have hRq : H.take (m - 1) ∈ R := by
      by_contra hnot
      apply hmin (m - 1) (by omega)
      rw [htm, selectedBits_append_singleton, ite_eq_right hnot, List.append_nil] at hmspec
      exact hmspec
    refine (isMisesKLRandomAt_of_isMartinLofRandom_aux_mem_partialRuleSet.mp hRq).1 (H.take k)
        ?_
    have hk' : H.take k = (H.take (m - 1)).take k := by
      rw [List.take_take]
      congr 1
      omega
    rw [hk']
    exact List.take_prefix _ _
  have hQ : ∀ k, k < m → ∃ M, ∃ (n : ℕ) (v b : Bool), H[k]? = some b ∧
      EF (H.take k) M = some n ∧ n < M ∧ w n = b ∧ EG (H.take k) M = some v := by
    intro k hk
    have hkH : k < H.length := lt_of_lt_of_le hk hmle
    have hpre : H.take k ++ [H[k]] <+: H := by
      have htk : H.take (k + 1) = H.take k ++ [H[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hkH]
        rfl
      rw [← htk]
      exact List.take_prefix _ _
    obtain ⟨n, hn, hwn⟩ := hpath _ _ hpre
    obtain ⟨s1, hs1⟩ := (hFspec _ _).mp hn
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp (hdomm k hk)
    obtain ⟨s2, hs2⟩ := (hGspec _ _).mp hv
    refine ⟨max (max s1 s2) (n + 1), n, v, H[k], List.getElem?_eq_getElem hkH, ?_, ?_, hwn, ?_⟩
    · exact hFmono _ _ _ _ ((le_max_left _ _).trans (le_max_left _ _)) hs1
    · exact lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)
    · exact hGmono _ _ _ _ ((le_max_right _ _).trans (le_max_left _ _)) hs2
  obtain ⟨M, hM⟩ := isMisesKLRandomAt_of_isMartinLofRandom_aux_common_stage
    (fun k M => ∃ (n : ℕ) (v b : Bool), H[k]? = some b ∧
      EF (H.take k) M = some n ∧ n < M ∧ w n = b ∧ EG (H.take k) M = some v)
    (fun k s t hst ⟨n, v, b, h1, h2, h3, h4, h5⟩ =>
      ⟨n, v, b, h1, hFmono _ _ _ _ hst h2, lt_of_lt_of_le h3 hst, h4, hGmono _ _ _ _ hst h5⟩)
    m hQ
  have hlen : (H.take m).length = m := by
    rw [List.length_take]
    exact min_eq_left hmle
  have htake : ∀ k, k ≤ m → (H.take m).take k = H.take k := fun k hk => by
    rw [List.take_take, min_eq_left hk]
  have hcert := isMisesKLRandomAt_of_isMartinLofRandom_aux_cert_eq ρ EF EG
      (fun a s v hv => (hGspec a v).mpr ⟨s, hv⟩) M
    (cantorPrefix w M) (H.take m) ?_ (H.take m).length le_rfl
  · rw [List.take_length] at hcert
    refine ⟨Encodable.encode (H.take m, M, cantorPrefix w M), cantorPrefix w M, ?_,
      mem_cantorCylinder_cantorPrefix w M⟩
    unfold isMisesKLRandomAt_of_isMartinLofRandom_aux_f
    rw [Encodable.encodek]
    simp only [Option.bind_some]
    rw [hcert]
    simp only [Option.bind_some]
    have hu_eq : u = (selectedBits R (H.take m)).take u.length :=
      List.prefix_iff_eq_take.mp hmspec
    have hdec : decide (u = (selectedBits R (H.take m)).take u.length) = true :=
      decide_eq_true hu_eq
    rw [hdec]
    rfl
  · intro k hk
    have hkm : k < m := by rw [hlen] at hk; exact hk
    obtain ⟨n, v, b, hb, hn1, hn2, hn3, hv⟩ := hM k hkm
    have hkH : k < H.length := lt_of_lt_of_le hkm hmle
    have hget : (H.take m)[k] = b := by
      have h1 : (H.take m)[k] = H[k] := List.getElem_take ..
      have h2 : H[k]? = some H[k] := List.getElem?_eq_getElem hkH
      rw [h2] at hb
      rw [h1]
      exact Option.some.inj hb
    have hxn : (cantorPrefix w M)[n]? = some (w n) := by
      have hn' : n < (cantorPrefix w M).length := by
        rw [cantorPrefix_length]
        exact hn2
      rw [List.getElem?_eq_getElem hn', cantorPrefix_getElem]
    refine ⟨n, v, by rw [htake k hkm.le]; exact hn1, ?_, by rw [htake k hkm.le]; exact hv⟩
    rw [hxn, hget, hn3]

/-- Step 3b: the events `{w | ∃ t, u <+: outputChain w t}` are uniformly effectively open for an
admissible rule. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_effopen {ρ : KLRule}
    (hρ : ρ.IsAdmissible) :
    ∃ f : BitString → ℕ → Option BitString, Computable₂ f ∧
      ∀ u : BitString, {w : CantorSeq | ∃ t, u <+: ρ.outputChain w t} =
        ⋃ i, (f u i).elim ∅ cantorCylinder := by
  obtain ⟨hF, hG⟩ := hρ
  obtain ⟨EF, hEFc, hEFm, hEFs⟩ := isMisesKLRandomAt_of_isMartinLofRandom_stepEval hF
  obtain ⟨EG, hEGc, hEGm, hEGs⟩ := isMisesKLRandomAt_of_isMartinLofRandom_stepEval hG
  refine ⟨isMisesKLRandomAt_of_isMartinLofRandom_aux_f EF EG,
      isMisesKLRandomAt_of_isMartinLofRandom_aux_f_computable hEFc hEGc, fun u => ?_⟩
  ext w
  constructor
  · intro hw
    obtain ⟨t, hu⟩ := hw
    obtain ⟨j, x, hj, hwx⟩ := isMisesKLRandomAt_of_isMartinLofRandom_aux_complete ρ EF EG hEFm
        hEFs hEGm hEGs u w t hu
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    rw [hj]
    exact hwx
  · intro hw
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hw
    cases hfj : isMisesKLRandomAt_of_isMartinLofRandom_aux_f EF EG u j with
    | none => rw [hfj] at hj; simp at hj
    | some x =>
      rw [hfj] at hj
      exact isMisesKLRandomAt_of_isMartinLofRandom_aux_sound ρ hEFs hEGs u j x hfj w hj

/-- The coordinates of a Cantor sequence are independent under independent trials. -/
lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_iIndep {p : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) :
    ProbabilityTheory.iIndepFun (fun (i : ℕ) (w : CantorSeq) => w i) (independentTrials p hp) :=
  ProbabilityTheory.iIndepFun_infinitePi (X := fun _ : ℕ => (id : Bool → Bool))
    (fun _ => measurable_id)

/-- The probability that the `n`-th coordinate is `b` under independent trials. -/
lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_coord_mass {p : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (n : ℕ) (b : Bool) :
    independentTrials p hp {w : CantorSeq | w n = b} =
      ENNReal.ofReal (if b then (p n : ℝ) else 1 - (p n : ℝ)) := by
  have hmp := measurePreserving_eval_infinitePi
    (fun i : ℕ => ProbabilityTheory.bernoulliMeasure true false
      ⟨p i, (p i).2, NNReal.coe_le_one.mpr (hp i)⟩) n
  have h1 : {w : CantorSeq | w n = b} = (Function.eval n : CantorSeq → Bool) ⁻¹' {b} := by
    ext w
    simp [Function.eval]
  unfold independentTrials
  rw [h1, hmp.measure_preimage (measurableSet_singleton b).nullMeasurableSet]
  cases b
  · rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem _
      (measurableSet_singleton false) (by simp) rfl]
    have hcoe : unitInterval.toNNReal
        (unitInterval.symm ⟨p n, (p n).2, NNReal.coe_le_one.mpr (hp n)⟩) = 1 - p n := by
      ext
      simp [unitInterval.coe_symm_eq, NNReal.coe_sub (hp n)]
    rw [hcoe]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h2 : ((1 - p n : NNReal) : ℝ) = 1 - (p n : ℝ) := by
      rw [NNReal.coe_sub (hp n), NNReal.coe_one]
    rw [← h2, ENNReal.ofReal_coe_nnreal]
  · rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem _
      (measurableSet_singleton true) rfl (by simp)]
    have hcoe : unitInterval.toNNReal
        (⟨p n, (p n).2, NNReal.coe_le_one.mpr (hp n)⟩ : unitInterval) = p n := rfl
    rw [hcoe]
    simp only [↓reduceIte]
    exact (ENNReal.ofReal_coe_nnreal).symm

/-- Step 2a of the proof of `isMisesKLRandomAt_of_isMartinLofRandom`: under independent
trials, a coordinate `n ∉ S` is independent of an event depending only on the coordinates in the
finite set `S`; the mass of the coordinate is `p n` (resp. `1 - p n`). -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_indep {p : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (S : Finset ℕ) (n : ℕ) (hn : n ∉ S) (E : Set CantorSeq)
    (hE : ∀ w w' : CantorSeq, (∀ i ∈ S, w i = w' i) → (w ∈ E ↔ w' ∈ E)) (b : Bool) :
    independentTrials p hp (E ∩ {w | w n = b}) =
      independentTrials p hp E * ENNReal.ofReal (if b then (p n : ℝ) else 1 - (p n : ℝ)) := by
  classical
  have hdisj : Disjoint S ({n} : Finset ℕ) := Finset.disjoint_singleton_right.2 hn
  have h := (isMisesKLRandomAt_of_isMartinLofRandom_aux_iIndep hp).indepFun_finset S {n}
    hdisj (fun i => measurable_pi_apply i)
  let E' : Set (S → Bool) := isMisesKLRandomAt_of_isMartinLofRandom_aux_restrict S '' E
  let t : Set (({n} : Finset ℕ) → Bool) :=
    {x | x ⟨n, Finset.mem_singleton_self n⟩ = b}
  have hE' : MeasurableSet E' := (Set.toFinite E').measurableSet
  have ht : MeasurableSet t := (Set.toFinite t).measurableSet
  have hEeq : E = isMisesKLRandomAt_of_isMartinLofRandom_aux_restrict S ⁻¹' E' :=
    isMisesKLRandomAt_of_isMartinLofRandom_aux_eq_preimage S E hE
  have hteq : {w : CantorSeq | w n = b} =
      (fun (w : CantorSeq) (i : ({n} : Finset ℕ)) => w i) ⁻¹' t := by
    ext w
    simp [t]
  have key := h.measure_inter_preimage_eq_mul E' t hE' ht
  have key' : independentTrials p hp (E ∩ {w | w n = b}) =
      independentTrials p hp E * independentTrials p hp {w : CantorSeq | w n = b} := by
    rw [hteq, hEeq]
    exact key
  rw [key', isMisesKLRandomAt_of_isMartinLofRandom_aux_coord_mass hp n b]

/-- Step 2b of the proof of `isMisesKLRandomAt_of_isMartinLofRandom`: the scenario
`{w | ρ.revealed w t = h}` is measurable. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_cell_measurable (ρ : KLRule) (t : ℕ)
    (h : BitString) : MeasurableSet {w : CantorSeq | ρ.revealed w t = h} := by
  classical
  induction t generalizing h with
  | zero =>
    by_cases hh : ([] : BitString) = h
    · have hs : {w : CantorSeq | ρ.revealed w 0 = h} = Set.univ := by
        ext w
        simp [KLRule.revealed, hh]
      rw [hs]
      exact MeasurableSet.univ
    · have hs : {w : CantorSeq | ρ.revealed w 0 = h} = ∅ := by
        ext w
        simp [KLRule.revealed, hh]
      rw [hs]
      exact MeasurableSet.empty
  | succ t ih =>
    have hstep : ∀ w : CantorSeq, ρ.revealed w (t + 1) =
        if hd : (ρ.next (ρ.revealed w t)).Dom then
          ρ.revealed w t ++ [w ((ρ.next (ρ.revealed w t)).get hd)] else ρ.revealed w t := by
      intro w
      by_cases hd : (ρ.next (ρ.revealed w t)).Dom
      · rw [dite_eq_left hd]
        exact isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_dom ρ w t hd
      · rw [dite_eq_right hd]
        exact isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_not_dom ρ w t hd
    have hset : {w : CantorSeq | ρ.revealed w (t + 1) = h} =
        ⋃ x : BitString, ({w : CantorSeq | ρ.revealed w t = x} ∩
          {w : CantorSeq | (if hd : (ρ.next x).Dom then x ++ [w ((ρ.next x).get hd)] else x) = h})
              := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hw
        refine ⟨ρ.revealed w t, rfl, ?_⟩
        rw [hstep w] at hw
        exact hw
      · rintro ⟨x, hx, hxh⟩
        rw [hstep w, hx]
        exact hxh
    rw [hset]
    refine MeasurableSet.iUnion (fun x => (ih x).inter ?_)
    by_cases hd : (ρ.next x).Dom
    · have hs : {w : CantorSeq | (if hd' : (ρ.next x).Dom then
            x ++ [w ((ρ.next x).get hd')] else x) = h} =
          (fun w : CantorSeq => w ((ρ.next x).get hd)) ⁻¹' {c : Bool | x ++ [c] = h} := by
        ext w
        simp [hd]
      rw [hs]
      exact (measurable_pi_apply _) (MeasurableSet.of_discrete)
    · by_cases hxh : x = h
      · have hs : {w : CantorSeq | (if hd' : (ρ.next x).Dom then
              x ++ [w ((ρ.next x).get hd')] else x) = h} = Set.univ := by
          ext w
          subst hxh
          simp [hd]
        rw [hs]
        exact MeasurableSet.univ
      · have hs : {w : CantorSeq | (if hd' : (ρ.next x).Dom then
              x ++ [w ((ρ.next x).get hd')] else x) = h} = ∅ := by
          ext w
          simp [hd, hxh]
        rw [hs]
        exact MeasurableSet.empty

/-- Auxiliary real inequality of the supermartingale step: with `E = exp lam`, `K = 1 + a (E - 1)`,
`(E/K) * pi + (1/K) * (1 - pi) ≤ 1` (resp. with the roles of the two bits exchanged) when the
probability of the bit `b` is at most `a`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_cell_aux_step_ineq (b : Bool)
    {a pi lam : ℝ} (ha : 0 < a) (hlam : 0 < lam)
    (hpb : (if b then pi else 1 - pi) ≤ a) :
    Real.exp (lam * (if true = b then 1 else 0) - Real.log (1 + a * (Real.exp lam - 1))) * pi +
      Real.exp (lam * (if false = b then 1 else 0) - Real.log (1 + a * (Real.exp lam - 1))) *
        (1 - pi) ≤ 1 := by
  have hE : 1 < Real.exp lam := Real.one_lt_exp_iff.mpr hlam
  have hKpos : 0 < 1 + a * (Real.exp lam - 1) := by nlinarith
  have e1 : Real.exp (lam * 1 - Real.log (1 + a * (Real.exp lam - 1))) =
      Real.exp lam / (1 + a * (Real.exp lam - 1)) := by
    rw [mul_one, Real.exp_sub, Real.exp_log hKpos]
  have e0 : Real.exp (lam * 0 - Real.log (1 + a * (Real.exp lam - 1))) =
      1 / (1 + a * (Real.exp lam - 1)) := by
    rw [mul_zero, zero_sub, Real.exp_neg, Real.exp_log hKpos, one_div]
  cases b
  · simp only [Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, ite_false,
      ite_true] at hpb ⊢
    rw [e0, e1]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_le_one hKpos]
    nlinarith
  · simp only [Bool.false_eq_true, ite_false, ite_true, ite_false, ite_true] at hpb ⊢
    rw [e1, e0]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_le_one hKpos]
    nlinarith

/-- The step factors are positive. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_cell_aux_stepFac_pos (ρ : KLRule)
    (b : Bool) (N0 n : ℕ) (lam kap : ℝ) (x : BitString) (c : Bool) :
    0 < isMisesKLRandomAt_of_isMartinLofRandom_stepFac ρ b N0 n lam kap x c := by
  unfold isMisesKLRandomAt_of_isMartinLofRandom_stepFac
  split_ifs <;> positivity

/-- The weights of histories are positive. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_cell_aux_gz_pos (ρ : KLRule)
    (b : Bool) (N0 n : ℕ) (lam kap : ℝ) (h : BitString) :
    0 < isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap h := by
  unfold isMisesKLRandomAt_of_isMartinLofRandom_gz
  exact Finset.prod_pos (fun i _ =>
    isMisesKLRandomAt_of_isMartinLofRandom_cell_aux_stepFac_pos ρ b N0 n lam kap _ _)

/-- The expected step factor is at most `1`: `F x` is defined, the next coordinate is `i = F x`,
and it carries `true` with probability `p i`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_cell_aux_stepFac_sum_le
    {p : ℕ → NNReal} (b : Bool) (N0 : ℕ) {a : ℝ} (ha : 0 < a)
    (hpa : ∀ i, N0 ≤ i → (if b then (p i : ℝ) else 1 - (p i : ℝ)) ≤ a) (ρ : KLRule) (n : ℕ)
    {lam : ℝ} (hlam : 0 < lam) (x : BitString) (hx : (ρ.next x).Dom) :
    isMisesKLRandomAt_of_isMartinLofRandom_stepFac ρ b N0 n lam
        (Real.log (1 + a * (Real.exp lam - 1))) x true * (p ((ρ.next x).get hx) : ℝ) +
      isMisesKLRandomAt_of_isMartinLofRandom_stepFac ρ b N0 n lam
        (Real.log (1 + a * (Real.exp lam - 1))) x false * (1 - (p ((ρ.next x).get hx) : ℝ)) ≤ 1 :=
            by
  have hpos : isMisesKLRandomAt_of_isMartinLofRandom_pos ρ x = (ρ.next x).get hx := by
    unfold isMisesKLRandomAt_of_isMartinLofRandom_pos
    exact dite_eq_left hx
  unfold isMisesKLRandomAt_of_isMartinLofRandom_stepFac
  by_cases hact : N0 ≤ isMisesKLRandomAt_of_isMartinLofRandom_pos ρ x ∧
      x ∈ partialRuleSet ρ.sel ∧ (selectedBits (partialRuleSet ρ.sel) x).length < n
  · rw [ite_eq_left hact, ite_eq_left hact]
    have h1 := hpa ((ρ.next x).get hx) (hpos ▸ hact.1)
    exact isMisesKLRandomAt_of_isMartinLofRandom_cell_aux_step_ineq b ha hlam h1
  · rw [ite_eq_right hact, ite_eq_right hact]
    linarith

/-- On a scenario where `F h` is defined, the next revealed string is `h` followed by the bit of
coordinate `F h`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_cell_aux_revealed_succ_of_eq
    (ρ : KLRule) (w : CantorSeq) (t : ℕ) (h : BitString) (hw : ρ.revealed w t = h)
    (hdom : (ρ.next h).Dom) :
    ρ.revealed w (t + 1) = h ++ [w ((ρ.next h).get hdom)] := by
  subst hw
  exact isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_dom ρ w t hdom

/-- Step 3a' of the proof of `isMisesKLRandomAt_of_isMartinLofRandom`: one step of the
supermartingale on one scenario `{w | ρ.revealed w t = h}`.  If `F h` is undefined the history does
not change; if `F h = i` is defined, the next bit is the independent coordinate `w i` (`i` is not
among the finitely many coordinates the scenario depends on, by `noRepeat`), and
`(1 - pb i) * e^{-kap} + pb i * e^{lam - kap} ≤ 1` since `pb i ≤ a` for `i ≥ N0` and
`e^kap = 1 + a * (e^lam - 1)`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_cell {p : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (b : Bool) (N0 : ℕ) {a : ℝ} (ha : 0 < a)
    (hpa : ∀ i, N0 ≤ i → (if b then (p i : ℝ) else 1 - (p i : ℝ)) ≤ a) (ρ : KLRule) (n : ℕ)
    {lam : ℝ} (hlam : 0 < lam) (t : ℕ) (h : BitString) :
    ∫⁻ w in {w : CantorSeq | ρ.revealed w t = h}, ENNReal.ofReal
        (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam
          (Real.log (1 + a * (Real.exp lam - 1))) (ρ.revealed w (t + 1))) ∂(independentTrials p hp)
              ≤
      ENNReal.ofReal (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam
          (Real.log (1 + a * (Real.exp lam - 1))) h) *
        independentTrials p hp {w : CantorSeq | ρ.revealed w t = h} := by
  classical
  obtain ⟨kap, hkap⟩ : ∃ kap : ℝ, kap = Real.log (1 + a * (Real.exp lam - 1)) := ⟨_, rfl⟩
  obtain ⟨cell, hcell⟩ : ∃ cell : Set CantorSeq,
      cell = {w : CantorSeq | ρ.revealed w t = h} := ⟨_, rfl⟩
  have hmem : ∀ w, w ∈ cell ↔ ρ.revealed w t = h := by
    intro w
    rw [hcell]
    rfl
  have hmeas : MeasurableSet cell := by
    rw [hcell]
    exact isMisesKLRandomAt_of_isMartinLofRandom_cell_measurable ρ t h
  rw [← hkap, ← hcell]
  by_cases hdom : (ρ.next h).Dom
  · by_cases hne : cell.Nonempty
    · obtain ⟨w0, hw0⟩ := hne
      have hw0' : ρ.revealed w0 t = h := (hmem w0).1 hw0
      have hlen : h.length = t := by
        have hd0 : (ρ.next (ρ.revealed w0 t)).Dom := by rw [hw0']; exact hdom
        have h1 := isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_length_eq ρ w0 t hd0
        rw [hw0'] at h1
        exact h1
      obtain ⟨S, hSn, hS⟩ := isMisesKLRandomAt_of_isMartinLofRandom_depends ρ h
      rw [hlen] at hS
      obtain ⟨i, hiMem⟩ : ∃ i, i ∈ ρ.next h := ⟨_, Part.get_mem hdom⟩
      have hget : (ρ.next h).get hdom = i := Part.get_eq_of_mem hiMem hdom
      have hiS : i ∉ S := hSn i hiMem
      have hE : ∀ w w' : CantorSeq, (∀ j ∈ S, w j = w' j) → (w ∈ cell ↔ w' ∈ cell) := by
        intro w w' hww'
        rw [hmem w, hmem w']
        exact hS w w' hww'
      have hsucc : ∀ w, w ∈ cell → ρ.revealed w (t + 1) = h ++ [w i] := by
        intro w hw
        rw [isMisesKLRandomAt_of_isMartinLofRandom_cell_aux_revealed_succ_of_eq ρ w t h
          ((hmem w).1 hw) hdom, hget]
      have hcoord : ∀ c : Bool, MeasurableSet {w : CantorSeq | w i = c} := by
        intro c
        have h1 : MeasurableSet ((fun w : CantorSeq => w i) ⁻¹' ({c} : Set Bool)) :=
          (measurable_pi_apply i) (measurableSet_singleton c)
        exact h1
      have hsum := isMisesKLRandomAt_of_isMartinLofRandom_cell_aux_stepFac_sum_le b N0
        ha hpa ρ n hlam h hdom
      rw [hget, ← hkap] at hsum
      have hindT : independentTrials p hp (cell ∩ {w : CantorSeq | w i = true}) =
          independentTrials p hp cell * ENNReal.ofReal (p i : ℝ) := by
        have := isMisesKLRandomAt_of_isMartinLofRandom_indep hp S i hiS cell hE true
        simpa using this
      have hindF : independentTrials p hp (cell ∩ {w : CantorSeq | w i = false}) =
          independentTrials p hp cell * ENNReal.ofReal (1 - (p i : ℝ)) := by
        have := isMisesKLRandomAt_of_isMartinLofRandom_indep hp S i hiS cell hE false
        simpa using this
      have hpart : ∀ (c : Bool) (m : ℝ≥0∞),
          independentTrials p hp (cell ∩ {w : CantorSeq | w i = c}) = m →
          ∫⁻ w in cell ∩ {w : CantorSeq | w i = c}, ENNReal.ofReal
              (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap
                (ρ.revealed w (t + 1))) ∂(independentTrials p hp) =
            ENNReal.ofReal (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap h *
              isMisesKLRandomAt_of_isMartinLofRandom_stepFac ρ b N0 n lam kap h c) * m := by
        intro c m hm
        have hmc : MeasurableSet (cell ∩ {w : CantorSeq | w i = c}) := hmeas.inter (hcoord c)
        have hcongr : Set.EqOn
            (fun w => ENNReal.ofReal (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap
              (ρ.revealed w (t + 1))))
            (fun _ => ENNReal.ofReal (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap h *
              isMisesKLRandomAt_of_isMartinLofRandom_stepFac ρ b N0 n lam kap h c))
            (cell ∩ {w : CantorSeq | w i = c}) := by
          intro w hw
          have hwi : w i = c := hw.2
          change ENNReal.ofReal (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap
              (ρ.revealed w (t + 1))) =
            ENNReal.ofReal (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap h *
              isMisesKLRandomAt_of_isMartinLofRandom_stepFac ρ b N0 n lam kap h c)
          rw [hsucc w hw.1, isMisesKLRandomAt_of_isMartinLofRandom_gz_append_singleton, hwi]
        rw [setLIntegral_congr_fun hmc hcongr, setLIntegral_const, hm]
      have hunion : cell = (cell ∩ {w : CantorSeq | w i = true}) ∪
          (cell ∩ {w : CantorSeq | w i = false}) := by
        ext w
        constructor
        · intro hw
          by_cases hwi : w i = true
          · exact Or.inl ⟨hw, hwi⟩
          · exact Or.inr ⟨hw, by simpa using hwi⟩
        · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
      have hdisj : Disjoint (cell ∩ {w : CantorSeq | w i = true})
          (cell ∩ {w : CantorSeq | w i = false}) := by
        rw [Set.disjoint_left]
        rintro w ⟨_, h1⟩ ⟨_, h2⟩
        have h1' : w i = true := h1
        have h2' : w i = false := h2
        rw [h1'] at h2'
        exact absurd h2' (by decide)
      have hB : MeasurableSet (cell ∩ {w : CantorSeq | w i = false}) := hmeas.inter (hcoord false)
      conv_lhs => rw [hunion]
      rw [lintegral_union hB hdisj, hpart true _ hindT, hpart false _ hindF]
      have hG := isMisesKLRandomAt_of_isMartinLofRandom_cell_aux_gz_pos ρ b N0 n lam kap h
      have hT := isMisesKLRandomAt_of_isMartinLofRandom_cell_aux_stepFac_pos ρ b N0 n lam
        kap h true
      have hFa := isMisesKLRandomAt_of_isMartinLofRandom_cell_aux_stepFac_pos ρ b N0 n lam
        kap h false
      have hpi0 : 0 ≤ (p i : ℝ) := (p i).coe_nonneg
      have hpi1 : (p i : ℝ) ≤ 1 := NNReal.coe_le_one.mpr (hp i)
      have hpf0 : 0 ≤ 1 - (p i : ℝ) := by linarith
      obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap
          h :=
        ⟨_, rfl⟩
      obtain ⟨T, hTdef⟩ : ∃ T : ℝ,
          T = isMisesKLRandomAt_of_isMartinLofRandom_stepFac ρ b N0 n lam kap h true := ⟨_, rfl⟩
      obtain ⟨Fa, hFadef⟩ : ∃ Fa : ℝ,
          Fa = isMisesKLRandomAt_of_isMartinLofRandom_stepFac ρ b N0 n lam kap h false := ⟨_, rfl⟩
      rw [← hGdef] at hG
      rw [← hTdef] at hT
      rw [← hFadef] at hFa
      rw [← hTdef, ← hFadef] at hsum
      rw [← hGdef, ← hTdef, ← hFadef]
      calc ENNReal.ofReal (G * T) * (independentTrials p hp cell * ENNReal.ofReal (p i : ℝ)) +
            ENNReal.ofReal (G * Fa) *
              (independentTrials p hp cell * ENNReal.ofReal (1 - (p i : ℝ)))
          = independentTrials p hp cell *
              (ENNReal.ofReal (G * T * (p i : ℝ)) + ENNReal.ofReal (G * Fa * (1 - (p i : ℝ)))) := by
            rw [ENNReal.ofReal_mul (mul_pos hG hT).le, ENNReal.ofReal_mul (mul_pos hG hFa).le]
            ring
        _ = independentTrials p hp cell *
              ENNReal.ofReal (G * T * (p i : ℝ) + G * Fa * (1 - (p i : ℝ))) := by
            rw [ENNReal.ofReal_add (mul_nonneg (mul_pos hG hT).le hpi0)
              (mul_nonneg (mul_pos hG hFa).le hpf0)]
        _ ≤ independentTrials p hp cell * ENNReal.ofReal G := by
            gcongr
            have h1 := mul_le_mul_of_nonneg_left hsum hG.le
            calc G * T * (p i : ℝ) + G * Fa * (1 - (p i : ℝ))
                = G * (T * (p i : ℝ) + Fa * (1 - (p i : ℝ))) := by ring
              _ ≤ G * 1 := h1
              _ = G := mul_one G
        _ = ENNReal.ofReal G * independentTrials p hp cell := mul_comm _ _
    · have hempty : cell = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]
      simp
  · have hcongr : Set.EqOn
        (fun w => ENNReal.ofReal (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap
          (ρ.revealed w (t + 1))))
        (fun _ => ENNReal.ofReal (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap h))
        cell := by
      intro w hw
      have hw' : ρ.revealed w t = h := (hmem w).1 hw
      have hnd : ¬ (ρ.next (ρ.revealed w t)).Dom := by rw [hw']; exact hdom
      change ENNReal.ofReal (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap
          (ρ.revealed w (t + 1))) =
        ENNReal.ofReal (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap h)
      rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_not_dom ρ w t hnd, hw']
    exact le_of_eq (by rw [setLIntegral_congr_fun hmeas hcongr, setLIntegral_const])

/-- An abstract supermartingale argument: if a weight `g` of the revealed history satisfies the
one-step inequality on every scenario `{w | ρ.revealed w t = h}`, and `g [] ≤ 1`, then
`∫ g (ρ.revealed w t) dμ ≤ 1` for every `t`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_supermart (ρ : KLRule)
    (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (g : BitString → ℝ≥0∞) (hg0 : g [] ≤ 1)
    (hstep : ∀ (t : ℕ) (h : BitString), ∫⁻ w in {w : CantorSeq | ρ.revealed w t = h},
        g (ρ.revealed w (t + 1)) ∂μ ≤ g h * μ {w : CantorSeq | ρ.revealed w t = h})
    (t : ℕ) :
    ∫⁻ w, g (ρ.revealed w t) ∂μ ≤ 1 := by
  induction t with
  | zero =>
    have h0 : ∀ w : CantorSeq, ρ.revealed w 0 = [] := fun w => by simp [KLRule.revealed]
    simp only [h0, lintegral_const, measure_univ, mul_one]
    exact hg0
  | succ t ih =>
    have hm : ∀ h : BitString, MeasurableSet {w : CantorSeq | ρ.revealed w t = h} :=
      fun h => isMisesKLRandomAt_of_isMartinLofRandom_cell_measurable ρ t h
    have hd : Pairwise (Function.onFun Disjoint
        (fun h : BitString => {w : CantorSeq | ρ.revealed w t = h})) := by
      intro h h' hne
      exact Set.disjoint_left.2 (fun w hw hw' => hne ((show ρ.revealed w t = h from hw).symm.trans
                                                   hw'))
    have hU : (⋃ h : BitString, {w : CantorSeq | ρ.revealed w t = h}) = Set.univ := by
      ext w
      simp
    have hcells : ∀ f : CantorSeq → ℝ≥0∞, ∫⁻ w, f w ∂μ =
        ∑' h : BitString, ∫⁻ w in {w : CantorSeq | ρ.revealed w t = h}, f w ∂μ := by
      intro f
      have := lintegral_iUnion (μ := μ) hm hd f
      rwa [hU, Measure.restrict_univ] at this
    have hZ : ∀ h : BitString, ∫⁻ w in {w : CantorSeq | ρ.revealed w t = h}, g (ρ.revealed w t) ∂μ =
        g h * μ {w : CantorSeq | ρ.revealed w t = h} := by
      intro h
      rw [setLIntegral_congr_fun (hm h) (g := fun _ => g h) (fun w hw => by
        have hw' : ρ.revealed w t = h := hw
        simp only [hw'])]
      exact setLIntegral_const _ _
    calc ∫⁻ w, g (ρ.revealed w (t + 1)) ∂μ
        = ∑' h : BitString, ∫⁻ w in {w : CantorSeq | ρ.revealed w t = h},
            g (ρ.revealed w (t + 1)) ∂μ := hcells _
      _ ≤ ∑' h : BitString, g h * μ {w : CantorSeq | ρ.revealed w t = h} :=
          ENNReal.tsum_le_tsum (fun h => hstep t h)
      _ = ∑' h : BitString, ∫⁻ w in {w : CantorSeq | ρ.revealed w t = h},
            g (ρ.revealed w t) ∂μ := tsum_congr (fun h => (hZ h).symm)
      _ = ∫⁻ w, g (ρ.revealed w t) ∂μ := (hcells _).symm
      _ ≤ 1 := ih

/-- Step 3a of the proof of `isMisesKLRandomAt_of_isMartinLofRandom`: the exponential
weight `gz` of the revealed history is a supermartingale, so its expectation is at most `1`.  Here
`lam > 0`, `kap = log (1 + a * (exp lam - 1))`, and `p`-probability of the bit `b` at every
coordinate `≥ N0` is at most `a`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_supermartingale {p : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (b : Bool) (N0 : ℕ) {a : ℝ} (ha : 0 < a)
    (hpa : ∀ i, N0 ≤ i → (if b then (p i : ℝ) else 1 - (p i : ℝ)) ≤ a) (ρ : KLRule) (n : ℕ)
    {lam : ℝ} (hlam : 0 < lam) (t : ℕ) :
    ∫⁻ w, ENNReal.ofReal (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam
        (Real.log (1 + a * (Real.exp lam - 1))) (ρ.revealed w t)) ∂(independentTrials p hp) ≤ 1 :=
            by
  refine isMisesKLRandomAt_of_isMartinLofRandom_aux_supermart ρ (independentTrials p hp)
    (fun h => ENNReal.ofReal (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam
      (Real.log (1 + a * (Real.exp lam - 1))) h)) ?_ (fun t h => ?_) t
  · simp [isMisesKLRandomAt_of_isMartinLofRandom_gz_nil]
  · exact isMisesKLRandomAt_of_isMartinLofRandom_cell hp b N0 ha hpa ρ n hlam t h

/-- Auxiliary: when `F x` is defined, `pos ρ x` is the coordinate `F x`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_pos_mem (ρ : KLRule) (x : BitString)
    (hd : (ρ.next x).Dom) :
    isMisesKLRandomAt_of_isMartinLofRandom_pos ρ x ∈ ρ.next x := by
  unfold isMisesKLRandomAt_of_isMartinLofRandom_pos
  rw [dite_eq_left hd]
  exact Part.get_mem hd

/-- Auxiliary: along a revealed history, `F` is defined on every history preceding a revealed bit.
-/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_valid (ρ : KLRule) (w : CantorSeq)
    (t : ℕ) : ∀ (y : BitString) (c : Bool), y ++ [c] <+: ρ.revealed w t → (ρ.next y).Dom := by
  induction t with
  | zero =>
    intro y c hyc
    exfalso
    have := hyc.length_le
    simp [KLRule.revealed] at this
  | succ t ih =>
    intro y c hyc
    by_cases hd : (ρ.next (ρ.revealed w t)).Dom
    · rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_dom ρ w t hd] at hyc
      rw [List.prefix_concat_iff] at hyc
      rcases hyc with hyc | hyc
      · obtain ⟨hy1, -⟩ := List.append_inj' hyc rfl
        rw [hy1]
        exact hd
      · exact ih y c hyc
    · rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_revealed_succ_not_dom ρ w t hd] at hyc
      exact ih y c hyc

/-- Auxiliary: a prefix of `x` is never `x ++ [c]`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_ne_snoc {y x : BitString} {c : Bool}
    (hy : y <+: x) : y ≠ x ++ [c] := by
  rintro rfl
  have := hy.length_le
  simp at this

/-- Auxiliary: the invariant of the weight of a history.  `P` is the set of the (distinct, `< N0`)
coordinates revealed by the *exceptional* active steps. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_inv (ρ : KLRule) (b : Bool)
    (N0 n : ℕ) {lam kap : ℝ} (hlam : 0 ≤ lam) (hkap : 0 ≤ kap) (x : BitString)
    (hx : ∀ (y : BitString) (c : Bool), y ++ [c] <+: x → (ρ.next y).Dom) :
    ∃ P : Finset ℕ, (∀ j ∈ P, j < N0) ∧
      (∀ j ∈ P, ∃ y : BitString, y <+: x ∧ y ≠ x ∧ (ρ.next y).Dom ∧
        isMisesKLRandomAt_of_isMartinLofRandom_pos ρ y = j) ∧
      Real.exp (lam * ((((selectedBits (partialRuleSet ρ.sel) x).take n).count b : ℝ) - P.card)
          - kap * ((min (selectedBits (partialRuleSet ρ.sel) x).length n : ℕ) : ℝ)) ≤
        isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap x := by
  induction x using List.reverseRecOn with
  | nil =>
    refine ⟨∅, by simp, by simp, ?_⟩
    simp [selectedBits, selectedAux, isMisesKLRandomAt_of_isMartinLofRandom_gz_nil]
  | append_singleton x c ih =>
    have hxd : (ρ.next x).Dom := hx x c List.prefix_rfl
    obtain ⟨P, hP1, hP2, hinv⟩ :=
      ih (fun y c' hy => hx y c' (hy.trans (List.prefix_append _ _)))
    have hP2' : ∀ j ∈ P, ∃ y : BitString, y <+: x ++ [c] ∧ y ≠ x ++ [c] ∧ (ρ.next y).Dom ∧
        isMisesKLRandomAt_of_isMartinLofRandom_pos ρ y = j := by
      intro j hj
      obtain ⟨y, hy1, -, hy3, hy4⟩ := hP2 j hj
      exact ⟨y, hy1.trans (List.prefix_append _ _),
        isMisesKLRandomAt_of_isMartinLofRandom_aux_ne_snoc hy1, hy3, hy4⟩
    rw [isMisesKLRandomAt_of_isMartinLofRandom_gz_append_singleton]
    by_cases hxR : x ∈ partialRuleSet ρ.sel
    · have hsel : selectedBits (partialRuleSet ρ.sel) (x ++ [c]) =
          selectedBits (partialRuleSet ρ.sel) x ++ [c] := by
        rw [selectedBits_append_singleton, ite_eq_left hxR]
      by_cases hs : (selectedBits (partialRuleSet ρ.sel) x).length < n
      · -- an active step
        have hcbR : ((((selectedBits (partialRuleSet ρ.sel) x ++ [c]).take n).count b : ℕ) : ℝ) =
            (((selectedBits (partialRuleSet ρ.sel) x).take n).count b : ℝ) +
              (if c = b then 1 else 0) := by
          rw [List.take_of_length_le (by simp; omega), List.take_of_length_le hs.le,
            List.count_append]
          by_cases hcb : c = b
          · subst hcb; simp
          · simp [hcb]
        have hmin1 : ((min (selectedBits (partialRuleSet ρ.sel) x ++ [c]).length n : ℕ) : ℝ) =
            ((selectedBits (partialRuleSet ρ.sel) x).length : ℝ) + 1 := by
          rw [min_eq_left (by simp; omega)]
          simp
        have hmin0 : ((min (selectedBits (partialRuleSet ρ.sel) x).length n : ℕ) : ℝ) =
            ((selectedBits (partialRuleSet ρ.sel) x).length : ℝ) := by
          rw [min_eq_left hs.le]
        by_cases hg : N0 ≤ isMisesKLRandomAt_of_isMartinLofRandom_pos ρ x
        · -- a good step
          have hfac : isMisesKLRandomAt_of_isMartinLofRandom_stepFac ρ b N0 n lam kap x c =
              Real.exp (lam * (if c = b then 1 else 0) - kap) := by
            unfold isMisesKLRandomAt_of_isMartinLofRandom_stepFac
            rw [ite_eq_left ⟨hg, hxR, hs⟩]
          refine ⟨P, hP1, hP2', ?_⟩
          rw [hsel, hfac, hcbR, hmin1]
          have key : lam * ((((selectedBits (partialRuleSet ρ.sel) x).take n).count b : ℝ) +
                (if c = b then 1 else 0) - P.card) -
              kap * (((selectedBits (partialRuleSet ρ.sel) x).length : ℝ) + 1) =
              (lam * ((((selectedBits (partialRuleSet ρ.sel) x).take n).count b : ℝ) - P.card) -
                kap * ((min (selectedBits (partialRuleSet ρ.sel) x).length n : ℕ) : ℝ)) +
              (lam * (if c = b then 1 else 0) - kap) := by
            rw [hmin0]
            ring
          rw [key, Real.exp_add]
          exact mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
        · -- an exceptional step
          have hg' : isMisesKLRandomAt_of_isMartinLofRandom_pos ρ x < N0 := by omega
          have hfac : isMisesKLRandomAt_of_isMartinLofRandom_stepFac ρ b N0 n lam kap x c = 1 := by
            unfold isMisesKLRandomAt_of_isMartinLofRandom_stepFac
            rw [ite_eq_right (fun h => hg h.1)]
          have hnotin : isMisesKLRandomAt_of_isMartinLofRandom_pos ρ x ∉ P := by
            intro hmem
            obtain ⟨y, hy1, hy2, hy3, hy4⟩ := hP2 _ hmem
            exact ρ.noRepeat y x hy1 hy2 _
                (hy4 ▸ isMisesKLRandomAt_of_isMartinLofRandom_aux_pos_mem ρ y hy3)
              _ (isMisesKLRandomAt_of_isMartinLofRandom_aux_pos_mem ρ x hxd) hy4
          refine ⟨insert (isMisesKLRandomAt_of_isMartinLofRandom_pos ρ x) P, ?_, ?_, ?_⟩
          · intro j hj
            rcases Finset.mem_insert.1 hj with rfl | hj
            · exact hg'
            · exact hP1 j hj
          · intro j hj
            rcases Finset.mem_insert.1 hj with rfl | hj
            · exact ⟨x, List.prefix_append _ _, fun h => by
                have := congrArg List.length h
                simp at this, hxd, rfl⟩
            · exact hP2' j hj
          · rw [hsel, hfac, hcbR, hmin1, Finset.card_insert_of_notMem hnotin, mul_one]
            refine le_trans (Real.exp_le_exp.2 ?_) hinv
            have h1 : (if c = b then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
            have h2 : lam * ((if c = b then (1 : ℝ) else 0) - 1) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos hlam (by linarith)
            rw [hmin0]
            push_cast
            nlinarith
      · -- not active: `n ≤ |selectedBits x|`
        have hs' : n ≤ (selectedBits (partialRuleSet ρ.sel) x).length := not_lt.1 hs
        have hfac : isMisesKLRandomAt_of_isMartinLofRandom_stepFac ρ b N0 n lam kap x c = 1 := by
          unfold isMisesKLRandomAt_of_isMartinLofRandom_stepFac
          rw [ite_eq_right (fun h => hs h.2.2)]
        refine ⟨P, hP1, hP2', ?_⟩
        rw [hsel, hfac, mul_one, List.take_append_of_le_length hs']
        have hm : min (selectedBits (partialRuleSet ρ.sel) x ++ [c]).length n =
            min (selectedBits (partialRuleSet ρ.sel) x).length n := by
          rw [min_eq_right hs', min_eq_right (by simp; omega)]
        rw [hm]
        exact hinv
    · -- not selected
      have hsel : selectedBits (partialRuleSet ρ.sel) (x ++ [c]) =
          selectedBits (partialRuleSet ρ.sel) x := by
        rw [selectedBits_append_singleton, ite_eq_right hxR, List.append_nil]
      have hfac : isMisesKLRandomAt_of_isMartinLofRandom_stepFac ρ b N0 n lam kap x c = 1 := by
        unfold isMisesKLRandomAt_of_isMartinLofRandom_stepFac
        rw [ite_eq_right (fun h => hxR h.2.1)]
      refine ⟨P, hP1, hP2', ?_⟩
      rw [hsel, hfac, mul_one]
      exact hinv

/-- Step 3b of the proof of `isMisesKLRandomAt_of_isMartinLofRandom`: if the first `n`
selected bits at time `t` contain more than `r * n` bits `b`, the weight of the revealed history is
at least `exp (lam * (r * n - N0) - kap * n)`: at most `N0` of the first `n` selected steps reveal a
coordinate `< N0` (`noRepeat`), and the other ones contribute `exp (lam * [bit = b] - kap)`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_counting (ρ : KLRule) (b : Bool)
    (N0 n : ℕ) {lam kap : ℝ} (hlam : 0 ≤ lam) (hkap : 0 ≤ kap) {r : ℝ} (w : CantorSeq) (t : ℕ)
    (hn : n ≤ (ρ.outputChain w t).length)
    (hr : r * n < (((ρ.outputChain w t).take n).count b : ℝ)) :
    Real.exp (lam * (r * n - N0) - kap * n) ≤
      isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap (ρ.revealed w t) := by
  obtain ⟨P, hP1, -, hinv⟩ := isMisesKLRandomAt_of_isMartinLofRandom_aux_inv ρ b N0 n hlam
    hkap (ρ.revealed w t) (isMisesKLRandomAt_of_isMartinLofRandom_aux_valid ρ w t)
  have hcard : (P.card : ℝ) ≤ N0 := by
    have hsub : P ⊆ Finset.range N0 := fun j hj => Finset.mem_range.2 (hP1 j hj)
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hout : ρ.outputChain w t = selectedBits (partialRuleSet ρ.sel) (ρ.revealed w t) := rfl
  rw [← hout] at hinv
  rw [min_eq_right hn] at hinv
  refine le_trans (Real.exp_le_exp.2 ?_) hinv
  have h1 : lam * (r * n - N0) ≤
      lam * ((((ρ.outputChain w t).take n).count b : ℝ) - P.card) :=
    mul_le_mul_of_nonneg_left (by linarith) hlam
  linarith

/-- Auxiliary for the Chernoff bound: a tilting parameter `lam > 0` with
`0 ≤ log (1 + a * (exp lam - 1)) < lam * r`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_chernoff_aux_lam {a r : ℝ} (ha : 0 < a)
    (har : a < r) :
    ∃ lam : ℝ, 0 < lam ∧ 0 ≤ Real.log (1 + a * (Real.exp lam - 1)) ∧
      Real.log (1 + a * (Real.exp lam - 1)) < lam * r := by
  have hr0 : 0 < r := lt_trans ha har
  have hra : 0 < r - a := sub_pos.2 har
  have hrne : r ≠ 0 := hr0.ne'
  obtain ⟨lam, hlam_def⟩ : ∃ lam : ℝ, lam = (r - a) / (2 * r) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by
    rw [hlam_def]
    exact div_pos hra (by linarith)
  have hrlam : r * lam = (r - a) / 2 := by
    rw [hlam_def]
    field_simp
  refine ⟨lam, hlam0, ?_⟩
  have hE1 : lam + 1 ≤ Real.exp lam := Real.add_one_le_exp lam
  have hE0 : 0 < Real.exp lam := Real.exp_pos lam
  have hEbound : Real.exp lam * (1 - lam) ≤ 1 := by
    have h1 : -lam + 1 ≤ Real.exp (-lam) := Real.add_one_le_exp (-lam)
    have h2 : Real.exp lam * Real.exp (-lam) = 1 := by
      rw [← Real.exp_add]
      simp
    calc Real.exp lam * (1 - lam) = Real.exp lam * (-lam + 1) := by ring
      _ ≤ Real.exp lam * Real.exp (-lam) := mul_le_mul_of_nonneg_left h1 hE0.le
      _ = 1 := h2
  have hnn : 0 ≤ a * (Real.exp lam - 1) := mul_nonneg ha.le (by linarith)
  have hpos : 0 < 1 + a * (Real.exp lam - 1) := by linarith
  refine ⟨Real.log_nonneg (by linarith), ?_⟩
  have hlog : Real.log (1 + a * (Real.exp lam - 1)) ≤ a * (Real.exp lam - 1) := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hA : a < r * (1 - lam) := by
    have : r * (1 - lam) = r - r * lam := by ring
    rw [this, hrlam]
    linarith
  have hB : (Real.exp lam - 1) * (1 - lam) ≤ lam := by
    have : (Real.exp lam - 1) * (1 - lam) = Real.exp lam * (1 - lam) - (1 - lam) := by ring
    rw [this]
    linarith
  have hE1' : 0 < Real.exp lam - 1 := by linarith
  calc Real.log (1 + a * (Real.exp lam - 1)) ≤ a * (Real.exp lam - 1) := hlog
    _ < (r * (1 - lam)) * (Real.exp lam - 1) := mul_lt_mul_of_pos_right hA hE1'
    _ = r * ((Real.exp lam - 1) * (1 - lam)) := by ring
    _ ≤ r * lam := mul_le_mul_of_nonneg_left hB hr0.le
    _ = lam * r := mul_comm _ _

/-- Auxiliary for the Chernoff bound: the event "among the first `n` selected bits at time `t`
there are more than `r * n` bits `b`" is a countable union of scenarios, hence measurable. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_chernoff_aux_measurable (ρ : KLRule)
    (b : Bool) (n : ℕ) (r : ℝ) (t : ℕ) :
    MeasurableSet {w : CantorSeq | n ≤ (ρ.outputChain w t).length ∧
        r * n < (((ρ.outputChain w t).take n).count b : ℝ)} := by
  have hset : {w : CantorSeq | n ≤ (ρ.outputChain w t).length ∧
        r * n < (((ρ.outputChain w t).take n).count b : ℝ)} =
      ⋃ h ∈ {h : BitString | n ≤ (selectedBits (partialRuleSet ρ.sel) h).length ∧
          r * n < (((selectedBits (partialRuleSet ρ.sel) h).take n).count b : ℝ)},
        {w : CantorSeq | ρ.revealed w t = h} := by
    ext w
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hw
      exact ⟨ρ.revealed w t, hw, rfl⟩
    · rintro ⟨h, hh, hrev⟩
      subst hrev
      exact hh
  rw [hset]
  exact MeasurableSet.biUnion (Set.to_countable _)
    (fun h _ => isMisesKLRandomAt_of_isMartinLofRandom_cell_measurable ρ t h)

/-- Auxiliary for the Chernoff bound: the event at a fixed time `t` has measure at most
`C * exp (-c * n)` (Markov's inequality for the supermartingale `gz`). -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_chernoff_aux_time {p : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (b : Bool) (N0 : ℕ) {a : ℝ} (ha : 0 < a)
    (hpa : ∀ i, N0 ≤ i → (if b then (p i : ℝ) else 1 - (p i : ℝ)) ≤ a) (ρ : KLRule) (n : ℕ)
    {lam kap : ℝ} (hlam : 0 < lam) (hkap_def : kap = Real.log (1 + a * (Real.exp lam - 1)))
    (hkap : 0 ≤ kap) {r : ℝ} (t : ℕ) :
    independentTrials p hp {w : CantorSeq | n ≤ (ρ.outputChain w t).length ∧
        r * n < (((ρ.outputChain w t).take n).count b : ℝ)} ≤
      ENNReal.ofReal (Real.exp (lam * N0) * Real.exp (-(lam * r - kap) * n)) := by
  obtain ⟨A, hA⟩ : ∃ A : Set CantorSeq, A = {w : CantorSeq | n ≤ (ρ.outputChain w t).length ∧
        r * n < (((ρ.outputChain w t).take n).count b : ℝ)} := ⟨_, rfl⟩
  rw [← hA]
  have hmeas : MeasurableSet A := by
    rw [hA]
    exact isMisesKLRandomAt_of_isMartinLofRandom_chernoff_aux_measurable ρ b n r t
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.exp (lam * (r * n - N0) - kap * n) := ⟨_, rfl⟩
  have hTpos : 0 < T := by
    rw [hT]
    exact Real.exp_pos _
  have h3a := isMisesKLRandomAt_of_isMartinLofRandom_supermartingale hp b N0 ha hpa ρ n hlam
      t
  rw [← hkap_def] at h3a
  have h1 : ENNReal.ofReal T * independentTrials p hp A ≤ 1 := by
    calc ENNReal.ofReal T * independentTrials p hp A
        = ∫⁻ w, A.indicator (fun _ => ENNReal.ofReal T) w ∂(independentTrials p hp) :=
          (lintegral_indicator_const hmeas _).symm
      _ ≤ ∫⁻ w, ENNReal.ofReal (isMisesKLRandomAt_of_isMartinLofRandom_gz ρ b N0 n lam kap
            (ρ.revealed w t)) ∂(independentTrials p hp) := by
          refine lintegral_mono (fun w => ?_)
          by_cases hw : w ∈ A
          · rw [Set.indicator_of_mem hw]
            rw [hA] at hw
            rw [hT]
            exact ENNReal.ofReal_le_ofReal
              (isMisesKLRandomAt_of_isMartinLofRandom_counting ρ b N0 n hlam.le hkap w t
                hw.1 hw.2)
          · rw [Set.indicator_of_notMem hw]
            exact zero_le
      _ ≤ 1 := h3a
  have h2 : independentTrials p hp A ≤ (ENNReal.ofReal T)⁻¹ := by
    rw [ENNReal.le_inv_iff_mul_le]
    rwa [mul_comm]
  rw [← ENNReal.ofReal_inv_of_pos hTpos] at h2
  refine h2.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [hT, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

/-- Step 3 of the proof of `isMisesKLRandomAt_of_isMartinLofRandom`: the Chernoff-type
bound for an arbitrary non-monotone rule: if the probability of the bit `b` at every coordinate
`≥ N0` is at most `a < r ≤ 1`, the probability that among the first `n` selected bits more than
`r * n` are `b` is at most `C * exp (-c * n)`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_chernoff {p : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (b : Bool) (N0 : ℕ) {a r : ℝ} (ha : 0 < a) (har : a < r)
    (hpa : ∀ i, N0 ≤ i → (if b then (p i : ℝ) else 1 - (p i : ℝ)) ≤ a) (ρ : KLRule) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, independentTrials p hp {w : CantorSeq |
        ∃ t, n ≤ (ρ.outputChain w t).length ∧
          r * n < (((ρ.outputChain w t).take n).count b : ℝ)} ≤
      ENNReal.ofReal (C * Real.exp (-c * n)) := by
  obtain ⟨lam, hlam0, hkap0, hc⟩ := isMisesKLRandomAt_of_isMartinLofRandom_chernoff_aux_lam ha har
  obtain ⟨kap, hkap_def⟩ : ∃ kap : ℝ, kap = Real.log (1 + a * (Real.exp lam - 1)) := ⟨_, rfl⟩
  rw [← hkap_def] at hkap0 hc
  refine ⟨Real.exp (lam * N0), lam * r - kap, Real.exp_pos _, by linarith, fun n => ?_⟩
  have hmono : Monotone (fun t : ℕ => {w : CantorSeq | n ≤ (ρ.outputChain w t).length ∧
        r * n < (((ρ.outputChain w t).take n).count b : ℝ)}) := by
    intro t t' htt' w hw
    obtain ⟨h1, h2⟩ := hw
    have hpre : ρ.outputChain w t <+: ρ.outputChain w t' :=
      chain_prefix_of_le (ρ.outputChain_prefix w) htt'
    have hlen : (ρ.outputChain w t).length ≤ (ρ.outputChain w t').length := hpre.length_le
    have htake : (ρ.outputChain w t').take n = (ρ.outputChain w t).take n := by
      rw [List.prefix_iff_eq_take] at hpre
      rw [hpre, List.take_take, Nat.min_eq_left h1]
    exact ⟨h1.trans hlen, by rw [htake]; exact h2⟩
  have hunion : {w : CantorSeq | ∃ t, n ≤ (ρ.outputChain w t).length ∧
          r * n < (((ρ.outputChain w t).take n).count b : ℝ)} =
      ⋃ t : ℕ, {w : CantorSeq | n ≤ (ρ.outputChain w t).length ∧
        r * n < (((ρ.outputChain w t).take n).count b : ℝ)} :=
    Set.ofPred_exists _
  rw [hunion, hmono.measure_iUnion]
  exact iSup_le (fun t => isMisesKLRandomAt_of_isMartinLofRandom_chernoff_aux_time hp b N0 ha hpa ρ
                            n
    hlam0 hkap_def hkap0 t)

/-- Step 4 of the proof of `isMisesKLRandomAt_of_isMartinLofRandom`: a Martin-Löf random
sequence for `independentTrials p hp` avoids the tail unions of the selection events, for any
computable family of strings `d` and computable thresholds `N` whose tail unions have measure at
most `2^{-m}`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_mltest {p : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) {ρ : KLRule} (hρ : ρ.IsAdmissible) (d : BitString → Bool)
    (hd : Computable d) (N : ℕ → ℕ) (hN : Computable N)
    (hbound : ∀ m : ℕ, independentTrials p hp {w : CantorSeq | ∃ t, ∃ v : BitString,
        N m ≤ v.length ∧ d v = true ∧ v <+: ρ.outputChain w t} ≤ dyadicValue 1 m)
    {w : CantorSeq} (hw : IsMartinLofRandom (independentTrials p hp) w) :
    ∃ m : ℕ, ∀ t : ℕ, ∀ v : BitString, N m ≤ v.length → d v = true → ¬ v <+: ρ.outputChain w t := by
  classical
  obtain ⟨f, hf, hfeq⟩ := isMisesKLRandomAt_of_isMartinLofRandom_effopen hρ
  set g : ℕ → ℕ → Option BitString := fun m j =>
    (Encodable.decode (α := BitString) j.unpair.1).bind
      (fun v => bif ((N m - v.length == 0) && d v) then f v j.unpair.2 else none) with hgdef
  have hg : Computable₂ g := by
    have h1 : Computable (fun q : ℕ × ℕ => Encodable.decode (α := BitString) q.2.unpair.1) :=
      Computable.decode.comp ((Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd)
    have hN1 : Computable (fun x : (ℕ × ℕ) × BitString => N x.1.1) :=
      hN.comp (Computable.fst.comp Computable.fst)
    have hlen : Computable (fun x : (ℕ × ℕ) × BitString => x.2.length) :=
      Primrec.list_length.to_comp.comp Computable.snd
    have hsub : Computable (fun x : (ℕ × ℕ) × BitString => N x.1.1 - x.2.length) :=
      Primrec.nat_sub.to_comp.comp hN1 hlen
    have hbeq : Computable (fun x : (ℕ × ℕ) × BitString => (N x.1.1 - x.2.length == 0)) :=
      Primrec.beq.to_comp.comp hsub (Computable.const 0)
    have hcond : Computable (fun x : (ℕ × ℕ) × BitString =>
        ((N x.1.1 - x.2.length == 0) && d x.2)) :=
      Primrec.and.to_comp.comp hbeq (hd.comp Computable.snd)
    have hj2 : Computable (fun x : (ℕ × ℕ) × BitString => x.1.2.unpair.2) :=
      (Primrec.snd.comp Primrec.unpair).to_comp.comp (Computable.snd.comp Computable.fst)
    have hfv : Computable (fun x : (ℕ × ℕ) × BitString => f x.2 x.1.2.unpair.2) :=
      Computable₂.comp (f := f) hf Computable.snd hj2
    exact Computable.option_bind h1 (Computable.cond hcond hfv (Computable.const none))
  have hU : ∀ m, {w : CantorSeq | ∃ t, ∃ v : BitString, N m ≤ v.length ∧ d v = true ∧
        v <+: ρ.outputChain w t} = ⋃ j, (g m j).elim ∅ cantorCylinder := by
    intro m
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨t, v, hNv, hdv, hpre⟩
      have hx : x ∈ {w : CantorSeq | ∃ t, v <+: ρ.outputChain w t} := ⟨t, hpre⟩
      rw [hfeq v] at hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      refine ⟨Nat.pair (Encodable.encode v) i, ?_⟩
      have hc : ((N m - v.length == 0) && d v) = true := by
        simp [hdv, Nat.sub_eq_zero_of_le hNv]
      simp only [hgdef, Nat.unpair_pair, Encodable.encodek, Option.bind_some, hc, Bool.cond_true]
      exact hi
    · rintro ⟨j, hj⟩
      simp only [hgdef] at hj
      cases hdec : Encodable.decode (α := BitString) j.unpair.1 with
      | none => simp [hdec] at hj
      | some v =>
        rw [hdec] at hj
        simp only [Option.bind_some] at hj
        by_cases hc : ((N m - v.length == 0) && d v) = true
        · rw [hc] at hj
          simp only [Bool.cond_true] at hj
          have hx : x ∈ {w : CantorSeq | ∃ t, v <+: ρ.outputChain w t} := by
            rw [hfeq v]
            exact Set.mem_iUnion.2 ⟨j.unpair.2, hj⟩
          obtain ⟨t, ht⟩ := hx
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          exact ⟨t, v, by omega, hc.2, ht⟩
        · have hc' : ((N m - v.length == 0) && d v) = false := by simpa using hc
          rw [hc'] at hj
          simp at hj
  have htest : IsMartinLofTest (independentTrials p hp)
      (fun m => {w : CantorSeq | ∃ t, ∃ v : BitString, N m ≤ v.length ∧ d v = true ∧
        v <+: ρ.outputChain w t}) :=
    ⟨⟨g, hg, hU⟩, hbound⟩
  have hnot := hw _ htest
  rw [Set.mem_iInter] at hnot
  push Not at hnot
  obtain ⟨m, hm⟩ := hnot
  exact ⟨m, fun t v hv hdv hpre => hm ⟨t, v, hv, hdv, hpre⟩⟩

/-- Step 5 aux: the event for the threshold `N` is covered by the shifted selection events
`B (N + k)`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_subset (b : Bool) (ρ : KLRule)
    (ra rb : ℕ) (hrb : 0 < rb) {r : ℝ} (hr_eq : r = ra / rb) (N : ℕ) :
    {w : CantorSeq | ∃ t, ∃ v : BitString, N ≤ v.length ∧
        decide (ra * v.length < rb * v.count b) = true ∧ v <+: ρ.outputChain w t} ⊆
      ⋃ k : ℕ, {w : CantorSeq | ∃ t, N + k ≤ (ρ.outputChain w t).length ∧
        r * ((N + k : ℕ) : ℝ) < (((ρ.outputChain w t).take (N + k)).count b : ℝ)} := by
  rintro w ⟨t, v, hN, hdec, hpre⟩
  rw [Set.mem_iUnion]
  have hk : N + (v.length - N) = v.length := by omega
  refine ⟨v.length - N, t, ?_, ?_⟩
  · rw [hk]
    exact hpre.length_le
  · rw [hk]
    have hv : v = (ρ.outputChain w t).take v.length := List.prefix_iff_eq_take.1 hpre
    rw [← hv]
    have hlt : ra * v.length < rb * v.count b := of_decide_eq_true hdec
    have hlt' : (ra : ℝ) * v.length < rb * (v.count b : ℝ) := by exact_mod_cast hlt
    have hrb' : (0 : ℝ) < rb := by exact_mod_cast hrb
    rw [hr_eq, div_mul_eq_mul_div, div_lt_iff₀ hrb']
    linarith

/-- Step 5 aux: the geometric tail of the bounds `C * exp (-c * n)`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_tsum {C c : ℝ} (hC : 0 < C)
    (hc : 0 < c) (N : ℕ) :
    ∑' k : ℕ, ENNReal.ofReal (C * Real.exp (-c * ((N + k : ℕ) : ℝ))) =
      ENNReal.ofReal (C * Real.exp (-c * (N : ℝ)) / (1 - Real.exp (-c))) := by
  have hq0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hq1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hform : ∀ k : ℕ, C * Real.exp (-c * ((N + k : ℕ) : ℝ)) =
      C * Real.exp (-c * (N : ℝ)) * Real.exp (-c) ^ k := by
    intro k
    rw [mul_assoc]
    congr 1
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hsum : Summable (fun k : ℕ => C * Real.exp (-c * (N : ℝ)) * Real.exp (-c) ^ k) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hnn : ∀ k : ℕ, 0 ≤ C * Real.exp (-c * (N : ℝ)) * Real.exp (-c) ^ k := fun k => by positivity
  simp_rw [hform]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum, tsum_mul_left,
    tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]

/-- Step 5 aux: natural constants `K1`, `K0` making the geometric tail at the affine threshold
`K1 * m + K0` at most `2^{-m}`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_const {C c : ℝ} (hC : 0 < C)
    (hc : 0 < c) :
    ∃ K1 K0 : ℕ, ∀ m : ℕ,
      C * Real.exp (-c * ((K1 * m + K0 : ℕ) : ℝ)) / (1 - Real.exp (-c)) ≤ (2⁻¹ : ℝ) ^ m := by
  have hq1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hden : 0 < 1 - Real.exp (-c) := by linarith
  set D : ℝ := C / (1 - Real.exp (-c)) with hD
  have hDpos : 0 < D := div_pos hC hden
  refine ⟨⌈Real.log 2 / c⌉₊, ⌈Real.log D / c⌉₊, fun m => ?_⟩
  have h1 : Real.log 2 ≤ c * (⌈Real.log 2 / c⌉₊ : ℝ) := by
    have := Nat.le_ceil (Real.log 2 / c)
    rw [div_le_iff₀ hc] at this
    linarith
  have h0 : Real.log D ≤ c * (⌈Real.log D / c⌉₊ : ℝ) := by
    have := Nat.le_ceil (Real.log D / c)
    rw [div_le_iff₀ hc] at this
    linarith
  have hE1 : Real.exp (-c * (⌈Real.log 2 / c⌉₊ : ℝ)) ≤ 2⁻¹ := by
    calc Real.exp (-c * (⌈Real.log 2 / c⌉₊ : ℝ)) ≤ Real.exp (-Real.log 2) :=
          Real.exp_le_exp.2 (by linarith)
      _ = 2⁻¹ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]
  have hE0 : Real.exp (-c * (⌈Real.log D / c⌉₊ : ℝ)) ≤ D⁻¹ := by
    calc Real.exp (-c * (⌈Real.log D / c⌉₊ : ℝ)) ≤ Real.exp (-Real.log D) :=
          Real.exp_le_exp.2 (by linarith)
      _ = D⁻¹ := by rw [Real.exp_neg, Real.exp_log hDpos]
  have hsplit : Real.exp (-c * ((⌈Real.log 2 / c⌉₊ * m + ⌈Real.log D / c⌉₊ : ℕ) : ℝ)) =
      Real.exp (-c * (⌈Real.log 2 / c⌉₊ : ℝ)) ^ m *
        Real.exp (-c * (⌈Real.log D / c⌉₊ : ℝ)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc C * Real.exp (-c * ((⌈Real.log 2 / c⌉₊ * m + ⌈Real.log D / c⌉₊ : ℕ) : ℝ)) /
        (1 - Real.exp (-c))
      = D * Real.exp (-c * ((⌈Real.log 2 / c⌉₊ * m + ⌈Real.log D / c⌉₊ : ℕ) : ℝ)) := by
        rw [hD]; ring
    _ = Real.exp (-c * (⌈Real.log 2 / c⌉₊ : ℝ)) ^ m *
          (D * Real.exp (-c * (⌈Real.log D / c⌉₊ : ℝ))) := by
        rw [hsplit]; ring
    _ ≤ (2⁻¹ : ℝ) ^ m * 1 := by
        apply mul_le_mul (pow_le_pow_left₀ (Real.exp_pos _).le hE1 m) _ (by positivity)
          (by positivity)
        calc D * Real.exp (-c * (⌈Real.log D / c⌉₊ : ℝ)) ≤ D * D⁻¹ := by gcongr
          _ = 1 := mul_inv_cancel₀ hDpos.ne'
    _ = (2⁻¹ : ℝ) ^ m := mul_one _

/-- Step 5 of the proof of `isMisesKLRandomAt_of_isMartinLofRandom`: from the bounds
`C * exp (-c * n)` to computable thresholds `N m` (an affine function of `m`) such that the union
over strings `v` of length `≥ N m` with `ra * |v| < rb * count b v` has measure at most `2^{-m}`;
here `r = ra / rb`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_tail {p : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (b : Bool) (ρ : KLRule) (ra rb : ℕ) (hrb : 0 < rb) {r : ℝ}
    (hr_eq : r = ra / rb) {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ n : ℕ, independentTrials p hp {w : CantorSeq | ∃ t,
        n ≤ (ρ.outputChain w t).length ∧ r * n < (((ρ.outputChain w t).take n).count b : ℝ)} ≤
      ENNReal.ofReal (C * Real.exp (-c * n))) :
    ∃ N : ℕ → ℕ, Computable N ∧ ∀ m : ℕ, independentTrials p hp {w : CantorSeq | ∃ t, ∃ v :
        BitString,
        N m ≤ v.length ∧ decide (ra * v.length < rb * v.count b) = true ∧
          v <+: ρ.outputChain w t} ≤ dyadicValue 1 m := by
  obtain ⟨K1, K0, hK⟩ := isMisesKLRandomAt_of_isMartinLofRandom_aux_const hC hc
  refine ⟨fun m => K1 * m + K0, ?_, fun m => ?_⟩
  · exact (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const K1) Primrec.id)
      (Primrec.const K0)).to_comp
  · change independentTrials p hp {w : CantorSeq | ∃ t, ∃ v : BitString,
        K1 * m + K0 ≤ v.length ∧ decide (ra * v.length < rb * v.count b) = true ∧
          v <+: ρ.outputChain w t} ≤ dyadicValue 1 m
    have hsub := isMisesKLRandomAt_of_isMartinLofRandom_aux_subset b ρ ra rb hrb hr_eq
      (K1 * m + K0)
    calc independentTrials p hp {w : CantorSeq | ∃ t, ∃ v : BitString,
          K1 * m + K0 ≤ v.length ∧ decide (ra * v.length < rb * v.count b) = true ∧
            v <+: ρ.outputChain w t}
        ≤ independentTrials p hp (⋃ k : ℕ, {w : CantorSeq | ∃ t,
            K1 * m + K0 + k ≤ (ρ.outputChain w t).length ∧
              r * ((K1 * m + K0 + k : ℕ) : ℝ) <
                (((ρ.outputChain w t).take (K1 * m + K0 + k)).count b : ℝ)}) := measure_mono hsub
      _ ≤ ∑' k : ℕ, independentTrials p hp {w : CantorSeq | ∃ t,
            K1 * m + K0 + k ≤ (ρ.outputChain w t).length ∧
              r * ((K1 * m + K0 + k : ℕ) : ℝ) <
                (((ρ.outputChain w t).take (K1 * m + K0 + k)).count b : ℝ)} :=
          measure_iUnion_le _
      _ ≤ ∑' k : ℕ, ENNReal.ofReal
            (C * Real.exp (-c * ((K1 * m + K0 + k : ℕ) : ℝ))) :=
          ENNReal.tsum_le_tsum (fun k => hbound (K1 * m + K0 + k))
      _ = ENNReal.ofReal (C * Real.exp (-c * ((K1 * m + K0 : ℕ) : ℝ)) / (1 - Real.exp (-c))) :=
          isMisesKLRandomAt_of_isMartinLofRandom_aux_tsum hC hc (K1 * m + K0)
      _ ≤ ENNReal.ofReal ((2⁻¹ : ℝ) ^ m) := ENNReal.ofReal_le_ofReal (hK m)
      _ = dyadicValue 1 m := by
          rw [dyadicValue_one_eq_inv_two_pow', ENNReal.ofReal_pow (by norm_num)]
          congr 1
          rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
          have h2 : ENNReal.ofReal 2 = 2 := by norm_num
          rw [h2]

/-- Step 6 of the proof of `isMisesKLRandomAt_of_isMartinLofRandom`: if the output of the
rule on `w` is the infinite sequence `u` and `u` has at least `s * n` bits `b` among its first `n`
bits for infinitely many `n`, with `r < s`, `r = ra / rb`, then for every `N` some selected prefix
`v` of length `≥ N` satisfies `ra * |v| < rb * count b v`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_event {ρ : KLRule} (b : Bool)
    {w u : CantorSeq} (hout : ρ.output w = .infinite u) {r s : ℝ} (hrs : r < s) (ra rb : ℕ)
    (hrb : 0 < rb) (hr_eq : r = ra / rb) (N : ℕ)
    (hfreq : ∃ᶠ n : ℕ in atTop, s * n ≤ ((cantorPrefix u n).count b : ℝ)) :
    ∃ t, ∃ v : BitString, N ≤ v.length ∧ decide (ra * v.length < rb * v.count b) = true ∧
      v <+: ρ.outputChain w t := by
  obtain ⟨n, hfn, hnmax⟩ := (hfreq.and_eventually (eventually_ge_atTop (max N 1))).exists
  have hnN : N ≤ n := le_trans (le_max_left _ _) hnmax
  have hpos : 0 < n := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _) hnmax)
  -- the prefix of length `n` of `u` is a prefix of the selected bits at some time
  have H2 : BitStream.finite (cantorPrefix u n) ≤ BitStream.infinite u := by
    apply BitStream.finite_le_infinite_iff.mpr
    rw [isCantorPrefix_iff_cantorPrefix_eq, cantorPrefix_length]
  have H := BitStream.finite_le_ofPrefixSet_iff
    (isStreamPrefixSet_chainPrefixSet (KLRule.outputChain_prefix ρ w)) (cantorPrefix u n)
  rw [← hout] at H2
  obtain ⟨t, ht⟩ := H.mp H2
  -- the counting inequality
  have hnR : (0 : ℝ) < n := by exact_mod_cast hpos
  have hrb' : (0 : ℝ) < rb := by exact_mod_cast hrb
  have h1 : r * n < ((cantorPrefix u n).count b : ℝ) :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right hrs hnR) hfn
  have h2 : (ra : ℝ) * n < rb * ((cantorPrefix u n).count b : ℝ) := by
    have h3 : (ra : ℝ) / rb * n < ((cantorPrefix u n).count b : ℝ) := by
      rw [← hr_eq]; exact h1
    rw [div_mul_eq_mul_div, div_lt_iff₀ hrb'] at h3
    linarith
  have h4 : ra * n < rb * (cantorPrefix u n).count b := by exact_mod_cast h2
  refine ⟨t, cantorPrefix u n, ?_, ?_, ht⟩
  · rw [cantorPrefix_length]; exact hnN
  · rw [cantorPrefix_length]; exact decide_eq_true h4

/-- Step 7 of the proof of `isMisesKLRandomAt_of_isMartinLofRandom`: if the frequency of
ones in `u` does not tend to `q`, then for some rational `ε > 0` the frequency of ones is at least
`q + ε` infinitely often (and then `q + ε ≤ 1`), or the frequency of zeros is at least `1 - q + ε`
infinitely often (and then `ε ≤ q`). -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_split {u : CantorSeq} {q : ℝ}
    (h : ¬ HasLimitFreq q u) :
    ∃ ε : ℚ, 0 < ε ∧
      ((q + (ε : ℝ) ≤ 1 ∧ ∃ᶠ n : ℕ in atTop, (q + (ε : ℝ)) * n ≤ ((cantorPrefix u n).count true :
          ℝ)) ∨
      ((ε : ℝ) ≤ q ∧ ∃ᶠ n : ℕ in atTop, (1 - q + (ε : ℝ)) * n ≤ ((cantorPrefix u n).count false :
          ℝ))) := by
  have hf : ∀ n : ℕ, (freqOne u n : ℝ) = ((cantorPrefix u n).count true : ℝ) / n := fun n => by
    simp [freqOne]
  unfold HasLimitFreq at h
  rw [Metric.tendsto_atTop] at h
  push Not at h
  obtain ⟨ε0, hε0, hfr⟩ := h
  obtain ⟨ε, hε1, hε2⟩ := exists_rat_btwn hε0
  have hεpos : (0 : ℚ) < ε := by exact_mod_cast hε1
  have hfr' : ∃ᶠ n : ℕ in atTop, (ε : ℝ) ≤ |(freqOne u n : ℝ) - q| := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hnN, hn⟩ := hfr N
    exact ⟨n, hnN, by rw [Real.dist_eq] at hn; linarith⟩
  have hfr'' := hfr'.and_eventually (eventually_gt_atTop 0)
  have hor : ∃ᶠ n : ℕ in atTop,
      ((q + (ε : ℝ) ≤ (freqOne u n : ℝ) ∧ 0 < n) ∨ ((freqOne u n : ℝ) ≤ q - (ε : ℝ) ∧ 0 < n)) := by
    refine hfr''.mono (fun n hn => ?_)
    obtain ⟨h1, h2⟩ := hn
    rcases le_abs'.1 h1 with h3 | h3
    · right; exact ⟨by linarith, h2⟩
    · left; exact ⟨by linarith, h2⟩
  refine ⟨ε, hεpos, ?_⟩
  rcases Filter.frequently_or_distrib.1 hor with hA | hB
  · left
    obtain ⟨n0, h1, h2⟩ := hA.exists
    refine ⟨?_, hA.mono (fun n hn => ?_)⟩
    · have hn0 : (0 : ℝ) < n0 := by exact_mod_cast h2
      have hle : (freqOne u n0 : ℝ) ≤ 1 := by
        rw [hf, div_le_one hn0]
        have := (List.count_le_length : (cantorPrefix u n0).count true ≤ (cantorPrefix u n0).length)
        rw [cantorPrefix_length] at this
        exact_mod_cast this
      linarith
    · obtain ⟨h1, h2⟩ := hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast h2
      rw [hf, le_div_iff₀ hn'] at h1
      exact h1
  · right
    obtain ⟨n0, h1, h2⟩ := hB.exists
    refine ⟨?_, hB.mono (fun n hn => ?_)⟩
    · have hge : (0 : ℝ) ≤ (freqOne u n0 : ℝ) := by rw [hf]; positivity
      linarith
    · obtain ⟨h1, h2⟩ := hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast h2
      rw [hf, div_le_iff₀ hn'] at h1
      have hsum : ((cantorPrefix u n).count true : ℝ) + ((cantorPrefix u n).count false : ℝ) = n :=
          by
        have := List.count_true_add_count_false (cantorPrefix u n)
        rw [cantorPrefix_length] at this
        exact_mod_cast this
      nlinarith

/-- A nonnegative rational number is a quotient of natural numbers. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_rat_eq_nat_div (q : ℚ) (hq : 0 ≤ q) :
    ∃ a b : ℕ, 0 < b ∧ (q : ℝ) = (a : ℝ) / b := by
  refine ⟨q.num.toNat, q.den, q.pos, ?_⟩
  have hnum : (0 : ℤ) ≤ q.num := Rat.num_nonneg.2 hq
  have h1 : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg hnum
  have h2 : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by exact_mod_cast h1
  rw [h2]
  exact Rat.cast_def q

/-- Counting the bits `b` of a bitstring is primitive recursive. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_aux_primrec_count (b : Bool) :
    Primrec (fun s : BitString => s.count b) := by
  have hstep : Primrec₂ (fun (_ : BitString) (xn : Bool × ℕ) =>
      bif (xn.1 == b) then xn.2 + 1 else xn.2) :=
    (Primrec.cond (Primrec.beq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const b))
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have heq : (fun s : BitString => s.count b)
      = fun s => s.foldr (fun x n => bif (x == b) then n + 1 else n) 0 := by
    funext s
    induction s with
    | nil => rfl
    | cons x s ih => by_cases hx : x = b <;> simp [ih, hx]
  rw [heq]
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) hstep

/-- Step 8 of the proof of `isMisesKLRandomAt_of_isMartinLofRandom`: the sign-uniform
core.  If the probability of the bit `b` at every coordinate `≥ N0` is at most `a < s ≤ 1`, a
Martin-Löf random sequence cannot be mapped by an admissible rule to an infinite sequence with
at least `s * n` bits `b` among the first `n` bits for infinitely many `n`. -/
private lemma isMisesKLRandomAt_of_isMartinLofRandom_main_b {p : ℕ → NNReal} (hp : ∀ i, p i ≤ 1)
    (b : Bool) (N0 : ℕ) {a s : ℝ} (ha : 0 < a) (has : a < s)
    (hpa : ∀ i, N0 ≤ i → (if b then (p i : ℝ) else 1 - (p i : ℝ)) ≤ a)
    {ρ : KLRule} (hρ : ρ.IsAdmissible) {w u : CantorSeq}
    (hw : IsMartinLofRandom (independentTrials p hp) w) (hout : ρ.output w = .infinite u) :
    ¬ ∃ᶠ n : ℕ in atTop, s * n ≤ ((cantorPrefix u n).count b : ℝ) := by
  intro hfreq
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn has
  have hr0 : (0 : ℚ) ≤ r := by
    have : (0 : ℝ) ≤ r := by linarith
    exact_mod_cast this
  obtain ⟨ra, rb, hrb, hreq⟩ :=
    isMisesKLRandomAt_of_isMartinLofRandom_aux_rat_eq_nat_div r hr0
  obtain ⟨C, c, hC, hc, hbound⟩ := isMisesKLRandomAt_of_isMartinLofRandom_chernoff hp b N0
    ha hr1 hpa ρ
  obtain ⟨N, hNc, hNb⟩ := isMisesKLRandomAt_of_isMartinLofRandom_tail hp b ρ ra rb hrb hreq
    hC hc hbound
  have hd : Computable (fun v : BitString => decide (ra * v.length < rb * v.count b)) := by
    have hl : Primrec (fun v : BitString => ra * v.length) :=
      Primrec.nat_mul.comp (Primrec.const ra) Primrec.list_length
    have hcn : Primrec (fun v : BitString => rb * v.count b) :=
      Primrec.nat_mul.comp (Primrec.const rb)
          (isMisesKLRandomAt_of_isMartinLofRandom_aux_primrec_count b)
    exact ((PrimrecRel.decide Primrec.nat_lt).comp hl hcn).to_comp
  obtain ⟨m, hm⟩ := isMisesKLRandomAt_of_isMartinLofRandom_mltest hp hρ _ hd N hNc hNb hw
  obtain ⟨t, v, hlen, hdec, hsub⟩ := isMisesKLRandomAt_of_isMartinLofRandom_event b hout
    hr2 ra rb hrb hreq (N m) hfreq
  exact hm t v hlen hdec hsub

/-- **SUV Theorem 202, p. 305.**  Every Martin-Löf random sequence with respect to the same measure
is Mises-Kolmogorov-Loveland random with limit frequency `q`. -/
theorem isMisesKLRandomAt_of_isMartinLofRandom {p : ℕ → NNReal} (hp : ∀ i, p i ≤ 1)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hconv : ConvergesComputably p q) {w : CantorSeq}
    (hw : IsMartinLofRandom (independentTrials p hp) w) : IsMisesKLRandomAt q w := by
  intro ρ hρ
  rcases hout : ρ.output w with l | u
  · trivial
  · change HasLimitFreq q u
    by_contra hnot
    obtain ⟨ε, hε, hcase⟩ := isMisesKLRandomAt_of_isMartinLofRandom_split hnot
    obtain ⟨N, -, hN⟩ := hconv.rate
    have hε' : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hε4 : (0 : ℚ) < ε / 4 := by positivity
    have hbd : ∀ i, N (ε / 4) ≤ i → |(p i : ℝ) - q| < (ε : ℝ) / 4 := fun i hi => by
      have := hN (ε / 4) hε4 i hi
      push_cast at this
      exact this
    rcases hcase with ⟨h1, hf⟩ | ⟨h1, hf⟩
    · refine isMisesKLRandomAt_of_isMartinLofRandom_main_b hp true (N (ε / 4))
        (a := q + (ε : ℝ) / 4) (s := q + (ε : ℝ)) (by linarith) (by linarith)
        (fun i hi => ?_) hρ hw hout hf
      have := (abs_lt.mp (hbd i hi)).2
      simp only [ite_true]
      linarith
    · refine isMisesKLRandomAt_of_isMartinLofRandom_main_b hp false (N (ε / 4))
        (a := 1 - q + (ε : ℝ) / 4) (s := 1 - q + (ε : ℝ)) (by linarith) (by linarith)
        (fun i hi => ?_) hρ hw hout hf
      have := (abs_lt.mp (hbd i hi)).1
      simp only [Bool.false_eq_true, ite_false]
      linarith

end Kolmogorov.FrequencyGames
