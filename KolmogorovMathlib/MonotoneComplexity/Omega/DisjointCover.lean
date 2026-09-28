/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.Painter

/-!
# Disjointification of an effectively open set with monotone left endpoints

`IsEffectivelyNullReal` asks for a cover of small total **length**, which is strictly more
than "effectively open of small **measure**": the intervals of a computable family may
overlap, and the components of their union are not computable in general.  For a family
whose left endpoints are *non-decreasing* they are, and this module computes them.

Writing `Rⱼ = max (r 0) … (r j)` for the running maximum of the right endpoints, the
emitted interval of step `j` is

  `(max (l j) R_{j-1}, r j)`  (and `(l 0, r 0)` at `j = 0`).

* these intervals are pairwise disjoint — everything emitted before step `j` lies to the
  left of `R_{j-1}`;
* each is contained in `(l j, r j)`, so their total length is at most the measure of the
  union;
* the union of the *original* intervals is caught: if `α ∈ (l j, r j)` for some `j`, then
  at the least `j₀` with `α < r j₀` one has `max (l j₀) R_{j₀-1} ≤ α`, because `l` is
  non-decreasing and every earlier right endpoint is `≤ α`.

The last point only gives `≤`, so the emitted intervals are padded on the left by a
summable amount; the padding is also what pays for the fact that `α` may be the left
endpoint itself.

This is the device recorded as missing in `(e9)` of the design document (the analogue for
`ℝ` of `AlgorithmicRandomness/Disjointify.lean`).  No statement of the source is rendered
in this file.
-/

namespace Kolmogorov

open ENNReal MeasureTheory

/-! ### The merged left endpoints -/

/-- `mergeRunMax r ε j = max (r ε 0) … (r ε j)`. -/
def mergeRunMax (r : ℚ → ℕ → ℚ) (ε : ℚ) : ℕ → ℚ
  | 0 => r ε 0
  | j + 1 => max (mergeRunMax r ε j) (r ε (j + 1))

/-- The left endpoint emitted at step `j`: the original left endpoint, pushed right past
everything already emitted. -/
def mergeLeft (l r : ℚ → ℕ → ℚ) (ε : ℚ) : ℕ → ℚ
  | 0 => l ε 0
  | j + 1 => max (l ε (j + 1)) (mergeRunMax r ε j)

/-- The running maximum of right endpoints starts at the first one. -/
@[simp] theorem mergeRunMax_zero (r : ℚ → ℕ → ℚ) (ε : ℚ) : mergeRunMax r ε 0 = r ε 0 := rfl

/-- One step of the running maximum of right endpoints. -/
@[simp] theorem mergeRunMax_succ (r : ℚ → ℕ → ℚ) (ε : ℚ) (j : ℕ) :
    mergeRunMax r ε (j + 1) = max (mergeRunMax r ε j) (r ε (j + 1)) := rfl

/-- The first emitted left endpoint is the original one. -/
@[simp] theorem mergeLeft_zero (l r : ℚ → ℕ → ℚ) (ε : ℚ) : mergeLeft l r ε 0 = l ε 0 := rfl

/-- A later left endpoint is pushed right past all earlier right endpoints. -/
@[simp] theorem mergeLeft_succ (l r : ℚ → ℕ → ℚ) (ε : ℚ) (j : ℕ) :
    mergeLeft l r ε (j + 1) = max (l ε (j + 1)) (mergeRunMax r ε j) := rfl

/-- Every right endpoint up to `j` is at most the running maximum at `j`. -/
theorem le_mergeRunMax (r : ℚ → ℕ → ℚ) (ε : ℚ) :
    ∀ (j i : ℕ), i ≤ j → r ε i ≤ mergeRunMax r ε j := by
  intro j
  induction j with
  | zero =>
      intro i hi
      rw [Nat.le_zero.1 hi]
      exact le_rfl
  | succ j ih =>
      intro i hi
      rcases Nat.eq_or_lt_of_le hi with h | h
      · subst h
        rw [mergeRunMax_succ]
        exact le_max_right _ _
      · exact le_trans (ih i (Nat.lt_succ_iff.1 h)) (le_max_left _ _)

/-- Pushing a left endpoint right never moves it left. -/
theorem le_mergeLeft (l r : ℚ → ℕ → ℚ) (ε : ℚ) (j : ℕ) : l ε j ≤ mergeLeft l r ε j := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact le_max_left _ _

/-- Everything emitted before step `j` lies to the left of the `j`-th emitted interval. -/
theorem mergeRunMax_le_mergeLeft_of_lt (l r : ℚ → ℕ → ℚ) (ε : ℚ) {i j : ℕ} (hij : i < j) :
    r ε i ≤ mergeLeft l r ε j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact le_trans (le_mergeRunMax r ε k i (Nat.lt_succ_iff.1 hij)) (le_max_right _ _)

/-- A running maximum bounded termwise is bounded. -/
theorem mergeRunMax_le_of_forall {r : ℚ → ℕ → ℚ} {ε : ℚ} {α : ℝ} :
    ∀ (k : ℕ), (∀ i, i ≤ k → ((r ε i : ℚ) : ℝ) ≤ α) → ((mergeRunMax r ε k : ℚ) : ℝ) ≤ α := by
  intro k
  induction k with
  | zero =>
      intro h
      rw [mergeRunMax_zero]
      exact h 0 le_rfl
  | succ m ih =>
      intro h
      have h1 := ih (fun i hi => h i (by omega))
      have h2 := h (m + 1) le_rfl
      rw [mergeRunMax_succ]
      push_cast
      exact max_le h1 h2

/-! ### Computability -/

/-- The running maximum of right endpoints of a computable family is computable. -/
theorem computable₂_mergeRunMax {r : ℚ → ℕ → ℚ} (hr : Computable₂ r) :
    Computable₂ (mergeRunMax r) := by
  have hbase : Computable (fun q : ℚ × ℕ => r q.1 0) := hr.comp Computable.fst
    (Computable.const 0)
  have hnext : Computable (fun s : (ℚ × ℕ) × ℕ × ℚ => r s.1.1 (s.2.1 + 1)) :=
    hr.comp (Computable.fst.comp Computable.fst)
      (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))
  have hIH : Computable (fun s : (ℚ × ℕ) × ℕ × ℚ => s.2.2) :=
    Computable.snd.comp Computable.snd
  have hstep : Computable₂ (fun (q : ℚ × ℕ) (s : ℕ × ℚ) => max s.2 (r q.1 (s.1 + 1))) :=
    Computable₂.comp computable₂_ratMax hIH hnext
  have hrec := Computable.nat_rec (σ := ℚ) Computable.snd hbase hstep
  refine hrec.of_eq (fun q => ?_)
  obtain ⟨ε, n⟩ := q
  have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => ℚ) (r ε 0)
      (fun y IH => max IH (r ε (y + 1))) m) = mergeRunMax r ε m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp only [mergeRunMax_succ]; rw [ih]
  exact key n

/-- The pushed left endpoints of a computable family are computable. -/
theorem computable₂_mergeLeft {l r : ℚ → ℕ → ℚ} (hl : Computable₂ l) (hr : Computable₂ r) :
    Computable₂ (mergeLeft l r) := by
  have hrun := computable₂_mergeRunMax hr
  have hbase : Computable (fun q : ℚ × ℕ => l q.1 0) := hl.comp Computable.fst
    (Computable.const 0)
  have hnext : Computable (fun s : (ℚ × ℕ) × ℕ × ℚ => l s.1.1 (s.2.1 + 1)) :=
    hl.comp (Computable.fst.comp Computable.fst)
      (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))
  have hprev : Computable (fun s : (ℚ × ℕ) × ℕ × ℚ => mergeRunMax r s.1.1 s.2.1) :=
    hrun.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)
  have hstep : Computable₂ (fun (q : ℚ × ℕ) (s : ℕ × ℚ) =>
      max (l q.1 (s.1 + 1)) (mergeRunMax r q.1 s.1)) :=
    Computable₂.comp computable₂_ratMax hnext hprev
  have hrec := Computable.nat_rec (σ := ℚ) Computable.snd hbase hstep
  refine hrec.of_eq (fun q => ?_)
  obtain ⟨ε, n⟩ := q
  have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => ℚ) (l ε 0)
      (fun y _ => max (l ε (y + 1)) (mergeRunMax r ε y)) m) = mergeLeft l r ε m := by
    intro m
    induction m with
    | zero => rfl
    | succ m _ => rfl
  exact key n

/-! ### The measure bound -/

/-- The emitted intervals are pairwise disjoint, so their total length is at most the
measure of the union of the original intervals. -/
theorem tsum_ofReal_merge_le (l r : ℚ → ℕ → ℚ) (ε : ℚ) :
    (∑' j, ENNReal.ofReal (((r ε j : ℚ) : ℝ) - ((mergeLeft l r ε j : ℚ) : ℝ)))
      ≤ volume (⋃ j, Set.Ioo ((l ε j : ℚ) : ℝ) ((r ε j : ℚ) : ℝ)) := by
  classical
  set E : ℕ → Set ℝ := fun j =>
    Set.Ioo ((mergeLeft l r ε j : ℚ) : ℝ) ((r ε j : ℚ) : ℝ) with hE
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    have key : ∀ {a b : ℕ}, a < b → Disjoint (E a) (E b) := by
      intro a b hab
      refine Set.disjoint_left.2 (fun x hx hx' => ?_)
      have h1 : x < ((r ε a : ℚ) : ℝ) := hx.2
      have h2 : ((mergeLeft l r ε b : ℚ) : ℝ) < x := hx'.1
      have h3 : ((r ε a : ℚ) : ℝ) ≤ ((mergeLeft l r ε b : ℚ) : ℝ) := by
        exact_mod_cast mergeRunMax_le_mergeLeft_of_lt l r ε hab
      linarith
    rcases lt_or_gt_of_ne hij with h | h
    · exact key h
    · exact (key h).symm
  have hmeas : ∀ j, MeasurableSet (E j) := fun j => measurableSet_Ioo
  have hvol : volume (⋃ j, E j) = ∑' j, volume (E j) := measure_iUnion hdisj hmeas
  have hterm : ∀ j, volume (E j)
      = ENNReal.ofReal (((r ε j : ℚ) : ℝ) - ((mergeLeft l r ε j : ℚ) : ℝ)) := by
    intro j
    rw [hE]
    exact Real.volume_Ioo
  have hsub : (⋃ j, E j) ⊆ ⋃ j, Set.Ioo ((l ε j : ℚ) : ℝ) ((r ε j : ℚ) : ℝ) := by
    refine Set.iUnion_mono (fun j => ?_)
    refine Set.Ioo_subset_Ioo ?_ le_rfl
    exact_mod_cast le_mergeLeft l r ε j
  calc (∑' j, ENNReal.ofReal (((r ε j : ℚ) : ℝ) - ((mergeLeft l r ε j : ℚ) : ℝ)))
      = ∑' j, volume (E j) := (tsum_congr (fun j => hterm j)).symm
    _ = volume (⋃ j, E j) := hvol.symm
    _ ≤ _ := measure_mono hsub

/-! ### Catching a point of the union -/

/-- At the least index whose right endpoint passes `α`, the merged left endpoint is still
at most `α`: the earlier right endpoints are all `≤ α`, and `l` is non-decreasing. -/
theorem exists_mergeLeft_le {l r : ℚ → ℕ → ℚ} {ε : ℚ} {α : ℝ}
    (hlmono : ∀ j, l ε j ≤ l ε (j + 1)) {j : ℕ}
    (hj : α ∈ Set.Ioo ((l ε j : ℚ) : ℝ) ((r ε j : ℚ) : ℝ)) :
    ∃ j₀, ((mergeLeft l r ε j₀ : ℚ) : ℝ) ≤ α ∧ α < ((r ε j₀ : ℚ) : ℝ) := by
  classical
  have hlmono' : Monotone (fun k => l ε k) := monotone_nat_of_le_succ hlmono
  have hex : ∃ k, α < ((r ε k : ℚ) : ℝ) := ⟨j, hj.2⟩
  obtain ⟨j₀, hj₀, hmin⟩ : ∃ j₀, α < ((r ε j₀ : ℚ) : ℝ) ∧
      ∀ k, k < j₀ → ¬ (α < ((r ε k : ℚ) : ℝ)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hj₀j : j₀ ≤ j := by
    by_contra hc
    exact absurd hj.2 (hmin j (by omega))
  have hlle : ((l ε j₀ : ℚ) : ℝ) ≤ α := by
    have hq : l ε j₀ ≤ l ε j := hlmono' hj₀j
    have h1 : ((l ε j₀ : ℚ) : ℝ) ≤ ((l ε j : ℚ) : ℝ) := by exact_mod_cast hq
    linarith [hj.1]
  refine ⟨j₀, ?_, hj₀⟩
  cases j₀ with
  | zero =>
      rw [mergeLeft_zero]
      exact hlle
  | succ k =>
      have hrun : ((mergeRunMax r ε k : ℚ) : ℝ) ≤ α :=
        mergeRunMax_le_of_forall k (fun i hi => not_lt.1 (hmin i (by omega)))
      rw [mergeLeft_succ]
      push_cast
      exact max_le hlle hrun

/-! ### The device -/

/-- **Effectively open of small measure, with non-decreasing left endpoints, implies
effectively null.**  This is the step where the frozen `IsEffectivelyNullReal` (total
*length* at most `ε`) is genuinely stronger than "effectively open of measure at most `ε`":
the merged intervals of this module are disjoint, so their total length is the measure. -/
theorem not_isMartinLofRandomReal_of_monotoneLeftCover {α : ℝ} {l r : ℚ → ℕ → ℚ}
    (hl : Computable₂ l) (hr : Computable₂ r)
    (hlmono : ∀ ε j, l ε j ≤ l ε (j + 1))
    (hmeas : ∀ ε : ℚ, 0 < ε →
      volume (⋃ j, Set.Ioo ((l ε j : ℚ) : ℝ) ((r ε j : ℚ) : ℝ))
        ≤ ENNReal.ofReal (((ε / 2 : ℚ)) : ℝ))
    (hmem : ∀ ε : ℚ, 0 < ε → ∃ j, α ∈ Set.Ioo ((l ε j : ℚ) : ℝ) ((r ε j : ℚ) : ℝ)) :
    ¬ IsMartinLofRandomReal α := by
  classical
  refine not_isMartinLofRandomReal_of_ratIntervals
    (C := fun ε j => (mergeLeft l r ε j - ratPad (ε / 4) j, r ε j)) ?_ (fun ε hε => ?_)
    (fun ε hε => ?_)
  · have h1 : Computable (fun q : ℚ × ℕ => q.1 / 4) :=
      (computable_ratDivConst (c := 4) (by norm_num)).comp Computable.fst
    have hpad : Computable (fun q : ℚ × ℕ => ratPad (q.1 / 4) q.2) :=
      computable₂_ratPad.comp h1 Computable.snd
    have hml := computable₂_mergeLeft hl hr
    have hsub := Computable₂.comp computable₂_ratSub hml hpad
    exact hsub.pair hr
  · -- total length
    have hε4 : (0 : ℚ) < ε / 4 := by linarith
    have hterm : ∀ j, ratIntervalLength (mergeLeft l r ε j - ratPad (ε / 4) j, r ε j)
        ≤ ENNReal.ofReal (((r ε j : ℚ) : ℝ) - ((mergeLeft l r ε j : ℚ) : ℝ))
          + ENNReal.ofReal ((ratPad (ε / 4) j : ℚ) : ℝ) := by
      intro j
      have hval : ((r ε j : ℚ) : ℝ) - ((mergeLeft l r ε j - ratPad (ε / 4) j : ℚ) : ℝ)
          = (((r ε j : ℚ) : ℝ) - ((mergeLeft l r ε j : ℚ) : ℝ))
            + ((ratPad (ε / 4) j : ℚ) : ℝ) := by
        push_cast
        ring
      rw [ratIntervalLength]
      change ENNReal.ofReal (((r ε j : ℚ) : ℝ)
        - ((mergeLeft l r ε j - ratPad (ε / 4) j : ℚ) : ℝ)) ≤ _
      rw [hval]
      exact ENNReal.ofReal_add_le
    refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
    rw [ENNReal.tsum_add, tsum_ofReal_ratPad hε4]
    have h1 := le_trans (tsum_ofReal_merge_le l r ε) (hmeas ε hε)
    have h2 : ENNReal.ofReal (((ε / 2 : ℚ)) : ℝ) + ENNReal.ofReal ((((ε / 4) / 2 : ℚ)) : ℝ)
        ≤ ENNReal.ofReal ((ε : ℚ) : ℝ) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hεR : (0 : ℝ) < ((ε : ℚ) : ℝ) := by exact_mod_cast hε
      push_cast
      linarith
    refine le_trans (add_le_add h1 (le_of_eq ?_)) h2
    congr 1
    push_cast
    ring
  · -- the merged family still catches `α`
    obtain ⟨j, hj⟩ := hmem ε hε
    obtain ⟨j₀, hle, hlt⟩ := exists_mergeLeft_le (hlmono ε) hj
    refine ⟨j₀, ?_⟩
    have hpad : (0 : ℝ) < ((ratPad (ε / 4) j₀ : ℚ) : ℝ) := by
      exact_mod_cast ratPad_pos (show (0 : ℚ) < ε / 4 by linarith) j₀
    refine Set.mem_Ioo.mpr ⟨?_, hlt⟩
    change ((mergeLeft l r ε j₀ - ratPad (ε / 4) j₀ : ℚ) : ℝ) < α
    push_cast
    linarith

end Kolmogorov
