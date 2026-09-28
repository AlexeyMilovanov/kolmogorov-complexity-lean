/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.BusyBeavers
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions

/-!
# SUV Section 5.7: required exercises (milestone C11)

The `required-planned` exercises of `COVERAGE_CHAPTER_5.md` that occur inside
`proof_loop/source/SUV_CHAPTER_5_7.txt` are **158, 161, 162 and 165**; each is
stated below as an honest leaf.

The remaining `required-planned` problems of the chapter — **135, 140, 143, 144,
145, 146, 147, 169, 170, 174, 176, 185, 187** — do *not* occur in Section 5.7 (they
belong to Sections 5.1–5.6 and 5.8–5.9) and are therefore not owned by this
milestone.

Problems 159, 160, 163 and 164 also occur in Section 5.7 but are
`optional-skipped` in `COVERAGE_CHAPTER_5.md` (isolated examples, or an alternative
proof), so per the exercise-scope policy they are not stated here.
-/

namespace Kolmogorov


open ComputableReals
open MeasureTheory ENNReal

/-! ### Problem 158 (SUV p. 158) -/

/-- **SUV Problem 158 (Section 5.7, p. 158).** A real number is random (according to
the definition of effectively null sets of reals on p. 157) if and only if its binary
representation is a random sequence with respect to the uniform measure on the Cantor
space.

`hw : cantorReal w = α` says that `w` is a binary representation of `α`; it forces
`α ∈ [0,1]`, which is the range in which the source statement is meant.

**Proved** in `Omega/NullRealCantor.lean` as
`isMartinLofRandomReal_iff_isMartinLofRandom_cantorReal`.  Both directions go through the
dyadic cells `[k/2ⁿ, (k+1)/2ⁿ]` of bit strings: a Cantor-space test is pushed forward by
padding each disjointified cylinder's cell into an open rational interval, and a real cover
is pulled back by taking, inside each covering interval, the *maximal* cells contained in
it — an antichain, so their total mass is at most the length of the interval. -/
theorem problem_158_isMartinLofRandomReal_iff {α : ℝ} {w : CantorSeq}
    (hw : cantorReal w = α) :
    IsMartinLofRandomReal α ↔ IsMartinLofRandom uniformMeasure w := by
  subst hw
  exact isMartinLofRandomReal_iff_isMartinLofRandom_cantorReal w

/-! ### Problem 161 (SUV p. 158) -/

/-- **SUV Problem 161 (Section 5.7, p. 158), forward direction.** A computable lower
semicomputable real is `≼₁`-below every lower semicomputable real. -/
theorem problem_161_solovayDominates_of_isComputableReal {α : ℝ}
    (hα : ComputableReals.IsComputableReal α) {β : ℝ} (hβ : IsLowerSemicomputableReal β) :
    SolovayDominates α β := by
  classical
  obtain ⟨approx, happroxc, happrox⟩ := hα
  obtain ⟨b, hbc, hbmono, hblim⟩ := hβ
  -- the reduction
  refine ⟨fun r => (Nat.rfind fun n => (Part.some (decide (r < b n)) : Part Bool)).bind
    (fun n => Part.some (approx ((b n - r) / 2 / 2) - (b n - r) / 2)), ?_, ?_⟩
  · -- computability
    have hchk : Computable₂ (fun (r : ℚ) (n : ℕ) => decide (r < b n)) :=
      computable₂_ratLt.comp Computable.fst (hbc.comp Computable.snd)
    have hdiff : Computable₂ (fun (r : ℚ) (n : ℕ) => b n - r) :=
      computable₂_ratSub.comp (hbc.comp Computable.snd) Computable.fst
    have hhalf : Computable₂ (fun (r : ℚ) (n : ℕ) => (b n - r) / 2) :=
      computable_ratHalf.comp hdiff
    have hbody : Computable₂ (fun (r : ℚ) (n : ℕ) =>
        approx ((b n - r) / 2 / 2) - (b n - r) / 2) :=
      computable₂_ratSub.comp (happroxc.comp (computable_ratHalf.comp hhalf)) hhalf
    exact Partrec.bind (Partrec.rfind hchk.partrec₂) hbody.partrec₂
  · -- the Solovay condition
    intro r hr
    have hble : ∀ n, ((b n : ℚ) : ℝ) ≤ β := by
      have hmono : Monotone (fun n : ℕ => ((b n : ℚ) : ℝ)) := by
        intro i j hij
        change ((b i : ℚ) : ℝ) ≤ ((b j : ℚ) : ℝ)
        exact_mod_cast hbmono hij
      exact hmono.ge_of_tendsto hblim
    -- the search halts
    obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, r < b n := by
      by_contra hcon
      push_neg at hcon
      have : β ≤ (r : ℝ) := by
        refine le_of_tendsto hblim ?_
        filter_upwards with n
        exact_mod_cast hcon n
      exact absurd hr (not_lt.2 this)
    have hdom : (Nat.rfind fun n => (Part.some (decide (r < b n)) : Part Bool)).Dom := by
      rw [Nat.rfind_dom]
      exact ⟨n₀, by simp [hn₀], fun _ => trivial⟩
    obtain ⟨n, hn⟩ := Part.dom_iff_mem.1 hdom
    have hrb : r < b n := by simpa using Nat.rfind_spec hn
    -- the returned rational
    set δ : ℚ := b n - r with hδdef
    have hδpos : 0 < δ := by simp [hδdef]; linarith
    have hq : approx (δ / 2 / 2) - δ / 2
        ∈ (Nat.rfind fun n => (Part.some (decide (r < b n)) : Part Bool)).bind
          (fun n => Part.some (approx ((b n - r) / 2 / 2) - (b n - r) / 2)) :=
      Part.mem_bind_iff.2 ⟨n, hn, by simp [hδdef]⟩
    refine ⟨_, hq, ?_, ?_⟩
    · have hbnd := happrox (δ / 2 / 2) (by positivity)
      have hδR : (0 : ℝ) < ((δ : ℚ) : ℝ) := by exact_mod_cast hδpos
      rw [abs_le] at hbnd
      push_cast
      push_cast at hbnd
      linarith [hbnd.1, hbnd.2]
    · have hbnd := happrox (δ / 2 / 2) (by positivity)
      have hδle : ((δ : ℚ) : ℝ) ≤ β - (r : ℝ) := by
        have := hble n
        simp only [hδdef]
        push_cast
        linarith
      rw [abs_le] at hbnd
      push_cast
      push_cast at hbnd
      linarith [hbnd.1, hbnd.2]

/-- **SUV Problem 161 (Section 5.7, p. 158), reverse direction.** A lower
semicomputable real that is `≼₁`-below every lower semicomputable real is
computable. -/
theorem problem_161_isComputableReal_of_forall_solovayDominates {α : ℝ}
    (_hα : IsLowerSemicomputableReal α)
    (h : ∀ β, IsLowerSemicomputableReal β → SolovayDominates α β) :
    ComputableReals.IsComputableReal α := by
  classical
  have hone : IsLowerSemicomputableReal (1 : ℝ) :=
    ⟨fun _ => 1, Computable.const 1, monotone_const, by simp⟩
  obtain ⟨p, hp, hspec⟩ := h 1 hone
  -- a total positive rational precision
  have hgc : Computable (fun ε : ℚ => bif decide (0 < ε) then ε else 1) :=
    Computable.cond (computable₂_ratLt.comp (Computable.const 0) Computable.id)
      Computable.id (Computable.const 1)
  have hgpos : ∀ ε : ℚ, 0 < (bif decide (0 < ε) then ε else 1) := by
    intro ε
    by_cases hε : 0 < ε <;> simp [hε]
  have hglt : ∀ ε : ℚ, (((1 - (bif decide (0 < ε) then ε else 1) : ℚ)) : ℝ) < 1 := by
    intro ε
    have hpos : (0 : ℝ) < (((bif decide (0 < ε) then ε else 1 : ℚ)) : ℝ) := by
      exact_mod_cast hgpos ε
    push_cast
    linarith
  have hp' : Partrec (fun ε : ℚ => p (1 - (bif decide (0 < ε) then ε else 1))) :=
    hp.comp (computable₂_ratSub.comp (Computable.const 1) hgc)
  have htot : ∀ ε : ℚ, (p (1 - (bif decide (0 < ε) then ε else 1))).Dom := by
    intro ε
    obtain ⟨q, hq, -, -⟩ := hspec _ (hglt ε)
    exact Part.dom_iff_mem.2 ⟨q, hq⟩
  refine ⟨fun ε => (p (1 - (bif decide (0 < ε) then ε else 1))).get (htot ε),
    Partrec.of_eq_tot hp' (fun ε => Part.get_mem _), ?_⟩
  intro ε hε
  dsimp only
  obtain ⟨q, hq, hqlt, hqclose⟩ := hspec _ (hglt ε)
  have hgeq : (bif decide (0 < ε) then ε else 1) = ε := by simp [hε]
  have hget : (p (1 - (bif decide (0 < ε) then ε else 1))).get (htot ε) = q :=
    Part.get_eq_of_mem hq _
  rw [hget, abs_le]
  rw [hgeq] at hqclose
  have hcast : (((1 - ε : ℚ)) : ℝ) = 1 - (ε : ℝ) := by push_cast; ring
  rw [hcast] at hqclose
  constructor <;> [linarith; linarith]

/-- **SUV Problem 161 (Section 5.7, p. 158).** A lower semicomputable number `α` is
computable if and only if `α ≼₁ β` for every lower semicomputable `β`. -/
theorem problem_161_isComputableReal_iff {α : ℝ} (hα : IsLowerSemicomputableReal α) :
    ComputableReals.IsComputableReal α ↔ ∀ β, IsLowerSemicomputableReal β → SolovayDominates α β :=
  ⟨fun h _ hβ => problem_161_solovayDominates_of_isComputableReal h hβ,
    problem_161_isComputableReal_of_forall_solovayDominates hα⟩

/-! ### Problem 162 (SUV p. 159) -/


/-! #### Problem 162, with its non-degeneracy hypothesis restored -/

/-- One step of the construction of SUV p. 159: the current approximation `a` of `α` is
moved up towards the value `a'` returned by the reduction function, but by at most `w`. -/
def dominStep (a a' w : ℚ) : ℚ := min (max a a') (a + w)

/-- One step of the dominating construction is computable in the two approximations and the
allowance. -/
theorem computable_dominStep : Computable (fun z : (ℚ × ℚ) × ℚ => dominStep z.1.1 z.1.2 z.2) :=
  computable₂_ratMin.comp
    (computable₂_ratMax.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.fst))
    (computable₂_ratAdd.comp (Computable.fst.comp Computable.fst) Computable.snd)

/-- The partial sums `∑_{j ≤ n} uⱼ` of the dominated series, as a partial recursion driven
by the reduction function `P`. -/
noncomputable def dominApprox (P : ℚ →. ℚ) (v : ℕ → ℚ) : ℕ → Part ℚ := fun n =>
  Nat.rec (P (partialSums v 1))
    (fun y IH => IH.bind fun a =>
      (P (partialSums v (y + 2))).map (fun a' => dominStep a a' (v (y + 1)))) n

/-- The dominating approximation starts at the value of the reduction function on the first
partial sum. -/
theorem dominApprox_zero (P : ℚ →. ℚ) (v : ℕ → ℚ) :
    dominApprox P v 0 = P (partialSums v 1) := rfl

/-- One step of the dominating approximation applies the step function to the next value of the
reduction function. -/
theorem dominApprox_succ (P : ℚ →. ℚ) (v : ℕ → ℚ) (n : ℕ) :
    dominApprox P v (n + 1) = (dominApprox P v n).bind (fun a =>
      (P (partialSums v (n + 2))).map (fun a' => dominStep a a' (v (n + 1)))) := rfl

/-- The dominating approximation of a partial recursive reduction function is partial recursive. -/
theorem partrec_dominApprox {P : ℚ →. ℚ} (hP : Partrec P) {v : ℕ → ℚ} (hv : Computable v) :
    Partrec (dominApprox P v) := by
  have hps : Computable (partialSums v) := computable_partialSums hv
  have hg : Partrec (fun _ : ℕ => P (partialSums v 1)) :=
    hP.comp (Computable.const (partialSums v 1))
  have hidx : Computable (fun z : ℕ × (ℕ × ℚ) => partialSums v (z.2.1 + 2)) :=
    hps.comp (Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd)
      (Computable.const 2))
  have hPz : Partrec (fun z : ℕ × (ℕ × ℚ) => P (partialSums v (z.2.1 + 2))) := hP.comp hidx
  have hmapf : Computable₂ (fun (z : ℕ × (ℕ × ℚ)) (a' : ℚ) =>
      dominStep z.2.2 a' (v (z.2.1 + 1))) := by
    have h1 : Computable (fun w : (ℕ × (ℕ × ℚ)) × ℚ => w.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    have h2 : Computable (fun w : (ℕ × (ℕ × ℚ)) × ℚ => w.2) := Computable.snd
    have h3 : Computable (fun w : (ℕ × (ℕ × ℚ)) × ℚ => v (w.1.2.1 + 1)) :=
      hv.comp (Primrec.nat_add.to_comp.comp
        (Computable.fst.comp (Computable.snd.comp Computable.fst)) (Computable.const 1))
    have hmax : Computable (fun w : (ℕ × (ℕ × ℚ)) × ℚ => max w.1.2.2 w.2) :=
      computable₂_ratMax.comp h1 h2
    have hadd : Computable (fun w : (ℕ × (ℕ × ℚ)) × ℚ => w.1.2.2 + v (w.1.2.1 + 1)) :=
      computable₂_ratAdd.comp h1 h3
    have hgoal : Computable (fun w : (ℕ × (ℕ × ℚ)) × ℚ =>
        min (max w.1.2.2 w.2) (w.1.2.2 + v (w.1.2.1 + 1))) :=
      computable₂_ratMin.comp hmax hadd
    exact hgoal
  exact Partrec.nat_rec Computable.id hg (hPz.map hmapf).to₂

-- The form without the non-degeneracy hypothesis `hlt` is false, so the corrected
-- statement carries it under the same name.
/-- **SUV p. 159, corrected.**  Problem 162 with the source's
own non-degeneracy assumption restored: the approximation `∑_{j<n} vⱼ` never *reaches* `β`,
which is exactly what makes the reduction function applicable at every stage. -/
theorem problem_162_exists_dominated_series {α β : ℝ} {v : ℕ → ℚ}
    (hv : Computable v) (hv0 : ∀ i, 0 < i → 0 ≤ v i)
    (hβ : Filter.Tendsto (fun n => (partialSums v n : ℝ)) Filter.atTop (nhds β))
    (hlt : ∀ n : ℕ, ((partialSums v n : ℚ) : ℝ) < β)
    (_hα : IsLowerSemicomputableReal α) (h : SolovayDominates α β) :
    ∃ u : ℕ → ℚ, Computable u ∧ (∀ i, 0 < i → 0 ≤ u i ∧ u i ≤ v i) ∧
      Filter.Tendsto (fun n => (partialSums u n : ℝ)) Filter.atTop (nhds α) := by
  classical
  obtain ⟨P, hPpart, hPspec⟩ := h
  -- the invariant
  have hinv : ∀ n : ℕ, ∃ a : ℚ, a ∈ dominApprox P v n ∧ ((a : ℚ) : ℝ) < α ∧
      α - ((a : ℚ) : ℝ) ≤ β - ((partialSums v (n + 1) : ℚ) : ℝ) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨q, hq, hqlt, hqgap⟩ := hPspec (partialSums v 1) (hlt 1)
      exact ⟨q, hq, hqlt, le_of_lt hqgap⟩
    | succ n ih =>
      obtain ⟨a, ha, halt, hagap⟩ := ih
      obtain ⟨a', ha', ha'lt, ha'gap⟩ := hPspec (partialSums v (n + 2)) (hlt (n + 2))
      refine ⟨dominStep a a' (v (n + 1)), ?_, ?_, ?_⟩
      · rw [dominApprox_succ]
        exact Part.mem_bind_iff.2 ⟨a, ha, Part.mem_map _ ha'⟩
      · have hmax : ((max a a' : ℚ) : ℝ) < α := by
          rcases max_cases a a' with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;> assumption
        have hle : ((dominStep a a' (v (n + 1)) : ℚ) : ℝ) ≤ ((max a a' : ℚ) : ℝ) := by
          exact_mod_cast min_le_left (max a a') (a + v (n + 1))
        linarith
      · have hstep : partialSums v (n + 2) = partialSums v (n + 1) + v (n + 1) := by
          rw [partialSums, partialSums, Finset.sum_range_succ]
        have hstepR : ((partialSums v (n + 2) : ℚ) : ℝ)
            = ((partialSums v (n + 1) : ℚ) : ℝ) + ((v (n + 1) : ℚ) : ℝ) := by
          rw [hstep]; push_cast; ring
        rcases min_cases (max a a') (a + v (n + 1)) with ⟨he, -⟩ | ⟨he, -⟩
        · have hge : ((a' : ℚ) : ℝ) ≤ ((dominStep a a' (v (n + 1)) : ℚ) : ℝ) := by
            rw [dominStep, he]
            exact_mod_cast le_max_right a a'
          linarith
        · have heq : ((dominStep a a' (v (n + 1)) : ℚ) : ℝ)
              = ((a : ℚ) : ℝ) + ((v (n + 1) : ℚ) : ℝ) := by
            rw [dominStep, he]; push_cast; ring
          rw [heq, hstepR]
          linarith
  have hdom : ∀ n : ℕ, (dominApprox P v n).Dom := by
    intro n
    obtain ⟨a, ha, -, -⟩ := hinv n
    exact Part.dom_iff_mem.2 ⟨a, ha⟩
  set cval : ℕ → ℚ := fun n => (dominApprox P v n).get (hdom n) with hcval
  have hcmem : ∀ n, cval n ∈ dominApprox P v n := fun n => Part.get_mem (hdom n)
  have hccomp : Computable cval :=
    Partrec.of_eq_tot (partrec_dominApprox hPpart hv) hcmem
  have hcinv : ∀ n : ℕ, ((cval n : ℚ) : ℝ) < α ∧
      α - ((cval n : ℚ) : ℝ) ≤ β - ((partialSums v (n + 1) : ℚ) : ℝ) := by
    intro n
    obtain ⟨a, ha, h1, h2⟩ := hinv n
    have : cval n = a := Part.mem_unique (hcmem n) ha
    rw [this]
    exact ⟨h1, h2⟩
  -- the series
  refine ⟨fun i => Nat.casesOn (motive := fun _ => ℚ) i (cval 0)
    (fun j => cval (j + 1) - cval j), ?_, ?_, ?_⟩
  · have hc1 : Computable (fun j : ℕ => cval (j + 1) - cval j) :=
      computable₂_ratSub.comp
        (hccomp.comp (Primrec.nat_add.to_comp.comp Computable.id (Computable.const 1))) hccomp
    exact Computable.nat_casesOn Computable.id (Computable.const (cval 0))
      (hc1.comp Computable.snd)
  · intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    -- read off the step
    have hmem := hcmem (j + 1)
    rw [dominApprox_succ] at hmem
    obtain ⟨a, ha, hmem'⟩ := Part.mem_bind_iff.1 hmem
    obtain ⟨a', ha', heq⟩ := (Part.mem_map_iff _).1 hmem'
    have haeq : a = cval j := Part.mem_unique ha (hcmem j)
    have hstep : cval (j + 1) = dominStep (cval j) a' (v (j + 1)) := by
      rw [← heq, haeq]
    have hw : 0 ≤ v (j + 1) := hv0 (j + 1) (by omega)
    constructor
    · simp only []
      rw [hstep, dominStep, sub_nonneg]
      exact le_min (le_max_left _ _) (by linarith)
    · simp only []
      rw [hstep, dominStep, sub_le_iff_le_add']
      have := min_le_right (max (cval j) a') (cval j + v (j + 1))
      linarith
  · -- convergence
    have hpartial : ∀ n : ℕ,
        partialSums (fun i => Nat.casesOn (motive := fun _ => ℚ) i (cval 0)
          (fun j => cval (j + 1) - cval j)) (n + 1) = cval n := by
      intro n
      induction n with
      | zero => simp [partialSums]
      | succ n ih =>
        rw [partialSums, Finset.sum_range_succ, ← partialSums, ih]
        simp only []
        ring
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hβ ε hε
    refine ⟨N + 1, fun n hn => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [hpartial j]
    obtain ⟨h1, h2⟩ := hcinv j
    have h3 := hN (j + 1) (by omega)
    rw [Real.dist_eq, abs_lt] at h3
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [h3.1], by linarith⟩

/-! ### Problem 165 (SUV p. 169) -/

/-! #### Halting times are partial

A non-terminating computation has **no** halting time.  Mapping it to `0` — as the
frozen `sInf`-based definition did — makes it look like the *fastest* computation, so
`T(m)`, and with it Problem 165, could be satisfied vacuously.  `haltTime` is
therefore `Option ℕ`-valued, and `maxHaltTime` is the maximum over the *terminating*
inputs of length `≤ m` only.  The machine and its code are no longer both taken as
arguments: `maxHaltTime` depends on the code alone, and the link to the machine `U`
of `BP U` is the single hypothesis `IsCodeFor c U`. -/

/-- The step counts at which `evaln` already returns a value for the code `c` on the
program `p` in the empty context.  Nonempty exactly when the computation terminates. -/
def haltStepSet (c : Nat.Partrec.Code) (p : BitString) : Set ℕ :=
  {t : ℕ | (Nat.Partrec.Code.evaln t c
    (Encodable.encode ((p, ([] : BitString)) : BitString × BitString))).isSome}

open scoped Classical in
/-- The least step count at which the computation of the code `c` on the program `p`
(in the empty context) terminates, and `none` when it never terminates.  This is the
book's implicit "time needed for termination" of p. 169, as a genuinely partial
value. -/
noncomputable def haltTime (c : Nat.Partrec.Code) (p : BitString) : Option ℕ :=
  if (haltStepSet c p).Nonempty then some (sInf (haltStepSet c p)) else none

/-- `haltTime` is defined exactly on the terminating computations. -/
theorem haltTime_isSome_iff (c : Nat.Partrec.Code) (p : BitString) :
    (haltTime c p).isSome ↔ (haltStepSet c p).Nonempty := by
  classical
  by_cases h : (haltStepSet c p).Nonempty <;> simp [haltTime, h]

/-- When defined, `haltTime` is a genuine step count at which the computation has
already returned. -/
theorem mem_haltStepSet_of_haltTime_eq_some {c : Nat.Partrec.Code} {p : BitString} {t : ℕ}
    (h : haltTime c p = some t) : t ∈ haltStepSet c p := by
  classical
  by_cases hne : (haltStepSet c p).Nonempty
  · have : sInf (haltStepSet c p) = t := by simpa [haltTime, hne] using h
    exact this ▸ Nat.sInf_mem hne
  · simp [haltTime, hne] at h

/-- The terminating programs of length at most `m`, as a `Finset`: the finitely many
bit strings of length `≤ m` (`boundedPrograms`) on which the code `c` halts. -/
noncomputable def haltingBoundedPrograms (c : Nat.Partrec.Code) (m : ℕ) : Finset BitString :=
  (boundedPrograms m).toFinset.filter (fun p => (haltTime c p).isSome)

/-- **SUV Problem 165 (Section 5.7, p. 169).** `T(m)` is the maximal time needed for
termination of *all terminating* computations on inputs of length at most `m`: the
`Finset.sup` over `haltingBoundedPrograms`.  Non-terminating inputs are excluded
rather than contributing a spurious `0`; the value `0` therefore occurs only in the
genuinely degenerate case in which no input of length `≤ m` terminates at all. -/
noncomputable def maxHaltTime (c : Nat.Partrec.Code) (m : ℕ) : ℕ :=
  (haltingBoundedPrograms c m).sup (fun p => (haltTime c p).getD 0)

/-- `maxHaltTime` really dominates every terminating computation on a short input. -/
theorem le_maxHaltTime {c : Nat.Partrec.Code} {m : ℕ} {p : BitString} {t : ℕ}
    (hp : p ∈ boundedPrograms m) (h : haltTime c p = some t) : t ≤ maxHaltTime c m := by
  classical
  refine Finset.le_sup (f := fun p => (haltTime c p).getD 0)
    (b := p) ?_ |>.trans_eq' ?_
  · simp [haltingBoundedPrograms, List.mem_toFinset, hp, h]
  · simp [h]

/-! #### The halting-time machine

The **upper** half of Problem 165 is proved below.  It rests on one observation of the
source's hint ("the same argument as for plain complexity"): the map that sends a
program to the number of steps its computation needs is itself a prefix decompressor
with the *same domain* as `U`, so the halting time of a program of length `m` has
prefix complexity at most `m + O(1)` and therefore does not exceed `BP(m + O(1))`.

The **lower** half, `BP U (m - k) ≤ maxHaltTime c m`, is proved further below. -/

/-- The **halting-time machine**: on a program `p` whose computation under the code
`c` terminates (in the empty context) it outputs the canonical `BitString` code of the
number of steps needed; on every other input it diverges.  This is the machine implicit
in the hint to SUV Problem 165 (p. 169). -/
noncomputable def haltTimeMachine (c : Nat.Partrec.Code) : Map := fun q =>
  if q.2 = [] then (haltTime c q.1).elim Part.none (fun t => Part.some (natToBitString t))
  else Part.none

/-- The halting-time machine outputs the code of the halting time, and only that. -/
theorem produces_haltTimeMachine {c : Nat.Partrec.Code} {p : BitString} {t : ℕ}
    (h : haltTime c p = some t) : produces (haltTimeMachine c) p [] (natToBitString t) := by
  simp [haltTimeMachine, produces, h]

/-- The halting domain of the halting-time machine in the empty context is exactly the
halting domain of `U`; in every other context it is empty. -/
theorem domainAt_haltTimeMachine_empty (c : Nat.Partrec.Code) :
    domainAt (haltTimeMachine c) [] = {p : BitString | (haltStepSet c p).Nonempty} := by
  ext p
  simp only [domainAt, Set.mem_setOf_eq, haltTimeMachine]
  rw [← haltTime_isSome_iff]
  cases haltTime c p <;> simp

/-- Outside the empty context the halting-time machine never halts. -/
theorem domainAt_haltTimeMachine_of_ne {c : Nat.Partrec.Code} {y : BitString} (hy : y ≠ []) :
    domainAt (haltTimeMachine c) y = ∅ := by
  ext p
  simp [domainAt, haltTimeMachine, hy]

/-- **The code's step set is nonempty exactly on the halting domain of `U`.** This is
where the hypothesis `IsCodeFor c U` is used: `evaln`-completeness turns "some step
count works" into "`c.eval` is defined", which `IsCodeFor` identifies with `U`. -/
theorem haltStepSet_nonempty_iff {c : Nat.Partrec.Code} {U : Map} (hc : IsCodeFor c U)
    (p : BitString) : (haltStepSet c p).Nonempty ↔ (U (p, ([] : BitString))).Dom := by
  have heval : Nat.Partrec.Code.eval c
      (Encodable.encode ((p, ([] : BitString)) : BitString × BitString))
      = Part.map Encodable.encode (U (p, ([] : BitString))) := by
    rw [hc]
    simp [Encodable.encodek]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ht
    have hx' : x ∈ Nat.Partrec.Code.eval c
        (Encodable.encode ((p, ([] : BitString)) : BitString × BitString)) :=
      Nat.Partrec.Code.evaln_complete.2 ⟨t, hx⟩
    rw [heval, Part.mem_map_iff] at hx'
    obtain ⟨a, ha, -⟩ := hx'
    exact Part.dom_iff_mem.2 ⟨a, ha⟩
  · intro hdom
    obtain ⟨a, ha⟩ := Part.dom_iff_mem.1 hdom
    have : Encodable.encode a ∈ Nat.Partrec.Code.eval c
        (Encodable.encode ((p, ([] : BitString)) : BitString × BitString)) := by
      rw [heval, Part.mem_map_iff]
      exact ⟨a, ha, rfl⟩
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.1 this
    exact ⟨t, by simpa [haltStepSet] using Option.isSome_of_mem ht⟩

/-- The halting-time machine is a prefix machine: its domain is `U`'s. -/
theorem haltTimeMachine_isPrefixMachine {c : Nat.Partrec.Code} {U : Map}
    (hc : IsCodeFor c U) (hU : IsPrefixDecompressor U) :
    IsPrefixMachine (haltTimeMachine c) := by
  intro y
  by_cases hy : y = []
  · subst hy
    have hdom : domainAt (haltTimeMachine c) [] = domainAt U [] := by
      rw [domainAt_haltTimeMachine_empty]
      ext p
      simp only [Set.mem_setOf_eq, domainAt]
      exact haltStepSet_nonempty_iff hc p
    rw [hdom]
    exact hU.isPrefixMachine []
  · rw [domainAt_haltTimeMachine_of_ne hy]
    intro p hp
    exact absurd hp (Set.notMem_empty p)

/-- The stage test behind `haltTimeMachine`: "the
context is empty, and the computation of the code `c` on the program `q.1` has already
returned after `t` steps". -/
def haltStepTest (c : Nat.Partrec.Code) (q : BitString × BitString) (t : ℕ) : Bool :=
  decide (q.2 = []) &&
    (Nat.Partrec.Code.evaln t c
      (Encodable.encode ((q.1, ([] : BitString)) : BitString × BitString))).isSome

/-- The stage test is primitive recursive: `evaln` is (`evaln_primrec` of
`AlgorithmicStatistics/Selector.lean`) and the guard is an equality test on bit strings. -/
theorem computable_haltStepTest (c : Nat.Partrec.Code) : Computable₂ (haltStepTest c) := by
  have h1 : Primrec (fun p : (BitString × BitString) × ℕ => decide (p.1.2 = [])) :=
    PrimrecPred.decide (PrimrecRel.comp Primrec.eq (Primrec.snd.comp Primrec.fst)
      (Primrec.const ([] : BitString)))
  have h2 : Primrec (fun p : (BitString × BitString) × ℕ =>
      (Nat.Partrec.Code.evaln p.2 c
          (Encodable.encode ((p.1.1, ([] : BitString)) : BitString × BitString))).isSome) :=
    Primrec.option_isSome.comp ((evaln_primrec c).comp Primrec.snd
      (Primrec.encode.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.const ([] : BitString)))))
  exact (Primrec.and.comp h1 h2).to_comp

/-- `Nat.rfind` of a decidable stage test returns the
least element of the set the test defines.  This is the `Nat.rfind` ↔ `sInf` bridge that
`haltTime` — an `sInf` — needs in order to be seen as an unbounded search. -/
theorem rfind_eq_some_sInf {P : ℕ → Bool} {S : Set ℕ} (hPS : ∀ t, P t = true ↔ t ∈ S)
    (hS : S.Nonempty) :
    (Nat.rfind fun t => (Part.some (P t) : Part Bool)) = Part.some (sInf S) := by
  rw [Part.eq_some_iff, Nat.mem_rfind]
  refine ⟨Part.mem_some_iff.2 ((hPS _).2 (Nat.sInf_mem hS)).symm, ?_⟩
  intro m hm
  refine Part.mem_some_iff.2 ?_
  have hne : P m ≠ true := fun hcon => absurd (Nat.sInf_le ((hPS m).1 hcon)) (not_le.2 hm)
  exact (Bool.eq_false_iff.2 hne).symm

/-- The companion of `rfind_eq_some_sInf`: an always-failing stage test makes the search
diverge, which is exactly the `none` branch of `haltTime`. -/
theorem rfind_eq_none_of_forall_false {P : ℕ → Bool} (hP : ∀ t, P t ≠ true) :
    (Nat.rfind fun t => (Part.some (P t) : Part Bool)) = Part.none := by
  rw [Part.eq_none_iff]
  intro t ht
  rw [Nat.mem_rfind] at ht
  exact hP t (Part.mem_some_iff.1 ht.1).symm

/-- **SUV Problem 165 (p. 169), computability of the halting-time machine.**
`haltTime c p` is the unbounded search
`Nat.rfind (fun t => (evaln t c ⟪p, []⟫).isSome)` guarded by `q.2 = []`: the guard and the
stage test are primitive recursive (`computable_haltStepTest`), `Partrec.rfind` turns the
search into a partial recursive function, and `rfind_eq_some_sInf` /
`rfind_eq_none_of_forall_false` identify its value with the `sInf` of `haltStepSet` used in
the definition of `haltTime`. -/
theorem haltTimeMachine_partrec (c : Nat.Partrec.Code) :
    isDecompressor (haltTimeMachine c) := by
  classical
  have hg : Computable₂ (fun (_ : BitString × BitString) (t : ℕ) => natToBitString t) :=
    computable_natToBitString.comp Computable.snd
  have hmain : Partrec (fun q : BitString × BitString =>
      (Nat.rfind fun t => (Part.some (haltStepTest c q t) : Part Bool)).map
        (fun t => natToBitString t)) :=
    (Partrec.rfind (computable_haltStepTest c).partrec₂).map hg
  refine hmain.of_eq ?_
  rintro ⟨p, y⟩
  by_cases hy : y = []
  · subst hy
    have hPS : ∀ t, haltStepTest c (p, ([] : BitString)) t = true ↔ t ∈ haltStepSet c p := by
      intro t
      simp [haltStepTest, haltStepSet]
    by_cases hS : (haltStepSet c p).Nonempty
    · rw [rfind_eq_some_sInf hPS hS]
      simp [haltTimeMachine, haltTime, hS]
    · rw [rfind_eq_none_of_forall_false (fun t hcon => hS ⟨t, (hPS t).1 hcon⟩)]
      simp [haltTimeMachine, haltTime, hS]
  · rw [rfind_eq_none_of_forall_false (fun t => by simp [haltStepTest, hy])]
    simp [haltTimeMachine, hy]

/-- The halting-time machine is a prefix decompressor. -/
theorem haltTimeMachine_isPrefixDecompressor {c : Nat.Partrec.Code} {U : Map}
    (hc : IsCodeFor c U) (hU : IsPrefixDecompressor U) :
    IsPrefixDecompressor (haltTimeMachine c) :=
  ⟨haltTimeMachine_partrec c, haltTimeMachine_isPrefixMachine hc hU⟩

/-- **SUV Problem 165 (Section 5.7, p. 169), upper half.**
`T(m) ≤ BP(m + k)` for some `k` and all `m`. -/
theorem problem_165_maxHaltTime_le_BP {U : Map} (hU : IsOptimalPrefixConditional U)
    {c : Nat.Partrec.Code} (hc : IsCodeFor c U) :
    ∃ k : ℕ, ∀ m : ℕ, maxHaltTime c m ≤ BP U (m + k) := by
  classical
  obtain ⟨k, hk⟩ :=
    hU.invariance (haltTimeMachine_isPrefixDecompressor hc hU.isPrefixDecompressor)
  refine ⟨k, fun m => ?_⟩
  rcases Finset.eq_empty_or_nonempty (haltingBoundedPrograms c m) with he | hne
  · simp [maxHaltTime, he]
  obtain ⟨p, hp, hsup⟩ :=
    Finset.exists_mem_eq_sup (haltingBoundedPrograms c m) hne (fun p => (haltTime c p).getD 0)
  have hpb : p ∈ boundedPrograms m := by
    have := Finset.mem_filter.1 hp
    simpa [List.mem_toFinset] using this.1
  have hps : (haltTime c p).isSome := (Finset.mem_filter.1 hp).2
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hps
  have hT : maxHaltTime c m = t := by simp [maxHaltTime, hsup, ht]
  have hlen : p.length ≤ m := (mem_boundedPrograms_iff p m).1 hpb
  have hprod := produces_haltTimeMachine ht
  have hKm : KPNat U t ≤ ((m + k : ℕ) : ENat) := by
    calc KPNat U t = KP U (natToBitString t) [] := rfl
      _ ≤ KP (haltTimeMachine c) (natToBitString t) [] + (k : ENat) := hk _ _
      _ ≤ ((p.length : ℕ) : ENat) + (k : ENat) := by
          gcongr
          exact KP_le_programLength_of_produces hprod
      _ ≤ ((m : ℕ) : ENat) + (k : ENat) := by gcongr
      _ = ((m + k : ℕ) : ENat) := by push_cast; ring
  rw [hT]
  exact le_BP_of_KPNat_le hKm

/-! #### The lower half of Problem 165

The plain-complexity argument of SUV pp. 24–25 (Theorem 14) does **not** need
"outputting `n` costs `n` steps": it only needs that the fuel approximation is
decidable, monotone and complete.

Given a step budget `t`, run every program on which `evaln` already returns within `t`
steps and collect the outputs; one more than the largest of them is a number `bigOutput c t`
that **no** such program produces.  If `t` exceeds `T(m)`, every program of length `≤ m`
that halts at all has already returned, so `bigOutput c t` has prefix complexity `> m`.
Since `bigOutput c t` is computed from `t`, its complexity is at most `K(t) + O(1)`, and
`t = BP(m - k)` has `K(t) ≤ m - k`; for `k` one more than that `O(1)` this is a
contradiction.  The `evaln` guard `n < t` is what makes the length restriction unnecessary:
a program that returns within `t` steps has code, hence length, below `t`.
-/

/-- The length of a bit string is at most its code. -/
theorem length_le_encode (p : BitString) : p.length ≤ Encodable.encode p := by
  induction p with
  | nil => simp
  | cons b l ih =>
    have h : Encodable.encode (b :: l)
        = Nat.pair (Encodable.encode b) (Encodable.encode l) + 1 := rfl
    rw [h, List.length_cons]
    have hp := Nat.right_le_pair (Encodable.encode b) (Encodable.encode l)
    omega

/-- Every entry of a list of naturals is at most the maximum of the list. -/
theorem le_foldr_max_nat : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro a h; simp at h
  | cons b t ih =>
    intro a h
    rw [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (ih h') (le_max_right _ _)

/-- **One more than every output that the code `c` can return within `t` steps.**  This is
the object "outside the enumerated list" of SUV p. 25. -/
noncomputable def bigOutput (c : Nat.Partrec.Code) (t : ℕ) : ℕ :=
  ((snapshotCodes c t t).map bitStringToNat).foldr max 0 + 1

/-- The bound "one more than every output within `t` steps" is primitive recursive. -/
theorem primrec_bigOutput (c : Nat.Partrec.Code) : Primrec (bigOutput c) := by
  have hmax : Primrec₂ (fun a b : ℕ => max a b) := by
    have h : Primrec₂ (fun a b : ℕ => a + (b - a)) :=
      Primrec₂.comp Primrec.nat_add Primrec.fst
        (Primrec₂.comp Primrec.nat_sub Primrec.snd Primrec.fst)
    exact h.of_eq (fun a b => by omega)
  have h1 : Primrec (fun t : ℕ => snapshotCodes c t t) :=
    (snapshotCodes_primrec c).comp (Primrec.pair Primrec.id Primrec.id)
  have h2 : Primrec (fun t : ℕ => (snapshotCodes c t t).map bitStringToNat) :=
    Primrec.list_map h1 (primrec_bitStringToNat.comp Primrec.snd).to₂
  have h3 : Primrec (fun t : ℕ => ((snapshotCodes c t t).map bitStringToNat).foldr max 0) :=
    Primrec.list_foldr h2 (Primrec.const 0)
      ((hmax.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)
  exact Primrec.succ.comp h3

/-- The bit code of the bound "one more than every output within `t` steps" is computable. -/
theorem computable_bigOutput (c : Nat.Partrec.Code) :
    Computable (fun t : ℕ => natToBitString (bigOutput c t)) :=
  computable_natToBitString.comp (primrec_bigOutput c).to_comp

/-- **Every object of prefix complexity `≤ m` is below `bigOutput c t`** as soon as the
budget `t` exceeds the maximal halting time on inputs of length `≤ m`. -/
theorem lt_bigOutput_of_KPNat_le {U : Map} {c : Nat.Partrec.Code} (hc : IsCodeFor c U)
    {m t k : ℕ} (hT : maxHaltTime c m < t) (hk : KPNat U k ≤ (m : ENat)) :
    k < bigOutput c t := by
  classical
  obtain ⟨p, hplen, hprod⟩ :=
    (condK_le_iff U (natToBitString k) [] m).1 (by simpa [KPNat, KP_eq_condK] using hk)
  -- the computation of `p` halts, and does so before `t`
  have hdom : (U (p, ([] : BitString))).Dom := Part.dom_iff_mem.2 ⟨_, hprod⟩
  have hne : (haltStepSet c p).Nonempty := (haltStepSet_nonempty_iff hc p).2 hdom
  have hht : haltTime c p = some (sInf (haltStepSet c p)) := by
    simp [haltTime, hne]
  have hs : sInf (haltStepSet c p) ≤ maxHaltTime c m :=
    le_maxHaltTime ((mem_boundedPrograms_iff p m).2 hplen) hht
  set N : ℕ := Encodable.encode ((p, ([] : BitString)) : BitString × BitString) with hN
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (Nat.sInf_mem hne : sInf (haltStepSet c p) ∈ _)
  have hvt : v ∈ Nat.Partrec.Code.evaln t c N :=
    Nat.Partrec.Code.evaln_mono (le_of_lt (lt_of_le_of_lt hs hT)) hv
  -- the returned value is the code of `natToBitString k`
  have heval : Nat.Partrec.Code.eval c N = Part.map Encodable.encode (U (p, ([] : BitString))) := by
    rw [hc]
    simp [hN, Encodable.encodek]
  have hsound : v ∈ Nat.Partrec.Code.eval c N := Nat.Partrec.Code.evaln_sound hvt
  rw [heval, Part.mem_map_iff] at hsound
  obtain ⟨a, ha, hav⟩ := hsound
  have hak : a = natToBitString k := Part.mem_unique ha hprod
  -- the program is short enough to be enumerated at budget `t`
  have hbound : N < t := Nat.Partrec.Code.evaln_bound hvt
  have hplt : p.length ≤ t := by
    have h1 : Encodable.encode p ≤ N := by
      rw [hN, show Encodable.encode ((p, ([] : BitString)) : BitString × BitString)
          = Nat.pair (Encodable.encode p) (Encodable.encode ([] : BitString)) from rfl]
      exact Nat.left_le_pair _ _
    have h2 := length_le_encode p
    omega
  -- so `natToBitString k` is one of the collected outputs
  have hrun : runOut c t p = some (natToBitString k) := by
    rw [runOut, ← hN]
    have hopt : Nat.Partrec.Code.evaln t c N = some v := hvt
    rw [hopt]
    change (Encodable.decode v : Option BitString) = some (natToBitString k)
    rw [← hav, ← hak, Encodable.encodek]
  have hmem : natToBitString k ∈ snapshotCodes c t t := by
    rw [snapshotCodes, List.mem_filterMap]
    exact ⟨p, (mem_boundedPrograms_iff p t).2 hplt, hrun⟩
  have hkmem : k ∈ (snapshotCodes c t t).map bitStringToNat := by
    rw [List.mem_map]
    exact ⟨natToBitString k, hmem, bitStringToNat_natToBitString k⟩
  have := le_foldr_max_nat hkmem
  rw [bigOutput]
  omega

/-- **The lower half of SUV Problem 165 (p. 169).**  `BP(m - k) ≤ T(m)`. -/
theorem problem_165_BP_le_maxHaltTime {U : Map} (hU : IsOptimalPrefixConditional U)
    {c : Nat.Partrec.Code} (hc : IsCodeFor c U) :
    ∃ k : ℕ, ∀ m : ℕ, BP U (m - k) ≤ maxHaltTime c m := by
  classical
  obtain ⟨c₀, hc₀⟩ := exists_const_KPPlain_le_KPNat U hU (computable_bigOutput c)
  refine ⟨c₀ + 1, fun m => ?_⟩
  by_cases hm : m ≤ c₀ + 1
  · rw [show m - (c₀ + 1) = 0 by omega, BP_zero hU]
    exact Nat.zero_le _
  · push_neg at hm
    by_contra hcon
    push_neg at hcon
    set t : ℕ := BP U (m - (c₀ + 1)) with ht
    have hne : (kpNatSublevel U (m - (c₀ + 1))).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have : t = 0 := by rw [ht, BP, hemp, csSup_empty]; rfl
      omega
    have hKt : KPNat U t ≤ ((m - (c₀ + 1) : ℕ) : ENat) := (BP_mem_and_le hne).1
    -- the fresh object has complexity above `m`
    have hbig : ¬ KPNat U (bigOutput c t) ≤ (m : ENat) := by
      intro hle
      exact absurd (lt_bigOutput_of_KPNat_le hc hcon hle) (lt_irrefl _)
    -- but it is computed from `t`
    have hcomp : KPNat U (bigOutput c t) ≤ KPNat U t + (c₀ : ENat) := hc₀ t
    have hchain : KPNat U (bigOutput c t) ≤ (((m - (c₀ + 1)) + c₀ : ℕ) : ENat) := by
      refine le_trans hcomp ?_
      calc KPNat U t + (c₀ : ENat) ≤ ((m - (c₀ + 1) : ℕ) : ENat) + (c₀ : ENat) := by gcongr
        _ = (((m - (c₀ + 1)) + c₀ : ℕ) : ENat) := by push_cast; ring
    refine hbig (le_trans hchain ?_)
    have : (m - (c₀ + 1)) + c₀ ≤ m := by omega
    exact_mod_cast this

/-- **SUV Problem 165 (Section 5.7, p. 169).** For an optimal prefix-free universal
machine `M` with code `c`, the maximal halting time `T(m)` of the terminating
computations on inputs of length at most `m` satisfies `BP(m - k) ≤ T(m) ≤ BP(m + k)`
for some `k` and all `m`. (The book writes `c` for this constant; here `c` is already
the code of the machine, and `k` is the constant.)

The right-hand inequality is `problem_165_maxHaltTime_le_BP` and the left-hand one is
`problem_165_BP_le_maxHaltTime`.  Neither needs the machine-model fact "a computation
that outputs `n` runs for at least `n` steps": the argument of SUV pp. 24–25 only uses
that the `evaln` approximation is decidable, monotone and complete. -/
theorem problem_165_BP_le_maxHaltTime_le_BP {U : Map} (hU : IsOptimalPrefixConditional U)
    {c : Nat.Partrec.Code} (hc : IsCodeFor c U) :
    ∃ k : ℕ, ∀ m : ℕ, BP U (m - k) ≤ maxHaltTime c m ∧ maxHaltTime c m ≤ BP U (m + k) := by
  obtain ⟨k₁, hk₁⟩ := problem_165_BP_le_maxHaltTime hU hc
  obtain ⟨k₂, hk₂⟩ := problem_165_maxHaltTime_le_BP hU hc
  refine ⟨max k₁ k₂, fun m => ⟨?_, ?_⟩⟩
  · refine le_trans (BP_mono U (Nat.sub_le_sub_left (le_max_left k₁ k₂) m)) (hk₁ m)
  · exact le_trans (hk₂ m) (BP_mono U (Nat.add_le_add_left (le_max_right k₁ k₂) m))

alias problem_162_exists_dominated_series_of_partialSums_lt := problem_162_exists_dominated_series

end Kolmogorov
