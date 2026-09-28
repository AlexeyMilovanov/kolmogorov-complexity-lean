/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.LscBasic
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealApi

/-!
# Splitting a computable series into non-increasing pieces (SUV p. 166)

SUV p. 166 remarks that the computable series with random sum constructed there "can be
made non-increasing … by splitting too big terms into small pieces".  This module carries
out that splitting for an arbitrary computable series of positive rationals.

The `n`-th term `uₙ` is cut into `kₙ` equal pieces `pₙ = uₙ / kₙ`, where `kₙ` is chosen
computably and large enough that `pₙ ≤ p_{n-1}`; the flat index `i` is mapped back to its
block by `blkOf`, whose defining recursion compares `i` with the cumulative block bounds.
The resulting series `blkSeries` is computable, positive, bounded by the original terms,
**non-increasing**, and its partial sums at the block boundaries are exactly the partial
sums of the original series, which is enough to transport the limit.

Everything is stated with `ratRangeSum` (`Omega/LscBasic.lean`), the recursive shape of a
partial sum; `Omega/SolovayFunctions.lean` converts to `partialSums`.
-/

namespace Kolmogorov

open ENNReal

/-! ### The block data -/

/-- A natural number strictly above `u_{n+1} · k · den(uₙ)`, computed by the dyadic floor
of `RatComputable`.  This is the bound that makes the pieces non-increasing. -/
def blkBound (u : ℕ → ℚ) (n k : ℕ) : ℕ :=
  ratDyadicFloor (u (n + 1) * (k : ℚ) * (((u n).den : ℕ) : ℚ)) 0 + 1

/-- The number of equal pieces the `n`-th term is split into. -/
def blkSize (u : ℕ → ℚ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => blkBound u n (blkSize u n)

/-- The size of each piece of the `n`-th block. -/
def blkPiece (u : ℕ → ℚ) (n : ℕ) : ℚ := u n / ((blkSize u n : ℕ) : ℚ)

/-- The first flat index of block `n`. -/
def blkCum (u : ℕ → ℚ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => blkCum u n + blkSize u n

/-- The block a flat index belongs to.  The step is written with truncated subtraction, so
that it is manifestly primitive recursive: `1 - (K(b+1) - (i+1))` is `1` exactly when the
index has just reached the end of block `b`. -/
def blkOf (u : ℕ → ℚ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => blkOf u i + (1 - (blkCum u (blkOf u i + 1) - (i + 1)))

/-- Unfolding of the block index at a successor flat index. -/
theorem blkOf_succ (u : ℕ → ℚ) (i : ℕ) :
    blkOf u (i + 1) = blkOf u i + (1 - (blkCum u (blkOf u i + 1) - (i + 1))) := rfl

/-- The split series: the flat index `i` is assigned the piece `blkPiece u (blkOf u i)` of the
block it belongs to. -/
def blkSeries (u : ℕ → ℚ) (i : ℕ) : ℚ := blkPiece u (blkOf u i)

/-! ### Elementary facts -/

/-- Every block is split into a positive number of pieces. -/
theorem blkSize_pos (u : ℕ → ℚ) (n : ℕ) : 0 < blkSize u n := by
  cases n with
  | zero => norm_num [blkSize]
  | succ k => rw [blkSize, blkBound]; omega

/-- The number of pieces of a block is positive as a rational. -/
theorem blkSize_cast_pos (u : ℕ → ℚ) (n : ℕ) : (0 : ℚ) < ((blkSize u n : ℕ) : ℚ) := by
  exact_mod_cast blkSize_pos u n

/-- The pieces of a positive term are positive. -/
theorem blkPiece_pos {u : ℕ → ℚ} (hu : ∀ n, 0 < u n) (n : ℕ) : 0 < blkPiece u n :=
  div_pos (hu n) (blkSize_cast_pos u n)

/-- A piece of the `n`-th block is at most the `n`-th term itself. -/
theorem blkPiece_le {u : ℕ → ℚ} (hu : ∀ n, 0 < u n) (n : ℕ) : blkPiece u n ≤ u n := by
  rw [blkPiece]
  refine div_le_self (hu n).le ?_
  exact_mod_cast blkSize_pos u n

/-- The chosen block size is strictly above `u_{n+1}·kₙ·den(uₙ)`. -/
theorem lt_blkBound (u : ℕ → ℚ) (n k : ℕ) :
    u (n + 1) * (k : ℚ) * (((u n).den : ℕ) : ℚ) < ((blkBound u n k : ℕ) : ℚ) := by
  set w : ℚ := u (n + 1) * (k : ℚ) * (((u n).den : ℕ) : ℚ) with hw
  have hfloor : ratDyadicFloor w 0 = ⌊w⌋₊ := by
    rw [ratDyadicFloor_eq_floor]
    norm_num
  rw [blkBound, hfloor]
  push_cast
  exact Nat.lt_floor_add_one w

/-- **The pieces are non-increasing.** -/
theorem blkPiece_succ_le {u : ℕ → ℚ} (hu : ∀ n, 0 < u n) (n : ℕ) :
    blkPiece u (n + 1) ≤ blkPiece u n := by
  have hkn : (0 : ℚ) < ((blkSize u n : ℕ) : ℚ) := blkSize_cast_pos u n
  have hkn1 : (0 : ℚ) < ((blkSize u (n + 1) : ℕ) : ℚ) := blkSize_cast_pos u (n + 1)
  have hden : (0 : ℚ) < (((u n).den : ℕ) : ℚ) := by
    exact_mod_cast (u n).pos
  -- `uₙ · den(uₙ) = num(uₙ) ≥ 1`
  have hnum : (1 : ℚ) ≤ u n * (((u n).den : ℕ) : ℚ) := by
    have hd : u n * (((u n).den : ℕ) : ℚ) = ((u n).num : ℚ) := by
      have := Rat.num_div_den (u n)
      field_simp at this ⊢
      linarith [this]
    rw [hd]
    have : (1 : ℤ) ≤ (u n).num := Rat.num_pos.2 (hu n)
    exact_mod_cast this
  have hkey : u (n + 1) * ((blkSize u n : ℕ) : ℚ)
      ≤ u n * ((blkSize u (n + 1) : ℕ) : ℚ) := by
    have h1 := lt_blkBound u n (blkSize u n)
    rw [show blkSize u (n + 1) = blkBound u n (blkSize u n) from rfl]
    have hpos : (0 : ℚ) < u (n + 1) * ((blkSize u n : ℕ) : ℚ) := mul_pos (hu (n + 1)) hkn
    nlinarith [h1, hnum, hpos, hu n]
  rw [blkPiece, blkPiece, div_le_div_iff₀ hkn1 hkn]
  linarith [hkey]

/-- The split series of a positive series is positive. -/
theorem blkSeries_pos {u : ℕ → ℚ} (hu : ∀ n, 0 < u n) (i : ℕ) : 0 < blkSeries u i :=
  blkPiece_pos hu _

/-- The split series of a series of terms below one stays below one. -/
theorem blkSeries_lt_one {u : ℕ → ℚ} (hu : ∀ n, 0 < u n) (hu1 : ∀ n, u n < 1) (i : ℕ) :
    blkSeries u i < 1 :=
  lt_of_le_of_lt (blkPiece_le hu _) (hu1 _)

/-! ### The block decomposition of the index set -/

/-- The first flat index of a block is strictly below that of the next block. -/
theorem blkCum_lt_succ (u : ℕ → ℚ) (n : ℕ) : blkCum u n < blkCum u (n + 1) := by
  rw [blkCum]
  have := blkSize_pos u n
  omega

/-- The first flat indices of the blocks are strictly increasing. -/
theorem blkCum_strictMono (u : ℕ → ℚ) : StrictMono (blkCum u) :=
  strictMono_nat_of_lt_succ (blkCum_lt_succ u)

/-- The first flat index of block `n` is at least `n`. -/
theorem le_blkCum (u : ℕ → ℚ) (n : ℕ) : n ≤ blkCum u n := by
  induction n with
  | zero => simp [blkCum]
  | succ k ih =>
    have := blkSize_pos u k
    rw [blkCum]
    omega

/-- The block of a flat index is the one whose range of flat indices contains it. -/
theorem blkOf_spec (u : ℕ → ℚ) (i : ℕ) :
    blkCum u (blkOf u i) ≤ i ∧ i < blkCum u (blkOf u i + 1) := by
  induction i with
  | zero =>
    have hb : blkOf u 0 = 0 := rfl
    have h := blkCum_lt_succ u 0
    have h0 : blkCum u 0 = 0 := rfl
    rw [hb]
    omega
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih
    have hstep := blkOf_succ u i
    have h3 := blkCum_lt_succ u (blkOf u i + 1)
    rcases Nat.lt_or_ge (i + 1) (blkCum u (blkOf u i + 1)) with hc | hc
    · have hb : blkOf u (i + 1) = blkOf u i := by omega
      rw [hb]
      omega
    · have hb : blkOf u (i + 1) = blkOf u i + 1 := by omega
      rw [hb]
      omega

/-- A flat index in the range of block `n` has block index `n`. -/
theorem blkOf_eq {u : ℕ → ℚ} {n i : ℕ} (h1 : blkCum u n ≤ i) (h2 : i < blkCum u (n + 1)) :
    blkOf u i = n := by
  obtain ⟨hb1, hb2⟩ := blkOf_spec u i
  by_contra hne
  rcases Nat.lt_or_ge (blkOf u i) n with hlt | hge
  · have : blkCum u (blkOf u i + 1) ≤ blkCum u n :=
      (blkCum_strictMono u).monotone (by omega)
    omega
  · have hgt : n < blkOf u i := by omega
    have : blkCum u (n + 1) ≤ blkCum u (blkOf u i) :=
      (blkCum_strictMono u).monotone (by omega)
    omega

/-- Passing to the next flat index either stays in the same block or moves to the next. -/
theorem blkOf_succ_cases (u : ℕ → ℚ) (i : ℕ) :
    blkOf u (i + 1) = blkOf u i ∨ blkOf u (i + 1) = blkOf u i + 1 := by
  have := blkOf_succ u i
  omega

/-- The block index is non-decreasing in the flat index. -/
theorem blkOf_le_succ (u : ℕ → ℚ) (i : ℕ) : blkOf u i ≤ blkOf u (i + 1) := by
  have := blkOf_succ u i
  omega

/-- The split series of a positive series is antitone, which is the point of the splitting. -/
theorem blkSeries_antitone {u : ℕ → ℚ} (hu : ∀ n, 0 < u n) : Antitone (blkSeries u) := by
  refine antitone_nat_of_succ_le fun i => ?_
  rcases blkOf_succ_cases u i with hc | hc
  · rw [blkSeries, blkSeries, hc]
  · rw [blkSeries, blkSeries, hc]
    exact blkPiece_succ_le hu _

/-! ### The partial sums -/

/-- Inside one block the partial sums of the split series grow by equal pieces. -/
theorem ratRangeSum_block {u : ℕ → ℚ} (n : ℕ) : ∀ t : ℕ, t ≤ blkSize u n →
    ratRangeSum (blkSeries u) (blkCum u n + t)
      = ratRangeSum (blkSeries u) (blkCum u n) + (t : ℚ) * blkPiece u n := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have ht' : t ≤ blkSize u n := by omega
    have hblk : blkOf u (blkCum u n + t) = n := by
      refine blkOf_eq (u := u) (by omega) ?_
      rw [blkCum]
      omega
    rw [show blkCum u n + (t + 1) = (blkCum u n + t) + 1 by omega, ratRangeSum, ih ht',
      blkSeries, hblk]
    push_cast
    ring

/-- At the first flat index of block `n`, the split series has the same partial sum as the
original series at `n`. -/
theorem ratRangeSum_blkSeries_blkCum (u : ℕ → ℚ) (n : ℕ) :
    ratRangeSum (blkSeries u) (blkCum u n) = ratRangeSum u n := by
  induction n with
  | zero => simp [blkCum, ratRangeSum]
  | succ n ih =>
    have hsize : (0 : ℚ) < ((blkSize u n : ℕ) : ℚ) := blkSize_cast_pos u n
    rw [show blkCum u (n + 1) = blkCum u n + blkSize u n from rfl,
      ratRangeSum_block n (blkSize u n) le_rfl, ih, ratRangeSum, blkPiece]
    congr 1
    field_simp

/-! ### Convergence -/

/-- Partial sums of a nonnegative rational series are non-decreasing as reals. -/
theorem monotone_ratRangeSum_real {v : ℕ → ℚ} (hv : ∀ n, 0 ≤ v n) :
    Monotone (fun n : ℕ => ((ratRangeSum v n : ℚ) : ℝ)) := by
  refine monotone_nat_of_le_succ fun n => ?_
  have h := hv n
  have : ((ratRangeSum v (n + 1) : ℚ) : ℝ) = ((ratRangeSum v n : ℚ) : ℝ) + ((v n : ℚ) : ℝ) := by
    rw [ratRangeSum]
    push_cast
    ring
  rw [this]
  have : (0 : ℝ) ≤ ((v n : ℚ) : ℝ) := by exact_mod_cast h
  linarith

/-- The split series has the same sum as the series it splits. -/
theorem tendsto_ratRangeSum_blkSeries {u : ℕ → ℚ} (hu : ∀ n, 0 < u n) {α : ℝ}
    (hlim : Filter.Tendsto (fun n => ((ratRangeSum u n : ℚ) : ℝ)) Filter.atTop (nhds α)) :
    Filter.Tendsto (fun j => ((ratRangeSum (blkSeries u) j : ℚ) : ℝ)) Filter.atTop (nhds α) := by
  have hmr : Monotone (fun j : ℕ => ((ratRangeSum (blkSeries u) j : ℚ) : ℝ)) :=
    monotone_ratRangeSum_real (fun i => (blkSeries_pos hu i).le)
  have hmu : Monotone (fun n : ℕ => ((ratRangeSum u n : ℚ) : ℝ)) :=
    monotone_ratRangeSum_real (fun n => (hu n).le)
  have hule : ∀ n, ((ratRangeSum u n : ℚ) : ℝ) ≤ α := hmu.ge_of_tendsto hlim
  have hcast : ∀ n : ℕ, ((ratRangeSum (blkSeries u) (blkCum u n) : ℚ) : ℝ)
      = ((ratRangeSum u n : ℚ) : ℝ) := by
    intro n
    rw [ratRangeSum_blkSeries_blkCum]
  have hrle : ∀ j, ((ratRangeSum (blkSeries u) j : ℚ) : ℝ) ≤ α := by
    intro j
    calc ((ratRangeSum (blkSeries u) j : ℚ) : ℝ)
        ≤ ((ratRangeSum (blkSeries u) (blkCum u j) : ℚ) : ℝ) := hmr (le_blkCum u j)
      _ = ((ratRangeSum u j : ℚ) : ℝ) := hcast j
      _ ≤ α := hule j
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim ε hε
  refine ⟨blkCum u N, fun j hj => ?_⟩
  have h1 : ((ratRangeSum u N : ℚ) : ℝ) ≤ ((ratRangeSum (blkSeries u) j : ℚ) : ℝ) := by
    rw [← hcast N]
    exact hmr hj
  have h2 := hN N le_rfl
  rw [Real.dist_eq, abs_lt] at h2
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith [h1, h2.1], by linarith [hrle j, hε]⟩

/-! ### Computability -/

/-- The number of pieces of each block is computable. -/
theorem computable_blkSize {u : ℕ → ℚ} (hu : Computable u) : Computable (blkSize u) := by
  have hstep : Computable₂ (fun (_ : ℕ) (p : ℕ × ℕ) => blkBound u p.1 p.2) := by
    have h1 : Computable (fun q : ℕ × ℕ × ℕ => u (q.2.1 + 1)) :=
      hu.comp (Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd)
        (Computable.const 1))
    have h2 : Computable (fun q : ℕ × ℕ × ℕ => ((q.2.2 : ℕ) : ℚ)) :=
      computable_nat_to_rat.comp (Computable.snd.comp Computable.snd)
    have h3 : Computable (fun q : ℕ × ℕ × ℕ => (((u q.2.1).den : ℕ) : ℚ)) :=
      computable_nat_to_rat.comp (computable_ratDen.comp
        (hu.comp (Computable.fst.comp Computable.snd)))
    have hw : Computable (fun q : ℕ × ℕ × ℕ =>
        u (q.2.1 + 1) * ((q.2.2 : ℕ) : ℚ) * (((u q.2.1).den : ℕ) : ℚ)) :=
      computable₂_ratMul.comp (computable₂_ratMul.comp h1 h2) h3
    have hfl : Computable (fun q : ℕ × ℕ × ℕ =>
        ratDyadicFloor (u (q.2.1 + 1) * ((q.2.2 : ℕ) : ℚ) * (((u q.2.1).den : ℕ) : ℚ)) 0) :=
      computable_ratDyadicFloor.comp hw (Computable.const 0)
    exact Primrec.nat_add.to_comp.comp hfl (Computable.const 1)
  have hrec := Computable.nat_rec (σ := ℕ) Computable.id (Computable.const 1) hstep
  refine hrec.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [blkSize]
    exact congrArg (fun x => blkBound u n x) ih

/-- A piece of the `n`-th block, written with numerator and denominator. -/
theorem blkPiece_num_den (u : ℕ → ℚ) (n : ℕ) :
    blkPiece u n = (((u n).num : ℤ) : ℚ) / (((u n).den * blkSize u n : ℕ) : ℚ) := by
  have hdpos : (0 : ℚ) < (((u n).den : ℕ) : ℚ) := by exact_mod_cast (u n).pos
  have hdne : (((u n).den : ℕ) : ℚ) ≠ 0 := ne_of_gt hdpos
  have hkpos : (0 : ℚ) < ((blkSize u n : ℕ) : ℚ) := blkSize_cast_pos u n
  have key : u n * (((u n).den : ℕ) : ℚ) = ((u n).num : ℚ) := by
    have h := Rat.num_div_den (u n)
    field_simp at h
    linarith [h]
  rw [blkPiece]
  push_cast
  rw [div_eq_div_iff (ne_of_gt hkpos) (by positivity)]
  calc u n * ((((u n).den : ℕ) : ℚ) * ((blkSize u n : ℕ) : ℚ))
      = (u n * (((u n).den : ℕ) : ℚ)) * ((blkSize u n : ℕ) : ℚ) := by ring
    _ = ((u n).num : ℚ) * ((blkSize u n : ℕ) : ℚ) := by rw [key]

/-- The piece size of each block is computable. -/
theorem computable_blkPiece {u : ℕ → ℚ} (hu : Computable u) : Computable (blkPiece u) :=
  computable_of_num_den (N := fun n : ℕ => (u n).num)
    (D := fun n : ℕ => (u n).den * blkSize u n)
    (computable_ratNum.comp hu)
    (Primrec.nat_mul.to_comp.comp (computable_ratDen.comp hu) (computable_blkSize hu))
    (fun n => Nat.mul_pos (u n).pos (blkSize_pos u n))
    (fun n => blkPiece_num_den u n)

/-- The first flat index of each block is computable. -/
theorem computable_blkCum {u : ℕ → ℚ} (hu : Computable u) : Computable (blkCum u) := by
  have hstep : Computable₂ (fun (_ : ℕ) (p : ℕ × ℕ) => p.2 + blkSize u p.1) := by
    have h1 : Computable (fun q : ℕ × ℕ × ℕ => q.2.2) := Computable.snd.comp Computable.snd
    have h2 : Computable (fun q : ℕ × ℕ × ℕ => blkSize u q.2.1) :=
      (computable_blkSize hu).comp (Computable.fst.comp Computable.snd)
    exact Primrec.nat_add.to_comp.comp h1 h2
  have hrec := Computable.nat_rec (σ := ℕ) Computable.id (Computable.const 0) hstep
  refine hrec.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [blkCum]
    exact congrArg (fun x => x + blkSize u n) ih

/-- The block index of a flat index is computable. -/
theorem computable_blkOf {u : ℕ → ℚ} (hu : Computable u) : Computable (blkOf u) := by
  have hadd : Computable₂ (fun a b : ℕ => a + b) := Primrec.nat_add.to_comp
  have hsub : Computable₂ (fun a b : ℕ => a - b) := Primrec.nat_sub.to_comp
  have hstep : Computable₂ (fun (_ : ℕ) (p : ℕ × ℕ) =>
      p.2 + (1 - (blkCum u (p.2 + 1) - (p.1 + 1)))) := by
    have hp2 : Computable (fun q : ℕ × ℕ × ℕ => q.2.2) := Computable.snd.comp Computable.snd
    have hp1 : Computable (fun q : ℕ × ℕ × ℕ => q.2.1) := Computable.fst.comp Computable.snd
    have hK : Computable (fun q : ℕ × ℕ × ℕ => blkCum u (q.2.2 + 1)) :=
      (computable_blkCum hu).comp (hadd.comp hp2 (Computable.const 1))
    have hi : Computable (fun q : ℕ × ℕ × ℕ => q.2.1 + 1) := hadd.comp hp1 (Computable.const 1)
    exact hadd.comp hp2 (hsub.comp (Computable.const 1) (hsub.comp hK hi))
  have hrec := Computable.nat_rec (σ := ℕ) Computable.id (Computable.const 0) hstep
  refine hrec.of_eq fun i => ?_
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [blkOf]
    exact congrArg (fun x => x + (1 - (blkCum u (x + 1) - (i + 1)))) ih

/-- The split series of a computable series is computable. -/
theorem computable_blkSeries {u : ℕ → ℚ} (hu : Computable u) : Computable (blkSeries u) :=
  (computable_blkPiece hu).comp (computable_blkOf hu)

end Kolmogorov
