/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint.GapCover
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealApi
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealCantor
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaPrefixCore

/-!
# Reading the leading bits of a random real off a lower approximation

The reverse direction of SUV Theorem 116 (p. 171) computes `Ω↾n` from `B(n + O(log n))`.
The computability half is routine — running the semimeasure enumeration for `B(·)` steps
gives a rational `q` with `q ≤ Ω < q + 2^{-M}` — but a lower approximation of a real does
**not** by itself determine its leading bits.  This module isolates the two
statements that supply the missing determinacy; both are about the binary expansion of a
random real and neither mentions complexity.

## The carry analysis

Write `Ω = cantorReal w`, `v_n := bitsValue (Ω↾n) = j_n · 2^{-n}` with
`j_n = bitsNum (Ω↾n) < 2^n`, and `tail_n := Ω − v_n = ∑_{k ≥ n} [w k]·2^{-(k+1)} ∈ [0, 2^{-n}]`
(`bitsValue_cantorPrefix_le`, `le_bitsValue_cantorPrefix_add`).  Suppose `0 ≤ q ≤ Ω < q + 2^{-M}`
and read off the `n` leading bits of `q`, i.e. `⌊q·2^n⌋`.  Two inequalities are needed.

* **Upper**, `⌊q·2^n⌋ ≤ j_n`.  From `q ≤ Ω ≤ v_n + 2^{-n}` and the fact that the second
  inequality is *strict* — `Ω` is irrational, so `Ω ≠ (j_n+1)·2^{-n}` — one gets
  `q·2^n < j_n + 1`.  This costs only irrationality; no slack is needed.
* **Lower**, `j_n ≤ ⌊q·2^n⌋`, i.e. `v_n ≤ q`.  All that is known is
  `q > Ω − 2^{-M} = v_n + tail_n − 2^{-M}`, so it suffices that `tail_n ≥ 2^{-M}`, and a
  single `k` with `n ≤ k < M` and `w k = true` already gives
  `tail_n ≥ 2^{-(k+1)} ≥ 2^{-M}`.

So **the one failure mode is a run of zeros**: if the bits `n, n+1, …, M−1` of `Ω` all
vanish then `q` may end in a run of ones just below `j_n·2^{-n}`, the carry sits inside the
error window, and `⌊q·2^n⌋ = j_n − 1`.  The window is the half-open `[n, M)`; the bound is
exact and needs no additive constant.

## What the `O(log n)` slack buys

`Ω` is Martin-Löf random (`isMartinLofRandomReal_omegaReal`), and randomness forbids zero
runs of length `2·log₂(n+2) + O(1)` at position `n`.  Indeed, put
`r n := 2 · Nat.log 2 (n + 2) + 2` and, at level `k`, cover

  `I_{n,j} := (j·2^{-n}, j·2^{-n} + 2^{-(n + r n + k)})`,  `n : ℕ`, `j < 2^n`.

If the bits `n, …, n + r n + k − 1` of `Ω` all vanish then `0 < tail_n < 2^{-(n + r n + k)}`
(both strict by irrationality), so `Ω ∈ I_{n, j_n}`.  The total length is

  `∑_n 2^n · 2^{-(n + r n + k)} = 2^{-k} · ∑_n 2^{-r n} ≤ 2^{-k} · ∑_n (n+2)^{-2} < 2^{-k}`,

using `2 ^ Nat.log 2 m > m / 2`.  The family is computable in `(k, ⟨n, j⟩)`, so if the
failure happened at *every* level `k` then `{Ω}` would be an effectively null set,
contradicting randomness.  Hence there is a single constant `c` with: for every `n` some
bit of `Ω` in the window `[n, n + c·log₂(n+2) + c)` is `1` — which is exactly the shape of
the slack in the frozen statement of Theorem 116.

The two leaves below are these two statements.  `Omega/SolovayFunctions.lean` combines them
with `exists_computable_ratApprox_le_BPlain` (the approximation side, which is where
`BPlain` enters) to close `omegaPrefix_of_busyBeaver`.
-/

namespace Kolmogorov

open scoped ENNReal


/-! ### The two bit-string helpers -/

/-- Horner's scheme (`bitsNum`) and the big-endian decoder (`devBitsToNat`) agree. -/
theorem bitsNum_eq_devBitsToNat (x : BitString) : bitsNum x = devBitsToNat x := by
  induction x using List.reverseRecOn with
  | nil => rfl
  | append_singleton t b ih =>
      rw [bitsNum_append_singleton, devBitsToNat_append, ih]
      cases b <;> simp [devBitsToNat] <;> ring

/-- The decoder `n, q ↦ natToBits n ⌊q·2ⁿ⌋` is computable. -/
theorem computable₂_bitDecoder :
    Computable₂ (fun (n : ℕ) (q : ℚ) => natToBits n (ratDyadicFloor q n)) := by
  have hfl : Computable (fun p : ℕ × ℚ => ratDyadicFloor p.2 p.1) :=
    computable_ratDyadicFloor.comp Computable.snd Computable.fst
  have haux : Computable (fun p : ℕ × ℚ => bitsAux p.1 (ratDyadicFloor p.2 p.1)) :=
    computable_bitsAux.comp Computable.fst hfl
  exact (Computable.fst.comp (Computable.snd.comp haux)).of_eq fun p => rfl

/-! ### The tail estimate: one `1` in the window is worth `2^{-M}` -/

/-- A `1` at a position `k ≥ n` pushes the real `2^{-(k+1)}` above the value of its
`n`-bit prefix.  This is the quantitative half of the carry analysis. -/
theorem bitsValue_add_le_cantorReal {w : CantorSeq} {n k : ℕ} (hnk : n ≤ k)
    (hwk : w k = true) :
    ((bitsValue (cantorPrefix w n) : ℚ) : ℝ) + (1 : ℝ) / 2 ^ (k + 1) ≤ cantorReal w := by
  have hS := summable_cantorTerm w
  have hnn : ∀ i : ℕ, 0 ≤ (if w i then (1 : ℝ) / 2 ^ (i + 1) else 0) := by
    intro i; by_cases h : w i <;> simp [h]
  have hcast : ((bitsValue (cantorPrefix w n) : ℚ) : ℝ)
      = ∑ i ∈ Finset.range n, (if w i then (1 : ℝ) / 2 ^ (i + 1) else 0) := by
    rw [bitsValue_cantorPrefix]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by by_cases h : w i <;> simp [h]
  have hknot : k ∉ Finset.range n := by simp; omega
  have hsum : ∑ i ∈ insert k (Finset.range n), (if w i then (1 : ℝ) / 2 ^ (i + 1) else 0)
      = (1 : ℝ) / 2 ^ (k + 1)
        + ∑ i ∈ Finset.range n, (if w i then (1 : ℝ) / 2 ^ (i + 1) else 0) := by
    rw [Finset.sum_insert hknot, hwk, ite_eq_left rfl]
  have hle := hS.sum_le_tsum (insert k (Finset.range n)) fun i _ => hnn i
  rw [hsum] at hle
  rw [hcast]
  have : cantorReal w = ∑' i : ℕ, (if w i then (1 : ℝ) / 2 ^ (i + 1) else 0) := rfl
  rw [this]
  linarith

/-! ### The floor identity -/

-- the cast juggling between `ℚ` and `ℝ` around `Nat.floor`
/-- **The carry analysis.**  A rational lower approximation `q` of `cantorReal w` within
`2^{-M}` has the same leading `n` binary digits, provided `cantorReal w` is irrational and
some bit of `w` in the window `[n, M)` is `1`. -/
theorem ratDyadicFloor_eq_bitsNum {w : CantorSeq} {q : ℚ} {n M : ℕ} (_hq0 : 0 ≤ q)
    (hirr : ∀ r : ℚ, cantorReal w ≠ (r : ℝ))
    (hlow : ((q : ℚ) : ℝ) ≤ cantorReal w)
    (hhigh : cantorReal w < ((q : ℚ) : ℝ) + 1 / 2 ^ M)
    (hone : ∃ k, n ≤ k ∧ k < M ∧ w k = true) :
    ratDyadicFloor q n = bitsNum (cantorPrefix w n) := by
  obtain ⟨k, hnk, hkM, hwk⟩ := hone
  set j : ℕ := bitsNum (cantorPrefix w n) with hj
  have hlen : (cantorPrefix w n).length = n := cantorPrefix_length w n
  have hbv : bitsValue (cantorPrefix w n) = (j : ℚ) / 2 ^ n := by rw [bitsValue, hlen]
  have hpowR : (0 : ℝ) < 2 ^ n := by positivity
  -- the upper inequality: irrationality makes the sandwich strict
  have hup : cantorReal w < ((j : ℝ) + 1) / 2 ^ n := by
    have h1 := le_bitsValue_cantorPrefix_add w n
    have h2 : ((bitsValue (cantorPrefix w n) : ℚ) : ℝ) = (j : ℝ) / 2 ^ n := by
      rw [hbv]; push_cast; ring
    have h3 : cantorReal w ≤ ((j : ℝ) + 1) / 2 ^ n := by
      have : cantorReal w = ∑' i : ℕ, (if w i then (1 : ℝ) / 2 ^ (i + 1) else 0) := rfl
      rw [this]
      rw [h2] at h1
      have : (j : ℝ) / 2 ^ n + 1 / 2 ^ n = ((j : ℝ) + 1) / 2 ^ n := by ring
      linarith [h1]
    rcases lt_or_eq_of_le h3 with h | h
    · exact h
    · exfalso
      refine hirr (((j : ℚ) + 1) / 2 ^ n) ?_
      rw [h]
      push_cast
      ring
  -- the lower inequality: the `1` in the window
  have hlo : (j : ℝ) / 2 ^ n < ((q : ℚ) : ℝ) := by
    have h1 := bitsValue_add_le_cantorReal (w := w) (n := n) (k := k) hnk hwk
    have h2 : ((bitsValue (cantorPrefix w n) : ℚ) : ℝ) = (j : ℝ) / 2 ^ n := by
      rw [hbv]; push_cast; ring
    rw [h2] at h1
    have h3 : (1 : ℝ) / 2 ^ M ≤ 1 / 2 ^ (k + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  -- transport to `ℚ` and read off the floor
  have hjq : (j : ℚ) < q * 2 ^ n := by
    have : ((j : ℚ) : ℝ) < ((q * 2 ^ n : ℚ) : ℝ) := by
      push_cast
      rw [div_lt_iff₀ hpowR] at hlo
      linarith
    exact_mod_cast this
  have hqj : q * 2 ^ n < (j : ℚ) + 1 := by
    have hR : ((q * 2 ^ n : ℚ) : ℝ) < (((j : ℚ) + 1 : ℚ) : ℝ) := by
      push_cast
      rw [lt_div_iff₀ hpowR] at hup
      nlinarith [hlow, hpowR, hup]
    exact_mod_cast hR
  rw [ratDyadicFloor_eq_floor]
  have hnn : (0 : ℚ) ≤ q * (2 ^ n : ℕ) := by
    have : (0 : ℚ) ≤ ((2 : ℚ) ^ n) := by positivity
    push_cast
    nlinarith
  refine (Nat.floor_eq_iff hnn).2 ⟨?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith

/-! ### Leaf 1: the decoder -/

/-- **Determinacy of the leading bits.** There is a *computable*
decoder `D` which, from the precision `n` and a rational lower approximation `q` of a real
`cantorReal w` that is accurate to `2^{-M}`, returns the first `n` bits of `w` — **provided**
the expansion of `w` carries a `1` somewhere in the window `[n, M)`.

Both hypotheses are necessary and both are cheap for `Ω`: irrationality is
`ne_ratCast_of_isMartinLofRandomReal`, and the `1` in the window is
`exists_const_window_true_of_isMartinLofRandomReal` below.  See the module docstring for the
carry analysis; the natural witness is `D n q := natToBits n (ratDyadicFloor q n)`
(`ratDyadicFloor`, `computable_ratDyadicFloor` in `AlgorithmicRandomness/RatComputable.lean`;
`natToBits`, `computable_bitsAux` in `AlgorithmicRandomness/EffectiveSLLNBernoulli.lean`), and
the proof is the pair of inequalities `⌊q·2^n⌋ = bitsNum (cantorPrefix w n)` spelled out
there, followed by injectivity of the fixed-width code on strings of length `n`
(`devBitsToNat_injective_of_length_eq`; note that the bridge `bitsNum = devBitsToNat` is a
routine induction that the repository does not yet have). -/
theorem exists_computable_cantorPrefix_of_ratApprox :
    ∃ D : ℕ → ℚ → BitString, Computable₂ D ∧
      ∀ (w : CantorSeq) (q : ℚ) (n M : ℕ), 0 ≤ q →
        (∀ r : ℚ, cantorReal w ≠ (r : ℝ)) →
        ((q : ℚ) : ℝ) ≤ cantorReal w →
        cantorReal w < ((q : ℚ) : ℝ) + 1 / 2 ^ M →
        (∃ k, n ≤ k ∧ k < M ∧ w k = true) →
        D n q = cantorPrefix w n :=
  ⟨fun n q => natToBits n (ratDyadicFloor q n), computable₂_bitDecoder,
    fun w q n M hq0 hirr hlow hhigh hone => by
      dsimp only
      rw [ratDyadicFloor_eq_bitsNum hq0 hirr hlow hhigh hone, bitsNum_eq_devBitsToNat]
      have h := natToBits_bitsToNat (cantorPrefix w n)
      rwa [cantorPrefix_length] at h⟩

/-! ### Leaf 2: randomness forbids long runs of zeros -/

/-! #### The Martin-Löf test that forbids the runs

The test of the module docstring, written out.  `zeroRunLen n = 2·log₂(n+2) + 2` is the
window the frozen statement asks for with `c = 2`; at level `k` (and a fixed shift `B`
absorbing the total mass of the family) the cover consists of the cells

  `I_{n,j} = (j·2^{-n}, j·2^{-n} + 2^{-(n + zeroRunLen n + k + B)})`,  `j < 2^n`,

whose total length is `2^{-(k+B)}·∑_n 2^{-zeroRunLen n} ≤ 2^{-k}`.
-/

/-- The zero run the test looks for at position `n`: the window `2·log₂(n+2) + 2` of the
frozen statement of the leaf, instantiated at `c = 2`. -/
def zeroRunLen (n : ℕ) : ℕ := 2 * Nat.log 2 (n + 2) + 2

/-- The left endpoint of the cover cell coded by `i = ⟨n, j⟩`: the dyadic rational
`j·2^{-n}`. -/
def zeroRunLeft (i : ℕ) : ℚ := ratOfDyadic i.unpair.2 i.unpair.1

/-- The precision of the cover cell coded by `i = ⟨n, j⟩` at level `k` and shift `B`. -/
def zeroRunExp (B k i : ℕ) : ℕ := i.unpair.1 + (zeroRunLen i.unpair.1 + k + B)

/-- The left endpoint of a zero-run cell is computable from its index. -/
theorem computable_zeroRunLeft : Computable zeroRunLeft := by
  have h1 : Computable (fun i : ℕ => i.unpair.2) := (Primrec.snd.comp Primrec.unpair).to_comp
  have h2 : Computable (fun i : ℕ => i.unpair.1) := (Primrec.fst.comp Primrec.unpair).to_comp
  exact Computable₂.comp computable₂_ratOfDyadic h1 h2

/-- The precision of a zero-run cell is computable in the level and the index. -/
theorem computable₂_zeroRunExp (B : ℕ) : Computable₂ (zeroRunExp B) := by
  have hadd : Computable₂ (fun a b : ℕ => a + b) := Primrec.nat_add.to_comp
  have hn : Computable (fun p : ℕ × ℕ => p.2.unpair.1) :=
    ((Primrec.fst.comp Primrec.unpair).to_comp).comp Computable.snd
  have hlog : Computable (fun p : ℕ × ℕ => Nat.log 2 (p.2.unpair.1 + 2)) :=
    computable_natLogTwo.comp (hadd.comp hn (Computable.const 2))
  have hlen : Computable (fun p : ℕ × ℕ => zeroRunLen p.2.unpair.1) := by
    have h2 : Computable (fun p : ℕ × ℕ => 2 * Nat.log 2 (p.2.unpair.1 + 2)) :=
      Computable₂.comp (Primrec.nat_mul.to_comp) (Computable.const 2) hlog
    exact hadd.comp h2 (Computable.const 2)
  exact hadd.comp hn (hadd.comp (hadd.comp hlen Computable.fst) (Computable.const B))

/-- The cell of the cover coded by `i = ⟨n, j⟩` at level `k` and shift `B`: the interval
`(j·2^{-n}, j·2^{-n} + 2^{-(n + zeroRunLen n + k + B)})`. -/
def zeroRunCell (B k i : ℕ) : ℚ × ℚ :=
  (zeroRunLeft i, zeroRunLeft i + ((2 : ℚ)⁻¹) ^ zeroRunExp B k i)

/-- The zero-run cell is computable in the level and the index. -/
theorem computable₂_zeroRunCell (B : ℕ) : Computable₂ (zeroRunCell B) := by
  have hleft : Computable (fun p : ℕ × ℕ => zeroRunLeft p.2) :=
    computable_zeroRunLeft.comp Computable.snd
  have hright : Computable (fun p : ℕ × ℕ =>
      zeroRunLeft p.2 + ((2 : ℚ)⁻¹) ^ zeroRunExp B p.1 p.2) :=
    Computable₂.comp computable₂_ratAdd hleft
      (computable_inv_two_pow_rat.comp (computable₂_zeroRunExp B))
  exact Computable.pair hleft hright

/-- The guard `j < 2^n` on the index, kept apart from the cell so that the two
computability elaborations stay small. -/
def zeroRunIdx (i : ℕ) : Option ℕ :=
  cond (decide (i.unpair.2 < 2 ^ i.unpair.1)) (some i) none

/-- The index guard of the zero-run test is computable. -/
theorem computable_zeroRunIdx : Computable zeroRunIdx := by
  have hn : Computable (fun i : ℕ => i.unpair.1) := (Primrec.fst.comp Primrec.unpair).to_comp
  have hj : Computable (fun i : ℕ => i.unpair.2) := (Primrec.snd.comp Primrec.unpair).to_comp
  have hpow : Computable (fun i : ℕ => 2 ^ i.unpair.1) := Computable.pow2.comp hn
  have hlt : Computable₂ (fun a b : ℕ => decide (a < b)) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp
  have htest : Computable (fun i : ℕ => decide (i.unpair.2 < 2 ^ i.unpair.1)) :=
    Computable₂.comp hlt hj hpow
  have h := Computable.cond htest Computable.option_some
    (Computable.const (none : Option ℕ))
  exact h.of_eq (fun i => rfl)

/-- **The Martin-Löf test of SUV p. 171.**  A real whose binary expansion has a run of
`zeroRunLen n + k + B` zeros starting at position `n` lies in the cell of its own `n`-bit
prefix, so failure at every level `k` makes the real effectively null. -/
def zeroRunCover (B k i : ℕ) : Option (ℚ × ℚ) := (zeroRunIdx i).map (zeroRunCell B k)

/-- The zero-run test is computable in the level and the index. -/
theorem computable₂_zeroRunCover (B : ℕ) : Computable₂ (zeroRunCover B) := by
  have hidx : Computable (fun p : ℕ × ℕ => zeroRunIdx p.2) :=
    computable_zeroRunIdx.comp Computable.snd
  have hcell : Computable₂ (fun (p : ℕ × ℕ) (i : ℕ) => zeroRunCell B p.1 i) :=
    Computable₂.comp (computable₂_zeroRunCell B) (Computable.fst.comp Computable.fst)
      Computable.snd
  exact Computable.option_map hidx hcell

/-! #### The total length of the family -/

/-- `2 ^ -B * 2 ^ B = 1` in the extended nonnegative reals. -/
theorem inv_two_pow_mul_two_pow (B : ℕ) : (2 : ℝ≥0∞)⁻¹ ^ B * 2 ^ B = 1 := by
  rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]

/-- `2 ^ n * 2 ^ -(n + e) = 2 ^ -e` in the extended nonnegative reals. -/
theorem two_pow_mul_inv_two_pow_add (n e : ℕ) :
    (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ (n + e) = (2 : ℝ≥0∞)⁻¹ ^ e := by
  rw [pow_add, ← mul_assoc, mul_comm ((2 : ℝ≥0∞) ^ n) ((2 : ℝ≥0∞)⁻¹ ^ n),
    inv_two_pow_mul_two_pow, one_mul]

/-- The interval from `a` to `a + d` has length `d`. -/
theorem ratIntervalLength_add (a d : ℚ) :
    ratIntervalLength (a, a + d) = ENNReal.ofReal ((d : ℚ) : ℝ) := by
  rw [ratIntervalLength]
  congr 1
  push_cast
  ring

/-- The Kraft sum of the family is finite: `2^{-zeroRunLen n} ≤ (n+2)^{-2}` because
`n + 2 < 2^{log₂(n+2)+1}`, and `∑ (n+2)^{-2}` converges. -/
theorem tsum_inv_two_pow_zeroRunLen_ne_top :
    (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ zeroRunLen n) ≠ ⊤ := by
  have hsummable : Summable (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) := by
    have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.2 (by norm_num)
    refine ((summable_nat_add_iff 2).2 hbase).congr (fun n => ?_)
    push_cast
    ring
  have hterm : ∀ n : ℕ,
      (2 : ℝ≥0∞)⁻¹ ^ zeroRunLen n ≤ ENNReal.ofReal (1 / ((n : ℝ) + 2) ^ 2) := by
    intro n
    rw [← ofReal_inv_two_pow]
    refine ENNReal.ofReal_le_ofReal ?_
    have hlt : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hN : (n + 2) ^ 2 ≤ 2 ^ zeroRunLen n := by
      have hsq : (n + 2) ^ 2 ≤ (2 ^ (Nat.log 2 (n + 2) + 1)) ^ 2 :=
        Nat.pow_le_pow_left hlt.le 2
      have hrw : (2 ^ (Nat.log 2 (n + 2) + 1)) ^ 2 = 2 ^ zeroRunLen n := by
        rw [← pow_mul, zeroRunLen]
        congr 1
        ring
      omega
    have hR : ((n : ℝ) + 2) ^ 2 ≤ 2 ^ zeroRunLen n := by
      have := (Nat.cast_le (α := ℝ)).2 hN
      push_cast at this
      linarith
    have hpos : (0 : ℝ) < ((n : ℝ) + 2) ^ 2 := by positivity
    rw [show ((2 : ℝ)⁻¹) ^ zeroRunLen n = 1 / 2 ^ zeroRunLen n by rw [inv_pow, one_div]]
    exact one_div_le_one_div_of_le hpos hR
  have hcmp : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ zeroRunLen n)
      ≤ ∑' n : ℕ, ENNReal.ofReal (1 / ((n : ℝ) + 2) ^ 2) := ENNReal.tsum_le_tsum hterm
  have heq : (∑' n : ℕ, ENNReal.ofReal (1 / ((n : ℝ) + 2) ^ 2))
      = ENNReal.ofReal (∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsummable).symm
  rw [heq] at hcmp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcmp

/-- The weights `2 ^ -zeroRunLen n` have a finite sum, bounded by `2 ^ B` for some shift `B`;
this is the shift the zero-run test is normalised by. -/
theorem exists_shift_tsum_inv_two_pow_zeroRunLen_le :
    ∃ B : ℕ, (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ zeroRunLen n) ≤ 2 ^ B := by
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt tsum_inv_two_pow_zeroRunLen_ne_top
  refine ⟨N, le_trans hN.le ?_⟩
  have h : N ≤ 2 ^ N := Nat.lt_two_pow_self.le
  calc (N : ℝ≥0∞) ≤ ((2 ^ N : ℕ) : ℝ≥0∞) := by exact_mod_cast h
    _ = 2 ^ N := by push_cast; ring

-- the pair-reindexing of the cover sum
/-- The level-`k` member of the family has total length at most `2^{-k}`. -/
theorem tsum_zeroRunCover_le {B : ℕ}
    (hB : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ zeroRunLen n) ≤ 2 ^ B) (k : ℕ) :
    (∑' i : ℕ, (zeroRunCover B k i).elim 0 ratIntervalLength) ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
  classical
  have hterm : ∀ n j : ℕ,
      (zeroRunCover B k (Nat.pair n j)).elim (0 : ℝ≥0∞) ratIntervalLength
        = if j < 2 ^ n then (2 : ℝ≥0∞)⁻¹ ^ (n + (zeroRunLen n + k + B)) else 0 := by
    intro n j
    by_cases hj : j < 2 ^ n
    · have hc : zeroRunCover B k (Nat.pair n j)
          = some (ratOfDyadic j n,
              ratOfDyadic j n + ((2 : ℚ)⁻¹) ^ (n + (zeroRunLen n + k + B))) := by
        simp [zeroRunCover, zeroRunIdx, zeroRunCell, zeroRunLeft, zeroRunExp,
          Nat.unpair_pair, hj]
      rw [hc, ite_eq_left hj]
      change ratIntervalLength (ratOfDyadic j n,
          ratOfDyadic j n + ((2 : ℚ)⁻¹) ^ (n + (zeroRunLen n + k + B))) = _
      rw [ratIntervalLength_add]
      exact ofReal_rat_inv_two_pow _
    · have hc : zeroRunCover B k (Nat.pair n j) = none := by
        simp [zeroRunCover, zeroRunIdx, Nat.unpair_pair, hj]
      rw [hc, ite_eq_right hj]
      rfl
  have hcol : ∀ n : ℕ,
      (∑' j : ℕ, (zeroRunCover B k (Nat.pair n j)).elim (0 : ℝ≥0∞) ratIntervalLength)
        = (2 : ℝ≥0∞)⁻¹ ^ (zeroRunLen n + k + B) := by
    intro n
    rw [tsum_congr (fun j => hterm n j),
      tsum_eq_sum (s := Finset.range (2 ^ n))
        (fun j hj => ite_eq_right (by simpa using hj)),
      Finset.sum_congr rfl (fun j hj => ite_eq_left (Finset.mem_range.1 hj)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    exact two_pow_mul_inv_two_pow_add n _
  have hprod : (∑' i : ℕ, (zeroRunCover B k i).elim (0 : ℝ≥0∞) ratIntervalLength)
      = ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (zeroRunLen n + k + B) := by
    calc (∑' i : ℕ, (zeroRunCover B k i).elim (0 : ℝ≥0∞) ratIntervalLength)
        = ∑' p : ℕ × ℕ,
            (zeroRunCover B k (Nat.pair p.1 p.2)).elim (0 : ℝ≥0∞) ratIntervalLength := by
          rw [← Equiv.tsum_eq Nat.pairEquiv
            (fun i => (zeroRunCover B k i).elim (0 : ℝ≥0∞) ratIntervalLength)]
          rfl
      _ = ∑' n : ℕ, ∑' j : ℕ,
            (zeroRunCover B k (Nat.pair n j)).elim (0 : ℝ≥0∞) ratIntervalLength :=
          ENNReal.tsum_prod
            (f := fun n j =>
              (zeroRunCover B k (Nat.pair n j)).elim (0 : ℝ≥0∞) ratIntervalLength)
      _ = ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (zeroRunLen n + k + B) := tsum_congr hcol
  rw [hprod]
  have hsplit : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (zeroRunLen n + k + B))
      = (2 : ℝ≥0∞)⁻¹ ^ (k + B) * ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ zeroRunLen n := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    rw [show zeroRunLen n + k + B = (k + B) + zeroRunLen n by ring, pow_add]
  rw [hsplit]
  calc (2 : ℝ≥0∞)⁻¹ ^ (k + B) * ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ zeroRunLen n
      ≤ (2 : ℝ≥0∞)⁻¹ ^ (k + B) * 2 ^ B := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ k := by rw [pow_add, mul_assoc, inv_two_pow_mul_two_pow, mul_one]

/-! #### A run of zeros freezes the value of the prefix -/

/-- If the bits `n, …, n+m−1` of `w` all vanish then the `n`-bit and the `(n+m)`-bit
prefixes of `w` have the same value. -/
theorem bitsValue_cantorPrefix_add_of_zero_run {w : CantorSeq} {n : ℕ} :
    ∀ m : ℕ, (∀ i, n ≤ i → i < n + m → w i = false) →
      bitsValue (cantorPrefix w (n + m)) = bitsValue (cantorPrefix w n) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hz
      have hrec := ih (fun i h1 h2 => hz i h1 (by omega))
      have hstep : bitsValue (cantorPrefix w (n + m + 1))
          = bitsValue (cantorPrefix w (n + m)) := by
        rw [bitsValue_cantorPrefix, bitsValue_cantorPrefix, Finset.sum_range_succ]
        simp [hz (n + m) (Nat.le_add_right n m) (by omega)]
      have hgoal : n + (m + 1) = n + m + 1 := by omega
      rw [hgoal, hstep, hrec]

/-- **No long zero runs.** The binary expansion of a Martin-Löf random
real has, for a single constant `c` and every position `n`, a `1` inside the window
`[n, n + c·log₂(n+2) + c)`.

This is the quantitative content of the `O(log n)` slack of SUV Theorem 116.  The proof is
the Martin-Löf test displayed in the module docstring: at level `k` cover, for every `n` and
every `j < 2^n`, the interval `(j·2^{-n}, j·2^{-n} + 2^{-(n + 2·log₂(n+2) + 2 + k)})`; the
cover is computable (`computable₂_ratOfDyadic`, `Primrec.unpair`), its total length is at
most `2^{-k}` (sum over `j` gives `2^n` copies, and `∑_n 2^{-2·log₂(n+2)−2} ≤ ∑_n (n+2)^{-2}`),
and failure at every level would put the real into `⋂ₖ ⋃ …`, an effectively null set, through
`isEffectivelyNullReal_of_pow_cover`.  Only `cantorReal w`'s membership needs the two strict
inequalities `0 < tail_n < 2^{-(n + r n + k)}`, both from irrationality. -/
theorem exists_const_window_true_of_isMartinLofRandomReal {w : CantorSeq}
    (h : IsMartinLofRandomReal (cantorReal w)) :
    ∃ c : ℕ, ∀ n : ℕ, ∃ k, n ≤ k ∧ k < n + c * Nat.log 2 (n + 2) + c ∧ w k = true := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hB⟩ := exists_shift_tsum_inv_two_pow_zeroRunLen_le
  refine h {cantorReal w} ?_ rfl
  refine isEffectivelyNullReal_of_pow_cover (zeroRunCover B) (computable₂_zeroRunCover B)
    (fun k => ?_) (fun k => tsum_zeroRunCover_le hB k)
  -- at level `k` the failure of the conclusion for `c = k + B + 2` supplies the run
  obtain ⟨n, hn⟩ := hcon (k + B + 2)
  have hwin : n + (zeroRunLen n + k + B)
      ≤ n + (k + B + 2) * Nat.log 2 (n + 2) + (k + B + 2) := by
    have h1 : 2 * Nat.log 2 (n + 2) ≤ (k + B + 2) * Nat.log 2 (n + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [zeroRunLen]
    omega
  have hzero : ∀ i, n ≤ i → i < n + (zeroRunLen n + k + B) → w i = false := by
    intro i h1 h2
    simpa using hn i h1 (lt_of_lt_of_le h2 hwin)
  -- the value of the `n`-bit prefix is the left endpoint of its cell
  have hjlt : bitsNum (cantorPrefix w n) < 2 ^ n := by
    have h2 := bitsToNat_lt (cantorPrefix w n)
    rw [cantorPrefix_length] at h2
    rw [bitsNum_eq_devBitsToNat]
    exact h2
  have hvalEq : bitsValue (cantorPrefix w n) = ratOfDyadic (bitsNum (cantorPrefix w n)) n := by
    rw [bitsValue, cantorPrefix_length, ratOfDyadic]
  have hshift : bitsValue (cantorPrefix w (n + (zeroRunLen n + k + B)))
      = ratOfDyadic (bitsNum (cantorPrefix w n)) n := by
    rw [bitsValue_cantorPrefix_add_of_zero_run _ hzero, hvalEq]
  -- the two strict inequalities, both from irrationality
  have hOm : cantorReal w = ∑' i : ℕ, (if w i then (1 : ℝ) / 2 ^ (i + 1) else 0) := rfl
  have hirr := ne_ratCast_of_isMartinLofRandomReal h
  have hlow : ((bitsValue (cantorPrefix w (n + (zeroRunLen n + k + B))) : ℚ) : ℝ)
      ≤ cantorReal w := by
    rw [hOm]
    exact bitsValue_cantorPrefix_le w (n + (zeroRunLen n + k + B))
  have hhigh : cantorReal w
      ≤ ((bitsValue (cantorPrefix w (n + (zeroRunLen n + k + B))) : ℚ) : ℝ)
        + (1 : ℝ) / 2 ^ (n + (zeroRunLen n + k + B)) := by
    rw [hOm]
    exact le_bitsValue_cantorPrefix_add w (n + (zeroRunLen n + k + B))
  rw [hshift] at hlow hhigh
  have hlt1 : ((ratOfDyadic (bitsNum (cantorPrefix w n)) n : ℚ) : ℝ) < cantorReal w :=
    lt_of_le_of_ne hlow (fun hE => hirr _ hE.symm)
  have hlt2 : cantorReal w
      < ((ratOfDyadic (bitsNum (cantorPrefix w n)) n
          + ((2 : ℚ)⁻¹) ^ (n + (zeroRunLen n + k + B)) : ℚ) : ℝ) := by
    have key : ((((2 : ℚ)⁻¹) ^ (n + (zeroRunLen n + k + B)) : ℚ) : ℝ)
        = (1 : ℝ) / 2 ^ (n + (zeroRunLen n + k + B)) := by
      rw [show ((2 : ℚ)⁻¹) ^ (n + (zeroRunLen n + k + B))
          = 1 / 2 ^ (n + (zeroRunLen n + k + B)) by rw [inv_pow, one_div]]
      push_cast
      ring
    refine lt_of_le_of_ne (le_trans hhigh (le_of_eq ?_)) ?_
    · rw [Rat.cast_add, key]
    · intro hE
      exact hirr _ hE
  -- the singleton is caught by the cell of the prefix
  refine Set.singleton_subset_iff.2 (Set.mem_iUnion.2 ⟨Nat.pair n (bitsNum (cantorPrefix w n)), ?_⟩)
  have hc : zeroRunCover B k (Nat.pair n (bitsNum (cantorPrefix w n)))
      = some (ratOfDyadic (bitsNum (cantorPrefix w n)) n,
          ratOfDyadic (bitsNum (cantorPrefix w n)) n
            + ((2 : ℚ)⁻¹) ^ (n + (zeroRunLen n + k + B))) := by
    simp [zeroRunCover, zeroRunIdx, zeroRunCell, zeroRunLeft, zeroRunExp,
      Nat.unpair_pair, hjlt]
  change cantorReal w
    ∈ (zeroRunCover B k (Nat.pair n (bitsNum (cantorPrefix w n)))).elim ∅ ratInterval
  rw [hc]
  exact Set.mem_Ioo.2 ⟨hlt1, hlt2⟩

end Kolmogorov
