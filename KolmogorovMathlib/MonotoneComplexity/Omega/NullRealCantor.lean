/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.Complexity.AlphabetComplexity.QAryDecompressors
import KolmogorovMathlib.MonotoneComplexity.ArithmeticCoding
import KolmogorovMathlib.MonotoneComplexity.BinaryInterval
import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint.GapCover
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealApi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The bridge between random reals and random sequences (SUV Problem 158, p. 158)

SUV Problem 158 asks for the equivalence "a real is random iff its binary expansion is a
random sequence"; `isMartinLofRandomReal_omegaReal` rests on this bridge.

The bridge is carried by the *dyadic interval* of a bit string, which the repository
already has as `binaryClosedInterval` (`MonotoneComplexity/BinaryInterval.lean`,
`= [k/2ⁿ, (k+1)/2ⁿ]` with `n = |p|` and `k = devBitsToNat p`).  What was missing is the
geometry that makes it a bridge:

* `dyIco` — the half-open dyadic cell, its Lebesgue measure `2^{-|p|}`, its monotonicity
  along prefixes and its **disjointness for prefix-incomparable strings**;
* `cantorReal_mem_binaryClosedInterval` — the value of a sequence lies in the dyadic cell
  of each of its prefixes, so a cylinder maps into a dyadic cell;
* `tsum_inv_two_pow_length_le_of_antichain` — an antichain of dyadic cells inside a
  rational interval has total weight at most the length of that interval.  This is the
  measure-theoretic core; it is what makes the pull-back of a real cover a Martin-Löf test
  on the Cantor space.

Both directions of Problem 158 are then proved here as
`isMartinLofRandom_uniform_of_isMartinLofRandomReal` and
`isMartinLofRandomReal_of_isMartinLofRandom_uniform`, and assembled into
`isMartinLofRandomReal_iff_isMartinLofRandom_cantorReal`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-! ### Dyadic cells of a bit string -/

/-- The left endpoint `0.p` of the dyadic cell of `p`, as a rational. -/
def dyLeft (p : BitString) : ℚ := (devBitsToNat p : ℚ) / 2 ^ p.length

/-- The right endpoint `0.p + 2^{-|p|}` of the dyadic cell of `p`, as a rational. -/
def dyRight (p : BitString) : ℚ := ((devBitsToNat p : ℚ) + 1) / 2 ^ p.length

/-- The left endpoint of the dyadic cell of `p` is the real `0.p`. -/
theorem dyLeft_cast (p : BitString) :
    ((dyLeft p : ℚ) : ℝ) = (devBitsToNat p : ℝ) / 2 ^ p.length := by
  rw [dyLeft]; push_cast; ring

/-- The right endpoint of the dyadic cell of `p` is the real `0.p + 2 ^ -|p|`. -/
theorem dyRight_cast (p : BitString) :
    ((dyRight p : ℚ) : ℝ) = ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length := by
  rw [dyRight]; push_cast; ring

/-- The closed dyadic cell of `p` is the closed interval between the two dyadic endpoints. -/
theorem binaryClosedInterval_eq_Icc_dy (p : BitString) :
    binaryClosedInterval p = Set.Icc ((dyLeft p : ℚ) : ℝ) ((dyRight p : ℚ) : ℝ) := by
  rw [binaryClosedInterval_eq_Icc, dyLeft_cast, dyRight_cast]

/-- The half-open dyadic cell `[0.p, 0.p + 2^{-|p|})` of `p`. -/
def dyIco (p : BitString) : Set ℝ := Set.Ico ((dyLeft p : ℚ) : ℝ) ((dyRight p : ℚ) : ℝ)

/-- The half-open dyadic cell is contained in the closed one. -/
theorem dyIco_subset_binaryClosedInterval (p : BitString) :
    dyIco p ⊆ binaryClosedInterval p := by
  rw [binaryClosedInterval_eq_Icc_dy, dyIco]
  exact Set.Ico_subset_Icc_self

/-- Dyadic cells are measurable. -/
theorem measurableSet_dyIco (p : BitString) : MeasurableSet (dyIco p) :=
  measurableSet_Ico

/-- The dyadic cell of `p` has Lebesgue measure `2 ^ -|p|`. -/
theorem volume_dyIco (p : BitString) : volume (dyIco p) = (2 : ℝ≥0∞)⁻¹ ^ p.length := by
  rw [dyIco, Real.volume_Ico, dyLeft_cast, dyRight_cast]
  have h : ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length - (devBitsToNat p : ℝ) / 2 ^ p.length
      = ((2 : ℝ)⁻¹) ^ p.length := by
    rw [div_sub_div_same, add_sub_cancel_left, inv_pow, one_div]
  rw [h, ofReal_inv_two_pow]

/-! ### Prefix geometry -/

/-- Reading a concatenation as a binary numeral shifts the first factor by the length of the
second. -/
theorem devBitsToNat_append (x z : BitString) :
    devBitsToNat (x ++ z) = devBitsToNat x * 2 ^ z.length + devBitsToNat z := by
  induction x with
  | nil => simp [devBitsToNat]
  | cons b t ih =>
    rw [List.cons_append, devBitsToNat, devBitsToNat, ih, List.length_append]
    ring

/-- Bit strings of the same length are determined by their value: both are recovered by
`natToBits` from the length and the value (`natToBits_bitsToNat`). -/
theorem devBitsToNat_injective_of_length_eq {p q : BitString} (hlen : p.length = q.length)
    (hval : devBitsToNat p = devBitsToNat q) : p = q := by
  calc p = natToBits p.length (devBitsToNat p) := (natToBits_bitsToNat p).symm
    _ = natToBits q.length (devBitsToNat q) := by rw [hlen, hval]
    _ = q := natToBits_bitsToNat q

/-- The dyadic cell of an extension is contained in the dyadic cell of the prefix. -/
theorem dyIco_subset_of_prefix {p q : BitString} (h : p <+: q) : dyIco q ⊆ dyIco p := by
  obtain ⟨z, rfl⟩ := h
  have hzlt : devBitsToNat z < 2 ^ z.length := bitsToNat_lt z
  have hzR : (devBitsToNat z : ℝ) + 1 ≤ (2 : ℝ) ^ z.length := by exact_mod_cast hzlt
  have hzR0 : (0 : ℝ) ≤ (devBitsToNat z : ℝ) := Nat.cast_nonneg _
  have hden : ((2 : ℝ) ^ (p.length + z.length)) = 2 ^ p.length * 2 ^ z.length := pow_add 2 _ _
  have hppos : (0 : ℝ) < 2 ^ p.length := by positivity
  have hzpos : (0 : ℝ) < 2 ^ z.length := by positivity
  have hLeq : (devBitsToNat p : ℝ) / 2 ^ p.length
      = ((devBitsToNat p : ℝ) * 2 ^ z.length) / 2 ^ (p.length + z.length) := by
    rw [hden]
    field_simp
  have hReq : ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length
      = ((devBitsToNat p : ℝ) * 2 ^ z.length + 2 ^ z.length) / 2 ^ (p.length + z.length) := by
    rw [hden]
    field_simp
  have key1 : (devBitsToNat p : ℝ) / 2 ^ p.length
      ≤ ((devBitsToNat p : ℝ) * 2 ^ z.length + (devBitsToNat z : ℝ))
          / 2 ^ (p.length + z.length) := by
    rw [hLeq]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have key2 : ((devBitsToNat p : ℝ) * 2 ^ z.length + (devBitsToNat z : ℝ) + 1)
          / 2 ^ (p.length + z.length)
      ≤ ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length := by
    rw [hReq]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  rw [dyIco, dyIco, dyLeft_cast, dyRight_cast, dyLeft_cast, dyRight_cast,
    devBitsToNat_append, List.length_append]
  intro x hx
  rw [Set.mem_Ico] at hx ⊢
  push_cast at hx
  exact ⟨le_trans key1 hx.1, lt_of_lt_of_le hx.2 key2⟩

/-- Distinct strings of equal length have disjoint dyadic cells. -/
theorem dyIco_disjoint_of_length_eq {p q : BitString} (hlen : p.length = q.length)
    (hne : p ≠ q) : Disjoint (dyIco p) (dyIco q) := by
  have hvne : devBitsToNat p ≠ devBitsToNat q := fun h =>
    hne (devBitsToNat_injective_of_length_eq hlen h)
  have key : ∀ a b : BitString, a.length = b.length → devBitsToNat a < devBitsToNat b →
      Disjoint (dyIco a) (dyIco b) := by
    intro a b hab hlt
    rw [Set.disjoint_left]
    intro x hxa hxb
    rw [dyIco, Set.mem_Ico, dyLeft_cast, dyRight_cast] at hxa hxb
    have hpow : (0 : ℝ) < 2 ^ a.length := by positivity
    have hstep : (devBitsToNat a : ℝ) + 1 ≤ (devBitsToNat b : ℝ) := by exact_mod_cast hlt
    rw [← hab] at hxb
    have h1 : x < ((devBitsToNat a : ℝ) + 1) / 2 ^ a.length := hxa.2
    have h2 : (devBitsToNat b : ℝ) / 2 ^ a.length ≤ x := hxb.1
    have h3 : ((devBitsToNat a : ℝ) + 1) / 2 ^ a.length
        ≤ (devBitsToNat b : ℝ) / 2 ^ a.length := by
      exact div_le_div_of_nonneg_right hstep hpow.le
    linarith
  rcases lt_or_gt_of_ne hvne with h | h
  · exact key p q hlen h
  · exact (key q p hlen.symm h).symm

/-- **Disjointness of dyadic cells.**  Two bit strings, neither of which is a prefix of the
other, have disjoint dyadic cells. -/
theorem dyIco_disjoint_of_incomparable {p q : BitString} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) :
    Disjoint (dyIco p) (dyIco q) := by
  have key : ∀ a b : BitString, a.length ≤ b.length → ¬ a <+: b →
      Disjoint (dyIco a) (dyIco b) := by
    intro a b hlen hnp
    have hpref : b.take a.length <+: b := List.take_prefix _ _
    have hlen' : (b.take a.length).length = a.length := by
      rw [List.length_take]
      omega
    have hne : a ≠ b.take a.length := by
      intro heq
      exact hnp (heq ▸ hpref)
    exact Disjoint.mono_right (dyIco_subset_of_prefix hpref)
      (dyIco_disjoint_of_length_eq hlen'.symm hne)
  rcases le_total p.length q.length with h | h
  · exact key p q h hpq
  · exact (key q p h hqp).symm

/-! ### The value of a sequence lies in the cell of each of its prefixes -/

/-- The `k`-th term of the binary expansion series. -/
noncomputable def bitTerm (w : CantorSeq) (k : ℕ) : ℝ := if w k then (1 : ℝ) / 2 ^ (k + 1) else 0

/-- The terms of the binary expansion series are nonnegative. -/
theorem bitTerm_nonneg (w : CantorSeq) (k : ℕ) : 0 ≤ bitTerm w k := by
  rw [bitTerm]
  split <;> positivity

/-- The `k`-th term of the binary expansion series is at most `2 ^ -(k + 1)`. -/
theorem bitTerm_le (w : CantorSeq) (k : ℕ) : bitTerm w k ≤ ((1 : ℝ) / 2) ^ (k + 1) := by
  have hpow : ((1 : ℝ) / 2) ^ (k + 1) = (1 : ℝ) / 2 ^ (k + 1) := by rw [div_pow, one_pow]
  rw [bitTerm, hpow]
  split
  · exact le_rfl
  · positivity

/-- The geometric series with ratio one half is summable. -/
theorem summable_geom_half : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ (k + 1)) := by
  have hgeom : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  simpa [pow_succ] using hgeom.mul_right ((1 : ℝ) / 2)

/-- The binary expansion series of a Cantor sequence is summable. -/
theorem summable_bitTerm (w : CantorSeq) : Summable (bitTerm w) :=
  Summable.of_nonneg_of_le (bitTerm_nonneg w) (bitTerm_le w) summable_geom_half

/-- The real of a Cantor sequence is the sum of its binary expansion series. -/
theorem cantorReal_eq_tsum_bitTerm (w : CantorSeq) : cantorReal w = ∑' k, bitTerm w k := rfl

/-- The left endpoint of the dyadic cell of `(w)ₙ` is the `n`-th partial sum of the
binary expansion series. -/
theorem dyLeft_cantorPrefix (w : CantorSeq) (n : ℕ) :
    ((dyLeft (cantorPrefix w n) : ℚ) : ℝ) = ∑ j ∈ Finset.range n, bitTerm w j := by
  induction n with
  | zero =>
    have hdev : devBitsToNat [] = 0 := rfl
    simp [dyLeft_cast, cantorPrefix, hdev]
  | succ n ih =>
    have hlen1 : ([w n] : BitString).length = 1 := rfl
    rw [Finset.sum_range_succ, ← ih, cantorPrefix_succ, dyLeft_cast, dyLeft_cast,
      devBitsToNat_append, cantorPrefix_length, List.length_append, cantorPrefix_length,
      hlen1, bitTerm]
    have hne : ((2 : ℝ) ^ n) ≠ 0 := by positivity
    cases h : w n
    · have hdev : devBitsToNat [false] = 0 := rfl
      simp only [Bool.false_eq_true, ite_false, hdev]
      push_cast
      field_simp
      ring_nf
    · have hdev : devBitsToNat [true] = 1 := rfl
      simp only [ite_true, hdev]
      push_cast
      field_simp
      ring_nf

/-- **The bridge inequality.**  The value of a sequence lies in the closed dyadic cell of
each of its prefixes. -/
theorem cantorReal_mem_binaryClosedInterval (w : CantorSeq) (n : ℕ) :
    cantorReal w ∈ binaryClosedInterval (cantorPrefix w n) := by
  have hsum := summable_bitTerm w
  have hsplit := hsum.sum_add_tsum_nat_add n
  have htail_nonneg : 0 ≤ ∑' i, bitTerm w (i + n) :=
    tsum_nonneg fun i => bitTerm_nonneg w _
  have htail_le : (∑' i, bitTerm w (i + n)) ≤ ((1 : ℝ) / 2) ^ n := by
    have hle : ∀ i : ℕ, bitTerm w (i + n) ≤ ((1 : ℝ) / 2) ^ n * ((1 : ℝ) / 2) ^ (i + 1) := by
      intro i
      calc bitTerm w (i + n) ≤ ((1 : ℝ) / 2) ^ (i + n + 1) := bitTerm_le w _
        _ = ((1 : ℝ) / 2) ^ n * ((1 : ℝ) / 2) ^ (i + 1) := by
            rw [← pow_add]; ring_nf
    have hsummable2 : Summable (fun i : ℕ => ((1 : ℝ) / 2) ^ n * ((1 : ℝ) / 2) ^ (i + 1)) :=
      summable_geom_half.mul_left _
    have hsub : Summable (fun i : ℕ => bitTerm w (i + n)) := hsum.comp_injective
      (add_left_injective n)
    have h1 : (∑' i, bitTerm w (i + n))
        ≤ ∑' i : ℕ, ((1 : ℝ) / 2) ^ n * ((1 : ℝ) / 2) ^ (i + 1) :=
      Summable.tsum_le_tsum hle hsub hsummable2
    have h2 : (∑' i : ℕ, ((1 : ℝ) / 2) ^ n * ((1 : ℝ) / 2) ^ (i + 1))
        = ((1 : ℝ) / 2) ^ n := by
      rw [summable_geom_half.tsum_mul_left]
      have : (∑' i : ℕ, ((1 : ℝ) / 2) ^ (i + 1)) = 1 := by
        have hgeom : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
          summable_geometric_of_lt_one (by norm_num) (by norm_num)
        have hs : ∑' k : ℕ, ((1 : ℝ) / 2) ^ k = 2 := by
          rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
        rw [tsum_congr (fun k : ℕ => pow_succ ((1 : ℝ) / 2) k), hgeom.tsum_mul_right, hs]
        norm_num
      rw [this, mul_one]
    linarith
  rw [binaryClosedInterval_eq_Icc_dy, Set.mem_Icc, dyLeft_cantorPrefix]
  have hR : ((dyRight (cantorPrefix w n) : ℚ) : ℝ)
      = (∑ j ∈ Finset.range n, bitTerm w j) + ((1 : ℝ) / 2) ^ n := by
    rw [← dyLeft_cantorPrefix w n, dyRight_cast, dyLeft_cast, cantorPrefix_length,
      show ((1 : ℝ) / 2) ^ n = 1 / 2 ^ n by rw [div_pow, one_pow], ← add_div]
  rw [hR, cantorReal_eq_tsum_bitTerm, ← hsplit]
  constructor
  · linarith
  · linarith

/-- A cylinder maps into the dyadic cell of its defining string. -/
theorem cantorReal_mem_binaryClosedInterval_of_mem_cylinder {x : BitString} {w : CantorSeq}
    (hw : w ∈ cantorCylinder x) : cantorReal w ∈ binaryClosedInterval x := by
  have hx : cantorPrefix w x.length = x := (isCantorPrefix_iff_cantorPrefix_eq x w).1 hw
  have := cantorReal_mem_binaryClosedInterval w x.length
  rwa [hx] at this

/-! ### Binary expansions exist -/

/-- The value of the greedy binary expansion of `β` after `n` bits, in its
*non-terminating* form: a bit is set only when the value stays **strictly** below `β`. -/
noncomputable def expandVal (β : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      if expandVal β n + (1 : ℝ) / 2 ^ (n + 1) < β then expandVal β n + (1 : ℝ) / 2 ^ (n + 1)
      else expandVal β n

/-- The greedy binary expansion of `β`. -/
noncomputable def expandSeq (β : ℝ) (n : ℕ) : Bool :=
  decide (expandVal β n + (1 : ℝ) / 2 ^ (n + 1) < β)

/-- `(1 / 2) ^ (n + 1)` equals `1 / 2 ^ (n + 1)`. -/
theorem half_pow_succ (n : ℕ) : ((1 : ℝ) / 2) ^ (n + 1) = (1 : ℝ) / 2 ^ (n + 1) := by
  rw [div_pow, one_pow]

/-- One step of the greedy binary expansion adds the corresponding term of the expansion series. -/
theorem expandVal_succ (β : ℝ) (n : ℕ) :
    expandVal β (n + 1) = expandVal β n + bitTerm (expandSeq β) n := by
  by_cases hc : expandVal β n + (1 : ℝ) / 2 ^ (n + 1) < β
  · rw [expandVal, ite_eq_left hc, bitTerm, ite_eq_left (by simpa [expandSeq] using hc)]
  · rw [expandVal, ite_eq_right hc, bitTerm, ite_eq_right (by simpa [expandSeq] using hc), add_zero]

/-- The greedy expansion keeps its value strictly below `β` and within `2^{-n}` of it. -/
theorem expandVal_spec {β : ℝ} (h0 : 0 < β) (h1 : β ≤ 1) (n : ℕ) :
    expandVal β n < β ∧ β ≤ expandVal β n + ((1 : ℝ) / 2) ^ n := by
  induction n with
  | zero => simpa [expandVal] using ⟨h0, h1⟩
  | succ n ih =>
    obtain ⟨hlt, hle⟩ := ih
    have hsplit : ((1 : ℝ) / 2) ^ n
        = (1 : ℝ) / 2 ^ (n + 1) + (1 : ℝ) / 2 ^ (n + 1) := by
      rw [← half_pow_succ, pow_succ]
      ring
    have hnext : ((1 : ℝ) / 2) ^ (n + 1) = (1 : ℝ) / 2 ^ (n + 1) := half_pow_succ n
    by_cases hc : expandVal β n + (1 : ℝ) / 2 ^ (n + 1) < β
    · rw [expandVal, ite_eq_left hc, hnext]
      rw [hsplit] at hle
      exact ⟨hc, by linarith⟩
    · rw [expandVal, ite_eq_right hc, hnext]
      push Not at hc
      exact ⟨hlt, hc⟩

/-- The first `n` terms of the expansion series of the greedy expansion of `β` sum to its value
after `n` bits. -/
theorem sum_bitTerm_expandSeq (β : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, bitTerm (expandSeq β) j = expandVal β n := by
  induction n with
  | zero => simp [expandVal]
  | succ n ih => rw [Finset.sum_range_succ, ih, ← expandVal_succ]

/-- **Every real of `(0,1]` has a binary expansion whose partial values stay strictly
below it.**  This is the surjectivity of `cantorReal` in the form the Levin–Schnorr step
of SUV p. 170 needs: the dyadic cell of every prefix has its left endpoint *strictly* to
the left of the value. -/
theorem exists_cantorReal_eq {β : ℝ} (h0 : 0 < β) (h1 : β ≤ 1) :
    ∃ w : CantorSeq, cantorReal w = β ∧
      ∀ n : ℕ, ((dyLeft (cantorPrefix w n) : ℚ) : ℝ) < β := by
  refine ⟨expandSeq β, ?_, fun n => ?_⟩
  · have hsum := (summable_bitTerm (expandSeq β)).hasSum.tendsto_sum_nat
    have h2 : Filter.Tendsto (fun n => expandVal β n) Filter.atTop
        (nhds (cantorReal (expandSeq β))) := by
      refine Filter.Tendsto.congr (sum_bitTerm_expandSeq β) ?_
      rw [cantorReal_eq_tsum_bitTerm]
      exact hsum
    have h3 : Filter.Tendsto (fun n : ℕ => expandVal β n) Filter.atTop (nhds β) := by
      have hlow : ∀ n : ℕ, β - ((1 : ℝ) / 2) ^ n ≤ expandVal β n := fun n => by
        linarith [(expandVal_spec h0 h1 n).2]
      have hhigh : ∀ n : ℕ, expandVal β n ≤ β := fun n => (expandVal_spec h0 h1 n).1.le
      have hgeo : Filter.Tendsto (fun n : ℕ => β - ((1 : ℝ) / 2) ^ n) Filter.atTop (nhds β) := by
        have hz := tendsto_pow_atTop_nhds_zero_of_lt_one
          (show (0 : ℝ) ≤ (1 : ℝ) / 2 by norm_num) (show (1 : ℝ) / 2 < 1 by norm_num)
        have hconst : Filter.Tendsto (fun _ : ℕ => β) Filter.atTop (nhds β) :=
          tendsto_const_nhds
        simpa using hconst.sub hz
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hgeo tendsto_const_nhds hlow hhigh
    exact tendsto_nhds_unique h2 h3
  · rw [dyLeft_cantorPrefix, sum_bitTerm_expandSeq]
    exact (expandVal_spec h0 h1 n).1

/-! ### The antichain bound -/

/-- **The measure-theoretic core.**  An antichain of bit strings whose dyadic cells all lie
inside `(l, r)` has total weight `∑ 2^{-|p|}` at most `r - l`.  The cells are pairwise
disjoint, so their Lebesgue measures add up inside the interval. -/
theorem tsum_inv_two_pow_length_le_of_antichain {P : BitString → Prop} [DecidablePred P]
    {l r : ℝ} (hin : ∀ p, P p → binaryClosedInterval p ⊆ Set.Ioo l r)
    (hanti : ∀ p, P p → ∀ q, P q → p ≠ q → ¬ p <+: q) :
    (∑' p : BitString, if P p then (2 : ℝ≥0∞)⁻¹ ^ p.length else 0)
      ≤ ENNReal.ofReal (r - l) := by
  classical
  have hterm : ∀ p : BitString, (if P p then (2 : ℝ≥0∞)⁻¹ ^ p.length else 0)
      = Set.indicator {p : BitString | P p} (fun p => volume (dyIco p)) p := by
    intro p
    by_cases hp : P p
    · have hp' : p ∈ {p : BitString | P p} := hp
      rw [Set.indicator_of_mem hp', volume_dyIco, ite_eq_left hp]
    · have hp' : p ∉ {p : BitString | P p} := hp
      rw [Set.indicator_of_notMem hp', ite_eq_right hp]
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun p : {p : BitString | P p} => dyIco (p : BitString))) := by
    intro a b hab
    have hne : (a : BitString) ≠ (b : BitString) := fun h => hab (Subtype.ext h)
    exact dyIco_disjoint_of_incomparable (hanti _ a.2 _ b.2 hne)
      (hanti _ b.2 _ a.2 hne.symm)
  calc (∑' p : BitString, if P p then (2 : ℝ≥0∞)⁻¹ ^ p.length else 0)
      = ∑' p : BitString, Set.indicator {p : BitString | P p}
          (fun p => volume (dyIco p)) p := tsum_congr hterm
    _ = ∑' p : {p : BitString | P p}, volume (dyIco (p : BitString)) :=
        (tsum_subtype _ _).symm
    _ = volume (⋃ p : {p : BitString | P p}, dyIco (p : BitString)) :=
        (measure_iUnion hdisj (fun p => measurableSet_dyIco _)).symm
    _ ≤ volume (Set.Ioo l r) := by
        refine measure_mono (Set.iUnion_subset fun p => ?_)
        exact (dyIco_subset_binaryClosedInterval _).trans (hin _ p.2)
    _ = ENNReal.ofReal (r - l) := Real.volume_Ioo


/-! ### Computability of the dyadic endpoints -/

/-- The left endpoint of a dyadic cell is computable from the string. -/
theorem computable_dyLeft : Computable dyLeft := by
  have h1 : Computable (fun p : BitString => ((devBitsToNat p : ℕ) : ℚ)) :=
    computable_nat_to_rat.comp primrec_devBitsToNat.to_comp
  have h2 : Computable (fun p : BitString => ((2 : ℚ)⁻¹) ^ p.length) :=
    computable_inv_two_pow_rat.comp Primrec.list_length.to_comp
  refine (computable₂_ratMul.comp h1 h2).of_eq fun p => ?_
  rw [dyLeft, inv_pow, div_eq_mul_inv]

/-- The right endpoint of a dyadic cell is computable from the string. -/
theorem computable_dyRight : Computable dyRight := by
  have h1 : Computable (fun p : BitString => ((devBitsToNat p : ℕ) : ℚ) + 1) :=
    computable₂_ratAdd.comp (computable_nat_to_rat.comp primrec_devBitsToNat.to_comp)
      (Computable.const 1)
  have h2 : Computable (fun p : BitString => ((2 : ℚ)⁻¹) ^ p.length) :=
    computable_inv_two_pow_rat.comp Primrec.list_length.to_comp
  refine (computable₂_ratMul.comp h1 h2).of_eq fun p => ?_
  rw [dyRight, inv_pow, div_eq_mul_inv]

/-- A dyadic cell is nondegenerate: its left endpoint is below its right endpoint. -/
theorem dyLeft_lt_dyRight (p : BitString) :
    ((dyLeft p : ℚ) : ℝ) < ((dyRight p : ℚ) : ℝ) := by
  rw [dyLeft_cast, dyRight_cast]
  have h : ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length - (devBitsToNat p : ℝ) / 2 ^ p.length
      = ((2 : ℝ)⁻¹) ^ p.length := by
    rw [div_sub_div_same, add_sub_cancel_left, inv_pow, one_div]
  have hp : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ p.length := by positivity
  linarith

/-- `dropLast` as a reverse-tail-reverse, which is the shape whose primitive recursiveness
the library supplies. -/
theorem reverse_tail_reverse_eq_dropLast (l : BitString) : l.reverse.tail.reverse = l.dropLast := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b _ => simp

/-! ### Cells inside a rational interval -/

/-- The closed dyadic cell of `p` sits inside the open rational interval `I`. -/
def dyInside (I : ℚ × ℚ) (p : BitString) : Bool :=
  decide (I.1 < dyLeft p) && decide (dyRight p < I.2)

/-- Deciding whether a closed dyadic cell sits inside a rational interval is computable in both
arguments. -/
theorem computable₂_dyInside : Computable₂ dyInside := by
  have hl : Computable (fun q : (ℚ × ℚ) × BitString => decide (q.1.1 < dyLeft q.2)) :=
    computable₂_ratLt.comp (Computable.fst.comp Computable.fst)
      (computable_dyLeft.comp Computable.snd)
  have hr : Computable (fun q : (ℚ × ℚ) × BitString => decide (dyRight q.2 < q.1.2)) :=
    computable₂_ratLt.comp (computable_dyRight.comp Computable.snd)
      (Computable.snd.comp Computable.fst)
  exact (Primrec.dom_bool₂ (fun a b : Bool => a && b)).to_comp.comp hl hr

/-- The decision procedure is correct: it returns `true` exactly when the closed cell of `p` is
contained in the interval. -/
theorem dyInside_iff (I : ℚ × ℚ) (p : BitString) :
    dyInside I p = true ↔ binaryClosedInterval p ⊆ ratInterval I := by
  rw [dyInside, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    binaryClosedInterval_eq_Icc_dy, ratInterval]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : ((I.1 : ℚ) : ℝ) < ((dyLeft p : ℚ) : ℝ) := by exact_mod_cast h1
    have h2' : ((dyRight p : ℚ) : ℝ) < ((I.2 : ℚ) : ℝ) := by exact_mod_cast h2
    exact Set.Icc_subset_Ioo h1' h2'
  · intro hsub
    have hle : ((dyLeft p : ℚ) : ℝ) ≤ ((dyRight p : ℚ) : ℝ) := (dyLeft_lt_dyRight p).le
    have hL := hsub (Set.mem_Icc.2 ⟨le_rfl, hle⟩)
    have hR := hsub (Set.mem_Icc.2 ⟨hle, le_rfl⟩)
    rw [Set.mem_Ioo] at hL hR
    exact ⟨by exact_mod_cast hL.1, by exact_mod_cast hR.2⟩

/-- If a cell sits inside an interval then so does every subcell. -/
theorem dyInside_of_prefix {I : ℚ × ℚ} {p q : BitString} (hpq : p <+: q)
    (h : dyInside I p = true) : dyInside I q = true :=
  (dyInside_iff I q).2 ((binaryClosedInterval_subset_of_prefix hpq).trans
    ((dyInside_iff I p).1 h))

/-- `p` is a *maximal* cell inside `I`: it lies inside `I` and its parent does not. -/
def dyMaximal (I : ℚ × ℚ) (p : BitString) : Bool :=
  dyInside I p && (p.isEmpty || !(dyInside I p.dropLast))

/-- Deciding maximality of a cell inside an interval is computable in both arguments. -/
theorem computable₂_dyMaximal : Computable₂ dyMaximal := by
  have h1 : Computable (fun q : (ℚ × ℚ) × BitString => dyInside q.1 q.2) := computable₂_dyInside
  have h2 : Computable (fun q : (ℚ × ℚ) × BitString => q.2.isEmpty) :=
    primrec_decide_list_isEmpty.to_comp.comp Computable.snd
  have h3 : Computable (fun q : (ℚ × ℚ) × BitString => dyInside q.1 q.2.dropLast) :=
    computable₂_dyInside.comp Computable.fst (dropLast_primrec.to_comp.comp Computable.snd)
  have h4 : Computable (fun q : (ℚ × ℚ) × BitString => !(dyInside q.1 q.2.dropLast)) :=
    (Primrec.dom_bool (fun a : Bool => !a)).to_comp.comp h3
  have h5 : Computable (fun q : (ℚ × ℚ) × BitString =>
      q.2.isEmpty || !(dyInside q.1 q.2.dropLast)) :=
    (Primrec.dom_bool₂ (fun a b : Bool => a || b)).to_comp.comp h2 h4
  exact (Primrec.dom_bool₂ (fun a b : Bool => a && b)).to_comp.comp h1 h5

/-- A maximal cell of an interval is in particular a cell inside it. -/
theorem dyInside_of_dyMaximal {I : ℚ × ℚ} {p : BitString} (h : dyMaximal I p = true) :
    dyInside I p = true := by
  rw [dyMaximal, Bool.and_eq_true] at h
  exact h.1

/-- Maximal cells inside a fixed interval form an antichain. -/
theorem dyMaximal_not_prefix {I : ℚ × ℚ} {p q : BitString} (hp : dyMaximal I p = true)
    (hq : dyMaximal I q = true) (hne : p ≠ q) : ¬ p <+: q := by
  intro hpre
  obtain ⟨z, rfl⟩ := hpre
  have hz : z ≠ [] := by
    intro h
    exact hne (by simp [h])
  have hdrop : (p ++ z).dropLast = p ++ z.dropLast := List.dropLast_append_of_ne_nil hz
  have hpre2 : p <+: (p ++ z).dropLast := by
    rw [hdrop]
    exact ⟨z.dropLast, rfl⟩
  have hin : dyInside I ((p ++ z).dropLast) = true :=
    dyInside_of_prefix hpre2 (dyInside_of_dyMaximal hp)
  rw [dyMaximal, Bool.and_eq_true, Bool.or_eq_true, hin] at hq
  rcases hq.2 with hemp | hnot
  · rw [List.isEmpty_iff] at hemp
    exact hz (List.append_eq_nil_iff.1 hemp).2
  · simp at hnot

/-- **The mass of the maximal cells inside `I` is at most the length of `I`.** -/
theorem tsum_dyMaximal_le (I : ℚ × ℚ) :
    (∑' p : BitString, if dyMaximal I p = true then (2 : ℝ≥0∞)⁻¹ ^ p.length else 0)
      ≤ ratIntervalLength I := by
  classical
  rw [ratIntervalLength]
  refine tsum_inv_two_pow_length_le_of_antichain (P := fun p => dyMaximal I p = true)
    (fun p hp => ?_) (fun p hp q hq hne => dyMaximal_not_prefix hp hq hne)
  exact (dyInside_iff I p).1 (dyInside_of_dyMaximal hp)

/-- Every sequence whose value lies in `I` has a prefix that is a maximal cell of `I`. -/
theorem exists_dyMaximal_cantorPrefix {I : ℚ × ℚ} {w : CantorSeq}
    (h : cantorReal w ∈ ratInterval I) : ∃ m : ℕ, dyMaximal I (cantorPrefix w m) = true := by
  classical
  rw [ratInterval, Set.mem_Ioo] at h
  have hgap : (0 : ℝ) < min (cantorReal w - (I.1 : ℝ)) ((I.2 : ℝ) - cantorReal w) :=
    lt_min (by linarith [h.1]) (by linarith [h.2])
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hgap (by norm_num : ((1 : ℝ) / 2) < 1)
  have hex : ∃ m : ℕ, dyInside I (cantorPrefix w m) = true := by
    refine ⟨m₀, (dyInside_iff I _).2 ?_⟩
    have hmem := cantorReal_mem_binaryClosedInterval w m₀
    rw [binaryClosedInterval_eq_Icc_dy, Set.mem_Icc] at hmem
    have hwidth : ((dyRight (cantorPrefix w m₀) : ℚ) : ℝ)
        = ((dyLeft (cantorPrefix w m₀) : ℚ) : ℝ) + ((1 : ℝ) / 2) ^ m₀ := by
      rw [dyRight_cast, dyLeft_cast, cantorPrefix_length,
        show ((1 : ℝ) / 2) ^ m₀ = 1 / 2 ^ m₀ by rw [div_pow, one_pow], ← add_div]
    have h1 := min_le_left (cantorReal w - (I.1 : ℝ)) ((I.2 : ℝ) - cantorReal w)
    have h2 := min_le_right (cantorReal w - (I.1 : ℝ)) ((I.2 : ℝ) - cantorReal w)
    rw [binaryClosedInterval_eq_Icc_dy, ratInterval]
    refine Set.Icc_subset_Ioo ?_ ?_
    · linarith [hmem.1, hmem.2]
    · linarith [hmem.1, hmem.2]
  refine ⟨Nat.find hex, ?_⟩
  have hspec := Nat.find_spec hex
  rw [dyMaximal, Bool.and_eq_true, Bool.or_eq_true, hspec]
  refine ⟨rfl, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · left
    rw [h0]
    rfl
  · right
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin : ¬ dyInside I (cantorPrefix w k) = true := Nat.find_min hex (by omega)
    have hdrop : (cantorPrefix w (k + 1)).dropLast = cantorPrefix w k := by
      rw [cantorPrefix_succ]
      simp
    rw [hk, hdrop]
    simp [hmin]

/-! ### From a real cover to a Martin-Löf test on sequences -/

/-- The pull-back of a real cover: at level `n` the index `j` decodes as a pair
`(i, c)`, and the maximal dyadic cell `natToBitString c` of the `i`-th covering interval
is emitted. -/
def cantorPullback (cover : ℕ → ℕ → Option (ℚ × ℚ)) (n j : ℕ) : Option BitString :=
  (cover n j.unpair.1).bind fun I =>
    if dyMaximal I (natToBitString j.unpair.2) then some (natToBitString j.unpair.2) else none

/-- The pull-back of a computable real cover is computable in both arguments. -/
theorem computable₂_cantorPullback {cover : ℕ → ℕ → Option (ℚ × ℚ)}
    (hcov : Computable₂ cover) : Computable₂ (cantorPullback cover) := by
  have hu1 : Computable (fun q : ℕ × ℕ => q.2.unpair.1) :=
    ((Primrec.fst.comp Primrec.unpair).to_comp).comp Computable.snd
  have hu2 : Computable (fun q : ℕ × ℕ => q.2.unpair.2) :=
    ((Primrec.snd.comp Primrec.unpair).to_comp).comp Computable.snd
  have hstr : Computable (fun q : ℕ × ℕ => natToBitString q.2.unpair.2) :=
    computable_natToBitString.comp hu2
  have hcov' : Computable (fun q : ℕ × ℕ => cover q.1 q.2.unpair.1) :=
    hcov.comp Computable.fst hu1
  have hbody : Computable₂ (fun (q : ℕ × ℕ) (I : ℚ × ℚ) =>
      if dyMaximal I (natToBitString q.2.unpair.2) then
        some (natToBitString q.2.unpair.2) else none) := by
    have hcond : Computable (fun z : (ℕ × ℕ) × (ℚ × ℚ) =>
        dyMaximal z.2 (natToBitString z.1.2.unpair.2)) :=
      computable₂_dyMaximal.comp Computable.snd (hstr.comp Computable.fst)
    have hsome : Computable (fun z : (ℕ × ℕ) × (ℚ × ℚ) =>
        some (natToBitString z.1.2.unpair.2)) :=
      Computable.option_some.comp (hstr.comp Computable.fst)
    exact (Computable.cond hcond hsome (Computable.const none)).of_eq fun z => by
      cases h : dyMaximal z.2 (natToBitString z.1.2.unpair.2) <;> simp [h]
  exact Computable.option_bind hcov' hbody

/-- Value of the pull-back at a paired index: the `i`-th interval of level `n` is refined by its
`c`-th maximal cell. -/
theorem cantorPullback_pair (cover : ℕ → ℕ → Option (ℚ × ℚ)) (n i c : ℕ) :
    cantorPullback cover n (Nat.pair i c) =
      (cover n i).bind fun I =>
        if dyMaximal I (natToBitString c) then some (natToBitString c) else none := by
  simp only [cantorPullback, Nat.unpair_pair]

/-- **Problem 158, the hard direction.**  A sequence that is Martin-Löf random for the
uniform measure has a Martin-Löf random value.  Contrapositively, a cover of `cantorReal w`
by rational intervals is pulled back to a test on the Cantor space by taking, in each
covering interval, the *maximal* dyadic cells contained in it: they form an antichain, so
their total mass is at most the length of the interval
(`tsum_dyMaximal_le`), and `w` is caught because some prefix of `w` is such a cell
(`exists_dyMaximal_cantorPrefix`). -/
theorem isMartinLofRandomReal_of_isMartinLofRandom_uniform {w : CantorSeq}
    (h : IsMartinLofRandom uniformMeasure w) : IsMartinLofRandomReal (cantorReal w) := by
  classical
  intro X hX hmem
  obtain ⟨cover, hcov, hsub, hlen⟩ := hX.exists_pow_cover
  set V : ℕ → Set CantorSeq :=
    fun n => ⋃ j, (cantorPullback cover n j).elim ∅ cantorCylinder with hV
  have hopen : IsUniformlyEffectiveOpen V :=
    ⟨cantorPullback cover, computable₂_cantorPullback hcov, fun n => rfl⟩
  have hmass : ∀ n : ℕ, uniformMeasure (V n) ≤ dyadicValue 1 n := by
    intro n
    rw [dyadicValue_one_eq_inv_two_pow']
    have hstep : ∀ i : ℕ,
        (∑' c : ℕ, uniformMeasure ((cantorPullback cover n (Nat.pair i c)).elim ∅ cantorCylinder))
          ≤ (cover n i).elim 0 ratIntervalLength := by
      intro i
      rcases hcase : cover n i with _ | I
      · have hz : ∀ c : ℕ,
            uniformMeasure ((cantorPullback cover n (Nat.pair i c)).elim ∅ cantorCylinder) = 0 := by
          intro c
          rw [cantorPullback_pair, hcase]
          simp
        simp [hz]
      · have hterm : ∀ c : ℕ,
            uniformMeasure ((cantorPullback cover n (Nat.pair i c)).elim ∅ cantorCylinder)
              = (fun p : BitString => if dyMaximal I p = true then
                  (2 : ℝ≥0∞)⁻¹ ^ p.length else 0) (natToBitString c) := by
          intro c
          rw [cantorPullback_pair, hcase]
          by_cases hm : dyMaximal I (natToBitString c) = true
          · simp only [Option.bind_some, hm, ite_true]
            exact uniformMeasure_cantorCylinder _
          · simp only [Bool.not_eq_true] at hm
            simp [hm]
        rw [tsum_congr hterm, tsum_comp_natToBitString
          (fun p : BitString => if dyMaximal I p = true then (2 : ℝ≥0∞)⁻¹ ^ p.length else 0)]
        exact tsum_dyMaximal_le I
    calc uniformMeasure (V n)
        ≤ ∑' j : ℕ, uniformMeasure ((cantorPullback cover n j).elim ∅ cantorCylinder) :=
          measure_iUnion_le _
      _ = ∑' p : ℕ × ℕ,
            uniformMeasure ((cantorPullback cover n (Nat.pair p.1 p.2)).elim ∅ cantorCylinder) := by
          rw [← Equiv.tsum_eq Nat.pairEquiv
            (fun j => uniformMeasure ((cantorPullback cover n j).elim ∅ cantorCylinder))]
          rfl
      _ = ∑' i : ℕ, ∑' c : ℕ,
            uniformMeasure ((cantorPullback cover n (Nat.pair i c)).elim ∅ cantorCylinder) :=
          ENNReal.tsum_prod (f := fun i c =>
            uniformMeasure ((cantorPullback cover n (Nat.pair i c)).elim ∅ cantorCylinder))
      _ ≤ ∑' i : ℕ, (cover n i).elim 0 ratIntervalLength := ENNReal.tsum_le_tsum hstep
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ n := hlen n
  refine h V ⟨hopen, hmass⟩ ?_
  rw [Set.mem_iInter]
  intro n
  have hmemn := hsub n hmem
  rw [Set.mem_iUnion] at hmemn
  obtain ⟨i, hi⟩ := hmemn
  rcases hcase : cover n i with _ | I
  · rw [hcase] at hi; simp at hi
  · rw [hcase] at hi
    obtain ⟨m, hm⟩ := exists_dyMaximal_cantorPrefix (I := I) (w := w) hi
    rw [hV, Set.mem_iUnion]
    refine ⟨Nat.pair i (bitStringToNat (cantorPrefix w m)), ?_⟩
    rw [cantorPullback_pair, hcase, natToBitString_bitStringToNat]
    simp only [Option.bind_some, hm, ite_true]
    exact mem_cantorCylinder_cantorPrefix w m

/-! ### From a Martin-Löf test on sequences to a real cover -/

/-- A dyadic cell of a string of length `n` has length `2 ^ -n`. -/
theorem dyRight_sub_dyLeft (p : BitString) :
    ((dyRight p : ℚ) : ℝ) - ((dyLeft p : ℚ) : ℝ) = ((2 : ℝ)⁻¹) ^ p.length := by
  rw [dyLeft_cast, dyRight_cast, div_sub_div_same, add_sub_cancel_left, inv_pow, one_div]

/-- Padding a dyadic cell by `2 ^ -d` on both sides gives an interval of length
`2 ^ -|x| + 2 * 2 ^ -d`. -/
theorem ratIntervalLength_pad (x : BitString) (d : ℕ) :
    ratIntervalLength (dyLeft x - ((2 : ℚ)⁻¹) ^ d, dyRight x + ((2 : ℚ)⁻¹) ^ d)
      = (2 : ℝ≥0∞)⁻¹ ^ x.length + 2 * (2 : ℝ≥0∞)⁻¹ ^ d := by
  rw [ratIntervalLength]
  have hcast : ((dyRight x + ((2 : ℚ)⁻¹) ^ d : ℚ) : ℝ) - ((dyLeft x - ((2 : ℚ)⁻¹) ^ d : ℚ) : ℝ)
      = (((dyRight x : ℚ) : ℝ) - ((dyLeft x : ℚ) : ℝ)) + 2 * ((2 : ℝ)⁻¹) ^ d := by
    push_cast
    ring
  rw [hcast, dyRight_sub_dyLeft, ENNReal.ofReal_add (by positivity) (by positivity),
    ofReal_inv_two_pow, ENNReal.ofReal_mul (by norm_num), ofReal_inv_two_pow]
  norm_num

/-- Every point of a closed dyadic cell lies in the padded open interval around it. -/
theorem mem_ratInterval_pad {x : BitString} {d : ℕ} {y : ℝ}
    (hy : y ∈ binaryClosedInterval x) :
    y ∈ ratInterval (dyLeft x - ((2 : ℚ)⁻¹) ^ d, dyRight x + ((2 : ℚ)⁻¹) ^ d) := by
  rw [binaryClosedInterval_eq_Icc_dy, Set.mem_Icc] at hy
  have hd : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ d := by positivity
  rw [ratInterval, Set.mem_Ioo]
  constructor <;> push_cast <;> linarith [hy.1, hy.2]

/-- The push-forward of a Cantor-space test: each cylinder becomes its dyadic cell, padded
by a summable amount so that the (closed) cell fits inside an *open* rational interval. -/
def realPushforward (g : ℕ → ℕ → Option BitString) (k i : ℕ) : Option (ℚ × ℚ) :=
  (disjEnum (g (k + 1)) i).map fun x =>
    (dyLeft x - ((2 : ℚ)⁻¹) ^ (k + i + 3), dyRight x + ((2 : ℚ)⁻¹) ^ (k + i + 3))

/-- The push-forward of a computable Cantor-space test is a computable family of rational
intervals. -/
theorem computable₂_realPushforward {g : ℕ → ℕ → Option BitString} (hg : Computable₂ g) :
    Computable₂ (realPushforward g) := by
  have hadd : Computable₂ (fun a b : ℕ => a + b) := Primrec.nat_add.to_comp
  have hshift : Computable (fun q : ℕ × ℕ => q.1 + 1) :=
    hadd.comp Computable.fst (Computable.const 1)
  have hde : Computable (fun q : ℕ × ℕ => disjEnum (g (q.1 + 1)) q.2) :=
    (computable_disjEnum hg).comp hshift Computable.snd
  have hexp : Computable (fun z : (ℕ × ℕ) × BitString => z.1.1 + z.1.2 + 3) :=
    hadd.comp (hadd.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.fst)) (Computable.const 3)
  have hpow : Computable (fun z : (ℕ × ℕ) × BitString => ((2 : ℚ)⁻¹) ^ (z.1.1 + z.1.2 + 3)) :=
    computable_inv_two_pow_rat.comp hexp
  have hmap : Computable₂ (fun (q : ℕ × ℕ) (x : BitString) =>
      ((dyLeft x - ((2 : ℚ)⁻¹) ^ (q.1 + q.2 + 3),
        dyRight x + ((2 : ℚ)⁻¹) ^ (q.1 + q.2 + 3)) : ℚ × ℚ)) :=
    Computable.pair
      (computable₂_ratSub.comp (computable_dyLeft.comp Computable.snd) hpow)
      (computable₂_ratAdd.comp (computable_dyRight.comp Computable.snd) hpow)
  exact Computable.option_map hde hmap

/-- **Problem 158, the easy direction.**  If the value of `w` is a Martin-Löf random real
then `w` is a Martin-Löf random sequence: a test on the Cantor space is pushed forward by
replacing each of its (disjointified) cylinders by the dyadic cell it maps into, padded by
a geometrically summable amount. -/
theorem isMartinLofRandom_uniform_of_isMartinLofRandomReal {w : CantorSeq}
    (h : IsMartinLofRandomReal (cantorReal w)) : IsMartinLofRandom uniformMeasure w := by
  classical
  intro U hU hmem
  obtain ⟨⟨g, hg, hgU⟩, hbound⟩ := hU
  refine h {cantorReal w} ?_ rfl
  refine isEffectivelyNullReal_of_pow_cover (realPushforward g)
    (computable₂_realPushforward hg) (fun k => ?_) (fun k => ?_)
  · have hwU : w ∈ U (k + 1) := Set.mem_iInter.1 hmem (k + 1)
    rw [hgU (k + 1)] at hwU
    have hwU' : w ∈ ⋃ i, coverSet (disjEnum (g (k + 1))) i := by
      rw [coverSet_disjEnum_iUnion]
      exact hwU
    rw [Set.mem_iUnion] at hwU'
    obtain ⟨i, hi⟩ := hwU'
    rcases hcase : disjEnum (g (k + 1)) i with _ | x
    · rw [coverSet, hcase] at hi; simp at hi
    · rw [coverSet, hcase] at hi
      rintro y rfl
      rw [Set.mem_iUnion]
      refine ⟨i, ?_⟩
      change cantorReal w ∈ ((disjEnum (g (k + 1)) i).map _).elim ∅ ratInterval
      rw [hcase]
      exact mem_ratInterval_pad (cantorReal_mem_binaryClosedInterval_of_mem_cylinder hi)
  · have hstep : ∀ i : ℕ, (realPushforward g k i).elim 0 ratIntervalLength
        ≤ (disjEnum (g (k + 1)) i).elim 0 (cantorMass uniformMeasure)
          + 2 * (2 : ℝ≥0∞)⁻¹ ^ (k + i + 3) := by
      intro i
      rcases hcase : disjEnum (g (k + 1)) i with _ | x
      · simp [realPushforward, hcase]
      · rw [realPushforward, hcase]
        simp only [Option.map_some, Option.elim]
        rw [ratIntervalLength_pad, cantorMass_uniformMeasure]
    have hmass : (∑' i : ℕ, (disjEnum (g (k + 1)) i).elim 0 (cantorMass uniformMeasure))
        ≤ (2 : ℝ≥0∞)⁻¹ ^ (k + 1) := by
      rw [tsum_measure_disjEnum]
      have := hbound (k + 1)
      rw [dyadicValue_one_eq_inv_two_pow'] at this
      have heq : (⋃ j, coverSet (g (k + 1)) j) = U (k + 1) := by
        rw [hgU (k + 1)]
        rfl
      rw [heq]
      exact this
    have hpad : (∑' i : ℕ, 2 * (2 : ℝ≥0∞)⁻¹ ^ (k + i + 3)) = (2 : ℝ≥0∞)⁻¹ ^ (k + 1) := by
      have hre : ∀ i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (k + i + 3) = (2 : ℝ≥0∞)⁻¹ ^ (k + 2 + i + 1) := by
        intro i; congr 1; omega
      rw [tsum_congr (fun i => by rw [hre i]), ENNReal.tsum_mul_left,
        tsum_inv_two_pow_shift (k + 2)]
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ, ← mul_assoc,
        mul_comm (2 : ℝ≥0∞) _, mul_assoc,
        ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
    calc (∑' i : ℕ, (realPushforward g k i).elim 0 ratIntervalLength)
        ≤ ∑' i : ℕ, ((disjEnum (g (k + 1)) i).elim 0 (cantorMass uniformMeasure)
            + 2 * (2 : ℝ≥0∞)⁻¹ ^ (k + i + 3)) := ENNReal.tsum_le_tsum hstep
      _ = (∑' i : ℕ, (disjEnum (g (k + 1)) i).elim 0 (cantorMass uniformMeasure))
            + ∑' i : ℕ, 2 * (2 : ℝ≥0∞)⁻¹ ^ (k + i + 3) := ENNReal.tsum_add
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (k + 1) + (2 : ℝ≥0∞)⁻¹ ^ (k + 1) := by
          rw [hpad]; exact add_le_add hmass le_rfl
      _ = (2 : ℝ≥0∞)⁻¹ ^ k := by
          rw [← two_mul, pow_succ, ← mul_assoc, mul_comm (2 : ℝ≥0∞) _, mul_assoc,
            ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]

/-- **SUV Problem 158 (p. 158).**  A real number is Martin-Löf random exactly when its
binary expansion is a Martin-Löf random sequence for the uniform measure. -/
theorem isMartinLofRandomReal_iff_isMartinLofRandom_cantorReal (w : CantorSeq) :
    IsMartinLofRandomReal (cantorReal w) ↔ IsMartinLofRandom uniformMeasure w :=
  ⟨isMartinLofRandom_uniform_of_isMartinLofRandomReal,
    isMartinLofRandomReal_of_isMartinLofRandom_uniform⟩

end Kolmogorov
