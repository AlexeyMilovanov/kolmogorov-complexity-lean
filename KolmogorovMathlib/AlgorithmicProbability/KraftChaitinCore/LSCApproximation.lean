import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith
import KolmogorovMathlib.Core.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import KolmogorovMathlib.AlgorithmicProbability.Coding
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.Prefix.Optimal
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Dyadic approximations of lower-semicomputable functions

A conditional function `f : output → context → ℝ≥0∞` is *lower semicomputable* (`IsLSC`) when
it is the supremum of a computable monotone sequence of dyadic values `dyadicValue (approx s
out ctx) s = approx s out ctx / 2 ^ s`.  This module sets up that interface and the online
truncation built on it.

### The dyadic value

`dyadicValue` and its arithmetic: additivity (`dyadicValue_add`), homogeneity
(`dyadicValue_natCast_mul_left`), invariance under rescaling numerator and stage together
(`dyadicValue_two_pow_mul_add`), monotonicity in the numerator (`monotone_dyadicValue_num`)
and finiteness (`dyadicValue_lt_top`).

### Truncation

`incNum` splits an approximation into its dyadic increments and `evK`, `evOut`, `evNum`,
`evVal` present those increments as a single stream of events.  `truncCum` is the running mass
of that stream, `truncGapprox` the stage approximation that accepts an event only while the
running mass stays below `2 ^ d`, and `truncG` their supremum.  The computability lemmas for
all of these are proved here; `IsLSC.truncate`, which states what the truncation achieves, is
in `RealizationEngine`.
-/



namespace Kolmogorov

open scoped ENNReal

/-- The **dyadic value** `n / 2^s` of a stage-`s` numerator `n`, in `ℝ≥0∞`. This is
the value carried by one stage of a lower-semicomputable approximation. -/
noncomputable def dyadicValue (n s : ℕ) : ℝ≥0∞ := (n : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s

/-- **Lower-semicomputable conditional function** interface.

`IsLSC f` says the conditional function `f : output → context → ℝ≥0∞` admits a
*computable, monotone, dyadic* approximation: a `ℕ`-valued numerator
`approx s out ctx`, whose dyadic value `approx s out ctx / 2^s` increases in the
stage `s` and converges (as a supremum) to `f out ctx`, and which is `Computable`
as a function of `(s, out, ctx)`.

This is exactly the data the Kraft–Chaitin allocator enumerates: at each stage it
reads finitely many dyadic increments of `f` and emits prefix codes for them. The
numerators are `ℕ` (not `ℝ≥0∞`) precisely so the approximation is genuinely
computable; the conversion to `ℝ≥0∞` happens only in the monotonicity/supremum
clauses. -/
def IsLSC (f : BitString → BitString → ℝ≥0∞) : Prop :=
  ∃ approx : ℕ → BitString → BitString → ℕ,
    (∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1)) ∧
    (∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx) ∧
    Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)

/-! ### The approximation layer of the coding theorem (hard direction)

Every lower-semicomputable conditional function `f` that is globally
`2^{d}`-subnormalized (`∀ ctx, ∑_out f out ctx ≤ 2^{d}`) is *realized* by a genuine
prefix decompressor `M'` up to an additive coding constant `c₀`:
`2^{-c₀} · f(out | ctx) ≤ 2^{-KP_{M'}(out | ctx)}`.

This is the online Kraft–Chaitin allocator: scale `f` down by `2^{-d}` to a
subprobability (mass `≤ 1`), enumerate its dyadic increments via the `IsLSC`
approximation, and assign each increment a prefix-free program of length
`⌈-log(f/2^d)⌉ + O(1)`; the resulting `Partrec` map is a prefix decompressor whose
program lengths realize `-log f` up to `c₀ = d + O(1)`.

The proof uses the Kraft–Chaitin enumeration/allocation machinery (prefix-free
online code assignment from a computable request stream): convert the
`IsLSC` dyadic increments of `f / 2^d` into a computable request stream whose
per-context Kraft weight is `≤ 1` (from `h_sum`), allocate prefix-free programs of
the requested lengths online, and read off the `KP` bound. The streaming allocator
is implemented in `KraftChaitinAllocator` by a computable leftmost-free construction;
the finite offline Kraft converse does not provide the required causality. The
realization bound is stated in the `≤×` direction (no logarithm and no equality),
and the constant `c₀` is genuine coding overhead.

This module supplies only the approximation layer that the construction reads:
the dyadic values, the `IsLSC` scaling, and the `incNum`/`evNum`/`cumNum`/`truncG`
numerators.  The engine that consumes them — request extraction and the
prefix-machine construction — is `KraftChaitinCore.RealizationEngine`. -/

/-
**`IsLSC` is closed under dividing by a fixed power of two.**

Dividing a lower-semicomputable conditional function by the constant `2^d`
preserves lower semicomputability: shift the dyadic approximation stage by `d`
(`approxG S = approx (S - d)` for `S ≥ d`, and `0` below `d`), which keeps the
numerators integral and computable, monotone in the stage, and converging to
`f / 2^d` (multiplication by the constant `(2⁻¹)^d` commutes with the supremum).

This is pure approximation bookkeeping (no allocator content) and lets the general
`2^d`-mass realization bound reduce to the unit-mass interface
`kraftChaitin_realization_bound_unit` below.

Supremum of the stage-shifted dyadic approximation equals the original
supremum scaled by `2^{-d}`. The shifted approximation is `0` for stages `< d` and
`approx (S - d)` for `S ≥ d`; reindexing `S = k + d` and pulling the constant
`(2⁻¹)^d` through the supremum gives the result.
-/
lemma iSup_dyadicValue_shift (approx : ℕ → BitString → BitString → ℕ) (d : ℕ)
    (out ctx : BitString) :
    (⨆ S, dyadicValue (if S < d then 0 else approx (S - d) out ctx) S)
      = (⨆ s, dyadicValue (approx s out ctx) s) / (2 : ℝ≥0∞) ^ d := by
  rw [ ENNReal.div_eq_inv_mul ];
  rw [ ENNReal.mul_iSup ];
  refine le_antisymm ( iSup_le ?_ ) ( iSup_le ?_ );
  · intro i
    split_ifs <;>
      simp_all only [ENNReal.zero_div, Nat.cast_zero, dyadicValue, not_lt, zero_le]
    refine le_trans ?_ ( le_iSup _ ( i - d ) );
    rw [ show ( 2 : ℝ≥0∞ ) ^ i = ( 2 : ℝ≥0∞ ) ^ d * ( 2 : ℝ≥0∞ ) ^ ( i - d ) by
      rw [ ← pow_add, Nat.add_sub_of_le ‹d ≤ i› ] ] ; ring_nf;
    rw [ ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul ] ; ring_nf;
    rw [ ENNReal.mul_inv ];
    · ring_nf
      norm_num
    · exact Or.inl <| by norm_num;
    · exact Or.inl <| ENNReal.pow_ne_top <| by norm_num;
  · intro i
    refine le_trans ?_ ( le_iSup _ ( i + d ) )
    simp only [add_lt_iff_neg_right, add_tsub_cancel_right, dyadicValue, not_lt_zero,
      ↓reduceIte]
    ring_nf
    rw [ ENNReal.div_eq_inv_mul ] ; ring_nf;
    rw [ ENNReal.div_eq_inv_mul ] ; ring_nf;
    rw [ mul_comm ] ; gcongr ; norm_num [ ENNReal.mul_inv ]

/-
Computability of the stage-shifted approximation, from computability of the
original approximation.
-/
lemma computable_dyadicValue_shift (approx : ℕ → BitString → BitString → ℕ) (d : ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString × BitString =>
      if p.1 < d then 0 else approx (p.1 - d) p.2.1 p.2.2) := by
  have hsub : Computable (fun p : ℕ × BitString × BitString => p.1 - d) :=
    (Primrec.nat_sub.comp Primrec.fst (Primrec.const d)).to_comp
  have hbranch : Computable (fun p : ℕ × BitString × BitString =>
      approx (p.1 - d) p.2.1 p.2.2) :=
    hcomp.comp (hsub.pair Computable.snd)
  obtain ⟨_, hP⟩ := (Primrec.nat_lt.comp Primrec.fst (Primrec.const d) :
      PrimrecPred (fun p : ℕ × BitString × BitString => p.1 < d))
  have hpred : Computable (fun p : ℕ × BitString × BitString => decide (p.1 < d)) :=
    hP.to_comp
  refine (Computable.cond hpred (Computable.const 0) hbranch).of_eq (fun p => ?_)
  by_cases h : p.1 < d <;> simp [h]

/-- Dividing a lower semicomputable function by a fixed power of two keeps it lower
semicomputable. -/
theorem IsLSC.div_two_pow {f : BitString → BitString → ℝ≥0∞}
    (hf : IsLSC f) (d : ℕ) :
    IsLSC (fun out ctx => f out ctx / (2 : ℝ≥0∞) ^ d) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hf
  refine ⟨fun S out ctx => if S < d then 0 else approx (S - d) out ctx, ?_, ?_, ?_⟩
  · -- monotonicity of the shifted approximation
    intro s out ctx
    have dv0 : ∀ n : ℕ, dyadicValue 0 n = 0 := fun n => by
      simp only [dyadicValue, Nat.cast_zero, div_eq_mul_inv, zero_mul]
    change dyadicValue (if s < d then 0 else approx (s - d) out ctx) s ≤ _
    change _ ≤ dyadicValue (if s + 1 < d then 0 else approx (s + 1 - d) out ctx) (s + 1)
    split_ifs with h1 h2
    · rw [dv0 s, dv0 (s + 1)]
    · rw [dv0 s]
      exact zero_le _
    · exact False.elim (by omega)
    · convert mul_le_mul_right (hmono (s - d) out ctx) (2⁻¹ ^ d) using 1
      · have h_eq : 2 ^ s = (2:ℝ≥0∞) ^ (s - d + d) :=
          congr_arg (fun x => (2:ℝ≥0∞)^x) (show s = s - d + d by omega)
        have h_inv : ((2:ℝ≥0∞) ^ d)⁻¹ = 2⁻¹ ^ d := by rw [← ENNReal.inv_pow]
        unfold dyadicValue
        rw [h_eq, pow_add, div_eq_mul_inv, ENNReal.mul_inv]
        · rw [← mul_assoc, mul_comm _ ((2:ℝ≥0∞) ^ d)⁻¹, h_inv, ← div_eq_mul_inv]
        · exact Or.inl (by norm_num)
        · exact Or.inl (ENNReal.pow_ne_top (by norm_num))
      · have hs1' : s + 1 - d = s - d + 1 := by omega
        have h_eq : 2 ^ (s + 1) = (2:ℝ≥0∞) ^ (s + 1 - d + d) :=
          congr_arg (fun x => (2:ℝ≥0∞)^x) (show s + 1 = s + 1 - d + d by omega)
        have h_inv : ((2:ℝ≥0∞) ^ d)⁻¹ = 2⁻¹ ^ d := by rw [← ENNReal.inv_pow]
        unfold dyadicValue
        rw [h_eq, pow_add, div_eq_mul_inv, ENNReal.mul_inv]
        · rw [hs1', ← mul_assoc, mul_comm _ ((2:ℝ≥0∞) ^ d)⁻¹, h_inv, ← div_eq_mul_inv]
        · exact Or.inl (by norm_num)
        · exact Or.inl (ENNReal.pow_ne_top (by norm_num))
  · -- supremum equals `f / 2^d`
    intro out ctx
    rw [iSup_dyadicValue_shift approx d out ctx, hsup out ctx]
  · -- computability of the shifted approximation
    exact computable_dyadicValue_shift approx d hcomp

/-! ### The online truncation construction

This block builds the truncated function used by `IsLSC.truncate`. Fix the
computable monotone dyadic approximation `approx` of `f`. We enumerate the
"atomic dyadic increments" of `f(·|ctx)` as a single ℕ-indexed stream and accept
each increment only while the running cumulative mass stays `≤ 2^d`.

The enumeration uses `Nat.unpair`: event `t` decodes to `(Nat.unpair t).1`
(an output index, decoded with `Encodable.decode₂`) and `(Nat.unpair t).2 = evK t`
(a stage). Crucially `evK t ≤ t`, so at level `S` every event `t < S` has
`evK t < S`, making its dyadic increment exactly representable over `2^S`. This is
what lets the accepted partial sums be exact numerators over `2^S`, monotone in
`S`, with supremum the truncated value. -/
section Truncate

/-- Numerator of the `k`-th dyadic increment of `approx · out ctx` (over `2^k`):
`approx 0` for `k = 0`, and `approx (k+1) - 2·approx k` for the step `k+1`. Under
monotonicity of `approx`, its dyadic value is the genuine increment. -/
def incNum (approx : ℕ → BitString → BitString → ℕ) : ℕ → BitString → BitString → ℕ
  | 0, out, ctx => approx 0 out ctx
  | (k + 1), out, ctx => approx (k + 1) out ctx - 2 * approx k out ctx

/-- The stage component of event `t`. Always `≤ t` since `Nat.unpair` shrinks. -/
def evK (t : ℕ) : ℕ := (Nat.unpair t).2

/-- The output decoded from event `t` (using `decode₂`, the proper partial
inverse of `Encodable.encode`), or `none` when `(Nat.unpair t).1` is not a code. -/
def evOut (t : ℕ) : Option BitString := Encodable.decode₂ BitString (Nat.unpair t).1

/-- The numerator (over `2^(evK t)`) of event `t`'s increment, `0` if no output. -/
def evNum (approx : ℕ → BitString → BitString → ℕ) (t : ℕ) (ctx : BitString) : ℕ :=
  match evOut t with
  | some out => incNum approx (evK t) out ctx
  | none => 0

/-- The dyadic value of event `t`'s increment. -/
noncomputable def evVal (approx : ℕ → BitString → BitString → ℕ) (t : ℕ) (ctx : BitString) :
    ℝ≥0∞ :=
  dyadicValue (evNum approx t ctx) (evK t)

/-- The natural-number cumulative numerator over `2^S` of the first `n` events.
Correct (i.e. equals `2^S · truncCum`) when every `evK i ≤ S` for `i < n`. -/
def cumNum (approx : ℕ → BitString → BitString → ℕ) (S n : ℕ) (ctx : BitString) : ℕ :=
  ∑ i ∈ Finset.range n, evNum approx i ctx * 2 ^ (S - evK i)

/-- The real cumulative mass of the first `n` events. -/
noncomputable def truncCum (approx : ℕ → BitString → BitString → ℕ) (n : ℕ) (ctx : BitString) :
    ℝ≥0∞ :=
  ∑ i ∈ Finset.range n, evVal approx i ctx

/-- The numerator (over `2^S`) of the stage-`S` approximation of the truncation:
sum over the first `S` events `t` whose running mass stays `≤ 2^d` and whose
output is `out`, of that event's increment numerator scaled to denominator `2^S`. -/
def truncGapprox (approx : ℕ → BitString → BitString → ℕ) (d : ℕ) :
    ℕ → BitString → BitString → ℕ :=
  fun S out ctx =>
    ∑ t ∈ Finset.range S,
      if cumNum approx S (t + 1) ctx ≤ 2 ^ (d + S) ∧ evOut t = some out then
        evNum approx t ctx * 2 ^ (S - evK t)
      else 0

/-- The truncated function: supremum over stages `S` of the dyadic value of the
stage-`S` accepted numerator. -/
noncomputable def truncG (approx : ℕ → BitString → BitString → ℕ) (d : ℕ)
    (out ctx : BitString) : ℝ≥0∞ :=
  ⨆ S, dyadicValue (truncGapprox approx d S out ctx) S

variable {f : BitString → BitString → ℝ≥0∞} {approx : ℕ → BitString → BitString → ℕ}

/-
Telescoping: the dyadic value of the increment numerator at step `k+1` is the
genuine dyadic increment, using monotonicity.
-/
lemma dyadicValue_incNum_succ
    (_hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (k : ℕ) (out ctx : BitString) :
    dyadicValue (incNum approx (k + 1) out ctx) (k + 1)
      = dyadicValue (approx (k + 1) out ctx) (k + 1)
          - dyadicValue (approx k out ctx) k := by
  unfold dyadicValue incNum; norm_num [ pow_succ' ] ; ring_nf;
  rw [ ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul ] ; ring_nf;
  rw [ ENNReal.mul_sub ] <;> norm_num ; ring_nf;
  norm_num [ mul_assoc, mul_comm, mul_left_comm, ENNReal.mul_inv ];
  norm_num [ ← mul_assoc, ENNReal.mul_inv_cancel ]

/-
Telescoping sum: the partial sum of the first `n+1` increment dyadic values
is the `n`-th dyadic approximation value.
-/
lemma sum_dyadicValue_incNum
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (n : ℕ) (out ctx : BitString) :
    ∑ k ∈ Finset.range (n + 1), dyadicValue (incNum approx k out ctx) k
      = dyadicValue (approx n out ctx) n := by
  induction n with
  | zero => simp only [Finset.range_one, Finset.sum_singleton, incNum, zero_add]
  | succ n ih =>
    convert congr_arg₂ ( · + · ) ih ( dyadicValue_incNum_succ hmono n out ctx ) using 1;
    · rw [Finset.sum_range_succ];
    · rw [ add_tsub_cancel_of_le ( hmono n out ctx ) ]

/-
The tsum of increment dyadic values for a fixed output recovers `f`.
-/
lemma tsum_dyadicValue_incNum
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx)
    (out ctx : BitString) :
    ∑' k : ℕ, dyadicValue (incNum approx k out ctx) k = f out ctx := by
  -- First, rewrite the tsum as an iSup of partial sums via `ENNReal.tsum_eq_iSup_nat`.
  have h_tsum : ∑' k : ℕ, dyadicValue (incNum approx k out ctx) k =
    ⨆ S : ℕ, ∑ k ∈ Finset.range S, dyadicValue (incNum approx k out ctx) k := by
      rw [ ENNReal.tsum_eq_iSup_nat ];
  rw [ ← hsup, h_tsum, iSup_eq_of_forall_le_of_forall_lt_exists_gt ];
  · intro i
    have h_partial_sum : ∑ k ∈ Finset.range i, dyadicValue (incNum approx k out ctx) k ≤ dyadicValue
        (approx (i - 1) out ctx) (i - 1) := by
      rcases i with _ | n
      · simp
      · simp only [add_tsub_cancel_right]
        rw [← sum_dyadicValue_incNum hmono n out ctx, Finset.sum_range_succ]
    exact le_trans h_partial_sum <| le_iSup_of_le _ le_rfl;
  · intro w hw; rcases exists_lt_of_lt_ciSup hw with ⟨ s, hs ⟩ ;
    use s + 1; simp_all only [Finset.sum_range_succ] ;
    have := sum_dyadicValue_incNum hmono s out ctx;
    rw [ Finset.sum_range_succ ] at this ; aesop

/-
Scaling: an event's increment numerator scaled to denominator `2^S` has dyadic
value (over `2^S`) equal to the event's increment value, when `evK t ≤ S`.
-/
lemma dyadicValue_evNum_scale (t S : ℕ) (ctx : BitString) (h : evK t ≤ S) :
    dyadicValue (evNum approx t ctx * 2 ^ (S - evK t)) S = evVal approx t ctx := by
  unfold evVal dyadicValue;
  rw [ ENNReal.div_eq_div_iff ] <;> norm_num;
  rw [ mul_left_comm, ← pow_add, Nat.add_sub_of_le h ];
  ring

/-
The cumulative numerator over `2^S` has dyadic value equal to the real
cumulative mass, when `n ≤ S` (so all events `i < n` have `evK i < S`).
-/
lemma dyadicValue_cumNum (S n : ℕ) (ctx : BitString) (h : n ≤ S) :
    dyadicValue (cumNum approx S n ctx) S = truncCum approx n ctx := by
  -- Apply the definition of `dyadicValue` to the sum.
  have h_dyadicValue_sum : dyadicValue (∑ i ∈ Finset.range n, evNum approx i ctx * 2 ^ (S - evK i))
      S = ∑ i ∈ Finset.range n, dyadicValue (evNum approx i ctx * 2 ^ (S - evK i)) S := by
    unfold dyadicValue; norm_num [ div_eq_mul_inv, Finset.sum_mul _ _ _ ] ;
  convert h_dyadicValue_sum using 2;
  exact Finset.sum_congr rfl fun i hi => by
    rw [ dyadicValue_evNum_scale i S ctx
      ( Nat.le_trans ( Nat.unpair_right_le i )
        ( by linarith [ Finset.mem_range.mp hi ] ) ) ] ;

/-
Key representation identity: the dyadic value of the stage-`S` numerator is the
partial sum over the first `S` events of the accepted (running mass `≤ 2^d`,
output `out`) increment values. The `S`-dependence of the natural-number
condition disappears (it is equivalent to the real cumulative condition).
-/
lemma dyadicValue_truncGapprox (d S : ℕ) (out ctx : BitString) :
    dyadicValue (truncGapprox approx d S out ctx) S
      = ∑ t ∈ Finset.range S,
          if truncCum approx (t + 1) ctx ≤ (2 : ℝ≥0∞) ^ d ∧ evOut t = some out then
            evVal approx t ctx
          else 0 := by
  unfold dyadicValue truncGapprox;
  simp only [Finset.sum_const_zero, Finset.sum_ite, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_pow, Nat.cast_sum, add_zero, not_and]
  rw [ ENNReal.div_eq_inv_mul, Finset.mul_sum ];
  refine Finset.sum_bij ( fun x hx => x ) ?_ ?_ ?_ ?_ <;>
    simp_all only [Finset.mem_filter, Finset.mem_range, and_imp, and_true,
      exists_eq_right, exists_prop, implies_true, true_and]
  · intro a ha₁ ha₂ ha₃;
    rw [ ← dyadicValue_cumNum S ( a + 1 ) ctx ( by linarith ) ] at *;
    simp_all only [dyadicValue] ;
    rw [ ENNReal.div_le_iff_le_mul ] <;> norm_cast <;> norm_num [ pow_add ] at * ; linarith;
  · intro b hb₁ hb₂ hb₃; contrapose! hb₂; simp_all only [truncCum] ;
    have h_div : (cumNum approx S (b + 1) ctx : ℝ≥0∞) / 2 ^ S > 2 ^ d := by
      rw [ gt_iff_lt, ENNReal.lt_div_iff_mul_lt ] <;> norm_cast <;> norm_num [ pow_add ] at * ;
      linarith;
    refine lt_of_lt_of_le h_div ?_;
    convert dyadicValue_cumNum S ( b + 1 ) ctx ( by linarith ) |> le_of_eq using 1;
  · intro a ha₁ ha₂ ha₃;
    rw [ ← dyadicValue_evNum_scale a S ctx
      ( Nat.le_of_lt ( Nat.unpair_right_le a |> lt_of_le_of_lt <| ha₁ ) ) ] ;
    ring_nf;
    unfold dyadicValue; norm_num [ mul_assoc, mul_comm, mul_left_comm, pow_add ] ;
    rw [ ENNReal.div_eq_inv_mul ];
    ring

/-
The stage-`S` numerator is monotone in the dyadic value.
-/
lemma truncGapprox_mono (d : ℕ) (S : ℕ) (out ctx : BitString) :
    dyadicValue (truncGapprox approx d S out ctx) S
      ≤ dyadicValue (truncGapprox approx d (S + 1) out ctx) (S + 1) := by
  rw [ dyadicValue_truncGapprox, dyadicValue_truncGapprox ];
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ _)) fun _ _ _ => by
    split_ifs <;> positivity;

/-
Computable finite sums over an initial segment whose bound is computable. A
reusable bridge: `Computable.nat_rec` builds `∑_{t<b a} g a t` as an accumulator.
-/
lemma computable_range_sum {α : Type*} [Primcodable α]
    (g : α → ℕ → ℕ) (hg : Computable₂ g) (b : α → ℕ) (hb : Computable b) :
    Computable (fun a => ∑ t ∈ Finset.range (b a), g a t) := by
  -- The sum of a finite number of computable functions is computable.
  have h_sum_computable : ∀ (f : α → ℕ → ℕ), Computable₂ f → Computable
      (fun a => ∑ t ∈ Finset.range (b a), f a t) := by
    intro f hf;
    have h_sum_computable : ∃ F : α → ℕ × ℕ → ℕ, Computable₂ F ∧ ∀ a n, F a
        (n, ∑ t ∈ Finset.range n, f a t) = ∑ t ∈ Finset.range (n + 1), f a t := by
      refine ⟨ fun a p => p.2 + f a p.1, ?_, ?_ ⟩
      · simp only [Computable₂] at *
        have h_sum_computable : Computable (fun p : α × ℕ × ℕ => p.2.2 + f p.1 p.2.1) := by
          have h_add : Computable (fun p : ℕ × ℕ => p.1 + p.2) := by
            -- The addition function is primitive recursive, hence computable.
            have h_add_primrec : Primrec (fun p : ℕ × ℕ => p.1 + p.2) := by
              exact Primrec.nat_add.comp ( Primrec.fst ) ( Primrec.snd );
            exact h_add_primrec.to_comp
          convert h_add.comp
            ( Computable.snd.comp ( Computable.snd ) |> Computable.pair <| hf.comp
              ( Computable.fst |> Computable.pair
                <| Computable.fst.comp ( Computable.snd ) ) ) using 1;
        exact h_sum_computable;
      · exact fun a n => by rw [ Finset.sum_range_succ ] ;
    obtain ⟨ F, hF₁, hF₂ ⟩ := h_sum_computable;
    convert Computable.nat_rec hb ( Computable.const 0 )
      ( hF₁.comp ( Computable.fst ) ( Computable.snd ) ) using 1;
    ext a; exact (by
    induction b a with
    | zero =>
      simp_all only [Finset.range_zero, Finset.sum_empty, Finset.sum_range_succ,
        Nat.rec_zero]
    | succ n ih =>
      simp_all only [Finset.sum_range_succ]
      rw [ ← ih, hF₂ ]);
  exact h_sum_computable g hg

/-- `n ↦ 2 ^ n` is primitive recursive. -/
lemma primrec_two_pow_aux : Primrec (fun n : ℕ => 2 ^ n) := by
  have h : (fun n : ℕ => 2 ^ n) = (fun n => Nat.rec 1 (fun _ ih => 2 * ih) n) := by
    funext n; induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, ih]; ring
  rw [h]
  exact Primrec.nat_rec' Primrec.id (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)).to₂

/-
`evOut` is computable.
-/
lemma evOut_computable : Computable evOut := by
  convert Computable.comp ?_ ( Computable.fst.comp ( Computable.unpair ) ) using 1;
  convert Computable.option_bind ( Computable.decode ) _ using 1;
  have h_computable : Primrec₂
      (fun (a : ℕ) (b : BitString) => if Encodable.encode b = a then some b else none) := by
    convert Primrec.ite _ _ _ using 1;
    · convert Primrec.eq.comp ( Primrec.encode.comp ( Primrec.snd ) ) ( Primrec.fst ) using 1;
    · exact Primrec.option_some.comp ( Primrec.snd );
    · exact Primrec.const none;
  convert h_computable.to_comp using 1;
  ext; simp [Option.guard]

/-
`evK` is computable.
-/
lemma evK_computable : Computable evK := by
  convert Computable.snd.comp ( Computable.unpair ) using 1

/-
The increment numerator is computable in `(k, out, ctx)`.
-/
lemma incNum_computable (hcomp : Computable
      (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString × BitString => incNum approx p.1 p.2.1 p.2.2) := by
  convert Computable.nat_casesOn ( Computable.fst ) _ _ using 1;
  rotate_left;
  · exact fun p => approx 0 p.2.1 p.2.2;
  · exact fun p k => approx ( k + 1 ) p.2.1 p.2.2 - 2 * approx k p.2.1 p.2.2;
  · convert hcomp.comp
      ( Computable.const 0 |> Computable.pair <| Computable.fst.comp Computable.snd
        |> Computable.pair <| Computable.snd.comp Computable.snd ) using 1;
  · have h_comp : Computable
      (fun p : ℕ × BitString × BitString => approx (p.1 + 1) p.2.1 p.2.2) := by
      convert hcomp.comp
        ( Computable.pair ( Computable.succ.comp Computable.fst ) ( Computable.snd ) ) using 1;
    have h_comp : Computable (fun p : ℕ × BitString × BitString => 2 * approx p.1 p.2.1 p.2.2) := by
      have h_comp : Computable (fun p : ℕ => 2 * p) :=
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp
      exact h_comp.comp hcomp;
    have h_comp : Computable
        (fun p : (BitString × BitString) × ℕ =>
          approx (p.2 + 1) p.1.1 p.1.2 - 2 * approx p.2 p.1.1 p.1.2) := by
      have h_comp : Computable (fun p : ℕ × ℕ => p.1 - p.2) := by
        -- The subtraction function is primitive recursive, hence computable.
        have h_sub_primrec : Primrec (fun p : ℕ × ℕ => p.1 - p.2) := by
          exact Primrec.nat_sub.comp ( Primrec.fst ) ( Primrec.snd );
        exact h_sub_primrec.to_comp;
      convert h_comp.comp ( Computable.pair
        ( ‹Computable fun p : ℕ × BitString × BitString => approx ( p.1 + 1 ) p.2.1 p.2.2›.comp
          ( Computable.snd.pair ( Computable.fst.comp ( Computable.fst )
            |> Computable.pair <| Computable.snd.comp ( Computable.fst ) ) ) )
        ( ‹Computable fun p : ℕ × BitString × BitString => 2 * approx p.1 p.2.1 p.2.2›.comp
          ( Computable.snd.pair ( Computable.fst.comp ( Computable.fst )
            |> Computable.pair <| Computable.snd.comp ( Computable.fst ) ) ) ) ) using 1;
    convert h_comp.comp
      ( Computable.pair ( Computable.snd.comp Computable.fst ) ( Computable.snd ) ) using 1;
  · exact funext fun p => by cases p.1 <;> rfl;

/-
The event increment numerator is computable in `(t, ctx)`.
-/
lemma evNum_computable (hcomp : Computable
      (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString => evNum approx p.1 p.2) := by
  convert Computable.option_casesOn
    ( show Computable fun p : ℕ × BitString => evOut p.1 from ?_ )
    ( show Computable fun p : ℕ × BitString => 0 from ?_ )
    ( show Computable₂ fun p : ℕ × BitString => fun out : BitString =>
        incNum approx ( evK p.1 ) out p.2 from ?_ ) using 1;
  · exact funext fun p => by unfold evNum; aesop;
  · exact evOut_computable.comp ( Computable.fst );
  · exact Computable.const 0;
  · have := incNum_computable hcomp;
    convert this.comp
      ( show Computable fun p : ( ℕ × BitString ) × BitString => ( evK p.1.1, p.2, p.1.2 ) from ?_ )
      using 1;
    exact Computable.pair ( evK_computable.comp ( Computable.fst.comp Computable.fst ) )
      ( Computable.pair ( Computable.snd ) ( Computable.snd.comp Computable.fst ) )

/-
The cumulative numerator is computable in `(S, n, ctx)`.
-/
lemma cumNum_computable (hcomp : Computable
      (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × ℕ × BitString => cumNum approx p.1 p.2.1 p.2.2) := by
  have h_computable : Computable
      (fun p : ℕ × ℕ × BitString =>
        ∑ i ∈ Finset.range p.2.1, evNum approx i p.2.2 * 2 ^ (p.1 - evK i)) := by
    have h_g : Computable
        (fun p : (ℕ × ℕ × BitString) × ℕ => evNum approx p.2 p.1.2.2 * 2 ^ (p.1.1 - evK p.2)) := by
      have h_f : Computable (fun p : (ℕ × ℕ × BitString) × ℕ => evNum approx p.2 p.1.2.2) := by
        convert evNum_computable hcomp |> Computable.comp <| _ using 1;
        rotate_left;
        · exact fun p => ( p.2, p.1.2.2 );
        · exact Computable.pair ( Computable.snd )
            ( Computable.snd.comp ( Computable.snd.comp ( Computable.fst ) ) );
        · rfl;
      have h_g : Computable (fun p : (ℕ × ℕ × BitString) × ℕ => 2 ^ (p.1.1 - evK p.2)) := by
        have h_g : Computable (fun p : ℕ × ℕ => 2 ^ (p.1 - evK p.2)) := by
          convert Primrec.to_comp
            ( show Primrec ( fun p : ℕ × ℕ => 2 ^ ( p.1 - evK p.2 ) ) from ?_ ) using 1;
          convert Primrec.comp ( show Primrec ( fun n => 2 ^ n ) from ?_ )
            ( show Primrec ( fun p : ℕ × ℕ => p.1 - evK p.2 ) from ?_ ) using 1;
          · convert primrec_two_pow_aux using 1;
          · exact Primrec.nat_sub.comp ( Primrec.fst ) ( Primrec.comp ( show Primrec evK from by
              exact Primrec.snd.comp ( Primrec.unpair ) ) ( Primrec.snd ) );
        convert h_g.comp
          ( Computable.fst.comp ( Computable.fst ) |> Computable.pair <| Computable.snd ) using 1;
      -- The product of two computable functions is computable.
      have h_prod : ∀ (f g : (ℕ × ℕ × BitString) × ℕ → ℕ), Computable f → Computable g → Computable
          (fun p => f p * g p) := by
        intros f g hf hg
        have h_prod : Computable (fun p : ℕ × ℕ => p.1 * p.2) := by
          -- The multiplication function is primitive recursive, hence computable.
          have h_mul_primrec : Primrec (fun p : ℕ × ℕ => p.1 * p.2) := by
            exact Primrec.nat_mul.comp ( Primrec.fst ) ( Primrec.snd )
          generalize_proofs at *;
          exact h_mul_primrec.to_comp;
        exact h_prod.comp (hf.pair hg);
      exact h_prod _ _ h_f h_g
    have := @computable_range_sum
    generalize_proofs at *;
    convert this _ _ _ _ using 1;
    · convert h_g using 1;
    · exact Computable.fst.comp Computable.snd
  generalize_proofs at *;
  convert h_computable using 1

/-
The decision `evOut t = some out` is computable in `(t, out)`.
-/
lemma evOutEq_decide_computable :
    Computable (fun p : ℕ × BitString => decide (evOut p.1 = some p.2)) := by
  have h_eq : PrimrecPred (fun q : Option BitString × BitString => q.1 = some q.2) := by
    convert PrimrecRel.comp Primrec.eq ( Primrec.fst )
      ( Primrec.option_some.comp ( Primrec.snd ) ) using 1;
  have h_eq : Computable (fun q : Option BitString × BitString => decide (q.1 = some q.2)) := by
    obtain ⟨ f, hf ⟩ := h_eq;
    convert hf.to_comp;
  convert h_eq.comp
    ( Computable.pair ( evOut_computable.comp Computable.fst ) Computable.snd ) using 1

/-
The full stage-term (with the running-mass and output guards) is computable.
-/
lemma truncGTerm_computable (hcomp : Computable
      (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) (d : ℕ) :
    Computable (fun q : (ℕ × BitString × BitString) × ℕ =>
      if cumNum approx q.1.1 (q.2 + 1) q.1.2.2 ≤ 2 ^ (d + q.1.1) ∧ evOut q.2 = some q.1.2.1 then
        evNum approx q.2 q.1.2.2 * 2 ^ (q.1.1 - evK q.2)
      else 0) := by
  have h_cond : Computable
      (fun q : ℕ × ℕ × BitString × BitString =>
        decide (cumNum approx q.1 (q.2.1 + 1) q.2.2.2 ≤ 2^(d + q.1)
          ∧ evOut q.2.1 = some q.2.2.1)) := by
    have h_cond : Computable
        (fun q : ℕ × ℕ × BitString × BitString =>
          decide (cumNum approx q.1 (q.2.1 + 1) q.2.2.2 ≤ 2^(d + q.1))) := by
      have h_cond : Computable (fun q : ℕ × ℕ × BitString => cumNum approx q.1 q.2.1 q.2.2) := by
        convert cumNum_computable hcomp using 1;
      have h_cond : Computable
          (fun q : ℕ × ℕ × BitString => decide (cumNum approx q.1 q.2.1 q.2.2 ≤ 2^(d + q.1))) := by
        have h_cond : Computable (fun q : ℕ × ℕ × BitString => cumNum approx q.1 q.2.1 q.2.2) ∧
            Computable (fun q : ℕ × ℕ × BitString => 2^(d + q.1)) := by
          refine ⟨ h_cond, ?_ ⟩;
          convert Primrec.to_comp
            ( show Primrec ( fun q : ℕ × ℕ × BitString => 2 ^ ( d + q.1 ) ) from ?_ ) using 1;
          convert Primrec.comp ( show Primrec ( fun n : ℕ => 2 ^ n ) from ?_ )
            ( show Primrec ( fun q : ℕ × ℕ × BitString => d + q.1 ) from ?_ ) using 1;
          · convert primrec_two_pow_aux using 1;
          · exact Primrec.nat_add.comp ( Primrec.const d ) ( Primrec.fst );
        have h_cond : Computable
            (fun q : ℕ × ℕ × BitString => (cumNum approx q.1 q.2.1 q.2.2, 2^(d + q.1))) := by
          exact Computable.pair h_cond.1 h_cond.2;
        have h_cond : Computable (fun q : ℕ × ℕ => decide (q.1 ≤ q.2)) := by
          convert Primrec.to_comp _;
          convert Primrec.nat_le using 1;
          simp only [PrimrecRel];
          constructor;
          · intro h; exact ⟨ inferInstance, h.of_eq (fun _ => by congr) ⟩;
          · rintro ⟨ _, hp ⟩; exact hp.of_eq (fun _ => by congr);
        convert h_cond.comp
          ‹Computable fun q : ℕ × ℕ × BitString =>
            ( cumNum approx q.1 q.2.1 q.2.2, 2 ^ ( d + q.1 ) ) › using 1;
      convert h_cond.comp
        ( show Computable ( fun q : ℕ × ℕ × BitString × BitString => ( q.1, q.2.1 + 1, q.2.2.2 ) )
          from ?_ ) using 1;
      exact Computable.pair ( Computable.fst )
        ( Computable.pair ( Computable.succ.comp ( Computable.fst.comp ( Computable.snd ) ) )
          ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd ) ) ) );
    have h_cond : Computable
        (fun q : ℕ × ℕ × BitString × BitString => decide (evOut q.2.1 = some q.2.2.1)) := by
      have h_cond : Computable (fun p : ℕ × BitString => decide (evOut p.1 = some p.2)) := by
        exact evOutEq_decide_computable;
      convert h_cond.comp
        ( Computable.fst.comp ( Computable.snd ) |> Computable.pair
          <| Computable.fst.comp ( Computable.snd.comp ( Computable.snd ) ) ) using 1;
    rename_i h;
    convert Computable.cond h ( h_cond ) ( Computable.const false ) using 1;
    ext; simp only [Bool.decide_and, Bool.cond_false_right]
  have h_then : Computable
      (fun q : ℕ × ℕ × BitString × BitString =>
        evNum approx q.2.1 q.2.2.2 * 2^(q.1 - evK q.2.1)) := by
    have h_then : Computable
      (fun q : ℕ × ℕ × BitString × BitString => evNum approx q.2.1 q.2.2.2) := by
      convert evNum_computable hcomp |> Computable.comp
        <| Computable.fst.comp ( Computable.snd ) |> Computable.pair
        <| Computable.snd.comp ( Computable.snd.comp ( Computable.snd ) ) using 1;
    have h_exp : Computable (fun q : ℕ × ℕ × BitString × BitString => 2 ^ (q.1 - evK q.2.1)) := by
      have h_exp : Computable (fun q : ℕ × ℕ × BitString × BitString => q.1 - evK q.2.1) := by
        have h_exp : Computable (fun q : ℕ × ℕ => q.1 - q.2) := by
          -- The subtraction function is primitive recursive, hence computable.
          have h_sub_primrec : Primrec (fun q : ℕ × ℕ => q.1 - q.2) := by
            exact Primrec.nat_sub.comp ( Primrec.fst ) ( Primrec.snd );
          exact h_sub_primrec.to_comp;
        convert h_exp.comp
          ( Computable.fst.pair
            ( evK_computable.comp ( Computable.fst.comp ( Computable.snd ) ) ) ) using 1;
      convert Computable.comp ( show Computable ( fun n : ℕ => 2 ^ n ) from ?_ ) h_exp using 1;
      convert Primrec.to_comp ( primrec_two_pow_aux ) using 1;
    have h_mul : Computable (fun p : ℕ × ℕ => p.1 * p.2) := by
      convert Primrec.nat_mul.to_comp using 1;
    convert h_mul.comp ( h_then.pair h_exp ) using 1;
  convert Computable.cond h_cond ( h_then.comp ( Computable.id ) ) ( Computable.const 0 ) using 1;
  constructor <;> intro h;
  · convert h_cond.cond h_then ( Computable.const 0 ) using 1;
  · convert h.comp ( Computable.pair ( Computable.fst.comp Computable.fst )
      ( Computable.pair ( Computable.snd ) ( Computable.snd.comp Computable.fst ) ) ) using 1;
    ext
    simp only [Bool.decide_and, id_eq, Bool.ite_eq_cond_iff, Bool.and_eq_true, decide_eq_true_eq]

/-
The stage-`S` numerator is computable in `(S, out, ctx)`.
-/
lemma truncGapprox_computable (hcomp : Computable
      (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) (d : ℕ) :
    Computable (fun p : ℕ × BitString × BitString => truncGapprox approx d p.1 p.2.1 p.2.2) := by
  convert computable_range_sum _ _ _ _ using 1;
  · convert truncGTerm_computable hcomp d using 1;
  · exact Computable.fst

end Truncate

/-- **Scale invariance of the dyadic value.**  Multiplying the numerator by `2 ^ k` and
raising the stage by `k` leaves `n / 2 ^ s` unchanged.  Every "rescale the numerator and
the stage together" lemma of the library is an instance of this one. -/
lemma dyadicValue_two_pow_mul_add (n s k : ℕ) :
    dyadicValue (2 ^ k * n) (s + k) = dyadicValue n s := by
  have h : ((2 : ℝ≥0∞) * 2⁻¹) ^ k = 1 := by
    rw [ENNReal.mul_inv_cancel two_ne_zero (by simp), one_pow]
  unfold dyadicValue
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.inv_pow, ENNReal.inv_pow]
  push_cast
  calc ((2 : ℝ≥0∞) ^ k * n) * (2⁻¹) ^ (s + k)
      = ((2 : ℝ≥0∞) * 2⁻¹) ^ k * ((n : ℝ≥0∞) * (2⁻¹) ^ s) := by
        rw [mul_pow, pow_add]; ring
    _ = (n : ℝ≥0∞) * (2⁻¹) ^ s := by rw [h, one_mul]

/-- **The dyadic value is `ℕ`-homogeneous in its numerator.**  Every "multiply the
numerator by a constant" lemma of the library is an instance of this one. -/
lemma dyadicValue_natCast_mul_left (c n s : ℕ) :
    dyadicValue (c * n) s = (c : ℝ≥0∞) * dyadicValue n s := by
  simp only [dyadicValue, Nat.cast_mul, mul_div_assoc]

/-- Doubling the numerator and passing to the next stage leaves the dyadic value unchanged. -/
lemma dyadicValue_two_mul_succ (n s : ℕ) :
    dyadicValue (2 * n) (s + 1) = dyadicValue n s := by
  simpa using dyadicValue_two_pow_mul_add n s 1

/-- The dyadic value of `2 ^ (s - k)` at stage `s` is `2 ^ (-k)` whenever `k ≤ s`. -/
lemma dyadicValue_two_pow_sub {k s : ℕ} (h : k ≤ s) :
    dyadicValue (2 ^ (s - k)) s = (2 : ℝ≥0∞)⁻¹ ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, s = j + k := ⟨s - k, by omega⟩
  have hj : j + k - k = j := by omega
  have hcast : ((2 ^ j : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ j := by push_cast; ring
  have hone : ((2 : ℝ≥0∞)⁻¹) ^ k * (2 : ℝ≥0∞) ^ k = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  have key : (2 : ℝ≥0∞)⁻¹ ^ k * (2 : ℝ≥0∞) ^ (j + k) = (2 : ℝ≥0∞) ^ j := by
    rw [pow_add, ← mul_assoc, mul_comm ((2 : ℝ≥0∞)⁻¹ ^ k) ((2 : ℝ≥0∞) ^ j), mul_assoc, hone,
      mul_one]
  rw [hj, dyadicValue, hcast, ← key, mul_div_assoc,
    ENNReal.div_self (by positivity) (ENNReal.pow_ne_top (by norm_num)), mul_one]

/-- The dyadic value of numerator one at stage `s` is `2^{-s}`. -/
lemma dyadicValue_one_eq_inv_two_pow' (s : ℕ) :
    dyadicValue 1 s = (2 : ℝ≥0∞)⁻¹ ^ s := by
  unfold dyadicValue
  simp only [Nat.cast_one, one_div, ENNReal.inv_pow]

/-- The dyadic value with numerator zero is zero. -/
lemma dyadicValue_zero (s : ℕ) : dyadicValue 0 s = 0 := by simp [dyadicValue]

/-- The dyadic value is additive in its numerator. -/
lemma dyadicValue_add (n m s : ℕ) : dyadicValue (n + m) s = dyadicValue n s + dyadicValue m s := by
  unfold dyadicValue
  have h : ((n + m : ℕ) : ℝ≥0∞) = (n : ℝ≥0∞) + (m : ℝ≥0∞) := by simp
  rw [h]
  exact ENNReal.add_div

/-- **The dyadic value is monotone in its numerator**, as a `Monotone` statement.  Every
"monotone in the numerator" lemma of the library — and, through `Monotone.map_max` and
`Monotone.map_min`, every lemma about the dyadic value of a `max` or a `min` — is an
instance of this one. -/
lemma monotone_dyadicValue_num (s : ℕ) : Monotone (fun n : ℕ => dyadicValue n s) := by
  intro n m h
  unfold dyadicValue
  exact ENNReal.div_le_div_right (by exact_mod_cast h) _

/-- The dyadic value is monotone in its numerator. -/
lemma dyadicValue_mono_num {n m : ℕ} (h : n ≤ m) (s : ℕ) :
    dyadicValue n s ≤ dyadicValue m s := monotone_dyadicValue_num s h

/-- A dyadic value is finite: it is a natural number divided by a positive power of two. -/
lemma dyadicValue_lt_top (n s : ℕ) : dyadicValue n s < ⊤ := by
  rw [dyadicValue, lt_top_iff_ne_top]
  exact ENNReal.div_ne_top (by simp) (pow_ne_zero s (by simp))

/-- The dyadic value of the numerator `2 ^ s` at stage `s` is one. -/
lemma dyadicValue_two_pow_eq_one (s : ℕ) : dyadicValue (2 ^ s) s = 1 := by
  have h : ((2 ^ s : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ s := by push_cast; ring
  rw [dyadicValue, h]
  exact ENNReal.div_self (pow_ne_zero s (by simp)) (ENNReal.pow_ne_top (by simp))

/-- The dyadic value `dyadicValue m s` is `m · 2^{-s}`. -/
lemma dyadicValue_eq_mul_inv_pow (m s : ℕ) :
    dyadicValue m s = (m : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ s := by
  unfold dyadicValue
  rw [div_eq_mul_inv, ENNReal.inv_pow]
end Kolmogorov
