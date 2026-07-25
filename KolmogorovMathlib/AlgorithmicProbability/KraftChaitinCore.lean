import KolmogorovMathlib.AlgorithmicProbability.Coding
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.Prefix.Optimal
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# The abstract Kraft–Chaitin realization engine

This module isolates the genuinely hard Chapter-4 (SUV §4.x) coding engine — the
**online Kraft–Chaitin allocator** — into a single, abstract, reusable obligation
`kraftChaitin_realization_bound`, decoupled from every particular semimeasure.

The engine consumes a *lower-semicomputable* conditional function
`f : output → context → ℝ≥0∞` (interface `IsLSC`: a computable, monotone, dyadic
approximation converging to `f`) that is globally `2^{d}`-subnormalized
(`∀ ctx, ∑_out f out ctx ≤ 2^{d}`), and produces a genuine prefix decompressor
`M'` realizing `f` up to an additive coding constant `c₀`:
`2^{-c₀} · f(out | ctx) ≤ 2^{-KP_{M'}(out | ctx)}`.

This is the canonical textbook statement of the Kraft–Chaitin coding theorem
(hard direction): it is `≤×`, with no logarithm and no equality, and the constant
`c₀` is genuine positive coding overhead (it absorbs the `2^{-d}` down-scaling the
truncated allocator hardcodes).

The two principal coding applications reduce to this single engine:

* `aprioriMeasure_prefix_realization` (in `KraftChaitin`) applies it to
  `aprioriMeasure M` at level `d = 0`, using `aprioriMeasure_isLSC` and
  `tsum_aprioriMeasure_le_one`;
* `conditional_coding_section_realization` (in `ConditionalCoding`) applies it to a
  dynamically *truncated* scaled section at level `d`.

The `IsLSC` interface deliberately keeps the approximation **concrete** (a
`ℕ`-valued numerator over the dyadic denominator `2^{s}`, with `Computable`
witnessing computability) rather than introducing a generic typeclass: this avoids
universe/computability-class friction and keeps the engine's hypotheses exactly
the data an allocator consumes.
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

/-! ### The abstract Kraft–Chaitin realization engine (coding theorem, hard direction)

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
and the constant `c₀` is genuine coding overhead. -/

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

/-- `n ↦ 2^n` is primitive recursive (local helper for computability proofs). -/
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

/-! ### Uniform (index-parameterized) computability of the dyadic numerators

The lemmas above establish computability of the numerator chain for a single fixed
approximation `approx`. The following *uniform* variants thread an extra leading
index coordinate `i : ℕ` through the chain, so that an entire jointly-computable
*family* `b : ℕ → ℕ → BitString → BitString → ℕ` of approximations yields a jointly
computable numerator family. These are needed for the lower-semicomputability of a
countable mixture of sanitized enumerations (see `UniversalSemimeasure`). Each
proof mirrors the corresponding fixed-`approx` lemma with `b i` substituted and `i`
carried as a `Computable.fst`-style coordinate. -/

lemma incNum_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun p : ℕ × ℕ × BitString × BitString =>
      incNum (b p.1) p.2.1 p.2.2.1 p.2.2.2) := by
  convert Computable.nat_casesOn ( Computable.fst.comp ( Computable.snd ) ) _ _ using 1;
  rotate_left;
  · exact fun p => b p.1 0 p.2.2.1 p.2.2.2;
  · exact fun p k => b p.1 ( k + 1 ) p.2.2.1 p.2.2.2 - 2 * b p.1 k p.2.2.1 p.2.2.2;
  · convert hb.comp
      ( Computable.fst.pair ( Computable.const 0 |> Computable.pair
        <| Computable.fst.comp ( Computable.snd.comp Computable.snd ) |> Computable.pair
        <| Computable.snd.comp ( Computable.snd.comp Computable.snd ) ) ) using 1;
  · apply Computable.of_eq;
    rotate_right;
    · exact fun p => b p.1.1 ( p.2 + 1 ) p.1.2.2.1 p.1.2.2.2 -
        2 * b p.1.1 p.2 p.1.2.2.1 p.1.2.2.2;
    · have h_sub : Computable
        (fun p : ℕ × ℕ × BitString × BitString => b p.1 (p.2.1 + 1) p.2.2.1 p.2.2.2) := by
        convert hb.comp _ using 1;
        rotate_left;
        · exact fun p => ( p.1, p.2.1 + 1, p.2.2.1, p.2.2.2 );
        · exact Computable.pair ( Computable.fst )
            ( Computable.pair ( Computable.succ.comp ( Computable.fst.comp ( Computable.snd ) ) )
              ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd ) ) )
                ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd ) ) ) ) );
        · rfl;
      have h_mul : Computable
          (fun p : ℕ × ℕ × BitString × BitString => 2 * b p.1 p.2.1 p.2.2.1 p.2.2.2) := by
        convert Computable.comp ( show Computable ( fun p : ℕ => 2 * p ) from ?_ ) hb using 1;
        convert Primrec.to_comp ( show Primrec ( fun p : ℕ => 2 * p ) from ?_ ) using 1;
        exact Primrec.nat_mul.comp ( Primrec.const 2 ) ( Primrec.id );
      have h_sub : Computable
          (fun p : ℕ × ℕ × BitString × BitString =>
            b p.1 (p.2.1 + 1) p.2.2.1 p.2.2.2 - 2 * b p.1 p.2.1 p.2.2.1 p.2.2.2) := by
        have h_sub : Computable (fun p : ℕ × ℕ => p.1 - p.2) := by
          -- The subtraction function is primitive recursive, hence computable.
          exact (Primrec.nat_sub.comp ( Primrec.fst ) ( Primrec.snd )).to_comp;
        convert h_sub.comp ( Computable.pair
          ‹Computable fun p : ℕ × ℕ × BitString × BitString => b p.1 ( p.2.1 + 1 ) p.2.2.1 p.2.2.2›
          ‹Computable fun p : ℕ × ℕ × BitString × BitString => 2 * b p.1 p.2.1 p.2.2.1 p.2.2.2› )
            using 1;
      convert h_sub.comp _ using 1;
      rotate_left;
      · exact fun p => ( p.1.1, p.2, p.1.2.2.1, p.1.2.2.2 );
      · exact Computable.pair ( Computable.fst.comp Computable.fst )
          ( Computable.pair ( Computable.snd )
            ( Computable.pair
              ( Computable.fst.comp
                ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) ) )
              ( Computable.snd.comp
                ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) ) ) ) );
      · rfl;
    · intro n; rfl
  · exact funext fun p => by cases p.2.1 <;> rfl;

lemma evNum_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun p : ℕ × ℕ × BitString =>
      evNum (b p.1) p.2.1 p.2.2) := by
  convert Computable.comp ( Computable.cond _ _ _ ) _ using 1;
  rotate_left;
  · exact fun p => ( p.1, p.2.1, p.2.2, evOut p.2.1, evK p.2.1 );
  · exact inferInstance;
  · exact fun p => p.2.2.2.1.isSome;
  · exact fun p => incNum ( b p.1 ) p.2.2.2.2 p.2.2.2.1.get! p.2.2.1;
  · exact fun p => 0;
  · have h_comp : Computable (fun p : Option BitString => p.isSome) := by
      convert Computable.of_eq _ _;
      · exact fun p => p.elim false fun _ => true;
      · convert Computable.option_casesOn _ _ _ using 1;
        rotate_left;
        · exact Bool;
        · exact Primcodable.bool;
        · exact fun p => p.map fun _ => Bool.true;
        · exact fun _ => false;
        · exact fun p b => b;
        · exact Computable.option_map ( Computable.id ) ( Computable.const true );
        · exact Computable.const false;
        · exact Computable.snd;
        · exact funext fun x => by cases x <;> rfl;
      · exact fun n => by cases n <;> rfl;
    exact h_comp.comp
      ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd ) ) ) );
  · convert incNum_computable_uniform b hb using 1;
    constructor <;> intro h;
    · convert incNum_computable_uniform b hb using 1;
    · convert h.comp _ using 1;
      rotate_left;
      · exact fun p => ( p.1, p.2.2.2.2, p.2.2.2.1.get!, p.2.2.1 );
      · apply Computable.pair;
        · exact Computable.fst;
        · apply Computable.pair;
          · exact Computable.snd.comp
              ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd ) ) );
          · apply Computable.pair;
            · convert Computable.option_getD _ _ using 1;
              · exact Computable.fst.comp
                  ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd ) ) );
              · exact Computable.const _;
            · exact Computable.fst.comp ( Computable.snd.comp ( Computable.snd ) );
      · rfl;
  · exact Computable.const 0;
  · apply Computable.pair;
    · exact Computable.fst;
    · apply Computable.pair;
      · exact Computable.fst.comp Computable.snd;
      · apply Computable.pair;
        · exact Computable.snd.comp Computable.snd;
        · apply Computable.pair;
          · exact evOut_computable.comp ( Computable.fst.comp Computable.snd );
          · exact evK_computable.comp ( Computable.fst.comp ( Computable.snd ) );
  · ext; simp [evNum];
    cases evOut ‹ℕ × ℕ × BitString›.2.1 <;>
      simp only [Option.get!_none, Option.get!_some, Option.isSome_none,
        Option.isSome_some, cond_false, cond_true]

lemma cumNum_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun p : ℕ × ℕ × ℕ × BitString =>
      cumNum (b p.1) p.2.1 p.2.2.1 p.2.2.2) := by
  have h_g : Computable
      (fun q : (ℕ × ℕ × Nat × BitString) × ℕ =>
        evNum (b q.1.1) q.2 q.1.2.2.2 * 2 ^ (q.1.2.1 - evK q.2)) := by
    apply Computable.of_eq;
    rotate_right;
    · exact fun p => evNum ( b p.1.1 ) p.2 p.1.2.2.2 * 2 ^ ( p.1.2.1 - evK p.2 );
    · have h_term_computable : Computable
        (fun p : (ℕ × ℕ × Nat × BitString) × ℕ => evNum (b p.1.1) p.2 p.1.2.2.2) := by
        convert evNum_computable_uniform b hb |> Computable.comp
          <| show Computable ( fun p : ( ℕ × ℕ × Nat × BitString ) × ℕ =>
              ( p.1.1, p.2, p.1.2.2.2 ) ) from ?_ using 1;
        apply Computable.pair;
        · exact Computable.fst.comp Computable.fst;
        · apply Computable.pair;
          · exact Computable.snd;
          · exact Computable.snd.comp
              ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) );
      have h_exp_computable : Computable
          (fun p : (ℕ × ℕ × Nat × BitString) × ℕ => p.1.2.1 - evK p.2) := by
        convert Primrec.to_comp _;
        exact Primrec.nat_sub.comp ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst ) ) )
          ( Primrec.snd.comp ( Primrec.unpair.comp ( Primrec.snd ) ) );
      apply Computable.comp (Primrec.nat_mul.to_comp)
        (h_term_computable.pair (Computable.comp (primrec_two_pow_aux.to_comp) h_exp_computable));
    · exact fun _ => rfl;
  convert computable_range_sum _ _ _ _;
  · convert h_g.comp _ using 1;
    exact Computable.id;
  · exact Computable.fst.comp ( Computable.snd.comp ( Computable.snd ) )

lemma truncGTerm_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2))
    (d : ℕ) :
    Computable (fun q : (ℕ × ℕ × BitString × BitString) × ℕ =>
      if cumNum (b q.1.1) q.1.2.1 (q.2 + 1) q.1.2.2.2 ≤ 2 ^ (d + q.1.2.1)
          ∧ evOut q.2 = some q.1.2.2.1 then
        evNum (b q.1.1) q.2 q.1.2.2.2 * 2 ^ (q.1.2.1 - evK q.2)
      else 0) := by
  convert Computable.cond _ _ _;
  rotate_left;
  · exact fun q =>
      decide ( cumNum ( b q.1.1 ) q.1.2.1 ( q.2 + 1 ) q.1.2.2.2 ≤ 2 ^ ( d + q.1.2.1 )
        ∧ evOut q.2 = some q.1.2.2.1 );
  · convert Computable.cond _ _ _ using 1;
    rotate_left;
    · exact fun q =>
        cumNum ( b q.1.1 ) q.1.2.1 ( q.2 + 1 ) q.1.2.2.2 ≤ 2 ^ ( d + q.1.2.1 );
    · exact fun q => evOut q.2 = some q.1.2.2.1;
    · exact fun _ => Bool.false;
    · have h_cumNum_computable : Computable
        (fun q : (ℕ × ℕ × BitString × BitString) × ℕ =>
          cumNum (b q.1.1) q.1.2.1 (q.2 + 1) q.1.2.2.2) := by
        convert cumNum_computable_uniform b hb |> Computable.comp <| _ using 1;
        rotate_left;
        · exact fun q => ( q.1.1, q.1.2.1, q.2 + 1, q.1.2.2.2 );
        · exact Computable.pair ( Computable.fst.comp Computable.fst )
            ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp Computable.fst ) )
              ( Computable.pair ( Computable.succ.comp Computable.snd )
                ( Computable.snd.comp
                  ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) ) ) ) );
        · rfl;
      have h_exp_computable : Computable
          (fun q : (ℕ × ℕ × BitString × BitString) × ℕ => 2 ^ (d + q.1.2.1)) := by
        have h_exp_computable : Computable (fun q : ℕ => 2 ^ q) := by
          exact Primrec.to_comp primrec_two_pow_aux;
        convert h_exp_computable.comp _ using 1;
        have h_add_computable : Computable (fun q : ℕ => d + q) := by
          induction d with
          | zero => simpa using Computable.id
          | succ d ih =>
            convert ih.comp ( Computable.succ ) using 1;
            exact funext fun n => by omega;
        exact h_add_computable.comp ( Computable.fst.comp ( Computable.snd.comp Computable.fst ) );
      have h_decide_computable : Computable (fun q : ℕ × ℕ => decide (q.1 ≤ q.2)) := by
        convert Primrec.nat_le using 1;
        constructor <;> intro h <;> simp_all only [PrimrecRel];
        · exact Primrec.nat_le;
        · obtain ⟨ x, hx ⟩ := h;
          convert hx.to_comp using 1;
          convert rfl;
      convert h_decide_computable.comp
        ( Computable.pair h_cumNum_computable h_exp_computable ) using 1;
    · convert evOutEq_decide_computable.comp _ using 1;
      rotate_left;
      · exact fun q => ( q.2, q.1.2.2.1 );
      · exact Computable.pair ( Computable.snd )
          ( Computable.fst.comp
            ( Computable.snd.comp ( Computable.snd.comp ( Computable.fst ) ) ) );
      · rfl;
    · exact Computable.const false;
    · ext; simp only [Bool.decide_and, Bool.cond_false_right]
  · convert Computable.comp ( Primrec.nat_mul.to_comp ) ( Computable.pair _ _ ) using 1;
    · convert evNum_computable_uniform b hb |> Computable.comp
        <| Computable.pair ( Computable.fst.comp Computable.fst )
            ( Computable.pair Computable.snd
              ( Computable.snd.comp
                ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) ) ) ) using 1;
    · convert ( primrec_two_pow_aux.to_comp.comp _ ) using 1;
      convert Computable.comp ( Primrec.nat_sub.to_comp ) ( Computable.pair _ _ ) using 1;
      · exact Computable.fst.comp ( Computable.snd.comp Computable.fst );
      · exact evK_computable.comp ( Computable.snd );
  · exact Computable.const 0;
  · ext; simp only [Bool.decide_and, Bool.ite_eq_cond_iff, Bool.and_eq_true, decide_eq_true_eq]

lemma truncGapprox_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2))
    (d : ℕ) :
    Computable (fun p : ℕ × ℕ × BitString × BitString =>
      truncGapprox (b p.1) d p.2.1 p.2.2.1 p.2.2.2) := by
  convert computable_range_sum _ _ _ _ using 1;
  · convert truncGTerm_computable_uniform b hb d using 1;
  · exact Computable.fst.comp Computable.snd

/-
The truncated value as a tsum of accepted increments.
-/
lemma truncG_eq_tsum (d : ℕ) (out ctx : BitString) :
    truncG approx d out ctx
      = ∑' t : ℕ,
          if truncCum approx (t + 1) ctx ≤ (2 : ℝ≥0∞) ^ d ∧ evOut t = some out then
            evVal approx t ctx
          else 0 := by
  rw [ ENNReal.tsum_eq_iSup_nat ];
  exact iSup_congr fun i => by rw [ ← dyadicValue_truncGapprox ] ;

/-
The accepted cumulative mass never exceeds `2^d`.
-/
lemma tsum_accepted_le (d : ℕ) (ctx : BitString) :
    (∑' t : ℕ, if truncCum approx (t + 1) ctx ≤ (2 : ℝ≥0∞) ^ d then evVal approx t ctx else 0)
      ≤ (2 : ℝ≥0∞) ^ d := by
  -- Let `aterm t := if truncCum approx (t+1) ctx ≤ (2:ℝ≥0∞)^d then evVal approx t ctx else 0`.
  set aterm : ℕ → ℝ≥0∞ := fun t =>
    if truncCum approx (t + 1) ctx ≤ (2 : ℝ≥0∞) ^ d then evVal approx t ctx else 0;
  have h_aterm : ∀ S, (∑ t ∈ Finset.range S, aterm t) ≤ (2 : ℝ≥0∞) ^ d := by
    intro S
    induction S with
    | zero => simp_all only [Finset.range_zero, Finset.sum_empty, zero_le]
    | succ S ih =>
      simp_all only [Finset.sum_range_succ]
      by_cases h : truncCum approx ( S + 1 ) ctx ≤ 2 ^ d <;> simp_all only [not_le, truncCum];
      · simp_all only [Finset.sum_range_succ, aterm];
        refine le_trans ( add_le_add ( Finset.sum_le_sum fun _ _ => ?_ ) ( ?_ ) ) h;
        all_goals split_ifs <;> norm_num;
      · simp only [aterm] at ih ⊢
        rw [ if_neg ] <;> simp_all only [Finset.sum_range_succ, add_zero, not_le, truncCum];
  convert ENNReal.tsum_le_of_sum_range_le h_aterm using 1

/-
The total truncated mass is at most `2^d`.
-/
lemma tsum_truncG_le (d : ℕ) (ctx : BitString) :
    (∑' out : BitString, truncG approx d out ctx) ≤ (2 : ℝ≥0∞) ^ d := by
  rw [ show truncG approx d = _ from funext fun out => funext fun ctx => truncG_eq_tsum d out ctx ];
  rw [ ENNReal.tsum_comm ];
  refine le_trans ( ENNReal.tsum_le_tsum ?_ ) ( tsum_accepted_le (approx := approx) d ctx );
  intro a;
  rw [ tsum_eq_single ( evOut a |> Option.get! ) ];
  · cases h : evOut a <;> aesop;
  · cases h : evOut a <;> aesop

/-
For a fixed output, the tsum of its accepted increments (ignoring the cap)
recovers `f`.
-/
lemma tsum_evVal_out
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx)
    (out ctx : BitString) :
    (∑' t : ℕ, if evOut t = some out then evVal approx t ctx else 0) = f out ctx := by
  classical
  -- By definition of $evOut$, we know that $evOut t = some out$ if and only if $t = Nat.pair
  --   (Encodable.encode out) k$ for some $k$.
  have h_evOut : ∀ t, evOut t = some out ↔ ∃ k, t = Nat.pair (Encodable.encode out) k := by
    intro t
    simp only [evOut];
    constructor <;> intro h;
    · have := Encodable.decode₂_eq_some.mp h;
      exact ⟨ _, by rw [ this, Nat.pair_unpair ] ⟩;
    · obtain ⟨ k, rfl ⟩ := h; simp only [Encodable.decode₂_encode, Nat.unpair_pair] ;
  -- Apply the fact that the sum over `t` where `evOut t = some out` is equal to the sum over `k` of
  --   `evVal approx (Nat.pair (Encodable.encode out) k) ctx`.
  have h_sum_eq : (∑' t, if evOut t = some out then evVal approx t ctx else 0) =
      (∑' k, evVal approx (Nat.pair (Encodable.encode out) k) ctx) := by
    simp +decide only [h_evOut];
    erw [ ← tsum_subtype ];
    erw [ ← Equiv.tsum_eq ( Equiv.ofBijective
      ( fun k : ℕ => ⟨ Nat.pair ( Encodable.encode out ) k, ⟨ k, rfl ⟩ ⟩ :
        ℕ → { t : ℕ // ∃ k : ℕ, t = Nat.pair ( Encodable.encode out ) k } )
      ⟨ fun a => by aesop, fun a => by aesop ⟩ ) ]
    aesop
  convert tsum_dyadicValue_incNum hmono hsup out ctx using 1;
  convert h_sum_eq using 3;
  unfold evVal; simp only [Nat.unpair_pair, evK] ;
  unfold evNum; simp only [Encodable.decode₂_encode, Nat.unpair_pair, evK, evOut] ;

/-
Summed over all events, the increment values recover the total `f`-mass.
-/
lemma tsum_evVal
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx)
    (ctx : BitString) :
    (∑' t : ℕ, evVal approx t ctx) = ∑' out : BitString, f out ctx := by
  -- Apply the fact that the sum over all out is the same as the sum over t of the sum over out of
  --   the terms where evOut t equals some out.
  have h_sum_out : ∀ t, ∑' out, (if evOut t = some out then evVal approx t ctx else 0) = evVal
      approx t ctx := by
    intro t
    by_cases h : evOut t = none;
    · simp only [h, evVal, evNum]
      unfold dyadicValue; norm_num;
    · obtain ⟨out, hout⟩ : ∃ out, evOut t = some out := by
        exact Option.ne_none_iff_exists'.mp h;
      rw [ tsum_eq_single out ] <;> aesop;
  rw [ ← funext h_sum_out, ENNReal.tsum_comm ];
  exact tsum_congr fun out => by rw [ ← tsum_evVal_out hmono hsup out ctx ] ;

/-
Agreement: where the total `f`-mass respects the cap, the truncation is `f`.
-/
lemma truncG_eq_f_of_le
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx)
    (d : ℕ) (ctx : BitString)
    (hle : (∑' out : BitString, f out ctx) ≤ (2 : ℝ≥0∞) ^ d) (out : BitString) :
    truncG approx d out ctx = f out ctx := by
  -- For the given `ctx`, the total `f`-mass is ≤ `2^d` (hypothesis `hle`).
  have h_sum_le : ∀ n, truncCum approx n ctx ≤ (2 : ℝ≥0∞) ^ d := by
    intro n
    have h_sum_le : truncCum approx n ctx ≤ ∑' t : ℕ, evVal approx t ctx := by
      exact ENNReal.sum_le_tsum _;
    exact h_sum_le.trans ( by rw [ tsum_evVal hmono hsup ctx ] ; exact hle );
  rw [ truncG_eq_tsum, ← tsum_evVal_out hmono hsup out ctx ];
  exact tsum_congr fun t => by aesop;

end Truncate

/-- **Dynamic truncation of a lower-semicomputable function to a global mass bound.**

Given a lower-semicomputable `f` and a level `d`, there is a lower-semicomputable
`g` that is *globally* `2^{d}`-subnormalized (`∀ ctx, ∑_out g out ctx ≤ 2^{d}`) and
agrees with `f` on every context whose own `f`-mass already respects the bound
(`∑_out f out ctx ≤ 2^{d} → g = f` on that context).

This is the online "cap the running mass at `2^{d}`" operator: enumerate the dyadic
increments of `f` (via its `IsLSC` approximation) and accept each only while the
accumulated per-context mass stays `≤ 2^{d}`. The accepted stream is itself
lower-semicomputable and globally bounded; where `f`'s total mass never exceeds the
cap, no increment is ever dropped, so `g = f` there.

This packages the dynamic-truncation half of the *conditional* Kraft–Chaitin
construction (SUV §4.5): it converts the merely per-context-guarded scaled section
into a globally-bounded l.s.c. function the abstract allocator
`kraftChaitin_realization_bound` can consume directly.

The construction is the take-while online truncation `truncG`: enumerate all dyadic
increments of `f` as a single `ℕ`-indexed stream (output decoded via
`Encodable.decode₂`, stage from `Nat.unpair`), accept an increment iff the running
cumulative mass stays `≤ 2^{d}`, and read off the accepted mass per output as the
supremum of exact dyadic numerators over `2^{S}`. The
`truncG*`/`ev*`/`cumNum`/`incNum` lemmas above establish lower semicomputability
(`truncGapprox_mono`, `truncGapprox_computable`), the global `2^{d}` bound
(`tsum_truncG_le`), and agreement (`truncG_eq_f_of_le`). -/
theorem IsLSC.truncate {f : BitString → BitString → ℝ≥0∞} (hf : IsLSC f) (d : ℕ) :
    ∃ g : BitString → BitString → ℝ≥0∞, IsLSC g ∧
      (∀ ctx : BitString, (∑' out : BitString, g out ctx) ≤ (2 : ℝ≥0∞) ^ d) ∧
      (∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ (2 : ℝ≥0∞) ^ d →
        ∀ out : BitString, g out ctx = f out ctx) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hf
  refine ⟨truncG approx d, ⟨truncGapprox approx d, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro S out ctx; exact truncGapprox_mono d S out ctx
  · intro out ctx; rfl
  · exact truncGapprox_computable hcomp d
  · intro ctx; exact tsum_truncG_le d ctx
  · intro ctx hle out; exact truncG_eq_f_of_le hmono hsup d ctx hle out

/-! ### Kraft–Chaitin realization engine

This section follows the truncation and `ev*` machinery so that
`extract_request_stream` can reuse it. -/

/-
Step 1: Extract dyadic increments from a unit-mass lower-semicomputable function
into a computable request stream family.
-/
lemma extract_request_stream {f : BitString → BitString → ℝ≥0∞}
    (hlsc : IsLSC f)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1) :
    ∃ req : BitString → ℕ → Option (BitString × ℕ),
      Computable (fun p : BitString × ℕ => req p.1 p.2) ∧
      (∀ ctx : BitString,
        (∑' n, match req ctx n with
          | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l
          | none => 0) ≤ 1) ∧
      (∀ ctx out : BitString,
        (∑' n, match req ctx n with
          | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0
          | none => 0) = f out ctx) := by
  obtain ⟨ approx, hmono ⟩ := hlsc;
  refine ⟨ fun ctx n =>
    if ( Nat.unpair n ).2 < evNum approx ( Nat.unpair n ).1 ctx then
      ( evOut ( Nat.unpair n ).1 ).map fun o => ( o, evK ( Nat.unpair n ).1 )
    else none, ?_, ?_, ?_ ⟩;
  · have h_cond : Computable
      (fun p : BitString × ℕ =>
        if (Nat.unpair p.2).2 < evNum approx (Nat.unpair p.2).1 p.1 then true
        else false) := by
      have h_cond : Computable (fun p : BitString × ℕ => evNum approx (Nat.unpair p.2).1 p.1) := by
        have := evNum_computable hmono.2.2;
        convert this.comp ( Computable.pair
          ( Computable.fst.comp ( Computable.unpair.comp ( Computable.snd ) ) )
          ( Computable.fst ) ) using 1;
      have h_cond : Computable (fun p : ℕ × ℕ => if p.1 < p.2 then true else false) := by
        convert Computable.of_eq _ _;
        · exact fun p => Nat.recOn ( p.2 - p.1 ) false fun _ _ => true;
        · apply Computable.nat_casesOn;
          · have h_cond : Computable (fun p : ℕ × ℕ => p.2 - p.1) := by
              exact (Primrec.nat_sub.comp ( Primrec.snd ) ( Primrec.fst )).to_comp;
            exact h_cond;
          · exact Computable.const false;
          · exact Computable.const true;
        · intro n
          cases le_total n.1 n.2 <;>
            simp only [*, Bool.and_true, Bool.if_false_right, Nat.rec_zero,
              Nat.sub_eq_zero_of_le, false_eq_decide_iff, not_lt]
          cases lt_or_eq_of_le ‹_› <;>
            simp only [*, Nat.rec_zero, decide_false, decide_true, lt_self_iff_false,
              tsub_self]
          exact Nat.le_induction ( by tauto ) ( fun k hk ih => by tauto ) _
            ( Nat.sub_pos_of_lt ‹_› );
      convert h_cond.comp ( Computable.pair
        ( Computable.snd.comp ( Computable.unpair.comp ( Computable.snd ) ) )
        ‹Computable fun p : BitString × ℕ =>
          evNum approx ( Nat.unpair p.2 ).1 p.1› ) using 1;
    have h_map : Computable
        (fun p : BitString × ℕ =>
          Option.map (fun o => (o, evK (Nat.unpair p.2).1))
            (evOut (Nat.unpair p.2).1)) := by
      have h_map : Computable
          (fun p : ℕ => Option.map (fun o => (o, evK (Nat.unpair p).1))
            (evOut (Nat.unpair p).1)) := by
        have h_map : Computable (fun p : ℕ => evOut (Nat.unpair p).1) := by
          exact evOut_computable.comp ( Computable.fst.comp ( Computable.unpair ) );
        convert Computable.option_map h_map _ using 1;
        exact Computable.pair ( Computable.snd )
          ( Computable.comp ( evK_computable )
            ( Computable.fst.comp ( Computable.unpair.comp ( Computable.fst ) ) ) );
      exact h_map.comp ( Computable.snd );
    convert Computable.cond h_cond h_map ( Computable.const none ) using 1;
    ext a; by_cases h : (Nat.unpair a.2).2 < evNum approx (Nat.unpair a.2).1 a.1 <;> simp [h]
  · intro ctx;
    -- Reindex the sum over `n` to a sum over `t` and `j`.
    have h_reindex :
        (∑' n : ℕ, (if (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx then
          (2⁻¹ : ℝ≥0∞) ^ (evK (Nat.unpair n).1) else 0)) =
        (∑' t : ℕ, (∑' j : ℕ,
          (if j < evNum approx t ctx then (2⁻¹ : ℝ≥0∞) ^ (evK t) else 0))) := by
      rw [ ← ENNReal.tsum_prod ];
      rw [ ← Equiv.tsum_eq ( Equiv.ofBijective
        ( fun n : ℕ => ( Nat.unpair n |>.1, Nat.unpair n |>.2 ) )
        ⟨ fun a => ?_, fun a => ?_ ⟩ ) ];
      · congr! 1;
      · exact fun n hn => by simpa using congr_arg ( fun p => Nat.pair p.1 p.2 ) hn;
      · exact ⟨ Nat.pair a.1 a.2, by simp only [Nat.unpair_pair, Prod.mk.eta] ⟩;
    convert h_reindex.le.trans _ using 1;
    · refine tsum_congr fun n => ?_;
      unfold evNum; aesop;
    · convert tsum_evVal hmono.1 hmono.2.1 ctx |> le_of_eq |> le_trans <| h_sum ctx using 1;
      refine tsum_congr fun t => ?_;
      rw [ tsum_eq_sum ];
      any_goals exact Finset.range ( evNum approx t ctx );
      · simp only [Finset.sum_const, Finset.sum_ite, evVal, not_lt, nsmul_eq_mul];
        rw [ Finset.filter_true_of_mem fun x hx => Finset.mem_range.mp hx ]
        norm_num [ dyadicValue ]
        rw [ div_eq_mul_inv, ENNReal.inv_pow ];
      · aesop;
  · intro ctx out
    have h_sum_eq :
        (∑' n : ℕ, (if (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx ∧
          evOut (Nat.unpair n).1 = some out then
            (2 : ℝ≥0∞)⁻¹ ^ evK (Nat.unpair n).1
          else 0)) = f out ctx := by
      have h_sum_eq :
          ∑' t : ℕ, (if evOut t = some out then evVal approx t ctx else 0) =
            f out ctx := by
        convert tsum_evVal_out hmono.1 hmono.2.1 out ctx using 1;
      convert h_sum_eq using 1;
      have h_sum_eq : ∀ t : ℕ, ∑' j : ℕ,
          (if j < evNum approx t ctx ∧ evOut t = some out then (2 : ℝ≥0∞)⁻¹ ^ (evK t) else 0) = if
          evOut t = some out then evVal approx t ctx else 0 := by
        intro t
        split_ifs <;>
          simp_all only [and_false, and_true, dyadicValue, evVal, tsum_zero,
            ↓reduceIte]
        rw [ tsum_eq_sum ];
        any_goals exact Finset.range ( evNum approx t ctx );
        · rw [ Finset.sum_congr rfl fun x hx => if_pos <| Finset.mem_range.mp hx ]
          norm_num [ div_eq_mul_inv ]
          norm_num [ ENNReal.inv_pow ];
        · intro b hb; rw [if_neg (by simpa using hb)]
      rw [ ← funext h_sum_eq ];
      rw [ ← ENNReal.tsum_prod ];
      rw [ ← Equiv.tsum_eq ( Equiv.ofBijective
        ( fun n : ℕ => ( Nat.unpair n |>.1, Nat.unpair n |>.2 ) )
        ⟨ fun n => ?_, fun n => ?_ ⟩ ) ];
      · congr! 1;
      · exact fun m hm => by simpa using congr_arg ( fun p => Nat.pair p.1 p.2 ) hm;
      · exact ⟨ Nat.pair n.1 n.2, by simp only [Nat.unpair_pair, Prod.mk.eta] ⟩;
    convert h_sum_eq using 3;
    cases h : evOut ( Nat.unpair ‹_› ).1 <;> aesop

/-- **The online Kraft–Chaitin allocator.**

Given, uniformly in `ctx`, a computable request stream `req ctx n = some (o, l)`
of total Kraft weight `≤ 1`, produce a computable prefix-free code assignment
`alloc ctx n` realizing every requested length, with codes for distinct indices
pairwise prefix-incomparable.

This is the genuine *online* (causal) allocator: `alloc ctx n` may depend only on
requests with index `< n`, which is what makes it computable. It is realized by the
leftmost-free-dyadic-interval algorithm maintaining a free list of tree nodes of
pairwise distinct lengths (so a length-`l` request is always serviceable once the
used measure leaves `≥ 2^{-l}` of free space, the nodes of length `> l` summing to
`< 2^{-l}`). Allocating the smallest fitting free interval and returning its
right-siblings to the free list preserves the invariant; disjoint dyadic intervals
yield prefix-incomparable codes.

This allocator is fully formalized in
`KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator`: the free-list data
structure (`allocFun`), its computability (`allocFun_computable`), the
prefix-incomparability of distinct codes (`allocFun_prefixFree`), and the
serviceability of every request under the unit Kraft bound (`allocFun_success`) are
all proved there.  Together with the surrounding development — the geometric dyadic
request extraction (`extract_request_stream_geometric`), the prefix-machine
construction (`construct_prefix_machine`), and the realization bound
(`realization_bound_of_machine`) — this completes `kraftChaitin_realization_bound_unit`. -/
lemma exists_online_prefixFree_family (req : BitString → ℕ → Option (BitString × ℕ))
    (hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2))
    (hweight : ∀ ctx,
      (∑' n, match req ctx n with
        | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l
        | none => 0) ≤ 1) :
    ∃ alloc : BitString → ℕ → Option BitString,
      Computable (fun p : BitString × ℕ => alloc p.1 p.2) ∧
      (∀ ctx n o l, req ctx n = some (o, l) → ∃ c, alloc ctx n = some c ∧ c.length = l) ∧
      (∀ ctx n m cn cm, alloc ctx n = some cn → alloc ctx m = some cm → n ≠ m →
        ¬ List.IsPrefix cn cm) := by
  refine ⟨fun ctx => KraftChaitin.allocFun (req ctx), ?_, ?_, ?_⟩
  · exact KraftChaitin.allocFun_computable req hcomp
  · intro ctx n o l hreq
    exact KraftChaitin.allocFun_success (req ctx) n o l hreq (hweight ctx)
  · intro ctx n m cn cm hn hm hneq
    exact KraftChaitin.allocFun_prefixFree (req ctx) n m cn cm hn hm hneq

/-
Computability of the inversion search predicate used to build the prefix machine.
-/
lemma construct_pred_computable (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (hreqcomp : Computable (fun p : BitString × ℕ => req p.1 p.2))
    (hcomp : Computable (fun p : BitString × ℕ => alloc p.1 p.2)) :
    Computable (fun p : (BitString × BitString) × ℕ =>
      decide (alloc p.1.2 p.2 = some p.1.1 ∧ (req p.1.2 p.2).isSome = true)) := by
  have hallocdec : Computable
      (fun p : BitString × BitString × ℕ => decide (alloc p.2.1 p.2.2 = some p.1)) := by
    have hdecid : Computable
        (fun p : Option BitString × BitString => decide (p.1 = some p.2)) := by
      have hdecid : Computable
          (fun p : Option BitString × Option BitString => decide (p.1 = p.2)) := by
        have hdecid : Primrec
            (fun p : Option BitString × Option BitString => decide (p.1 = p.2)) := by
          convert Primrec.eq;
          any_goals exact Option BitString;
          constructor <;> intro h <;> rw [ PrimrecRel ] at *;
          · convert h using 1;
            constructor <;> intro h <;> rw [ PrimrecPred ] at *;
            · assumption
            · exact ⟨ inferInstance, h ⟩;
          · obtain ⟨ _, hp ⟩ := h; exact hp.of_eq (fun _ => by congr);
        exact hdecid.to_comp;
      convert hdecid.comp
        ( Computable.fst.pair ( Computable.option_some.comp Computable.snd ) ) using 1;
    convert hdecid.comp
      ( hcomp.comp ( Computable.snd ) |> Computable.pair <| Computable.fst ) using 1
  have hreqdec : Computable (fun p : BitString × BitString × ℕ => (req p.2.1 p.2.2).isSome) := by
    have hreqdec : Computable (fun p : BitString × Nat => (req p.1 p.2).isSome) := by
      have hreqdec : Computable (fun p : BitString × Nat => req p.1 p.2) := hreqcomp
      convert Computable.comp _ hreqdec using 1;
      convert Primrec.option_isSome.to_comp using 1;
    convert hreqdec.comp
      ( Computable.fst.comp ( Computable.snd ) |> Computable.pair
        <| Computable.snd.comp ( Computable.snd ) ) using 1;
  have h_computable_and : Computable
      (fun p : BitString × BitString × ℕ =>
        decide (alloc p.2.1 p.2.2 = some p.1 ∧ (req p.2.1 p.2.2).isSome)) := by
    convert Computable.cond ( hallocdec ) ( hreqdec ) ( Computable.const false ) using 1;
    ext a; simp only [Bool.decide_and, Bool.decide_eq_true, Bool.cond_false_right]
  convert h_computable_and.comp
    ( Computable.fst.comp ( Computable.fst ) |> Computable.pair
      <| Computable.snd.comp ( Computable.fst ) |> Computable.pair
      <| Computable.snd ) using 1

/-
Partrec output stage used to build the prefix machine: at the found index `n`,
emit the first component of `req ctx n` (undefined if `req ctx n = none`).
-/
lemma construct_out_partrec (req : BitString → ℕ → Option (BitString × ℕ))
    (hreqcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Partrec₂ (fun (p : BitString × BitString) (n : ℕ) =>
      ((req p.2 n).map Prod.fst : Option BitString) |> Part.ofOption) := by
  -- The function `if p.2 = some x then some x.1 else none` is computable.
  have h_if_computable : Computable
      (fun p : Option (BitString × ℕ) => Option.map Prod.fst p) := by
    refine Computable.option_map ?_ ?_;
    · exact Computable.id;
    · exact Computable.fst.comp ( Computable.snd ) |> Computable.comp <| Computable.id;
  have h_partrec : Computable
      (fun p : (BitString × BitString) × ℕ => Option.map Prod.fst (req p.1.2 p.2)) := by
    convert h_if_computable.comp
      ( hreqcomp.comp ( Computable.snd.comp ( Computable.fst ) |> Computable.pair
        <| Computable.snd ) ) using 1;
  convert h_partrec.partrec using 1;
  constructor <;> intro h <;> rw [ Partrec₂ ] at *;
  · convert h_partrec using 1;
  · exact h_partrec.ofOption

/-
Step 4: Construct a prefix decompressor from an allocator and a request stream.
-/
lemma construct_prefix_machine (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (hreqcomp : Computable (fun p : BitString × ℕ => req p.1 p.2))
    (hcomp : Computable (fun p : BitString × ℕ => alloc p.1 p.2))
    (_halloc : ∀ ctx n o l, req ctx n = some (o, l) →
      ∃ c, alloc ctx n = some c ∧ c.length = l)
    (hprefix : ∀ ctx n m cn cm, alloc ctx n = some cn → alloc ctx m = some cm →
      n ≠ m → ¬ List.IsPrefix cn cm) :
    ∃ M' : Map, IsPrefixDecompressor M' ∧
      ∀ ctx n o l c, req ctx n = some (o, l) → alloc ctx n = some c →
        M' (c, ctx) = Part.some o := by
  refine ⟨ ?_, ⟨ ?_, ?_ ⟩, ?_ ⟩;
  · refine fun p =>
      ( Nat.rfind fun n => Part.some
        ( decide ( alloc p.2 n = some p.1 ∧ ( req p.2 n ).isSome = true ) ) ) >>=
        fun n => Part.ofOption ( ( req p.2 n ).map Prod.fst );
  · refine Partrec.bind ?_ ?_;
    · convert Partrec.rfind _;
      convert construct_pred_computable req alloc hreqcomp hcomp |> Computable.partrec using 1;
    · convert construct_out_partrec req hreqcomp using 1;
  · intro ctx p hp q hq hpre;
    simp_all only [Bool.and_eq_true, Bool.decide_and, Bool.decide_eq_true, Bool.true_eq,
      Nat.rfind_dom, Option.isSome_map, Part.bind_dom, Part.bind_eq_bind,
      Part.mem_some_iff, Part.ofOption_dom, Part.some_dom, Set.mem_setOf_eq, and_true,
      decide_eq_true_eq, domainAt, implies_true, ne_eq]
    obtain ⟨n, hn₁, _⟩ := hp.1
    obtain ⟨m, hm₁, _⟩ := hq.1
    by_cases hnm : n = m
    · cases hnm; rw [hn₁] at hm₁; cases hm₁; rfl
    · exact (hprefix ctx n m p q hn₁ hm₁ hnm hpre).elim
  · intro ctx n o l c hreq halloc'
    have hn : n ∈ Nat.rfind
        (fun n => Part.some (decide (alloc ctx n = some c ∧ (req ctx n).isSome = true))) := by
      rw [Nat.mem_rfind];
      refine ⟨?_, fun {m} hm => ?_⟩;
      · simp only [Part.mem_some_iff, eq_comm (a := true), decide_eq_true_eq];
        exact ⟨halloc', by rw [hreq]; rfl⟩;
      · simp only [Part.mem_some_iff, eq_comm (a := false), decide_eq_false_iff_not, not_and];
        intro hm_alloc;
        exact absurd (List.prefix_refl c)
          (hprefix ctx n m c c halloc' hm_alloc (Nat.ne_of_lt hm).symm);
    rw [ show Nat.rfind ( fun n => Part.some
      ( decide ( alloc ctx n = some c ∧ ( req ctx n ).isSome = true ) ) ) =
        Part.some n from ?_ ];
    · aesop;
    · convert Part.eq_some_iff.mpr hn using 1

/-! ### Geometric (threshold-crossing) dyadic request extraction

The geometric request stream emits, for each output `o` and dyadic length `l ≥ 1`,
exactly one request `(o, l)` precisely when the lower-semicomputable approximation
of `f o ctx` first crosses the threshold `2^{-(l-1)}` at some stage `s`. The
per-output requested lengths therefore form an upward-closed set `{ l ≥ L }`, whose
Kraft tail `∑_{l ≥ L} 2^{-l} = 2 · 2^{-L}` is bounded by `f o ctx`, while the
largest single weight `2^{-L}` geometrically dominates `f o ctx` (within `2^2`).
This is the decomposition consumed by `realization_bound_of_machine`. -/

/-- The threshold-crossing predicate: the stage-`s` dyadic value of `approx · o ctx`
has reached `2^{-(l-1)}`, i.e. `2^s ≤ approx s o ctx · 2^(l-1)` (and `l ≥ 1`). -/
def geomCross (approx : ℕ → BitString → BitString → ℕ) (o ctx : BitString)
    (l s : ℕ) : Prop :=
  1 ≤ l ∧ 2 ^ s ≤ approx s o ctx * 2 ^ (l - 1)

instance (approx : ℕ → BitString → BitString → ℕ) (o ctx : BitString) (l s : ℕ) :
    Decidable (geomCross approx o ctx l s) := by
  unfold geomCross; infer_instance

/-- The geometric request stream. Decode `n` into `(o, l, s)` via two `Nat.unpair`s
(and `evOut` for the output), and emit `(o, l)` exactly at the first stage `s` at
which `geomCross` becomes true for `(o, l)`. -/
lemma decide_or_not_eq {a b : Prop} [Decidable a] [Decidable b] :
    decide (a ∨ ¬b) = cond (decide a) true (cond (decide b) false true) := by
  by_cases ha : a <;> by_cases hb : b <;> simp_all

lemma decide_and_eq {a b : Prop} [Decidable a] [Decidable b] :
    decide (a ∧ b) = cond (decide a) (decide b) false := by
  by_cases ha : a <;> by_cases hb : b <;> simp_all

lemma ite_eq_some {P : Prop} [Decidable P] {α : Type _} {x : α} :
    (if P then some x else none) = cond (decide P) (some x) none := by
  by_cases hP : P <;> simp_all

def geomReqBody (approx : ℕ → BitString → BitString → ℕ)
    (p : (BitString × ℕ) × BitString) : Option (BitString × ℕ) :=
  if geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1) ∧
      ((evK (Nat.unpair p.1.2).1) = 0 ∨
        ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
          ((evK (Nat.unpair p.1.2).1) - 1)) then
    some (p.2, ((Nat.unpair p.1.2).2))
  else none

lemma geomReqBody_eq (approx : ℕ → BitString → BitString → ℕ)
    (p : (BitString × ℕ) × BitString) :
  geomReqBody approx p =
    if geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1) ∧
        ((evK (Nat.unpair p.1.2).1) = 0 ∨
          ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
            ((evK (Nat.unpair p.1.2).1) - 1)) then
      some (p.2, ((Nat.unpair p.1.2).2))
    else none := rfl

def geomReq (approx : ℕ → BitString → BitString → ℕ) (ctx : BitString) (n : ℕ) :
    Option (BitString × ℕ) :=
  (evOut (Nat.unpair n).1).bind fun o => geomReqBody approx ((ctx, n), o)

/-
Computability of the `geomCross` decision in `(l, s, o, ctx)`.
-/
lemma geomCross_decide_computable (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun q : ℕ × ℕ × BitString × BitString =>
      decide (geomCross approx q.2.2.1 q.2.2.2 q.1 q.2.1)) := by
  have hdec : Computable
      (fun q : ℕ × ℕ × BitString × BitString =>
        decide (2 ^ q.2.1 ≤ approx q.2.1 q.2.2.1 q.2.2.2 * 2 ^ (q.1 - 1))) := by
    have hdec : Computable
        (fun q : ℕ × ℕ × BitString × BitString =>
          approx q.2.1 q.2.2.1 q.2.2.2 * 2 ^ (q.1 - 1)) := by
      apply Computable.comp (Primrec.nat_mul.to_comp) (Computable.pair _ _);
      · convert hcomp.comp ( Computable.snd ) using 1;
      · convert primrec_two_pow_aux.to_comp.comp
          ( Primrec.nat_sub.comp ( Primrec.fst ) ( Primrec.const 1 ) |>
            Primrec.to_comp ) using 1;
    have hdec : Primrec (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
      convert Primrec.nat_le using 1;
      constructor <;> intro h <;> simp_all only [PrimrecPred, PrimrecRel];
      · exact ⟨ inferInstance, h ⟩;
      · exact PrimrecRel.decide Primrec.nat_le
    convert hdec.to_comp.comp ( Computable.pair
      ( primrec_two_pow_aux.to_comp.comp ( Computable.fst.comp ( Computable.snd ) ) )
      ‹Computable fun q : ℕ × ℕ × BitString × BitString =>
        approx q.2.1 q.2.2.1 q.2.2.2 * 2 ^ ( q.1 - 1 )› ) using 1;
  have hdec : Computable (fun q : ℕ × ℕ × BitString × BitString => decide (1 ≤ q.1)) := by
    have hdec : Computable (fun q : ℕ => decide (1 ≤ q)) := by
      convert Computable.of_eq _ _;
      · exact fun n => Nat.recOn n Bool.false fun _ _ => Bool.true;
      · exact Computable.nat_casesOn ( Computable.id )
          ( Computable.const false ) ( Computable.const true );
      · rintro ( _ | _ ) <;> rfl;
    exact hdec.comp ( Computable.fst );
  rename_i h;
  convert Computable.cond hdec h ( Computable.const false ) using 1;
  ext; simp [geomCross]

/-- The geometric request stream is computable (uniformly in `ctx`). -/
lemma geomReq_computable (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : BitString × ℕ => geomReq approx p.1 p.2) := by
  change Computable (fun p : BitString × ℕ =>
    (evOut (Nat.unpair p.2).1).bind fun o => geomReqBody approx (p, o))
  have hl : Computable (fun p : BitString × ℕ => (Nat.unpair p.2).2) :=
    Computable.snd.comp (Computable.unpair.comp Computable.snd)
  have hevK_primrec : Primrec evK := Primrec.snd.comp Primrec.unpair
  have hs : Computable (fun p : BitString × ℕ => evK (Nat.unpair p.2).1) :=
    hevK_primrec.to_comp.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
  have hevOut : Computable (fun p : BitString × ℕ => evOut (Nat.unpair p.2).1) :=
    evOut_computable.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
  have hcond1 : Computable (fun p : (BitString × ℕ) × BitString =>
      decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
        (evK (Nat.unpair p.1.2).1))) := by
    have h_cross := geomCross_decide_computable approx hcomp
    have h_args : Computable (fun p : (BitString × ℕ) × BitString =>
        (((Nat.unpair p.1.2).2), (evK (Nat.unpair p.1.2).1), p.2, p.1.1)) :=
      Computable.pair (hl.comp Computable.fst)
        (Computable.pair (hs.comp Computable.fst)
          (Computable.pair Computable.snd (Computable.fst.comp Computable.fst)))
    exact (h_cross.comp h_args).of_eq (fun p => by dsimp only [Prod.fst, Prod.snd])
  have h_cross_eval : Computable
      (fun p : (BitString × ℕ) × BitString =>
        decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
          (evK (Nat.unpair p.1.2).1 - 1))) := by
    have h_cross := geomCross_decide_computable approx hcomp
    have hsub : Computable
        (fun p : (BitString × ℕ) × BitString => evK (Nat.unpair p.1.2).1 - 1) := by
      have h_sub_primrec : Primrec (fun n : ℕ => n - 1) :=
        Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
      exact h_sub_primrec.to_comp.comp (hs.comp Computable.fst)
    have h_args : Computable (fun p : (BitString × ℕ) × BitString =>
        (((Nat.unpair p.1.2).2), (evK (Nat.unpair p.1.2).1 - 1), p.2, p.1.1)) :=
      Computable.pair (hl.comp Computable.fst)
        (Computable.pair hsub
          (Computable.pair Computable.snd (Computable.fst.comp Computable.fst)))
    exact (h_cross.comp h_args).of_eq (fun p => by dsimp only [Prod.fst, Prod.snd])
  have heq0 : Computable
      (fun p : (BitString × ℕ) × BitString => decide (evK (Nat.unpair p.1.2).1 = 0)) := by
    have hsucc : Computable₂ (fun (n : ℕ) (m : ℕ) => false) := Computable.const false
    have h_dec : Computable (fun n : ℕ => decide (n = 0)) :=
      Computable.of_eq
        (Computable.nat_casesOn Computable.id (Computable.const true) hsucc)
        (by intro n; cases n <;> rfl)
    exact h_dec.comp (hs.comp Computable.fst)
  have hcond2 : Computable (fun p : (BitString × ℕ) × BitString =>
      decide (evK (Nat.unpair p.1.2).1 = 0 ∨
        ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
          (evK (Nat.unpair p.1.2).1 - 1))) := by
    have h_not : Computable (fun p : (BitString × ℕ) × BitString =>
        cond (decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
          (evK (Nat.unpair p.1.2).1 - 1))) false true) :=
      Computable.cond h_cross_eval (Computable.const false) (Computable.const true)
    have h_or : Computable (fun p : (BitString × ℕ) × BitString =>
        cond (decide (evK (Nat.unpair p.1.2).1 = 0)) true
          (cond (decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
            (evK (Nat.unpair p.1.2).1 - 1))) false true)) :=
      Computable.cond heq0 (Computable.const true) h_not
    exact h_or.of_eq (fun p => decide_or_not_eq.symm)
  have hcond : Computable (fun p : (BitString × ℕ) × BitString =>
      decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1) ∧
        (evK (Nat.unpair p.1.2).1 = 0 ∨
          ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
            (evK (Nat.unpair p.1.2).1 - 1)))) := by
    have h_and : Computable (fun p : (BitString × ℕ) × BitString =>
        cond (decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
          (evK (Nat.unpair p.1.2).1)))
          (decide (evK (Nat.unpair p.1.2).1 = 0 ∨
            ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
              (evK (Nat.unpair p.1.2).1 - 1))) false) :=
      Computable.cond hcond1 hcond2 (Computable.const false)
    exact h_and.of_eq (fun p => decide_and_eq.symm)
  have hbranch : Computable
      (fun p : (BitString × ℕ) × BitString => geomReqBody approx p) := by
    have h_then : Computable
        (fun p : (BitString × ℕ) × BitString =>
          some (p.2, ((Nat.unpair p.1.2).2))) :=
      Computable.option_some.comp (Computable.pair Computable.snd (hl.comp Computable.fst))
    have h_else : Computable
        (fun p : (BitString × ℕ) × BitString => (none : Option (BitString × ℕ))) :=
      Computable.const none
    have h_ite : Computable (fun p : (BitString × ℕ) × BitString =>
        cond (decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
          (evK (Nat.unpair p.1.2).1) ∧
          (evK (Nat.unpair p.1.2).1 = 0 ∨
            ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
              (evK (Nat.unpair p.1.2).1 - 1))))
          (some (p.2, ((Nat.unpair p.1.2).2))) none) :=
      Computable.cond hcond h_then h_else
    exact h_ite.of_eq (fun p => by
      rw [geomReqBody_eq]
      exact ite_eq_some.symm)
  exact Computable.option_bind hevOut hbranch

/-
**Evaluation of `geomReq` at a canonical paired index.** Decoding
`Nat.pair (Nat.pair (Encodable.encode o) s) l` recovers output `o`, stage `s`
(`= evK`) and length `l`, so `geomReq` emits `(o, l)` here exactly when level `l`
is first crossed at stage `s`. This is the clean interface used by the Kraft and
geometric-bound proofs.
-/
lemma geomReq_pair (approx : ℕ → BitString → BitString → ℕ) (ctx o : BitString)
    (s l : ℕ) :
    geomReq approx ctx (Nat.pair (Nat.pair (Encodable.encode o) s) l) =
      if geomCross approx o ctx l s ∧ (s = 0 ∨ ¬ geomCross approx o ctx l (s - 1)) then
        some (o, l) else none := by
  unfold geomReq; simp only [Encodable.decode₂_encode, Nat.unpair_pair, Option.bind_some, evOut] ;
  convert geomReqBody_eq approx _ using 1;
  unfold evK; simp only [Nat.unpair_pair] ;

open Classical in
/-- **Per-output Kraft tail bound.** For a fixed output `o`, the crossed levels
`{ l ≥ 1 : ∃ s, geomCross approx o ctx l s }` form an upward-closed set `{ l ≥ L }`,
whose geometric Kraft tail `∑_{l ≥ L} 2⁻¹^l = 2⁻¹^(L-1)` is bounded by the limit
mass `f o ctx` (because the least crossed level `L` already has
`2⁻¹^(L-1) ≤ dyadicValue ... ≤ f o ctx`). -/
lemma geomReq_crossed_kraft_perOutput {f : BitString → BitString → ℝ≥0∞}
    {approx : ℕ → BitString → BitString → ℕ}
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx)
    (o ctx : BitString) :
    (∑' l : ℕ, if 1 ≤ l ∧ (∃ s, geomCross approx o ctx l s) then (2 : ℝ≥0∞)⁻¹ ^ l else 0)
      ≤ f o ctx := by
  by_cases h : ∃ l, 1 ≤ l ∧ ∃ s, 2 ^ s ≤ approx s o ctx * 2 ^ ( l - 1 );
  · obtain ⟨L, hL⟩ : ∃ L, 1 ≤ L ∧ ∃ s, 2 ^ s ≤ approx s o ctx * 2 ^ (L - 1) ∧ ∀ l < L,
      ¬(1 ≤ l ∧ ∃ s, 2 ^ s ≤ approx s o ctx * 2 ^ (l - 1)) := by
      exact ⟨ Nat.find h, Nat.find_spec h |>.1, Nat.find_spec h |>.2.choose,
        Nat.find_spec h |>.2.choose_spec,
        fun l hl hl' => Nat.find_min h hl hl' ⟩;
    have h_sum : (∑' l : ℕ, if L ≤ l then (2 : ℝ≥0∞)⁻¹ ^ l else 0) ≤ f o ctx := by
      have h_sum : (∑' l : ℕ, if L ≤ l then (2 : ℝ≥0∞)⁻¹ ^ l else 0) = (2 : ℝ≥0∞)⁻¹ ^ (L - 1) := by
        have h_sum : (∑' l : ℕ, if L ≤ l then (2 : ℝ≥0∞)⁻¹ ^ l else 0) =
            (∑' l : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (L + l)) := by
          rw [ ← tsum_eq_tsum_of_ne_zero_bij ];
          · use fun x => x.val - L;
          · -- Adding `L` to `x.val - L = y.val - L` gives `x.val = y.val`.
            intro x y hxy
            have h_eq : x.val = y.val := by
              linarith [ Nat.sub_add_cancel
                  ( show L ≤ x.val from by by_contra hc; exact x.2 (if_neg hc) ),
                Nat.sub_add_cancel
                  ( show L ≤ y.val from by by_contra hc; exact y.2 (if_neg hc) ) ]
            exact Subtype.ext h_eq;
          · exact fun x _ => ⟨⟨x + L, by simp⟩, by simp⟩
          · rintro ⟨x, hx⟩
            have hle : L ≤ x := by by_contra hc; exact hx (if_neg hc)
            rw [Nat.add_sub_cancel' hle, if_pos hle]
        simp_all +decide only [not_and, not_exists, not_le, exists_and_right,
          pow_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ENNReal.one_sub_inv_two, inv_inv]
        rcases L with ( _ | L )
        · simp_all +decide only [zero_tsub, pow_zero, mul_one, not_lt_zero,
            not_isEmpty_of_nonempty, IsEmpty.forall_iff, implies_true, and_true, false_and]
        · simp_all +decide only [le_add_iff_nonneg_left, zero_le,
            add_tsub_cancel_right, Order.lt_add_one_iff, true_and,
            Order.add_one_le_iff, pow_succ, mul_assoc]
          rw [ ENNReal.inv_mul_cancel ] <;> norm_num
      obtain ⟨ s, hs₁, hs₂ ⟩ := hL.2;
      have h_le : (2 : ℝ≥0∞)⁻¹ ^ (L - 1) ≤ dyadicValue (approx s o ctx) s := by
        unfold dyadicValue; norm_num [ ENNReal.div_eq_inv_mul ] ;
        rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
        · field_simp;
          rw [ div_pow, div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast <;> norm_num;
          exact_mod_cast hs₁;
        · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
      exact h_sum.symm ▸ h_le.trans
        ( hsup o ctx ▸ le_iSup ( fun s => dyadicValue ( approx s o ctx ) s ) s );
    convert h_sum using 3;
    split_ifs <;>
      simp_all +decide only [not_and, not_exists, not_le, exists_and_right,
        geomCross, exists_and_left, and_self_left, pow_eq_zero_iff', ENNReal.inv_eq_zero,
        ne_eq, false_and]
    · rename_i k hk₁ hk₂
      obtain ⟨x, hx⟩ := hk₁.2
      have contra := hL.2.2 k hk₂ hk₁.1 x
      exact (Nat.not_lt_of_ge hx contra).elim
    · rename_i k hk₁ hk₂;
      contrapose! hk₁;
      exact ⟨ by linarith, by
        obtain ⟨ x, hx ⟩ := hL.2.1
        exact ⟨ x, by
          exact le_trans hx ( Nat.mul_le_mul_left _
            ( pow_le_pow_right₀ ( by decide ) ( Nat.sub_le_sub_right hk₂ 1 ) ) ) ⟩ ⟩;
  · simp_all +decide only [not_exists, not_and, not_le, geomCross,
      exists_and_left, and_self_left]
    rw [ tsum_eq_single 0 ]
    · simp_all +decide only [zero_tsub, pow_zero, mul_one, false_and, ↓reduceIte,
        zero_le]
    · simp_all +decide only [ne_eq, ite_eq_right_iff, not_false_eq_true,
        pow_eq_zero_iff, ENNReal.inv_eq_zero, imp_false, not_and, not_exists, not_le,
        implies_true]

open Classical in
/-- Under stagewise monotonicity, the threshold-crossing predicate is monotone in
the stage: once level `l` is crossed it stays crossed. -/
lemma geomCross_succ_of_geomCross {approx : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (o ctx : BitString) (l s : ℕ) (h : geomCross approx o ctx l s) :
    geomCross approx o ctx l (s + 1) := by
  cases l <;> simp_all only [dyadicValue, pow_succ];
  · exact absurd h.1 ( by norm_num );
  · convert hmono s o ctx |> le_trans _ using 1;
    rotate_left;
    · exact 1 / 2 ^ ‹_›;
    · convert ENNReal.div_le_div
        ( show ( 2 ^ s : ENNReal ) ≤ approx s o ctx * 2 ^ ‹_› from ?_ ) le_rfl using 1;
      any_goals exact 2 ^ s * 2 ^ ‹_›;
      · rw [ ENNReal.div_eq_div_iff ] <;> ring_nf <;> norm_num;
        exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
      · rw [ ENNReal.mul_div_mul_right ];
        · norm_num
        · exact ENNReal.pow_ne_top ( by norm_num );
      · exact_mod_cast h.2;
    · rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
      · field_simp;
        norm_cast ; simp_all only [mul_comm];
        unfold geomCross
        simp only [add_tsub_cancel_right, le_add_iff_nonneg_left, pow_succ', true_and,
          zero_le]
      · norm_num [ ENNReal.div_eq_top ]

open Classical in
/-- **Reindexing the geometric Kraft sum by output.** Every index `n` emitting a
request `(o, l)` corresponds (injectively) to a crossed level `l ≥ 1` of output `o`
(the unique first-crossing stage), so the total Kraft weight is bounded by the
double sum over outputs and their crossed levels. -/
lemma geomReq_kraft_le_perOutput_sum {approx : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (ctx : BitString) :
    (∑' n, match geomReq approx ctx n with
      | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0)
      ≤ ∑' o : BitString, ∑' l : ℕ,
          (if 1 ≤ l ∧ (∃ s, geomCross approx o ctx l s) then (2 : ℝ≥0∞)⁻¹ ^ l else 0) := by
  have h_reindex :
      (∑' n : ℕ, (match geomReq approx ctx n with | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0)) =
      (∑' a : ℕ, ∑' s : ℕ, ∑' l : ℕ,
        (match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with
          | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l'
          | none => 0)) := by
    have h_reindex : ∀ (f : ℕ → ℝ≥0∞), (∑' n : ℕ, f n) =
        (∑' a : ℕ, ∑' s : ℕ, ∑' l : ℕ, f (Nat.pair (Nat.pair a s) l)) := by
      intro f;
      rw [ ← ENNReal.tsum_prod, ← ENNReal.tsum_prod ];
      rw [ ← Equiv.tsum_eq ( Equiv.ofBijective
        ( fun p : ( ℕ × ℕ ) × ℕ => Nat.pair ( Nat.pair p.1.1 p.1.2 ) p.2 )
        ⟨ fun p => ?_, fun p => ?_ ⟩ ) ];
      · congr! 1;
      · simp only [Nat.pair_eq_pair, Prod.forall, Prod.mk.eta, and_imp,
          forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂, forall_eq']
      · exact ⟨ ⟨ ⟨ Nat.unpair p |>.1 |> Nat.unpair |>.1,
            Nat.unpair p |>.1 |> Nat.unpair |>.2 ⟩,
          Nat.unpair p |>.2 ⟩, by simp only [Nat.pair_unpair] ⟩;
    exact h_reindex _;
  -- By `tsum_eq_tsum_of_ne_zero_bij`, we can restrict the sum over `a` to outputs.
  have h_restrict :
      (∑' a : ℕ, (∑' s : ℕ, (∑' l : ℕ,
        (match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with
          | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l'
          | none => 0)))) ≤
      (∑' o : BitString, (∑' s : ℕ, (∑' l : ℕ,
        (match geomReq approx ctx (Nat.pair (Nat.pair (Encodable.encode o) s) l) with
          | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l'
          | none => 0)))) := by
    have h_restrict :
        (∑' a : ℕ, (∑' s : ℕ, (∑' l : ℕ,
          (match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with
            | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l'
            | none => 0)))) =
        (∑' a : ℕ, if a ∈ Set.range (Encodable.encode : BitString → ℕ) then
          (∑' s : ℕ, (∑' l : ℕ,
            (match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with
              | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l'
              | none => 0))) else 0) := by
      congr;
      ext a
      split_ifs <;>
        simp_all only [ENNReal.tsum_eq_zero, Nat.unpair_pair, Set.mem_range, geomReq,
          not_exists]
      unfold evOut
      simp only [*, Encodable.decode₂, Nat.unpair_pair, Option.bind_fun_none,
        Option.bind_none, Option.guard_false, decide_false, implies_true]
    convert h_restrict.le using 1;
    erw [ ← tsum_subtype ];
    erw [ ← Equiv.tsum_eq ( Equiv.ofInjective _ <| Encodable.encode_injective ) ] ; aesop;
  refine le_trans h_reindex.le <| h_restrict.trans ?_;
  refine ENNReal.tsum_le_tsum fun o => ?_;
  rw [ ENNReal.tsum_comm ];
  refine ENNReal.tsum_le_tsum fun l => ?_;
  split_ifs with h;
  · obtain ⟨ s₀, hs₀ ⟩ := Nat.findX h.2;
    rw [ tsum_eq_single s₀ ];
    · rw [geomReq_pair]; split_ifs <;> simp;
    · intro b' hb'
      by_cases hb'_lt : b' < s₀;
      · rw [ geomReq_pair ] ; simp only [false_and, hs₀.2 b' hb'_lt, ↓reduceIte];
      · rw [ geomReq_pair ];
        split_ifs <;> norm_num;
        rename_i h;
        exact h.2.elim
          ( fun h => by
            linarith [ Nat.pos_of_ne_zero ( show s₀ ≠ 0 from by
              rintro rfl
              exact hs₀.2 0 ( Nat.pos_of_ne_zero ( by aesop ) ) hs₀.1 ) ] )
          fun h => h ( by
            exact Nat.le_induction ( by tauto )
              ( fun k hk ih => by exact geomCross_succ_of_geomCross hmono o ctx l k ih ) _
              ( show b' - 1 ≥ s₀ from Nat.le_sub_one_of_lt
                ( lt_of_le_of_ne ( le_of_not_gt hb'_lt ) ( Ne.symm hb' ) ) ) );
  · convert tsum_nonpos _;
    · infer_instance;
    · infer_instance;
    · intro s; rw [ geomReq_pair ] ;
      split_ifs <;> norm_num;
      exact h ⟨ by unfold geomCross at *; aesop, s, by tauto ⟩

open Classical in
/-- **Kraft bound for the geometric request stream.** Because each output's emitted
lengths form an upward-closed set `{ l ≥ L }` with `2 · 2^{-L} ≤ f o ctx`, the total
Kraft weight is bounded by `∑_o f o ctx ≤ 1`. -/
lemma geomReq_kraft_le_one {f : BitString → BitString → ℝ≥0∞}
    {approx : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1)
    (ctx : BitString) :
    (∑' n, match geomReq approx ctx n with
      | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0) ≤ 1 := by
  calc (∑' n, match geomReq approx ctx n with
          | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0)
      ≤ ∑' o : BitString, ∑' l : ℕ,
          (if 1 ≤ l ∧ (∃ s, geomCross approx o ctx l s) then (2 : ℝ≥0∞)⁻¹ ^ l else 0) :=
        geomReq_kraft_le_perOutput_sum hmono ctx
    _ ≤ ∑' o : BitString, f o ctx :=
        ENNReal.tsum_le_tsum (fun o => geomReq_crossed_kraft_perOutput hsup o ctx)
    _ ≤ 1 := h_sum ctx

/-
**Geometric domination for the geometric request stream.** Each output's mass
`f out ctx` is within a factor `2^2` of its largest single emitted request weight.

The mass bound `h_sum` (hence `f out ctx ≤ 1`) is genuinely needed: the smallest
emitted length is `1` (weight `2⁻¹`), so an output with `f out ctx ≥ 2` would
violate the `2^2`-domination. With `f out ctx ≤ 1` the largest crossed level `L`
satisfies `2⁻¹^L ≤ f out ctx < 2^2 · 2⁻¹^L`.
-/
lemma geomReq_geometric_bound {f : BitString → BitString → ℝ≥0∞}
    {approx : ℕ → BitString → BitString → ℕ}
    (_hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1)
    (ctx out : BitString) :
    f out ctx ≤ (2 : ℝ≥0∞) ^ 2 *
      (⨆ n, match geomReq approx ctx n with
        | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0) := by
  by_contra h_contra;
  obtain ⟨l, hl⟩ : ∃ l : ℕ, 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s ∧ ∀ l' : ℕ, l' < l → ¬∃ s'
      : ℕ, geomCross approx out ctx l' s' := by
    have hL : ∃ l : ℕ, 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s := by
      -- Since $f(out, ctx) > 0$, there exists some $s$ such that $dyadicValue (approx s out ctx) s
      --   > 0$.
      obtain ⟨s, hs⟩ : ∃ s : ℕ, dyadicValue (approx s out ctx) s > 0 := by
        have h_pos : f out ctx > 0 := by
          exact lt_of_not_ge fun h => h_contra <| le_trans h <| by positivity;
        exact not_forall_not.mp fun h => h_pos.ne' <| hsup out ctx ▸ by
          simp +decide [ show ∀ s : ℕ, dyadicValue ( approx s out ctx ) s = 0 from
            fun s => le_antisymm ( le_of_not_gt fun hs => h s hs ) ( zero_le _ ) ]
      refine ⟨ s + 1, ?_, s, ?_, ?_ ⟩ <;> norm_num [ geomCross ] at *;
      exact Nat.pos_of_ne_zero fun h => hs.ne' <| by unfold dyadicValue; simp +decide [ h ] ;
    obtain ⟨l, hl⟩ : ∃ l : ℕ, 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s ∧ ∀ l' : ℕ, l' < l → ¬∃
        s' : ℕ, geomCross approx out ctx l' s' := by
      have h_well_founded : WellFounded (fun l l' : ℕ => l < l') := by
        exact wellFounded_lt
      obtain ⟨l, hl⟩ : ∃ l : ℕ, l ∈ {l : ℕ | 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s} ∧ ∀ l' :
          ℕ, l' ∈ {l : ℕ | 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s} → ¬l' < l := by
        have := h_well_founded.has_min
          { l | 1 ≤ l ∧ ∃ s, geomCross approx out ctx l s } ⟨ _, hL.choose_spec ⟩
        tauto
      exact ⟨ l, hl.1.1, hl.1.2.choose, hl.1.2.choose_spec,
        fun l' hl' hl'' => hl.2 l'
          ⟨ Nat.pos_of_ne_zero fun h => by
              subst h
              exact absurd hl'' ( by
                rintro ⟨ s', hs' ⟩
                exact absurd hs'.1 ( by norm_num ) ), hl'' ⟩ hl' ⟩;
    use l;
  obtain ⟨s, hs⟩ := hl.right
  have h_emitted :
      ⨆ n, (match geomReq approx ctx n with
        | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0
        | none => 0) ≥ (2 : ℝ≥0∞)⁻¹ ^ l := by
    obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℕ, geomCross approx out ctx l s₀ ∧ ∀ s' : ℕ, s' < s₀ → ¬geomCross
        approx out ctx l s' := by
      exact ⟨ Nat.find ( ⟨ s, hs.1 ⟩ : ∃ s, geomCross approx out ctx l s ),
        Nat.find_spec ( ⟨ s, hs.1 ⟩ : ∃ s, geomCross approx out ctx l s ),
        fun s' hs' =>
          Nat.find_min ( ⟨ s, hs.1 ⟩ : ∃ s, geomCross approx out ctx l s ) hs' ⟩;
    refine le_trans ?_
      ( le_ciSup ?_ ( Nat.pair ( Nat.pair ( Encodable.encode out ) s₀ ) l ) )
    · simp +decide only [geomReq_pair, hs₀, true_and]
      rcases s₀ with ( _ | s₀ ) <;> simp +decide [ hs₀ ] at hs₀ ⊢;
    · refine ⟨ 1, Set.forall_mem_range.2 fun n => ?_ ⟩
      rcases geomReq approx ctx n with ( _ | ⟨ o, l ⟩ ) <;> norm_num;
      split_ifs <;> norm_num;
      exact pow_le_one₀ ( by norm_num ) ( by norm_num );
  -- Since $l$ is the smallest level where the cross condition holds, for any $s$, we have
  --   $dyadicValue (approx s out ctx) s < 2⁻¹^(l-2)$.
  have h_dyadic_lt : ∀ s, dyadicValue (approx s out ctx) s < (2 : ℝ≥0∞)⁻¹ ^ (l - 2) := by
    intro s
    by_cases hl_ge_2 : 2 ≤ l;
    · have h_dyadic_lt : ¬geomCross approx out ctx (l - 1) s := by
        exact fun h => hs.2 ( l - 1 ) ( Nat.sub_lt ( by linarith ) zero_lt_one ) ⟨ s, h ⟩;
      unfold geomCross at h_dyadic_lt; norm_num at h_dyadic_lt;
      unfold dyadicValue; norm_num [ ENNReal.div_lt_iff ] ;
      rw [ ← ENNReal.toReal_lt_toReal ] <;> norm_num;
      · rw [ div_pow, div_mul_eq_mul_div, lt_div_iff₀ ] <;> norm_cast;
        · norm_num
          exact h_dyadic_lt ( Nat.le_sub_one_of_lt hl_ge_2 );
        · positivity;
      · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
    · interval_cases l ; norm_num at *;
      contrapose! h_contra;
      refine le_trans ?_ ( mul_le_mul_right h_emitted _ );
      refine le_trans ( h_sum ctx |> le_trans ( ENNReal.le_tsum out ) ) ?_ ; norm_num;
      rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
      norm_num [ ENNReal.mul_eq_top ];
  -- Therefore, $f out ctx \leq 2⁻¹^(l-2)$.
  have h_f_le : f out ctx ≤ (2 : ℝ≥0∞)⁻¹ ^ (l - 2) := by
    exact hsup out ctx ▸ iSup_le fun s => le_of_lt ( h_dyadic_lt s );
  refine h_contra <| h_f_le.trans ?_;
  refine le_trans ?_ ( mul_le_mul_right h_emitted _ );
  rcases l with ( _ | _ | l ) <;> norm_num [ pow_succ' ] at *;
  · rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
    norm_num [ ENNReal.mul_eq_top ];
  · ring_nf;
    norm_num [ mul_assoc, mul_comm, mul_left_comm ];
    rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
    norm_num [ ENNReal.mul_eq_top ]

/-- **Geometric dyadic request extraction.** A unit-mass lower-semicomputable `f`
admits a computable request stream of total Kraft weight `≤ 1` together with a
constant `K` such that, for every output `out`, the total mass `f out ctx` is
within a factor `2^K` of the *largest single* request weight for `out`
(`⨆ n, …`). This is the threshold-crossing decomposition (one request per dyadic
level crossed, so the per-output requested lengths are strictly decreasing and the
shortest dominates the geometric tail). Unlike the unit-increment
`extract_request_stream` (which realizes `f` exactly but may split one output's
mass into arbitrarily many equal-length requests), this geometric form is exactly
what `realization_bound_of_machine` needs: `2^{-KP}` only sees the largest single
request, so the realization bound is provable iff `f out` is geometrically
dominated by that largest request. -/
lemma extract_request_stream_geometric {f : BitString → BitString → ℝ≥0∞}
    (hlsc : IsLSC f)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1) :
    ∃ (req : BitString → ℕ → Option (BitString × ℕ)) (K : ℕ),
      Computable (fun p : BitString × ℕ => req p.1 p.2) ∧
      (∀ ctx : BitString,
        (∑' n, match req ctx n with
          | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l
          | none => 0) ≤ 1) ∧
      (∀ ctx out : BitString, f out ctx ≤ (2 : ℝ≥0∞) ^ K *
        (⨆ n, match req ctx n with
          | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0
          | none => 0)) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hlsc
  exact ⟨geomReq approx, 2, geomReq_computable approx hcomp,
    geomReq_kraft_le_one hmono hsup h_sum,
    geomReq_geometric_bound hmono hsup h_sum⟩

/-- **Realization bound from a matched allocator (geometric form).** If a request
stream is realized by a prefix machine `M'` (each requested `(out, l)` gets an
allocated code of length `l` that `M'` maps back to `out`), and each output's mass
`f out` is within a factor `2^K` of its *largest single* request weight, then `M'`
achieves the multiplicative coding bound `2^{-K} · f(out|ctx) ≤ 2^{-KP_{M'}(out|ctx)}`.

An exact identity `∑ requests = f` alone would be insufficient: with many
equal-length requests, `f out` can be arbitrarily larger than the single largest
request weight `= 2^{-KP}`. -/
lemma realization_bound_of_machine (f : BitString → BitString → ℝ≥0∞)
    (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (M' : Map) (K : ℕ)
    (hmatch : ∀ ctx n o l, req ctx n = some (o, l) → ∃ c, alloc ctx n = some c ∧ c.length = l)
    (hmachine : ∀ ctx n o l c, req ctx n = some (o, l) → alloc ctx n = some c →
      M' (c, ctx) = Part.some o)
    (hgeo : ∀ ctx out : BitString, f out ctx ≤ (2 : ℝ≥0∞) ^ K *
      (⨆ n, match req ctx n with
        | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0
        | none => 0)) :
    ∃ c₀ : ℕ, ∀ out ctx : BitString, (2 : ℝ≥0∞)⁻¹ ^ c₀ * f out ctx ≤ complexityWeight
        (KP M' out ctx) := by
  -- The supremum of the per-request weights for `out` is `≤ 2^{-KP M' out ctx}`,
  -- since every realized request gives a code of its length producing `out`.
  have hS : ∀ ctx out : BitString,
      (⨆ n, match req ctx n with
        | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0)
        ≤ complexityWeight (KP M' out ctx) := by
    intro ctx out
    apply iSup_le
    intro n
    rcases h : req ctx n with _ | ⟨o, l⟩
    · simp
    · by_cases ho : o = out
      · subst ho
        obtain ⟨c, hc₁, hc₂⟩ := hmatch ctx n o l h
        have hprod : produces M' c ctx o := by
          have := hmachine ctx n o l c h hc₁
          simp [produces, this]
        have hKP : KP M' o ctx ≤ (programLength c : ENat) :=
          KP_le_programLength_of_produces hprod
        simpa [complexityWeight_programLength, progWeight, programLength, hc₂]
          using complexityWeight_le_of_le hKP
      · simp [ho]
  refine ⟨K, fun out ctx => ?_⟩
  calc (2 : ℝ≥0∞)⁻¹ ^ K * f out ctx
      ≤ (2 : ℝ≥0∞)⁻¹ ^ K * ((2 : ℝ≥0∞) ^ K *
          (⨆ n, match req ctx n with
            | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0)) := by
        gcongr
        exact hgeo ctx out
    _ = (⨆ n, match req ctx n with
            | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0) := by
        rw [← mul_assoc, ← mul_pow,
          ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]
    _ ≤ complexityWeight (KP M' out ctx) := hS ctx out

/-- **The abstract Kraft–Chaitin realization engine, unit-mass interface.**

This is the genuinely hard online prefix-free allocator, stated at the *unit mass*
level: a lower-semicomputable `f` whose per-context total mass is `≤ 1` is realized
by a genuine prefix decompressor up to an additive coding constant.

The general `2^d`-mass theorem below reduces to this unit-mass interface through
`IsLSC.div_two_pow` and the corresponding `ℝ≥0∞` exponent algebra. The online
leftmost-free construction is supplied above by `exists_online_prefixFree_family`. -/
theorem kraftChaitin_realization_bound_unit {f : BitString → BitString → ℝ≥0∞}
    (hlsc : IsLSC f)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1) :
    ∃ M' : Map, IsPrefixDecompressor M' ∧ ∃ c₀ : ℕ, ∀ out ctx : BitString,
      (2 : ℝ≥0∞)⁻¹ ^ c₀ * f out ctx ≤ complexityWeight (KP M' out ctx) := by
  -- The genuinely hard online allocator (leftmost-free-dyadic-interval) at mass ≤ 1:
  -- 1. Extract the dyadic increments from `hlsc` as a computable request stream.
  obtain ⟨req, K, hreq_comp, hreq_wt, hgeo⟩ := extract_request_stream_geometric hlsc h_sum
  -- 2 & 3. Allocate prefix-free programs of the requested lengths online.
  obtain ⟨alloc, halloc_comp, halloc_match, halloc_pref⟩ :=
    exists_online_prefixFree_family req hreq_comp hreq_wt
  -- 4. Construct `M'` via `Partrec` combinators from the resulting computable allocator.
  obtain ⟨M', hM', hM_match⟩ :=
    construct_prefix_machine req alloc hreq_comp halloc_comp halloc_match halloc_pref
  obtain ⟨c₀, hc₀⟩ := realization_bound_of_machine f req alloc M' K halloc_match hM_match hgeo
  exact ⟨M', hM', c₀, hc₀⟩

theorem kraftChaitin_realization_bound {f : BitString → BitString → ℝ≥0∞}
    (hlsc : IsLSC f) (d : ℕ)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ (2 : ℝ≥0∞) ^ d) :
    ∃ M' : Map, IsPrefixDecompressor M' ∧ ∃ c₀ : ℕ, ∀ out ctx : BitString,
      (2 : ℝ≥0∞)⁻¹ ^ c₀ * f out ctx ≤ complexityWeight (KP M' out ctx) := by
  -- Reduce the `2^d`-mass case to the unit-mass interface by dividing `f` by `2^d`.
  have hg_lsc : IsLSC (fun out ctx => f out ctx / (2 : ℝ≥0∞) ^ d) := hlsc.div_two_pow d
  have hg_sum : ∀ ctx : BitString,
      (∑' out : BitString, f out ctx / (2 : ℝ≥0∞) ^ d) ≤ 1 := by
    intro ctx
    simp_rw [ENNReal.div_eq_inv_mul]
    rw [ENNReal.tsum_mul_left]
    rw [ENNReal.inv_mul_le_iff (by positivity) (by simp), mul_one]
    exact h_sum ctx
  obtain ⟨M', hM', c₀, hc₀⟩ := kraftChaitin_realization_bound_unit hg_lsc hg_sum
  refine ⟨M', hM', c₀ + d, fun out ctx => ?_⟩
  have hkey := hc₀ out ctx
  have hrw : (2 : ℝ≥0∞)⁻¹ ^ (c₀ + d) * f out ctx
      = (2 : ℝ≥0∞)⁻¹ ^ c₀ * (f out ctx / (2 : ℝ≥0∞) ^ d) := by
    rw [pow_add, div_eq_mul_inv]
    simp only [← ENNReal.inv_pow]
    ring
  rw [hrw]
  exact hkey

end Kolmogorov
