import Mathlib
import KolmogorovMathlib.AlgorithmicProbability.LSC.Defs

namespace Kolmogorov

open scoped ENNReal
open Computability

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

open Classical

/-- Numerator of the `k`-th dyadic increment of `approx · out ctx` (over `2^k`):
`approx 0` for `k = 0`, and `approx (k+1) - 2·approx k` for the step `k+1`. Under
monotonicity of `approx`, its dyadic value is the genuine increment. -/
def incNum (approx : ℕ → BitString → BitString → ℕ) : ℕ → BitString → BitString → ℕ
  | 0, out, ctx => approx 0 out ctx
  | (k + 1), out, ctx => approx (k + 1) out ctx - 2 * approx k out ctx

/-- The stage component of event `t`. Always `≤ t` since `Nat.unpair` shrinks. -/
@[irreducible] def evK (t : ℕ) : ℕ := (Nat.unpair t).2

/-- The output decoded from event `t` (using `decode₂`, the proper partial
inverse of `Encodable.encode`), or `none` when `(Nat.unpair t).1` is not a code. -/
@[irreducible] def evOut (t : ℕ) : Option BitString := Encodable.decode₂ BitString (Nat.unpair t).1

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

/-- Internal helper for `cumNum`. -/
def cumNumTerm (approx : ℕ → BitString → BitString → ℕ)
    (p : ℕ × ℕ × BitString) (i : ℕ) : ℕ :=
  evNum approx i p.2.2 * 2 ^ (p.1 - evK i)

/-- Internal helper for `truncGTerm`. -/
def truncGTerm (approx : ℕ → BitString → BitString → ℕ) (d : ℕ)
    (q : (ℕ × BitString × BitString) × ℕ) : ℕ :=
  if cumNum approx q.1.1 (q.2 + 1) q.1.2.2 ≤ 2 ^ (d + q.1.1) ∧
      evOut q.2 = some q.1.2.1 then
    evNum approx q.2 q.1.2.2 * 2 ^ (q.1.1 - evK q.2)
  else 0

/-- Internal helper for `cumNumTermUniform`. -/
def cumNumTermUniform (b : ℕ → ℕ → BitString → BitString → ℕ)
    (p : ℕ × ℕ × ℕ × BitString) (i : ℕ) : ℕ :=
  evNum (b p.1) i p.2.2.2 * 2 ^ (p.2.1 - evK i)

/-- Internal helper for `truncGTermUniform`. -/
def truncGTermUniform (b : ℕ → ℕ → BitString → BitString → ℕ) (d : ℕ)
    (q : (ℕ × ℕ × BitString × BitString) × ℕ) : ℕ :=
  if cumNum (b q.1.1) q.1.2.1 (q.2 + 1) q.1.2.2.2 ≤ 2 ^ (d + q.1.2.1)
      ∧ evOut q.2 = some q.1.2.2.1 then
    evNum (b q.1.1) q.2 q.1.2.2.2 * 2 ^ (q.1.2.1 - evK q.2)
  else 0

/-- Internal helper for `cumNumPacked`. -/
def cumNumPacked (approx : ℕ → BitString → BitString → ℕ)
    (p : ℕ × ℕ × BitString) : ℕ :=
  cumNum approx p.1 p.2.1 p.2.2

/-- Internal helper for `incNumUniformPacked`. -/
def incNumUniformPacked (b : ℕ → ℕ → BitString → BitString → ℕ)
    (p : ℕ × ℕ × BitString × BitString) : ℕ :=
  incNum (b p.1) p.2.1 p.2.2.1 p.2.2.2

/-- Internal helper for `evNumUniformPacked`. -/
def evNumUniformPacked (b : ℕ → ℕ → BitString → BitString → ℕ)
    (p : ℕ × ℕ × BitString) : ℕ :=
  evNum (b p.1) p.2.1 p.2.2

/-- Internal helper for `cumNumUniformPacked`. -/
def cumNumUniformPacked (b : ℕ → ℕ → BitString → BitString → ℕ)
    (p : ℕ × ℕ × ℕ × BitString) : ℕ :=
  cumNum (b p.1) p.2.1 p.2.2.1 p.2.2.2

/-- The truncated function: supremum over stages `S` of the dyadic value of the
stage-`S` accepted numerator. -/
noncomputable def truncG (approx : ℕ → BitString → BitString → ℕ) (d : ℕ)
    (out ctx : BitString) : ℝ≥0∞ :=
  ⨆ S, dyadicValue (truncGapprox approx d S out ctx) S


lemma cumNumPacked_eq (approx : ℕ → BitString → BitString → ℕ) (p : ℕ × ℕ × BitString) :
    cumNumPacked approx p = ∑ i ∈ Finset.range p.2.1, cumNumTerm approx p i := by
  unfold cumNumPacked cumNum cumNumTerm; rfl

lemma truncGTerm_eq (approx : ℕ → BitString → BitString → ℕ) (d : ℕ) (q : (ℕ × BitString × BitString) × ℕ) :
    truncGTerm approx d q = if cumNum approx q.1.1 (q.2 + 1) q.1.2.2 ≤ 2 ^ (d + q.1.1) ∧ evOut q.2 = some q.1.2.1 then evNum approx q.2 q.1.2.2 * 2 ^ (q.1.1 - evK q.2) else 0 := by
  unfold truncGTerm; rfl

lemma truncGTerm_eq_cond (approx : ℕ → BitString → BitString → ℕ) (d : ℕ) (q : (ℕ × BitString × BitString) × ℕ) :
    cond (decide (cumNum approx q.1.1 (q.2 + 1) q.1.2.2 ≤ 2 ^ (d + q.1.1) ∧ evOut q.2 = some q.1.2.1)) (evNum approx q.2 q.1.2.2 * 2 ^ (q.1.1 - evK q.2)) 0 = truncGTerm approx d q := by
  rw [truncGTerm_eq]
  exact Bool.cond_decide (cumNum approx q.1.1 (q.2 + 1) q.1.2.2 ≤ 2 ^ (d + q.1.1) ∧ evOut q.2 = some q.1.2.1) _ _

lemma truncGapprox_eq (approx : ℕ → BitString → BitString → ℕ) (d : ℕ) (p : ℕ × BitString × BitString) :
    truncGapprox approx d p.1 p.2.1 p.2.2 = ∑ t ∈ Finset.range p.1, truncGTerm approx d (p, t) := by
  unfold truncGapprox truncGTerm; rfl

lemma cumNumUniformPacked_eq (b : ℕ → ℕ → BitString → BitString → ℕ) (p : ℕ × ℕ × ℕ × BitString) :
    cumNumUniformPacked b p = ∑ i ∈ Finset.range p.2.2.1, cumNumTermUniform b p i := by
  unfold cumNumUniformPacked cumNum cumNumTermUniform; rfl

lemma truncGTermUniform_eq (b : ℕ → ℕ → BitString → BitString → ℕ) (d : ℕ) (q : (ℕ × ℕ × BitString × BitString) × ℕ) :
    truncGTermUniform b d q = if cumNum (b q.1.1) q.1.2.1 (q.2 + 1) q.1.2.2.2 ≤ 2 ^ (d + q.1.2.1) ∧ evOut q.2 = some q.1.2.2.1 then evNum (b q.1.1) q.2 q.1.2.2.2 * 2 ^ (q.1.2.1 - evK q.2) else 0 := by
  unfold truncGTermUniform; rfl

lemma truncGTermUniform_eq_cond (b : ℕ → ℕ → BitString → BitString → ℕ) (d : ℕ) (q : (ℕ × ℕ × BitString × BitString) × ℕ) :
    cond (decide (cumNum (b q.1.1) q.1.2.1 (q.2 + 1) q.1.2.2.2 ≤ 2 ^ (d + q.1.2.1) ∧ evOut q.2 = some q.1.2.2.1)) (evNum (b q.1.1) q.2 q.1.2.2.2 * 2 ^ (q.1.2.1 - evK q.2)) 0 = truncGTermUniform b d q := by
  rw [truncGTermUniform_eq]
  exact Bool.cond_decide (cumNum (b q.1.1) q.1.2.1 (q.2 + 1) q.1.2.2.2 ≤ 2 ^ (d + q.1.2.1) ∧ evOut q.2 = some q.1.2.2.1) _ _

lemma truncGapproxUniform_eq (b : ℕ → ℕ → BitString → BitString → ℕ) (d : ℕ) (p : ℕ × ℕ × BitString × BitString) :
    truncGapprox (b p.1) d p.2.1 p.2.2.1 p.2.2.2 = ∑ t ∈ Finset.range p.2.1, truncGTermUniform b d (p, t) := by
  unfold truncGapprox truncGTermUniform; rfl

lemma cumNumTerm_eq (approx : ℕ → BitString → BitString → ℕ) (p : ℕ × ℕ × BitString) (i : ℕ) :
    cumNumTerm approx p i = evNum approx i p.2.2 * 2 ^ (p.1 - evK i) := by
  unfold cumNumTerm; rfl

lemma cumNumTerm_eq_packed (approx : ℕ → BitString → BitString → ℕ) (q : (ℕ × ℕ × BitString) × ℕ) :
    evNum approx q.2 q.1.2.2 * 2 ^ (q.1.1 - evK q.2) = cumNumTerm approx q.1 q.2 := by
  unfold cumNumTerm; rfl

lemma cumNumTermUniform_eq (b : ℕ → ℕ → BitString → BitString → ℕ) (p : ℕ × ℕ × ℕ × BitString) (i : ℕ) :
    cumNumTermUniform b p i = evNum (b p.1) i p.2.2.2 * 2 ^ (p.2.1 - evK i) := by
  unfold cumNumTermUniform; rfl

lemma cumNumTermUniform_eq_packed (b : ℕ → ℕ → BitString → BitString → ℕ) (q : (ℕ × ℕ × ℕ × BitString) × ℕ) :
    evNum (b q.1.1) q.2 q.1.2.2.2 * 2 ^ (q.1.2.1 - evK q.2) = cumNumTermUniform b q.1 q.2 := by
  unfold cumNumTermUniform; rfl


lemma incNumUniformPacked_eq (b : ℕ → ℕ → BitString → BitString → ℕ) (p : ℕ × ℕ × BitString × BitString) :
    incNumUniformPacked b p = incNum (b p.1) p.2.1 p.2.2.1 p.2.2.2 := by
  unfold incNumUniformPacked; rfl

lemma incNumUniformPacked_eq_cases (b : ℕ → ℕ → BitString → BitString → ℕ) (p : ℕ × ℕ × BitString × BitString) :
    Nat.casesOn p.2.1 (b p.1 0 p.2.2.1 p.2.2.2) (fun k => b p.1 (k + 1) p.2.2.1 p.2.2.2 - 2 * b p.1 k p.2.2.1 p.2.2.2) = incNumUniformPacked b p := by
  unfold incNumUniformPacked
  cases p.2.1 <;> rfl

lemma evNumUniformPacked_eq (b : ℕ → ℕ → BitString → BitString → ℕ) (p : ℕ × ℕ × BitString) :
    evNumUniformPacked b p = evNum (b p.1) p.2.1 p.2.2 := by
  unfold evNumUniformPacked; rfl

lemma evNumUniformPacked_eq_cases (b : ℕ → ℕ → BitString → BitString → ℕ) (p : ℕ × ℕ × BitString) :
    Option.casesOn (evOut p.2.1) 0 (fun o => incNum (b p.1) (evK p.2.1) o p.2.2) = evNumUniformPacked b p := by
  unfold evNumUniformPacked evNum
  cases evOut p.2.1 <;> rfl

lemma incNum_eq_zero (approx : ℕ → BitString → BitString → ℕ) (out ctx : BitString) :
    incNum approx 0 out ctx = approx 0 out ctx := rfl

lemma incNum_eq_succ (approx : ℕ → BitString → BitString → ℕ) (k : ℕ) (out ctx : BitString) :
    incNum approx (k + 1) out ctx = approx (k + 1) out ctx - 2 * approx k out ctx := rfl

lemma incNum_eq_cases (approx : ℕ → BitString → BitString → ℕ)
    (p : ℕ × BitString × BitString) :
    Nat.casesOn p.1 (approx 0 p.2.1 p.2.2)
        (fun k => approx (k + 1) p.2.1 p.2.2 - 2 * approx k p.2.1 p.2.2) =
      incNum approx p.1 p.2.1 p.2.2 := by
  cases p.1 <;> rfl

lemma evNum_eq_some (approx : ℕ → BitString → BitString → ℕ) (t : ℕ) (ctx : BitString) (out : BitString) (h : evOut t = some out) :
    evNum approx t ctx = incNum approx (evK t) out ctx := by
  unfold evNum; simp [h]

lemma evNum_eq_none (approx : ℕ → BitString → BitString → ℕ) (t : ℕ) (ctx : BitString) (h : evOut t = none) :
    evNum approx t ctx = 0 := by
  unfold evNum; simp [h]

-- Keep the numerator combinators opaque for `Computable` unification: their
-- equational behavior is unfolded explicitly in the proofs that need it.
attribute [local irreducible] incNum evNum cumNum truncGapprox
  cumNumTerm truncGTerm cumNumTermUniform truncGTermUniform
  cumNumPacked incNumUniformPacked evNumUniformPacked cumNumUniformPacked


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
  | zero => simp +decide [ incNum ]
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
    have h_partial_sum : ∑ k ∈ Finset.range i, dyadicValue (incNum approx k out ctx) k ≤ dyadicValue (approx (i - 1) out ctx) (i - 1) := by
      rcases i <;> simp_all +decide [ Finset.sum_range_succ ];
      rename_i n; rw [ ← sum_dyadicValue_incNum hmono n out ctx ] ;
      rw [ Finset.sum_range_succ ];
    exact le_trans h_partial_sum <| le_iSup_of_le _ le_rfl;
  · intro w hw; rcases exists_lt_of_lt_ciSup hw with ⟨ s, hs ⟩ ; use s + 1; simp_all +decide [ Finset.sum_range_succ ] ;
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
  have h_dyadicValue_sum : dyadicValue (∑ i ∈ Finset.range n, evNum approx i ctx * 2 ^ (S - evK i)) S = ∑ i ∈ Finset.range n, dyadicValue (evNum approx i ctx * 2 ^ (S - evK i)) S := by
    unfold dyadicValue; norm_num [ div_eq_mul_inv, Finset.sum_mul _ _ _ ] ;
  unfold cumNum truncCum
  rw [h_dyadicValue_sum]
  exact Finset.sum_congr rfl fun i hi => by
    rw [dyadicValue_evNum_scale i S ctx (by
      unfold evK
      exact Nat.le_trans (Nat.unpair_right_le i) (by linarith [Finset.mem_range.mp hi]))]

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
  simp +decide [ Finset.sum_ite ];
  rw [ ENNReal.div_eq_inv_mul, Finset.mul_sum ];
  refine Finset.sum_bij ( fun x hx => x ) ?_ ?_ ?_ ?_ <;> simp_all +decide ;
  · intro a ha₁ ha₂ ha₃; rw [ ← dyadicValue_cumNum S ( a + 1 ) ctx ( by linarith ) ] at *; simp_all +decide [ dyadicValue ] ;
    rw [ ENNReal.div_le_iff_le_mul ] <;> norm_cast <;> norm_num [ pow_add ] at * ; linarith;
  · intro b hb₁ hb₂ hb₃; contrapose! hb₂; simp_all +decide [ truncCum ] ;
    have h_div : (cumNum approx S (b + 1) ctx : ℝ≥0∞) / 2 ^ S > 2 ^ d := by
      rw [ gt_iff_lt, ENNReal.lt_div_iff_mul_lt ] <;> norm_cast <;> norm_num [ pow_add ] at * ; linarith;
    refine lt_of_lt_of_le h_div ?_;
    change dyadicValue (cumNum approx S (b + 1) ctx) S ≤ truncCum approx (b + 1) ctx
    exact le_of_eq (dyadicValue_cumNum (approx := approx) S (b + 1) ctx (by linarith))
  · intro a ha₁ ha₂ ha₃
    have ha_evK : evK a < S := by
      unfold evK
      exact lt_of_le_of_lt (Nat.unpair_right_le a) ha₁
    rw [ ← dyadicValue_evNum_scale a S ctx (Nat.le_of_lt ha_evK) ] ; ring_nf;
    unfold dyadicValue; norm_num [ mul_assoc, mul_comm, mul_left_comm, pow_add ] ;
    rw [ ENNReal.div_eq_inv_mul ];
    ring_nf

/-
The stage-`S` numerator is monotone in the dyadic value.
-/
lemma truncGapprox_mono (d : ℕ) (S : ℕ) (out ctx : BitString) :
    dyadicValue (truncGapprox approx d S out ctx) S
      ≤ dyadicValue (truncGapprox approx d (S + 1) out ctx) (S + 1) := by
  rw [ dyadicValue_truncGapprox, dyadicValue_truncGapprox ];
  exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.le_succ _ ) ) fun _ _ _ => by split_ifs <;> positivity;


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
  set aterm : ℕ → ℝ≥0∞ := fun t => if truncCum approx (t + 1) ctx ≤ (2 : ℝ≥0∞) ^ d then evVal approx t ctx else 0;
  have h_aterm : ∀ S, (∑ t ∈ Finset.range S, aterm t) ≤ (2 : ℝ≥0∞) ^ d := by
    intro S
    induction S with
    | zero => simp_all +decide
    | succ S ih =>
      simp_all +decide [ Finset.sum_range_succ ]
      by_cases h : truncCum approx ( S + 1 ) ctx ≤ 2 ^ d <;> simp_all +decide [ truncCum ];
      · simp_all +decide [ Finset.sum_range_succ, aterm ];
        refine le_trans ( add_le_add ( Finset.sum_le_sum fun _ _ => ?_ ) ( ?_ ) ) h; all_goals split_ifs <;> norm_num;
      · simp +zetaDelta at *;
        rw [ if_neg ] <;> simp_all +decide [ Finset.sum_range_succ, truncCum ]; -- Also `∑ range S ≤ cum approx S` / * improving inductive step * /;
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
  -- By definition of $evOut$, we know that $evOut t = some out$ if and only if $t = Nat.pair (Encodable.encode out) k$ for some $k$.
  have h_evOut : ∀ t, evOut t = some out ↔ ∃ k, t = Nat.pair (Encodable.encode out) k := by
    intro t
    simp [evOut];
    constructor <;> intro h;
    · have := Encodable.decode₂_eq_some.mp h;
      exact ⟨ _, by rw [ this, Nat.pair_unpair ] ⟩;
    · obtain ⟨ k, rfl ⟩ := h; simp +decide [ Nat.unpair_pair ] ;
  -- Apply the fact that the sum over `t` where `evOut t = some out` is equal to the sum over `k` of `evVal approx (Nat.pair (Encodable.encode out) k) ctx`.
  have h_sum_eq : (∑' t, if evOut t = some out then evVal approx t ctx else 0) = (∑' k, evVal approx (Nat.pair (Encodable.encode out) k) ctx) := by
    simp +decide only [h_evOut];
    erw [ ← tsum_subtype ];
    erw [ ← Equiv.tsum_eq ( Equiv.ofBijective ( fun k : ℕ => ⟨ Nat.pair ( Encodable.encode out ) k, ⟨ k, rfl ⟩ ⟩ : ℕ → ( { t : ℕ // ∃ k : ℕ, t = Nat.pair ( Encodable.encode out ) k } ) ) ⟨ fun a => by aesop, fun a => by aesop ⟩ ) ] ; aesop;
  convert tsum_dyadicValue_incNum hmono hsup out ctx using 1;
  convert h_sum_eq using 3;
  unfold evVal; simp +decide [  evK ] ;
  unfold evNum; simp +decide [ evOut, evK ] ;

/-
Summed over all events, the increment values recover the total `f`-mass.
-/
lemma tsum_evVal
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx)
    (ctx : BitString) :
    (∑' t : ℕ, evVal approx t ctx) = ∑' out : BitString, f out ctx := by
  -- Apply the fact that the sum over all out is the same as the sum over t of the sum over out of the terms where evOut t equals some out.
  have h_sum_out : ∀ t, ∑' out, (if evOut t = some out then evVal approx t ctx else 0) = evVal approx t ctx := by
    intro t
    by_cases h : evOut t = none;
    · simp [h, evVal, evNum];
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

end Kolmogorov
