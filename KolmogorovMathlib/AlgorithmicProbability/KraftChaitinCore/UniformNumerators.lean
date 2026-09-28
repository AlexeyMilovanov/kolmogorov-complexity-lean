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
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore.LSCApproximation

namespace Kolmogorov
section Truncate
open scoped ENNReal
variable {f : BitString → BitString → ℝ≥0∞} {approx : ℕ → BitString → BitString → ℕ}

/-! ### Uniform (index-parameterized) computability of the dyadic numerators

The lemmas above establish computability of the numerator chain for a single fixed
approximation `approx`. The following *uniform* variants thread an extra leading
index coordinate `i : ℕ` through the chain, so that an entire jointly-computable
*family* `b : ℕ → ℕ → BitString → BitString → ℕ` of approximations yields a jointly
computable numerator family. These are needed for the lower-semicomputability of a
countable mixture of sanitized enumerations (see `UniversalSemimeasure`). Each
proof mirrors the corresponding fixed-`approx` lemma with `b i` substituted and `i`
carried as a `Computable.fst`-style coordinate. -/

private lemma incNum_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
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

private lemma evNum_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
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

private lemma cumNum_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
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

private lemma truncGTerm_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
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

/-- The truncated stage approximation is computable uniformly in the index of the approximated
family. -/
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

end Kolmogorov


