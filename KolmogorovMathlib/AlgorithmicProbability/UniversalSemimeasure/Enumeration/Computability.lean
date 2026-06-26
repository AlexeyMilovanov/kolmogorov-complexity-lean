/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure.Enumeration.Basic
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure.Basic

namespace Kolmogorov

open scoped ENNReal

/-
Computability of a stagewise `Finset.range` supremum: if `g` and the
two-argument family `f` are computable, then so is `a ↦ (Finset.range (g a)).sup (f a)`.
Proved by rewriting the `Finset.range` sup as a `List.range` fold.
-/
lemma computable_finset_range_sup {α : Type*} [Primcodable α]
    (g : α → ℕ) (f : α → ℕ → ℕ)
    (hg : Computable g) (hf : Computable (fun p : α × ℕ => f p.1 p.2)) :
  Computable (fun a => (Finset.range (g a)).sup (f a)) := by
  have hstep : Computable (fun p : α × ℕ × ℕ => max (f p.1 p.2.1) p.2.2) := by
    exact Primrec.nat_max.to_comp.comp
      (hf.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd)
  have hrec : Computable (fun a : α =>
      Nat.rec (motive := fun _ => ℕ) 0 (fun n acc => max (f a n) acc) (g a)) :=
    Computable.nat_rec hg (Computable.const 0) hstep.to₂
  exact hrec.of_eq (fun a => by
    induction g a with
    | zero => simp
    | succ n ih =>
      rw [Finset.range_add_one, Finset.sup_insert, ← ih])

lemma approxEnum_computable :
    Computable (fun p : ℕ × ℕ × BitString × BitString =>
      approxEnum p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  apply Computable.of_eq;
  rotate_right;
  exact fun p => ( Finset.range ( p.2.1 + 1 ) ).sup fun s' => match Nat.Partrec.Code.evaln p.2.1 ( ( Encodable.decode ( α := Nat.Partrec.Code ) p.1 ).getD Nat.Partrec.Code.zero ) ( Encodable.encode ( s', p.2.2.1, p.2.2.2 ) ) with | some v => v * 2 ^ ( p.2.1 - s' ) | none => 0;
  · convert computable_finset_range_sup _ _ _ _;
    · exact Computable.succ.comp ( Computable.fst.comp ( Computable.snd ) );
    · convert Computable.option_casesOn _ _ _ using 1;
      rotate_left;
      exact ℕ;
      exact inferInstance;
      exact fun p => Nat.Partrec.Code.evaln p.1.2.1 ( ( Encodable.decode p.1.1 ).getD Nat.Partrec.Code.zero ) ( Encodable.encode ( p.2, p.1.2.2.1, p.1.2.2.2 ) );
      exact fun p => 0;
      exact fun p v => v * 2 ^ ( p.1.2.1 - p.2 );
      · convert Nat.Partrec.Code.primrec_evaln.to_comp.comp _ using 1;
        rotate_left;
        exact fun p => ( ( p.1.2.1, ( Encodable.decode p.1.1 ).getD Nat.Partrec.Code.zero ), Encodable.encode ( p.2, p.1.2.2.1, p.1.2.2.2 ) );
        · apply Computable.pair;
          · apply Computable.pair;
            · exact Computable.fst.comp ( Computable.snd.comp Computable.fst );
            · convert Computable.option_getD ( Computable.decode.comp ( Computable.fst.comp Computable.fst ) ) ( Computable.const Nat.Partrec.Code.zero ) using 1;
          · apply Computable.pair;
            · exact Computable.snd;
            · exact Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) ) ) ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) ) );
        · rfl;
      · exact Computable.const 0;
      · refine Computable.of_eq
          (f := fun p : ((ℕ × (ℕ × BitString × BitString)) × ℕ) × ℕ =>
            p.2 * 2 ^ ( p.1.1.2.1 - p.1.2 )) ?_ ?_;
        · have h_primrec : Primrec (fun p : ℕ × ℕ × BitString × BitString × ℕ => p.2.2.2.2 * 2 ^ (p.2.1 - p.1)) := by
            have h_primrec : Primrec (fun p : ℕ × ℕ × BitString × BitString × ℕ => p.2.2.2.2) := by
              exact Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd ) ) );
            have h_primrec : Primrec (fun p : ℕ × ℕ × BitString × BitString × ℕ => 2 ^ (p.2.1 - p.1)) := by
              have h_primrec : Primrec (fun p : ℕ × ℕ => 2 ^ (p.2 - p.1)) := by
                have h_primrec : Primrec (fun p : ℕ × ℕ => p.2 - p.1) := by
                  exact Primrec.nat_sub.comp ( Primrec.snd ) ( Primrec.fst );
                have h_primrec : Primrec (fun p : ℕ => 2 ^ p) := by
                  convert primrec_two_pow using 1;
                exact h_primrec.comp ‹_›;
              convert h_primrec.comp ( show Primrec ( fun p : ℕ × ℕ × BitString × BitString × ℕ => ( p.1, p.2.1 ) ) from ?_ ) using 1;
              exact Primrec.pair ( Primrec.fst ) ( Primrec.fst.comp ( Primrec.snd ) );
            exact Primrec.nat_mul.comp ( by assumption ) ( by assumption );
          convert h_primrec.to_comp.comp _ using 1;
          rotate_left;
          exact fun p => ( p.1.2, p.1.1.2.1, p.1.1.2.2.1, p.1.1.2.2.2, p.2 );
          · exact Computable.pair ( Computable.snd.comp Computable.fst ) ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.fst.comp Computable.fst ) ) ) ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.fst.comp Computable.fst ) ) ) ) ( Computable.pair ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.fst.comp Computable.fst ) ) ) ) ( Computable.snd ) ) ) );
          · exact funext fun p => by cases p; rfl;
        · aesop;
      · exact funext fun p => by cases Nat.Partrec.Code.evaln p.1.2.1 ( ( Encodable.decode p.1.1 ).getD Nat.Partrec.Code.zero ) ( Encodable.encode ( p.2, p.1.2.2.1, p.1.2.2.2 ) ) <;> rfl;
  · intro p; cases p with | mk p_1 p_2 => cases p_2 with | mk p_2_1 p_2_2 => cases p_2_2 with | mk p_2_2_1 p_2_2_2 => unfold approxEnum; rfl

lemma makeMono_computable (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString × BitString => makeMono approx p.1 p.2.1 p.2.2) := by
  let base : ℕ × BitString × BitString → ℕ := fun p => approx 0 p.2.1 p.2.2
  let step : ℕ × BitString × BitString → ℕ × ℕ → ℕ :=
    fun p q => max (2 * q.2) (approx (q.1 + 1) p.2.1 p.2.2)
  have hbase : Computable base := by
    exact hcomp.comp ((Computable.const 0).pair Computable.snd)
  have hmul_two : Computable (fun n : ℕ => 2 * n) := by
    exact (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp
  have hstep_uncurried :
      Computable (fun r : (ℕ × BitString × BitString) × (ℕ × ℕ) =>
        step r.1 r.2) := by
    have hleft : Computable (fun r : (ℕ × BitString × BitString) × (ℕ × ℕ) =>
        2 * r.2.2) :=
      hmul_two.comp (Computable.snd.comp Computable.snd)
    have hstage : Computable (fun r : (ℕ × BitString × BitString) × (ℕ × ℕ) =>
        r.2.1 + 1) := by
      exact (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)).to_comp
    have hright : Computable (fun r : (ℕ × BitString × BitString) × (ℕ × ℕ) =>
        approx (r.2.1 + 1) r.1.2.1 r.1.2.2) := by
      exact hcomp.comp (hstage.pair (Computable.snd.comp Computable.fst))
    exact (Primrec.nat_max.to_comp.comp hleft hright).of_eq (fun r => by rfl)
  have hrec :
      Computable (fun p : ℕ × BitString × BitString =>
        Nat.rec (motive := fun _ => ℕ) (base p) (fun y ih => step p (y, ih)) p.1) :=
    Computable.nat_rec Computable.fst hbase hstep_uncurried.to₂
  exact hrec.of_eq (fun p => by
    induction p.1 with
    | zero => rfl
    | succ s ih =>
        change Nat.rec (motive := fun _ => ℕ) (base p)
            (fun y ih => step p (y, ih)) (s + 1)
          = makeMono approx (s + 1) p.2.1 p.2.2
        simp [makeMono, step, ih])

/-
Uniform (index-parameterized) computability of `makeMono`: a jointly
computable family of approximations `b i` yields a jointly computable family
`fun (i, s, out, ctx) => makeMono (b i) s out ctx`. Mirrors `makeMono_computable`
with the index `i` carried as the leading coordinate.
-/
lemma makeMono_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun p : ℕ × ℕ × BitString × BitString =>
      makeMono (b p.1) p.2.1 p.2.2.1 p.2.2.2) := by
  apply Computable.of_eq;
  apply Computable.nat_rec;
  exact Computable.fst.comp Computable.snd;
  convert hb.comp _;
  exact fun p => ( p.1, 0, p.2.2.1, p.2.2.2 );
  exact Computable.pair ( Computable.fst ) ( Computable.pair ( Computable.const 0 ) ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd ) ) ) ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd ) ) ) ) );
  rotate_left;
  exact fun p q => max ( 2 * q.2 ) ( b p.1 ( q.1 + 1 ) p.2.2.1 p.2.2.2 );
  · intro n; induction n.2.1 <;> simp +decide [ *, makeMono ] ;
  · apply Computable.of_eq;
    rotate_right;
    exact fun p => max ( 2 * p.2.2 ) ( b p.1.1 ( p.2.1 + 1 ) p.1.2.2.1 p.1.2.2.2 );
    · apply Computable.of_eq;
      apply Computable.comp (Primrec.nat_max.to_comp);
      rotate_left;
      exact fun p => ( 2 * p.2.2, b p.1.1 ( p.2.1 + 1 ) p.1.2.2.1 p.1.2.2.2 );
      · grind;
      · apply Computable.pair;
        · apply Computable.comp (Primrec.nat_mul.to_comp) (Computable.const 2 |> Computable.pair <| Computable.snd.comp Computable.snd);
        · convert hb.comp _ using 1;
          rotate_left;
          exact fun p => ( p.1.1, p.2.1 + 1, p.1.2.2.1, p.1.2.2.2 );
          · apply Computable.pair;
            · exact Computable.fst.comp Computable.fst;
            · apply Computable.pair;
              · exact Computable.succ.comp ( Computable.fst.comp ( Computable.snd ) );
              · apply Computable.pair;
                · exact Computable.fst.comp ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) );
                · exact Computable.snd.comp ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) );
          · rfl;
    · grind +extAll

lemma lscEnum_isLSC (i : ℕ) : IsLSC (lscEnum i) := by
  refine ⟨truncGapprox (makeMono (approxEnum i)) 0, ?_, ?_, ?_⟩
  · intro S out ctx; exact truncGapprox_mono 0 S out ctx
  · intro out ctx; rfl
  · apply truncGapprox_computable
    exact makeMono_computable (approxEnum i)
      (approxEnum_computable.comp
        ((Computable.const i).pair (Computable.fst.pair Computable.snd)))

/-
**Uniform computable dyadic-mixture closure (LSC).**

If a countable family `μ i` of conditional functions has a *jointly computable*,
stagewise-monotone dyadic approximation `a i s` (numerators over the denominator
`2^s`) converging to `μ i`, then the canonical `dyadicWeight`-weighted mixture
`fun out ctx => ∑' i, dyadicWeight i * μ i out ctx` is lower-semicomputable.

The witnessing approximation is the diagonal numerator `mixtureDyadicApprox a`,
whose stage-`S` dyadic value is the partial mixture over the first `S/2`
components at substage `S/2` (see `dyadicValue_mixtureDyadicApprox`). Monotonicity
in `S` comes from the per-component monotonicity (more components, each read
later); the supremum is the double monotone limit, which equals the mixture by
the monotone convergence theorem for `ℝ≥0∞` sums; computability is a finite
`Finset.range` sum of a jointly computable term (`computable_range_sum`).
-/
lemma isLSC_unaryMixture_dyadicWeight_of_uniform
    (μ : ℕ → BitString → BitString → ℝ≥0∞)
    (a : ℕ → ℕ → BitString → BitString → ℕ)
    (hmono : ∀ i s out ctx,
      dyadicValue (a i s out ctx) s ≤ dyadicValue (a i (s + 1) out ctx) (s + 1))
    (hsup : ∀ i out ctx, ⨆ s, dyadicValue (a i s out ctx) s = μ i out ctx)
    (hcomp : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      a p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    IsLSC (fun out ctx => ∑' i, dyadicWeight i * μ i out ctx) := by
  revert μ a hmono hsup hcomp;
  -- Define the mixture approximation `a' S out ctx` as `mixtureDyadicApprox a S out ctx`.
  intro μ a hmono hsup hcomp
  set a' : ℕ → BitString → BitString → ℕ := fun S out ctx => mixtureDyadicApprox a S out ctx;
  -- Prove that `a'` is monotone in `S`.
  have ha'_mono : ∀ S out ctx, dyadicValue (a' S out ctx) S ≤ dyadicValue (a' (S + 1) out ctx) (S + 1) := by
    intros S out ctx
    simp [a', dyadicValue_mixtureDyadicApprox];
    refine le_trans ?_ ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.div_le_div_right ( Nat.le_succ _ ) ) ) fun _ _ _ => by positivity );
    gcongr;
    cases Nat.mod_two_eq_zero_or_one S <;> simp_all +decide [ Nat.add_div ];
  -- Prove that `a'` converges to the mixture.
  have ha'_sup : ∀ out ctx, ⨆ S, dyadicValue (a' S out ctx) S = ∑' i, dyadicWeight i * μ i out ctx := by
    intro out ctx
    have h_double_sup : ⨆ k, ∑ i ∈ Finset.range k, dyadicWeight i * dyadicValue (a i k out ctx) k = ∑' i, dyadicWeight i * μ i out ctx := by
      have h_double_sup : ⨆ k, ∑ i ∈ Finset.range k, dyadicWeight i * dyadicValue (a i k out ctx) k = ⨆ k, ∑ i ∈ Finset.range k, dyadicWeight i * (⨆ s, dyadicValue (a i s out ctx) s) := by
        apply le_antisymm;
        · refine iSup_mono fun k => Finset.sum_le_sum fun i hi => mul_le_mul_right ?_ _;
          exact le_iSup_of_le k le_rfl;
        · refine iSup_le fun k => ?_;
          refine le_of_forall_lt_imp_le_of_dense fun x hx => ?_;
          -- Since $x < \sum_{i=0}^{k-1} \text{dyadicWeight}(i) \cdot \sup_{s} \text{dyadicValue}(a(i, s, out, ctx))$, there exists some $N$ such that $x < \sum_{i=0}^{k-1} \text{dyadicWeight}(i) \cdot \text{dyadicValue}(a(i, N, out, ctx))$.
          obtain ⟨N, hN⟩ : ∃ N, x < ∑ i ∈ Finset.range k, dyadicWeight i * dyadicValue (a i N out ctx) N := by
            have h_lim : Filter.Tendsto (fun N => ∑ i ∈ Finset.range k, dyadicWeight i * dyadicValue (a i N out ctx) N) Filter.atTop (nhds (∑ i ∈ Finset.range k, dyadicWeight i * ⨆ s, dyadicValue (a i s out ctx) s)) := by
              refine tendsto_finsetSum _ fun i _ => ?_;
              refine ENNReal.Tendsto.const_mul ?_ ?_;
              · exact tendsto_atTop_iSup fun s t hst => monotone_nat_of_le_succ ( fun s => hmono i s out ctx ) hst;
              · exact Or.inr ( by simp +decide [ dyadicWeight ] );
            exact ( h_lim.eventually ( lt_mem_nhds hx ) ) |> fun h => h.exists;
          refine le_trans hN.le ( le_trans ?_ ( le_iSup _ ( Max.max k N ) ) );
          refine le_trans ?_ ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( le_max_left k N ) ) fun _ _ _ => by positivity );
          gcongr;
          exact monotone_nat_of_le_succ ( fun s => hmono _ s _ _ ) ( le_max_right _ _ );
      simp_all +decide [ ENNReal.tsum_eq_iSup_nat ];
    rw [ ← h_double_sup, iSup_eq_of_forall_le_of_forall_lt_exists_gt ];
    · intro S;
      refine le_trans ?_ ( le_iSup _ ( S / 2 ) );
      rw [ dyadicValue_mixtureDyadicApprox ];
    · intro w hw;
      obtain ⟨ k, hk ⟩ := exists_lt_of_lt_ciSup hw;
      use 2 * k;
      refine hk.trans_le ?_;
      rw [ dyadicValue_mixtureDyadicApprox ];
      norm_num;
  -- Prove that `a'` is computable.
  have ha'_comp : Computable (fun p : ℕ × BitString × BitString => a' p.1 p.2.1 p.2.2) := by
    apply Computable.of_eq;
    convert computable_range_sum _ _ _ _ using 1;
    use fun p i => a i ( p.1 / 2 ) p.2.1 p.2.2 * 2 ^ ( p.1 - ( i + 1 ) - p.1 / 2 );
    rotate_left;
    use fun p => p.1 / 2;
    · convert Primrec.to_comp ( Primrec.nat_div.comp ( Primrec.fst ) ( Primrec.const 2 ) ) using 1;
    · aesop;
    · apply Computable₂.comp;
      · exact Primrec.to_comp ( Primrec.nat_mul.comp ( Primrec.fst ) ( Primrec.snd ) );
      · convert hcomp.comp _ using 1;
        rotate_left;
        exact fun p => ( p.2, p.1.1 / 2, p.1.2.1, p.1.2.2 );
        · apply Computable.pair;
          · exact Computable.snd;
          · apply Computable.pair;
            · have h_div : Primrec (fun n : ℕ => n / 2) := by
                exact Primrec.nat_div.comp ( Primrec.id ) ( Primrec.const 2 );
              exact h_div.to_comp.comp ( Computable.fst.comp Computable.fst );
            · exact Computable.pair ( Computable.fst.comp ( Computable.snd.comp Computable.fst ) ) ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) );
        · rfl;
      · apply Computable.of_eq;
        rotate_right;
        exact fun p => 2 ^ ( p.1.1 - ( p.2 + 1 ) - p.1.1 / 2 );
        · convert Primrec.to_comp _;
          convert Primrec.comp ( primrec_two_pow ) ( Primrec.nat_sub.comp ( Primrec.nat_sub.comp ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.succ.comp ( Primrec.snd ) ) ) ( Primrec.nat_div.comp ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.const 2 ) ) ) using 1;
        · exact fun _ => rfl;
  use a'

/-
**Uniform computability of the sanitized enumeration approximation.**

The stage-`s` numerators of the sanitized components `lscEnum i` form a jointly
computable family in `(i, s, out, ctx)`. This is the only remaining effective
ingredient of the mixture LSC closure: it reduces precisely to the joint
computability of the enumeration core `approxEnum` (`approxEnum_computable`),
threaded through `makeMono` and `truncGapprox` (via the uniform
`makeMono_computable_uniform` and `truncGapprox_computable_uniform`).
-/
lemma lscEnumApprox_uniform_computable :
    Computable (fun p : ℕ × ℕ × BitString × BitString =>
      truncGapprox (makeMono (approxEnum p.1)) 0 p.2.1 p.2.2.1 []) := by
  convert Computable.comp ( show Computable ( fun p : ℕ × ℕ × BitString × BitString => truncGapprox ( makeMono ( approxEnum p.1 ) ) 0 p.2.1 p.2.2.1 p.2.2.2 ) from ?_ ) ( show Computable ( fun p : ℕ × ℕ × BitString × BitString => ( p.1, p.2.1, p.2.2.1, [] ) ) from ?_ ) using 1;
  · convert truncGapprox_computable_uniform ( fun i => makeMono ( approxEnum i ) ) ( makeMono_computable_uniform _ _ ) 0 using 1;
    exact approxEnum_computable;
  · exact Computable.pair ( Computable.fst ) ( Computable.pair ( Computable.fst.comp ( Computable.snd ) ) ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd ) ) ) ( Computable.const [] ) ) )

/-- The dyadic mixture of the sanitized enumeration is a lower-semicomputable
unary semimeasure. The mass bound is immediate from the generic mixture theorem;
the LSC half is the general `isLSC_unaryMixture_dyadicWeight_of_uniform` closure
applied to the sanitized family, whose uniform approximation is
`lscEnumApprox_uniform_computable`. -/
lemma unaryMixture_dyadicWeight_lscEnum_isLowerSemicomputable :
    IsLowerSemicomputableSemimeasure
      (unaryMixture dyadicWeight (fun i x => lscEnum i x [])) := by
  refine ⟨?_, ?_⟩
  · exact unaryMixture_isSemimeasure dyadicWeight (fun i x => lscEnum i x [])
      tsum_dyadicWeight.le (fun i => lscEnum_isSemimeasure i)
  · have h :=
      isLSC_unaryMixture_dyadicWeight_of_uniform
        (fun i out _ => lscEnum i out [])
        (fun i s out _ => truncGapprox (makeMono (approxEnum i)) 0 s out [])
        (fun i s out ctx => truncGapprox_mono 0 s out [])
        (fun i out ctx => rfl)
        lscEnumApprox_uniform_computable
    exact h

end Kolmogorov
