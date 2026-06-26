/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.OptimalCoding
import KolmogorovMathlib.AlgorithmicProbability.Bounds
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.Prefix.CountableKraft
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.AlgorithmicProbability.Computability.Tuple

/-!
# The Kraft–Chaitin Coding Theorem (hard direction)

This module isolates the genuinely hard Chapter-4 engine behind the *lower*
direction of prefix symmetry of information: the **Kraft–Chaitin realization**
of the a priori semimeasure of a prefix decompressor.

The a priori semimeasure `m_M(x | y)` of a prefix decompressor `M` is a
*lower-semicomputable conditional subsemimeasure* (`∑_x m_M(x | y) ≤ 1`,
`tsum_aprioriMeasure_le_one`, and l.s.c. because `M` is partial recursive). The
Kraft–Chaitin construction turns any such object into an actual prefix
decompressor `M'` whose program lengths realize `-log m_M` up to an additive
constant, i.e. `2^{-c₀} · m_M(x | y) ≤ 2^{-KP_{M'}(x | y)}`.

Everything *downstream* of this realization is already in the repository:
`complexityWeight_dominates_of_prefix_realization` (in `OptimalCoding`) transfers
the realization from `M'` to the optimal prefix decompressor `U`, absorbing the
coding loss into the constant. We package that transfer here as the **coding
theorem** `aprioriMeasure_le_complexityWeight_optimal`:
`m_M(x | y) ≤ 2^{c} · 2^{-KP_U(x | y)}`.

The canonical textbook obligation (the Kraft–Chaitin / "coding theorem, hard
direction" realization) is stated in the *true* `≤×` direction, with no logarithm
and no equality claim; the constant `c₀` is genuine positive coding overhead.
-/

namespace Kolmogorov

open scoped ENNReal
open Computability

/-! **Lower-semicomputability of the a priori semimeasure.** For a prefix
decompressor `M`, the conditional a priori semimeasure `m_M(x | y)` is
lower-semicomputable (`IsLSC`): the stage-`s` numerator sums `2^{s - |p|}` over the
finitely many programs `p` (of length `≤ s`) that produce `x` from `y` within `s`
steps; this is `Computable` in `(s, x, y)`, monotone in `s`, and its supremum is
`m_M(x | y)`.

This is the standard `evaln`-staged dyadic approximation of a partial-recursive
machine's a priori semimeasure. It is strictly the *computability/analysis* half
of the coding theorem — once available, the realization follows from the abstract
allocator `kraftChaitin_realization_bound` with no further coding content. This
is the mathematically local input to `aprioriMeasure_prefix_realization`. -/
section AprioriLSC

/-- The list of programs of length `≤ s` that, run with fuel `s` under code `c` on
input `(p, y)`, output `Encodable.encode x`. This is the stage-`s` accepted set used
to approximate `aprioriMeasure`. -/
def aprioriAcceptedList (c : Nat.Partrec.Code) (s : ℕ) (x y : BitString) : List BitString :=
  (boundedPrograms s).filter
    (fun p => decide
      (Nat.Partrec.Code.evaln s c (Encodable.encode (p, y)) = some (Encodable.encode x)))

/-- The stage-`s` numerator: `∑` over accepted programs `p` of `2^(s - |p|)`. Its
dyadic value `·/2^s` is `∑ (2⁻¹)^|p|` over accepted programs. -/
def aprioriApprox (c : Nat.Partrec.Code) (s : ℕ) (x y : BitString) : ℕ :=
  ((aprioriAcceptedList c s x y).map (fun p => 2 ^ (s - p.length))).sum

/-- The accepted programs as a finset (the underlying list is nodup). -/
noncomputable def aprioriAcc (c : Nat.Partrec.Code) (s : ℕ) (x y : BitString) :
    Finset BitString :=
  (aprioriAcceptedList c s x y).toFinset

/-- The accepted list has no duplicates. -/
lemma aprioriAcceptedList_nodup (c : Nat.Partrec.Code) (s : ℕ) (x y : BitString) :
    (aprioriAcceptedList c s x y).Nodup :=
  (boundedPrograms_nodup s).filter _

/-- Membership in the accepted finset. -/
lemma mem_aprioriAcc {c : Nat.Partrec.Code} {s : ℕ} {x y p : BitString} :
    p ∈ aprioriAcc c s x y ↔
      p.length ≤ s ∧
        Nat.Partrec.Code.evaln s c (Encodable.encode (p, y)) = some (Encodable.encode x) := by
  unfold aprioriAcc;
  simp +decide [ aprioriAcceptedList, mem_boundedPrograms_iff ]

/-- Producing `x` from `p` in context `y` is equivalent to some fuel making the staged
evaluation under the code `c` of `M` output `Encodable.encode x`.
-/
lemma produces_iff_evaln {M : Map} (c : Nat.Partrec.Code)
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (M a)))
    (p x y : BitString) :
    produces M p y x ↔
      ∃ k, Nat.Partrec.Code.evaln k c (Encodable.encode (p, y)) = some (Encodable.encode x) := by
  constructor;
  · intro hx
    have h_eval : (Encodable.encode x) ∈ c.eval (Encodable.encode (p, y)) := by
      simp_all +decide [ produces, Part.mem_map_iff ];
    exact Nat.Partrec.Code.evaln_complete.mp h_eval
  · rintro ⟨ k, hk ⟩;
    have h_eval : Encodable.encode x ∈ c.eval (Encodable.encode (p, y)) := by
      exact Nat.Partrec.Code.evaln_sound hk
    simp_all +decide [ Part.mem_map_iff ]

/-
The accepted finset grows with the stage.
-/
lemma aprioriAcc_mono (c : Nat.Partrec.Code) (s : ℕ) (x y : BitString) :
    aprioriAcc c s x y ⊆ aprioriAcc c (s + 1) x y := by
  intro p hp;
  rw [ mem_aprioriAcc ] at *;
  exact ⟨ Nat.le_succ_of_le hp.1, by rw [ Nat.Partrec.Code.evaln_mono ( Nat.le_succ s ) ] ; aesop ⟩

/-
The dyadic value of the stage-`s` numerator is the finite sum of program weights
over the accepted finset.
-/
lemma dyadicValue_aprioriApprox (c : Nat.Partrec.Code) (s : ℕ) (x y : BitString) :
    dyadicValue (aprioriApprox c s x y) s = ∑ p ∈ aprioriAcc c s x y, progWeight p := by
  convert Finset.sum_congr rfl fun p hp => ?_ using 1;
  any_goals exact fun p ↦ ( 2 ^ ( s - p.length ) : ℝ≥0∞ ) / ( 2 ^ s : ℝ≥0∞ );
  · unfold dyadicValue aprioriApprox aprioriAcc;
    rw [ List.sum_toFinset ];
    · induction ( aprioriAcceptedList c s x y ) <;> simp_all +decide [ div_eq_mul_inv, mul_comm ];
      rw [ mul_add, mul_comm ] ; aesop;
    · exact aprioriAcceptedList_nodup c s x y
  · rw [ ENNReal.div_eq_inv_mul ];
    rw [ show ( 2 ^ s : ℝ≥0∞ ) = 2 ^ ( s - List.length p ) * 2 ^ List.length p by rw [ ← pow_add, Nat.sub_add_cancel ( show List.length p ≤ s from by simpa using mem_aprioriAcc.mp hp |>.1 ) ] ] ; norm_num [ progWeight ];
    rw [ ENNReal.mul_inv, mul_comm ];
    · rw [ ← mul_assoc, ENNReal.mul_inv_cancel ] <;> norm_num;
      exact ENNReal.inv_pow
    · exact Or.inl <| by positivity;
    · exact Or.inl <| ENNReal.pow_ne_top <| by norm_num;

/-- Monotonicity of the dyadic approximation in the stage. -/
lemma aprioriApprox_mono (c : Nat.Partrec.Code) (s : ℕ) (x y : BitString) :
    dyadicValue (aprioriApprox c s x y) s
      ≤ dyadicValue (aprioriApprox c (s + 1) x y) (s + 1) := by
  rw [dyadicValue_aprioriApprox, dyadicValue_aprioriApprox]
  exact Finset.sum_le_sum_of_subset (aprioriAcc_mono c s x y)

/-
The supremum of the dyadic approximation is the a priori semimeasure.
-/
lemma aprioriApprox_iSup {M : Map} (c : Nat.Partrec.Code)
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (M a)))
    (x y : BitString) :
    ⨆ s, dyadicValue (aprioriApprox c s x y) s = aprioriMeasure M x y := by
  -- Rewrite the left-hand side using the definition of aprioriApprox.
  have h_lhs : ⨆ s, dyadicValue (aprioriApprox c s x y) s = ⨆ s, ∑ p ∈ Kolmogorov.aprioriAcc c s x y, Kolmogorov.progWeight p := by
    exact iSup_congr fun s => dyadicValue_aprioriApprox c s x y;
  refine le_antisymm ( h_lhs ▸ ?_ ) ( h_lhs ▸ ?_ );
  · refine iSup_le fun s => ?_;
    classical
    refine le_trans ?_ ( ENNReal.sum_le_tsum (f := fun p => if produces M p y x then Kolmogorov.progWeight p else 0) ( Kolmogorov.aprioriAcc c s x y ) );
    refine Finset.sum_le_sum fun p hp => ?_;
    rw [ if_pos ];
    exact produces_iff_evaln c hc p x y |>.2 ⟨ s, by simpa using mem_aprioriAcc.mp hp |>.2 ⟩;
  · refine ENNReal.tsum_eq_iSup_sum.trans_le ?_;
    refine iSup_le fun S => ?_;
    -- For each $p \in S$, if $produces M p y x$, then there exists $k_p$ such that $Nat.Partrec.Code.evaln k_p c (Encodable.encode (p, y)) = some (Encodable.encode x)$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ p ∈ S, produces M p y x → Nat.Partrec.Code.evaln k c (Encodable.encode (p, y)) = some (Encodable.encode x) ∧ p.length ≤ k := by
      have h_finite : ∀ p ∈ S, produces M p y x → ∃ k : ℕ, Nat.Partrec.Code.evaln k c (Encodable.encode (p, y)) = some (Encodable.encode x) ∧ p.length ≤ k := by
        intro p hp hproduces
        obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.Partrec.Code.evaln k c (Encodable.encode (p, y)) = some (Encodable.encode x) :=
          (produces_iff_evaln c hc p x y).mp hproduces
        exact ⟨ k + p.length, by simpa using Nat.Partrec.Code.evaln_mono ( by linarith ) hk, by linarith ⟩;
      choose! k hk₁ hk₂ using h_finite;
      use Finset.sup S k;
      exact fun p hp hp' => ⟨ Nat.Partrec.Code.evaln_mono ( Finset.le_sup ( f := k ) hp ) ( hk₁ p hp hp' ), le_trans ( hk₂ p hp hp' ) ( Finset.le_sup ( f := k ) hp ) ⟩;
    refine le_trans ?_ ( le_iSup _ k );
    rw [ ← Finset.sum_filter ];
    refine Finset.sum_le_sum_of_subset ?_;
    intro p hp; specialize hk p; simp_all +decide [ Kolmogorov.mem_aprioriAcc ] ;

/-- Compatibility alias for the reusable power helper. -/
lemma primrec_two_pow : Primrec (fun n : ℕ => 2 ^ n) :=
  Computability.primrec_two_pow

/-
The numerator function is computable in `(s, x, y)`.
-/
lemma aprioriApprox_computable (c : Nat.Partrec.Code) :
    Computable (fun q : ℕ × BitString × BitString => aprioriApprox c q.1 q.2.1 q.2.2) := by
  -- Prove `Primrec` of the function and finish with `.to_comp`.
  have h_primrec : Primrec (fun q : ℕ × BitString × BitString => aprioriApprox c q.1 q.2.1 q.2.2) := by
    convert Primrec.comp ( show Primrec ( fun l : List ℕ => l.sum ) from ?_ ) ( show Primrec ( fun q : ℕ × BitString × BitString => ( boundedPrograms q.1 ).map ( fun p => if Nat.Partrec.Code.evaln q.1 c ( Encodable.encode ( p, q.2.2 ) ) = some ( Encodable.encode q.2.1 ) then 2 ^ ( q.1 - p.length ) else 0 ) ) from ?_ ) using 1;
    · ext ⟨s, ⟨x, y⟩⟩; simp [aprioriApprox, aprioriAcceptedList];
      induction ( boundedPrograms s ) <;> aesop;
    · -- The sum of a list is primitive recursive.
      have h_sum : Primrec (fun l : List ℕ => l.foldr (· + ·) 0) :=
        Primrec.list_foldr Primrec.id (Primrec.const 0)
          (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
            (Primrec.snd.comp Primrec.snd)).to₂
      simpa [List.sum] using h_sum
    · refine Primrec.list_map ?_ ?_;
      · exact Primrec.comp primrec_boundedPrograms ( Primrec.fst );
      · refine Primrec.ite ?_ ?_ ?_;
        · refine ⟨ ?_, ?_ ⟩;
          infer_instance;
          have h_evaln : Primrec (fun p : ℕ × BitString × BitString => Nat.Partrec.Code.evaln p.1 c (Encodable.encode (p.2.1, p.2.2))) := by
            exact Nat.Partrec.Code.primrec_evaln.comp
              (Primrec.pair
                (Primrec.pair Primrec.fst (Primrec.const c))
                (Primrec.encode.comp
                  (Primrec.pair
                    (Primrec.fst.comp Primrec.snd)
                    (Primrec.snd.comp Primrec.snd))))
          convert Primrec.eq.comp ( h_evaln.comp ( show Primrec ( fun p : ( ℕ × BitString × BitString ) × BitString => ( p.1.1, p.2, p.1.2.2 ) ) from ?_ ) ) ( show Primrec ( fun p : ( ℕ × BitString × BitString ) × BitString => some ( Encodable.encode p.1.2.1 ) ) from ?_ ) using 1;
          · exact Iff.symm primrecPred_iff_primrec_decide
          · exact Primrec.pair ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.pair ( Primrec.snd ) ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) );
          · convert Primrec.option_some.comp ( show Primrec ( fun p : ( ℕ × BitString × BitString ) × BitString => Encodable.encode p.1.2.1 ) from ?_ ) using 1;
            exact Primrec.encode.comp ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst ) ) );
        · exact Primrec.comp ( primrec_two_pow ) ( Primrec.nat_sub.comp ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.list_length.comp ( Primrec.snd ) ) );
        · exact Primrec.const 0;
  exact h_primrec.to_comp

end AprioriLSC

/-- **Lower-semicomputability of the a priori semimeasure** (assembled from the
staged-`evaln` dyadic approximation `aprioriApprox`). -/
theorem aprioriMeasure_isLSC (M : Map) (hM : IsPrefixDecompressor M) :
    IsLSC (aprioriMeasure M) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hM.isDecompressor
  refine ⟨aprioriApprox c, ?_, ?_, ?_⟩
  · intro s out ctx; exact aprioriApprox_mono c s out ctx
  · intro out ctx; exact aprioriApprox_iSup c hc out ctx
  · exact aprioriApprox_computable c

/-- **Kraft–Chaitin realization of a prefix decompressor's a priori semimeasure**
(coding theorem, hard direction).

For every prefix decompressor `M`, there is a prefix decompressor `M'` and a
constant `c₀` such that `M'` realizes the a priori semimeasure `m_M` up to `c₀`:
`2^{-c₀} · m_M(x | y) ≤ 2^{-KP_{M'}(x | y)}` for all `x, y`.

This is the standard Kraft–Chaitin construction: `m_M` is a lower-semicomputable
conditional subsemimeasure (`aprioriMeasure_isLSC`, `tsum_aprioriMeasure_le_one`),
and the Kraft–Chaitin algorithm assigns to each output `x` a prefix-free program of
length `⌈-log m_M(x | y)⌉ + O(1)`, yielding a prefix decompressor with the stated
bound.

The proof now reduces (with no remaining coding content) to the abstract engine
`kraftChaitin_realization_bound` applied at subnormalization level `d = 0`, fed by
lower-semicomputability `aprioriMeasure_isLSC` and the normalization
`tsum_aprioriMeasure_le_one`. -/
theorem aprioriMeasure_prefix_realization (M : Map) (hM : IsPrefixDecompressor M) :
    ∃ M' : Map, IsPrefixDecompressor M' ∧ ∃ c₀ : ℕ, ∀ x y : BitString,
      (2 : ℝ≥0∞)⁻¹ ^ c₀ * aprioriMeasure M x y ≤ complexityWeight (KP M' x y) := by
  -- The a priori semimeasure is lower-semicomputable and (at level `d = 0`)
  -- globally subnormalized (`∑_x m_M(x | y) ≤ 1`), so the abstract Kraft–Chaitin
  -- engine realizes it directly.
  refine kraftChaitin_realization_bound (aprioriMeasure_isLSC M hM) 0 (fun y => ?_)
  rw [pow_zero]
  exact tsum_aprioriMeasure_le_one M y hM.isPrefixMachine

/-- **Coding theorem, optimal form (`≤×`).** For an optimal prefix decompressor
`U` and any prefix decompressor `M`, the a priori semimeasure `m_M` is dominated
by the optimal complexity weight `2^{-KP_U}` up to a constant:
`2^{-c} · m_M(x | y) ≤ 2^{-KP_U(x | y)}`.

This is the Kraft–Chaitin realization `aprioriMeasure_prefix_realization`
followed by the optimal-transfer lemma
`complexityWeight_dominates_of_prefix_realization`: the realizer `M'` is absorbed
into `U`'s invariance bound. -/
theorem aprioriMeasure_le_complexityWeight_optimal {U : Map}
    (hU : IsOptimalPrefixConditional U) {M : Map} (hM : IsPrefixDecompressor M) :
    ∃ c : ℕ, ∀ x y : BitString,
      (2 : ℝ≥0∞)⁻¹ ^ c * aprioriMeasure M x y ≤ complexityWeight (KP U x y) := by
  obtain ⟨M', hM', c₀, hreal⟩ := aprioriMeasure_prefix_realization M hM
  exact complexityWeight_dominates_of_prefix_realization hU hM' hreal

end Kolmogorov
