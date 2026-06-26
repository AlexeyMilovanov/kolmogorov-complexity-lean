/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.PairMarginal
import KolmogorovMathlib.AlgorithmicProbability.OptimalCoding
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.AlgorithmicProbability.Computability.Tuple

/-!
# Conditional Coding for the Pair-Section Semimeasure

This module isolates the genuinely hard Chapter-4 (SUV §4.5) content of the
*lower* direction of prefix symmetry of information into precise coding
obligations, and proves all of the connecting algebra around them.

The reduction theorem `KPPair_chain_lower_of_conditional_coding`
(`KolmogorovMathlib.Prefix.Symmetry`) shows that the whole counting content of
the Levin–Gács lower direction collapses to a single conditional coding bound
`hcode`: at `k = K(x)`, the conditional weight `2^{-K(y | x, k)}` dominates the
scaled section mass `2^{-c₁} · m_U(⟨x,y⟩) · 2^{k}`. This file assembles exactly
that bound (`section_coding_bound`) from two independent obligations:

* `pairMarginal_coding_bound` — the **marginal coding bound** at `k = K(x)`: the
  coding theorem applied to the lower-semicomputable pair marginal
  `x ↦ pairMarginal U x` (whose normalization `∑_x pairMarginal U x ≤ 1` is
  already proved in `PairMarginal`). It is stated in the *true* direction, with
  the constant on the side that makes it provable: `pairMarginal U x · 2^{k} ≤ 2^{c₂}`
  at `k = K(x)`. The constant-free form `pairMarginal U x ≤ 2^{-K(x)}` (i.e.
  section mass `≤ 1`) is **false** — the coding theorem only gives
  `pairMarginal U x ≤ 2^{c₂} · 2^{-K(x)}` with a genuine positive overhead `c₂`.

* `conditional_coding_section_realization` — the **conditional Kraft–Chaitin
  realization** of the scaled section family `y ↦ m_U(⟨x,y⟩) · 2^{k}`. Because the
  section is only *constant*-subnormalized (mass `≤ 2^{d}`, not `≤ 1`), the
  realization is stated uniformly in the subnormalization level `d`: for each `d`
  there is a prefix decompressor `M` and loss `c₀` realizing every section of
  mass `≤ 2^{d}` (per-context guard `∑_y m_U(⟨x,y⟩) · 2^{k} ≤ 2^{d}`) up to `c₀`.
  The guard keeps the statement honest: a truncated Kraft–Chaitin machine
  (down-scaling by the fixed `2^{-d}` it hardcodes) realizes the section only
  where its running mass stays `≤ 2^{d}`. The loss `c₀` absorbs the `d`-level
  overhead. No false lower-semicomputability claim about a `K(x)`-guarded object
  is made — the raw section is l.s.c.; the guard restricts where the bound holds.

The glue (`section_coding_bound`) is pure `ℝ≥0∞`/exponent algebra: the marginal
bound puts the section mass at `≤ 2^{c₂}` at `k = K(x)` (via `pairSection_tsum`),
which discharges the realization guard at level `d = c₂`; `M`'s realization is
transferred to the optimal `U` by `optimalPrefix_complexityWeight_bound`, and the
constants combine with `pow_add`. The guard is never instantiated at `k ≠ K(x)`,
so the false unguarded `∀ k` coding bound never appears.
-/

namespace Kolmogorov

open scoped ENNReal
open Computability

/-- **The scaled pair section as a total function of `(output y, context ctx)`.**

For a context that decodes as `pairCode x (natCode k)`, this returns the scaled
section value `m_U(⟨x,y⟩) · 2^{k}`; on any context not of that form it returns `0`.
Totality is obtained via a supremum over all valid decodings `(x, k)` of `ctx`
(there is at most one, by injectivity of `pairCode`/`natCode`), which keeps the
function defined on every `BitString` so it can carry a lower-semicomputability
witness. -/
noncomputable def scaledSection (U : Map) (y ctx : BitString) : ℝ≥0∞ :=
  ⨆ (x : BitString) (k : ℕ) (_ : ctx = pairCode x (natCode k)),
    aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k

/-- **Evaluation of the scaled section on a faithful context.** On the context
`pairCode x (natCode k)`, the supremum collapses to the single matching summand,
because `pairCode` and `natCode` are injective. -/
theorem scaledSection_eq (U : Map) (x y : BitString) (k : ℕ) :
    scaledSection U y (pairCode x (natCode k))
      = aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k := by
  apply le_antisymm
  · -- Every valid decoding `(x', k')` of `pairCode x (natCode k)` equals `(x, k)`.
    refine iSup_le fun x' => iSup_le fun k' => iSup_le fun hxk => ?_
    have hpair : (fun p : BitString × BitString => pairCode p.1 p.2) (x, natCode k)
        = (fun p : BitString × BitString => pairCode p.1 p.2) (x', natCode k') := hxk
    have hxx : (x, natCode k) = (x', natCode k') := pairCode_injective hpair
    obtain ⟨hx, hnat⟩ := Prod.mk.injEq .. ▸ hxx
    have hk : k = k' := natCode_injective hnat
    subst hx; subst hk
    exact le_refl _
  · -- The matching summand `(x, k)` is below the supremum.
    exact le_iSup_of_le x (le_iSup_of_le k (le_iSup_of_le rfl (le_refl _)))

/-! **Lower-semicomputability of the scaled pair section.** The section family
`(y, ctx) ↦ scaledSection U y ctx` is lower-semicomputable (`IsLSC`): on a faithful
context it is the a priori semimeasure (l.s.c. via `aprioriMeasure_isLSC`) scaled by
the computable factor `2^{k}` recovered from the context, and `0` elsewhere.

This is the computability half of the conditional construction, assembled from
the a priori l.s.c. approximation `aprioriApprox` and a computable pair-context
decoder. -/
section ScaledLSC

/-- Decoder for the unary-coded second index `k` of a `pairCode x (natCode k)`
context: the leading run of `true`s after the first-component block. -/
def decodeNat (ctx : BitString) : ℕ :=
  ((ctx.drop (2 * (ctx.takeWhile id).length + 1)).takeWhile id).length

/-- The decoder recovers the second index of a faithful pair-context. -/
lemma decodeNat_pairCode (x : BitString) (k : ℕ) :
    decodeNat (pairCode x (natCode k)) = k := by
  -- Unfold `decodeNat` and `pairCode` to express `decodeNat (pairCode x (natCode k))` in terms of `takeWhile` and `drop`.
  simp [decodeNat, pairCode];
  simp +decide [ two_mul, List.drop_append ];
  simp +decide [ List.drop_eq_nil_of_le, natCode ]

/-- The second-index decoder is computable. -/
lemma decodeNat_computable : Computable decodeNat := by
  have h_len : Primrec (fun z : BitString => (z.takeWhile id).length) :=
    (Primrec.list_findIdx Primrec.id (Primrec.not.comp Primrec.snd).to₂).of_eq
      (fun z => (takeWhile_id_length_eq_findIdx z).symm)
  have h_skip : Primrec (fun ctx : BitString => 2 * (ctx.takeWhile id).length + 1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) h_len) (Primrec.const 1)
  have h_drop : Primrec (fun ctx : BitString => ctx.drop (2 * (ctx.takeWhile id).length + 1)) :=
    primrec_list_drop.comp Primrec.id h_skip
  exact ((h_len.comp h_drop).of_eq (fun _ => rfl)).to_comp

/-
A context decodes back to itself under `(decodeFirst, decodeNat)` exactly when
it is a genuine pair code.
-/
lemma pairCode_decode_eq_iff (ctx : BitString) :
    pairCode (decodeFirst ctx) (natCode (decodeNat ctx)) = ctx
      ↔ ∃ x k, ctx = pairCode x (natCode k) := by
  constructor <;> intro h;
  · exact ⟨ _, _, h.symm ⟩;
  · obtain ⟨ x, k, rfl ⟩ := h; simp +decide [ decodeFirst_pairCode, decodeNat_pairCode ] ;

/-
The scaled section vanishes on contexts that are not genuine pair codes.
-/
lemma scaledSection_eq_zero_of_not_pairCode (U : Map) (out ctx : BitString)
    (h : ∀ x k, ctx ≠ pairCode x (natCode k)) : scaledSection U out ctx = 0 := by
  unfold scaledSection;
  simp +decide [ h ]

/-- The staged numerator for the scaled section: the a priori numerator on the
decoded first component, scaled by `2^{k}`, guarded by the decode-validity check. -/
def scaledApprox (c : Nat.Partrec.Code) (s : ℕ) (out ctx : BitString) : ℕ :=
  if pairCode (decodeFirst ctx) (natCode (decodeNat ctx)) = ctx then
    aprioriApprox c s (pairCode (decodeFirst ctx) out) [] * 2 ^ (decodeNat ctx)
  else 0

/-
Scaling a dyadic value by `2^k` in both numerator and value.
-/
lemma dyadicValue_mul_pow (n s k : ℕ) :
    dyadicValue (n * 2 ^ k) s = dyadicValue n s * (2 : ℝ≥0∞) ^ k := by
  cases s <;> simp +decide [ dyadicValue ] ; ring_nf;
  rw [ ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul ] ; ring_nf

/-
Monotonicity of the scaled-section approximation in the stage.
-/
lemma scaledApprox_mono (c : Nat.Partrec.Code) (s : ℕ) (out ctx : BitString) :
    dyadicValue (scaledApprox c s out ctx) s
      ≤ dyadicValue (scaledApprox c (s + 1) out ctx) (s + 1) := by
  by_cases h : pairCode ( decodeFirst ctx ) ( natCode ( decodeNat ctx ) ) = ctx <;> simp_all +decide [ scaledApprox ];
  · convert mul_le_mul_left ( aprioriApprox_mono c s ( pairCode ( decodeFirst ctx ) out ) [] ) ( 2 ^ decodeNat ctx : ℝ≥0∞ ) using 1; all_goals convert dyadicValue_mul_pow _ _ _ using 1;
  · unfold dyadicValue; norm_num;

/-
The supremum of the scaled-section approximation is the scaled section.
-/
lemma scaledApprox_iSup {U : Map} (c : Nat.Partrec.Code)
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (U a)))
    (out ctx : BitString) :
    ⨆ s, dyadicValue (scaledApprox c s out ctx) s = scaledSection U out ctx := by
  by_cases h : pairCode (decodeFirst ctx) (natCode (decodeNat ctx)) = ctx;
  · calc
      ⨆ s, dyadicValue (scaledApprox c s out ctx) s
          = ⨆ s, dyadicValue (aprioriApprox c s (pairCode (decodeFirst ctx) out) [] *
              2 ^ decodeNat ctx) s := by
            apply iSup_congr
            intro s
            simp [scaledApprox, h]
      _ = ⨆ s, dyadicValue (aprioriApprox c s (pairCode (decodeFirst ctx) out) []) s *
              (2 : ℝ≥0∞) ^ decodeNat ctx := by
            apply iSup_congr
            intro s
            rw [dyadicValue_mul_pow]
      _ = (⨆ s, dyadicValue (aprioriApprox c s (pairCode (decodeFirst ctx) out) []) s) *
              (2 : ℝ≥0∞) ^ decodeNat ctx := by
            rw [ENNReal.iSup_mul]
      _ = aprioriMeasure U (pairCode (decodeFirst ctx) out) [] *
              (2 : ℝ≥0∞) ^ decodeNat ctx := by
            rw [aprioriApprox_iSup c hc]
      _ = scaledSection U out ctx := by
            rw [← h, scaledSection_eq]
            simp [decodeFirst_pairCode, decodeNat_pairCode]
  · rw [ scaledSection_eq_zero_of_not_pairCode ];
    · simp [scaledApprox, h];
      unfold dyadicValue; norm_num;
    · grind +suggestions

/-- The decode-then-reencode candidate context is computable. -/
lemma reencode_computable :
    Computable (fun ctx : BitString =>
      pairCode (decodeFirst ctx) (natCode (decodeNat ctx))) := by
  have h : (fun ctx : BitString => pairCode (decodeFirst ctx) (natCode (decodeNat ctx)))
      = (fun p : BitString × BitString => pairCode p.1 p.2) ∘
          (fun ctx : BitString => (decodeFirst ctx, natCode (decodeNat ctx))) := rfl
  rw [h]
  exact pairCode_computable.comp
    (decodeFirst_computable.pair (natCode_computable.comp decodeNat_computable))

/-
The (unguarded) scaled numerator value is computable.
-/
lemma scaledApproxVal_computable (c : Nat.Partrec.Code) :
    Computable (fun q : ℕ × BitString × BitString =>
      aprioriApprox c q.1 (pairCode (decodeFirst q.2.2) q.2.1) [] * 2 ^ (decodeNat q.2.2)) := by
  have h_comp : Computable (fun q : ℕ × BitString × BitString => aprioriApprox c q.1 (pairCode (decodeFirst q.2.2) q.2.1) []) := by
    convert aprioriApprox_computable c |> Computable.comp <| _ using 1;
    rotate_left;
    exact fun q => ( q.1, pairCode ( decodeFirst q.2.2 ) q.2.1, [] );
    · convert Computable.pair ( Computable.fst ) ( Computable.pair ( Computable.comp ( pairCode_computable ) ( Computable.pair ( decodeFirst_computable.comp ( Computable.snd.comp Computable.snd ) ) ( Computable.fst.comp Computable.snd ) ) ) ( Computable.const [] ) ) using 1;
    · rfl;
  convert Computable.comp ( _ : Computable fun q : ℕ × ℕ => q.1 * 2 ^ q.2 ) ( h_comp.pair ( _ : Computable fun q : ℕ × BitString × BitString => decodeNat q.2.2 ) ) using 1;
  · have h_mul : Computable (fun q : ℕ × ℕ => q.1 * 2 ^ q.2) := by
      have h_exp : Computable (fun n : ℕ => 2 ^ n) := primrec_two_pow.to_comp
      have h_mul : Computable (fun q : ℕ × ℕ => q.1 * q.2) := by
        convert Primrec.to_comp ( show Primrec ( fun q : ℕ × ℕ => q.1 * q.2 ) from ?_ ) using 1;
        exact Primrec.nat_mul.comp ( Primrec.fst ) ( Primrec.snd );
      convert h_mul.comp ( Computable.fst.pair ( h_exp.comp Computable.snd ) ) using 1;
    exact h_mul;
  · exact decodeNat_computable.comp ( Computable.snd.comp Computable.snd )

/-
The scaled-section numerator is computable.
-/
lemma scaledApprox_computable (c : Nat.Partrec.Code) :
    Computable (fun q : ℕ × BitString × BitString => scaledApprox c q.1 q.2.1 q.2.2) := by
  apply Computable.of_eq;
  convert Computable.cond _ _ _;
  exact fun q => decide ( pairCode ( decodeFirst q.2.2 ) ( natCode ( decodeNat q.2.2 ) ) = q.2.2 );
  exact fun q => aprioriApprox c q.1 ( pairCode ( decodeFirst q.2.2 ) q.2.1 ) [] * 2 ^ ( decodeNat q.2.2 );
  exact fun _ => 0;
  · have h_reencode_computable :
        Computable (fun q : BitString => pairCode (decodeFirst q) (natCode (decodeNat q))) :=
      reencode_computable
    have h_eq_computable : Computable (fun q : BitString × BitString => decide (q.1 = q.2)) := by
      have h_eq_primrec : Primrec (fun q : BitString × BitString => decide (q.1 = q.2)) := by
        convert Primrec.eq.comp Primrec.fst Primrec.snd using 1
        exact Iff.symm primrecPred_iff_primrec_decide
      exact Primrec.to_comp h_eq_primrec
    convert h_eq_computable.comp ( h_reencode_computable.comp ( Computable.snd.comp Computable.snd ) |> Computable.pair <| Computable.snd.comp Computable.snd ) using 1;
  · convert scaledApproxVal_computable c using 1;
  · exact Computable.const 0;
  · unfold scaledApprox; aesop;

end ScaledLSC

/-- **Lower-semicomputability of the scaled pair section**, assembled from
`scaledApprox`. -/
theorem scaledSection_isLSC (U : Map) (hU : IsPrefixDecompressor U) :
    IsLSC (scaledSection U) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  exact ⟨scaledApprox c, fun s out ctx => scaledApprox_mono c s out ctx,
    fun out ctx => scaledApprox_iSup c hc out ctx, scaledApprox_computable c⟩

/-- **Conditional Kraft–Chaitin realization of the scaled pair section** (SUV
§4.5), uniform in the subnormalization level `d`.

For every level `d`, a single prefix decompressor `M` (depending on `d`) realizes
the lower-semicomputable section family `y ↦ m_U(⟨x,y⟩) · 2^{k}` — up to a uniform
constant `c₀` (absorbing the `d`-overhead) — at every context `(x, k)` where the
section is `2^{d}`-subnormalized, i.e. where the per-context guard
`∑_y m_U(⟨x,y⟩) · 2^{k} ≤ 2^{d}` holds.

The output is a conditional program for `y` in the faithful context
`pairCode x (natCode k)` (definitionally `prefixComplexityContext x k`). The guard
is what makes the statement true: the truncated Kraft–Chaitin construction
down-scales by the fixed factor `2^{-d}` it hardcodes (yielding a genuine
subsemimeasure of mass `≤ 1`) and emits prefix codes for `y` only while the
running mass stays bounded; the `2^{-d}` down-scale costs an additive `d` in code
length, folded into `c₀`.

The proof now reduces to the abstract engine: the scaled section is l.s.c.
(`scaledSection_isLSC`); dynamic truncation (`IsLSC.truncate`) caps its global mass
at `2^{d}` while leaving it untouched wherever the guard holds; and
`kraftChaitin_realization_bound` realizes the truncated function. `scaledSection_eq`
identifies the per-context guard with the truncation's mass bound. The guard is
never dropped, so the false unguarded `∀ k` bound is never asserted. -/
theorem conditional_coding_section_realization (U : Map)
    (hU : IsOptimalPrefixConditional U) (d : ℕ) :
    ∃ M : Map, IsPrefixDecompressor M ∧ ∃ c₀ : ℕ,
      ∀ (x : BitString) (k : ℕ),
        (∑' y : BitString, aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)
            ≤ (2 : ℝ≥0∞) ^ d →
        ∀ y : BitString,
          (2 : ℝ≥0∞)⁻¹ ^ c₀ * (aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)
            ≤ complexityWeight (KP M y (pairCode x (natCode k))) := by
  -- Truncate the (globally l.s.c.) scaled section to a global `2^{d}`-mass bound,
  -- then feed it to the abstract Kraft–Chaitin engine. Where the per-context guard
  -- holds, the truncation is inert, so the realization is for the raw section.
  obtain ⟨g, hg_lsc, hg_sum, hg_agree⟩ :=
    (scaledSection_isLSC U hU.isPrefixDecompressor).truncate d
  obtain ⟨M, hM, c₀, hreal⟩ := kraftChaitin_realization_bound hg_lsc d hg_sum
  refine ⟨M, hM, c₀, fun x k hguard y => ?_⟩
  -- The guard for `(x, k)` is exactly the truncation's per-context mass bound for
  -- the section at context `pairCode x (natCode k)` (via `scaledSection_eq`).
  have hctx_sum :
      (∑' out : BitString, scaledSection U out (pairCode x (natCode k)))
        ≤ (2 : ℝ≥0∞) ^ d := by
    rw [tsum_congr (fun y => scaledSection_eq U x y k)]
    exact hguard
  have hagree := hg_agree (pairCode x (natCode k)) hctx_sum y
  rw [scaledSection_eq] at hagree
  have hM_bound := hreal y (pairCode x (natCode k))
  rwa [hagree] at hM_bound

/-- **Assembled conditional coding bound `hcode`.** Combines the marginal coding
bound and the conditional Kraft–Chaitin realization into exactly the hypothesis
consumed by `KPPair_chain_lower_of_conditional_coding`.

The proof is pure `ℝ≥0∞`/exponent algebra:

* the marginal bound puts the section mass at `≤ 2^{c₂}` at `k = K(x)` (via
  `pairSection_tsum`), discharging the realization guard at level `d = c₂`;
* the realization gives `2^{-c₀} · section ≤ 2^{-K_M(y | x,k)}`;
* `optimalPrefix_complexityWeight_bound` transfers `M`'s weight to `U`, absorbing
  the coding overhead into the constant via `pow_add`.

The guard `(k : ENat) = KP U x []` is definitionally `HasPrefixComplexityValue`,
and `pairCode x (natCode k)` is definitionally `prefixComplexityContext x k`, so
this is `defeq` to the `hcode` shape required in `Symmetry`. -/
theorem section_coding_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c₁ : ℕ, ∀ (x y : BitString) (k : ℕ), (k : ENat) = KP U x [] →
      (2 : ℝ≥0∞)⁻¹ ^ c₁ * (aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)
        ≤ complexityWeight (KP U y (pairCode x (natCode k))) := by
  obtain ⟨c₂, hmarg⟩ := pairMarginal_coding_bound U hU
  obtain ⟨M, hM, c₀, hreal⟩ := conditional_coding_section_realization U hU c₂
  obtain ⟨c₁, hopt⟩ := optimalPrefix_complexityWeight_bound hU hM
  refine ⟨c₀ + c₁, fun x y k hk => ?_⟩
  -- The marginal coding bound puts the section mass at `≤ 2^{c₂}` at `k = K(x)`,
  -- discharging the realization guard at level `d = c₂`.
  have hsemi : (∑' y : BitString, aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)
      ≤ (2 : ℝ≥0∞) ^ c₂ := by
    exact pairSection_tsum_le_of_marginal_scaled U x k c₂ (hmarg x k hk)
  have hM_bound := hreal x k hsemi y
  -- Transfer the realization from `M` to the optimal `U`, absorbing `c₀` via `pow_add`.
  calc (2 : ℝ≥0∞)⁻¹ ^ (c₀ + c₁)
          * (aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)
      = (2 : ℝ≥0∞)⁻¹ ^ c₁
          * ((2 : ℝ≥0∞)⁻¹ ^ c₀
            * (aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)) := by
        rw [pow_add]; ring
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c₁ * complexityWeight (KP M y (pairCode x (natCode k))) :=
        mul_le_mul_right hM_bound _
    _ ≤ complexityWeight (KP U y (pairCode x (natCode k))) :=
        hopt y (pairCode x (natCode k))

end Kolmogorov
