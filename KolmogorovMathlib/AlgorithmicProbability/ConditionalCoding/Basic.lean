/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.PairProjection

/-!
# Conditional Coding for the Pair-Section Semimeasure (Definitions)
-/

namespace Kolmogorov

open scoped ENNReal

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

end Kolmogorov
