/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure.Enumeration.Defs

namespace Kolmogorov

open scoped ENNReal

/-!
# Evaluation Helpers for Enumeration

Helper lemmas for evaluating decoded codes where they previously appeared inline.
-/

lemma dyadicValue_evalnDecodedScaled_le_of_eval_eq_some
    {c : Nat.Partrec.Code} {s' i : ℕ} {out ctx : BitString} {v : ℕ}
    (hc : Nat.Partrec.Code.eval c (Encodable.encode (s', out, ctx)) = some v)
    (hle : s' ≤ i) :
    dyadicValue (evalnDecodedScaled i (Encodable.encode c) (s', out, ctx) (i - s')) i
      ≤ dyadicValue v s' := by
  have h_term : Computability.evalnDecoded i (Encodable.encode c) (s', out, ctx) = some v ∨
                Computability.evalnDecoded i (Encodable.encode c) (s', out, ctx) = none := by
    cases h : Computability.evalnDecoded i (Encodable.encode c) (s', out, ctx)
    · exact Or.inr rfl
    · have := Nat.Partrec.Code.evaln_sound (by
        simpa [Computability.evalnDecoded, Encodable.encodek] using h)
      simp_all [Part.mem_eq]
  cases h_term with
  | inr h => simp [h, dyadicValue, evalnDecodedScaled]
  | inl h =>
    simp [h, dyadicValue, evalnDecodedScaled]
    norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_add ]
    rw [ show ( 2 ^ i : ℝ≥0∞ ) = 2 ^ ( i - s' ) * 2 ^ s' by rw [ ← pow_add, Nat.sub_add_cancel hle ] ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm ]
    simp [ ENNReal.mul_inv ]
    simp [ mul_left_comm ( 2 ^ ( i - s' ) : ℝ≥0∞ ), ENNReal.mul_inv_cancel ]

lemma dyadicValue_evalnDecodedScaled_of_evaln_eq_some
    {c : Nat.Partrec.Code} {s k : ℕ} {out ctx : BitString} {v : ℕ}
    (hk : Nat.Partrec.Code.evaln k c (Encodable.encode (s, out, ctx)) = some v) :
    dyadicValue (evalnDecodedScaled (max s k) (Encodable.encode c) (s, out, ctx) (max s k - s)) (max s k)
      = dyadicValue v s := by
  have hevaln : Computability.evalnDecoded (max s k) (Encodable.encode c) (s, out, ctx) = some v := by
    simpa [Computability.evalnDecoded, Encodable.encodek] using
      Nat.Partrec.Code.evaln_mono (Nat.le_max_right s k) hk
  simp [evalnDecodedScaled, hevaln, dyadicValue]
  norm_num [ pow_add, pow_one, pow_mul, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ]
  rw [ show ( 2 : ℝ≥0∞ ) ^ max s k = ( 2 : ℝ≥0∞ ) ^ ( max s k - s ) * ( 2 : ℝ≥0∞ ) ^ s by rw [ ← pow_add, Nat.sub_add_cancel ( le_max_left s k ) ] ] ; ring_nf
  simp [ mul_comm, mul_left_comm, ENNReal.mul_inv ]
  rw [ mul_left_comm ( 2 ^ ( max s k - s ) : ℝ≥0∞ ), ENNReal.mul_inv_cancel ( by norm_num ) ( by norm_num ), mul_one ]

end Kolmogorov
