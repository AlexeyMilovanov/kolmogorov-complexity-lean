/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.ConditionalCoding.Basic
import KolmogorovMathlib.AlgorithmicProbability.Computability.Tuple

/-!
# Lower-semicomputability of the scaled pair section
-/

namespace Kolmogorov

open scoped ENNReal
open Computability

section ScaledLSC

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

end Kolmogorov
