/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure.Enumeration.Defs
import KolmogorovMathlib.AlgorithmicProbability.Computability.Tuple

namespace Kolmogorov

open scoped ENNReal
open Computability

/-
**Sup-preservation of the dovetailed enumeration (SUV/LV universality core).**

For any jointly computable approximation `approx`, the enumeration `approxEnum`
contains an index `i` whose stage supremum reproduces that of `approx`. This is the
correct *limit/sup-preservation* statement (it does **not** demand exact stagewise
reproduction, which is genuinely impossible for a total computable family): only
the suprema must agree.

Proof idea. Totalise `approx` to `h : ℕ → ℕ`, `h (Encodable.encode (s', out, ctx)) =
approx s' out ctx`; `h` is computable, so by `Nat.Partrec.Code.exists_code` there is
a code `c` with `c.eval = h`; set `i := Encodable.encode c`.
* `≤` : every observed `evaln s c n = some v` is sound (`evaln_sound`), so
  `v = approx s' out ctx`, giving `dyadicValue (approxEnum i s out ctx) s =
  ⨆_{s' ≤ s, observed} dyadicValue (approx s' out ctx) s' ≤ ⨆ s', dyadicValue ...`.
* `≥` : for each `s'`, `approx s' out ctx ∈ c.eval (encode (s', out, ctx))`, so by
  `evaln_complete` there is a budget `k` with `evaln k c ... = some (approx s')`;
  taking `s := max s' k` and `evaln_mono` puts that dyadic value into
  `dyadicValue (approxEnum i s out ctx) s`, so `⨆ s, ... ≥ dyadicValue (approx s') s'`.
-/
lemma exists_approxEnum (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    ∃ i, ∀ out ctx,
      (⨆ s, dyadicValue (approxEnum i s out ctx) s) =
      (⨆ s, dyadicValue (approx s out ctx) s) := by
        revert hcomp;
        intro hcomp
        obtain ⟨c, hc⟩ : ∃ c : Nat.Partrec.Code, ∀ s out ctx, Nat.Partrec.Code.eval c (Encodable.encode (s, out, ctx)) = some (approx s out ctx) := by
          have h_total : ∃ h : ℕ → ℕ, Computable h ∧ ∀ s out ctx, h (Encodable.encode (s, out, ctx)) = approx s out ctx := by
            use fun n => approx (Encodable.decode (α := ℕ × BitString × BitString) n |>.getD (0, [], [])).1 (Encodable.decode (α := ℕ × BitString × BitString) n |>.getD (0, [], [])).2.1 (Encodable.decode (α := ℕ × BitString × BitString) n |>.getD (0, [], [])).2.2;
            convert hcomp.comp (comp_decode_getD Computable.id (Computable.const (0, [], []))) using 1;
            simp +decide [ Encodable.encodek ];
          obtain ⟨ h, hh₁, hh₂ ⟩ := h_total;
          have := @Nat.Partrec.Code.exists_code;
          obtain ⟨ c, hc ⟩ := this.mp (by
            simpa [Computable, Partrec] using hh₁);
          exact ⟨ c, fun s out ctx => by simp +decide [ ← hh₂, hc ] ⟩;
        refine ⟨ Encodable.encode c, fun out ctx => le_antisymm ?_ ?_ ⟩ <;> simp_all +decide [ approxEnum ];
        · intro i
          have h_term : ∀ s' ∈ Finset.range (i + 1),
              dyadicValue
                (evalnDecodedScaled i (Encodable.encode c) (s', out, ctx) (i - s')) i
                ≤ ⨆ s, dyadicValue (approx s out ctx) s := by
              intro s' hs'
              have h_term : Computability.evalnDecoded i (Encodable.encode c) (s', out, ctx) = some (approx s' out ctx) ∨ Computability.evalnDecoded i (Encodable.encode c) (s', out, ctx) = none := by
                cases h : Computability.evalnDecoded i (Encodable.encode c) (s', out, ctx) <;> simp_all +decide [ Part.eq_some_iff ];
                have := Nat.Partrec.Code.evaln_sound (by
                  simpa [Computability.evalnDecoded, Encodable.encodek] using h)
                simp_all +decide [ Part.mem_eq ] ;
                cases hc s' out ctx ; aesop
              generalize_proofs at *; (
              cases h_term <;> simp +decide [ *, dyadicValue, evalnDecodedScaled ];
              refine le_trans ?_ ( le_ciSup ?_ s' ) <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_add ];
              rw [ show ( 2 ^ i : ℝ≥0∞ ) = 2 ^ ( i - s' ) * 2 ^ s' by rw [ ← pow_add, Nat.sub_add_cancel ( Finset.mem_range_succ_iff.mp hs' ) ] ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm ];
              simp +decide [    ENNReal.mul_inv ];
              simp +decide [ mul_left_comm ( 2 ^ ( i - s' ) : ℝ≥0∞ ), ENNReal.mul_inv_cancel ]);
          have h_sup : ∀ {S : Finset ℕ} {f : ℕ → ℕ}, (∀ s' ∈ S, dyadicValue (f s') i ≤ ⨆ s, dyadicValue (approx s out ctx) s) → dyadicValue (S.sup f) i ≤ ⨆ s, dyadicValue (approx s out ctx) s := by
            intro S f
            induction S using Finset.induction with
            | empty => intro hf; simp_all +decide [ dyadicValue ]
            | @insert s' S' hs' ih =>
              intro hf
              cases max_cases ( f s' ) ( S'.sup f ) <;> simp +decide [ * ]
              exact ih fun s' hs' => hf s' ( Finset.mem_insert_of_mem hs' )
          exact h_sup h_term;
        · intro s;
          -- By definition of `Nat.Partrec.Code.evaln`, there exists some `k` such that `Nat.Partrec.Code.evaln k c (Nat.pair s (Nat.pair (Encodable.encode out) (Encodable.encode ctx))) = some (approx s out ctx)`.
          obtain ⟨k, hk⟩ : ∃ k, Nat.Partrec.Code.evaln k c (Nat.pair s (Nat.pair (Encodable.encode out) (Encodable.encode ctx))) = some (approx s out ctx) := by
            simp_all +decide [ Part.eq_some_iff ];
            obtain ⟨ h, hh ⟩ := hc s out ctx;
            exact Nat.Partrec.Code.evaln_complete.mp (hc s out ctx);
          refine le_trans ?_ ( le_iSup _ ( Max.max s k ) );
          refine le_trans ?_ ( ENNReal.div_le_div ( Nat.cast_le.mpr <| Finset.le_sup <| Finset.mem_range.mpr <| Nat.lt_succ_of_le <| le_max_left s k ) le_rfl );
          unfold evalnDecodedScaled
          rw [ show Computability.evalnDecoded (Max.max s k) (Encodable.encode c) (s, out, ctx) = some ( approx s out ctx ) from ?_ ];
          · unfold dyadicValue; norm_num [ pow_add, pow_one, pow_mul, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ;
            rw [ show ( 2 : ℝ≥0∞ ) ^ max s k = ( 2 : ℝ≥0∞ ) ^ ( max s k - s ) * ( 2 : ℝ≥0∞ ) ^ s by rw [ ← pow_add, Nat.sub_add_cancel ( le_max_left _ _ ) ] ] ; ring_nf ;
            simp +decide [  mul_comm, mul_left_comm, ENNReal.mul_inv ];
            rw [ mul_left_comm ( 2 ^ ( max s k - s ) : ℝ≥0∞ ), ENNReal.mul_inv_cancel ( by norm_num ) ( by norm_num ), mul_one ];
          · simpa [Computability.evalnDecoded, Encodable.encodek] using
              Nat.Partrec.Code.evaln_mono ( le_max_right _ _ ) hk

lemma makeMono_mono (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (out ctx : BitString) :
    dyadicValue (makeMono approx s out ctx) s ≤ dyadicValue (makeMono approx (s + 1) out ctx) (s + 1) := by
  change dyadicValue (makeMono approx s out ctx) s
      ≤ dyadicValue (max (2 * makeMono approx s out ctx) (approx (s + 1) out ctx)) (s + 1)
  calc
    dyadicValue (makeMono approx s out ctx) s
        = dyadicValue (2 * makeMono approx s out ctx) (s + 1) := by
          unfold dyadicValue
          rw [pow_succ', div_eq_mul_inv, div_eq_mul_inv]
          rw [ENNReal.mul_inv]
          · norm_num
            rw [show (2 : ℝ≥0∞) * (makeMono approx s out ctx : ℝ≥0∞) *
                  ((2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) ^ s)⁻¹)
                = (makeMono approx s out ctx : ℝ≥0∞) *
                  (((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) * ((2 : ℝ≥0∞) ^ s)⁻¹) by ring,
              ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
          · exact Or.inl two_ne_zero
          · exact Or.inl ENNReal.ofNat_ne_top
    _ ≤ dyadicValue (max (2 * makeMono approx s out ctx) (approx (s + 1) out ctx)) (s + 1) := by
          unfold dyadicValue
          gcongr
          exact_mod_cast Nat.le_max_left (2 * makeMono approx s out ctx)
            (approx (s + 1) out ctx)

lemma makeMono_ge (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (out ctx : BitString) :
    dyadicValue (approx s out ctx) s ≤ dyadicValue (makeMono approx s out ctx) s := by
  cases s with
  | zero =>
      rfl
  | succ s =>
      change dyadicValue (approx (s + 1) out ctx) (s + 1)
        ≤ dyadicValue (max (2 * makeMono approx s out ctx) (approx (s + 1) out ctx))
          (s + 1)
      unfold dyadicValue
      gcongr
      exact_mod_cast Nat.le_max_right (2 * makeMono approx s out ctx)
        (approx (s + 1) out ctx)

lemma dyadicValue_two_mul_succ (n s : ℕ) :
    dyadicValue (2 * n) (s + 1) = dyadicValue n s := by
  unfold dyadicValue
  rw [pow_succ', div_eq_mul_inv, div_eq_mul_inv]
  rw [ENNReal.mul_inv]
  · norm_num
    rw [show (2 : ℝ≥0∞) * (n : ℝ≥0∞) *
          ((2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) ^ s)⁻¹)
        = (n : ℝ≥0∞) *
          (((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) * ((2 : ℝ≥0∞) ^ s)⁻¹) by ring,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  · exact Or.inl two_ne_zero
  · exact Or.inl ENNReal.ofNat_ne_top

lemma lscEnum_isSemimeasure (i : ℕ) : IsSemimeasure (fun x => lscEnum i x []) := by
  change (∑' x, truncG (makeMono (approxEnum i)) 0 x []) ≤ 1
  exact tsum_truncG_le 0 []

lemma iSup_makeMono_eq_iSup (approx : ℕ → BitString → BitString → ℕ) (out ctx : BitString) :
    (⨆ s, dyadicValue (makeMono approx s out ctx) s) = (⨆ s, dyadicValue (approx s out ctx) s) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    induction s with
    | zero =>
        exact le_iSup (fun t => dyadicValue (approx t out ctx) t) 0
    | succ s ih =>
        change dyadicValue
            (max (2 * makeMono approx s out ctx) (approx (s + 1) out ctx))
            (s + 1) ≤ ⨆ t, dyadicValue (approx t out ctx) t
        by_cases h :
            2 * makeMono approx s out ctx ≤ approx (s + 1) out ctx
        · rw [max_eq_right h]
          exact le_iSup (fun t => dyadicValue (approx t out ctx) t) (s + 1)
        · have h' : approx (s + 1) out ctx ≤ 2 * makeMono approx s out ctx := by
            exact le_of_not_ge h
          rw [max_eq_left h']
          rw [dyadicValue_two_mul_succ]
          exact ih
  · apply iSup_le
    intro s
    exact le_trans (makeMono_ge approx s out ctx)
      (le_iSup (fun t => dyadicValue (makeMono approx t out ctx) t) s)

/-
The dyadic value of `mixtureDyadicApprox` at stage `S` is exactly the partial
`dyadicWeight`-weighted sum (over the first `S/2` components at substage `S/2`)
of the component dyadic values. This is the key algebraic identity behind the
mixture LSC closure.
-/
lemma dyadicValue_mixtureDyadicApprox
    (a : ℕ → ℕ → BitString → BitString → ℕ) (S : ℕ) (out ctx : BitString) :
    dyadicValue (mixtureDyadicApprox a S out ctx) S
      = ∑ i ∈ Finset.range (S / 2),
          dyadicWeight i * dyadicValue (a i (S / 2) out ctx) (S / 2) := by
  unfold dyadicValue mixtureDyadicApprox dyadicWeight;
  rw [ Nat.cast_sum, ENNReal.div_eq_inv_mul ];
  rw [ Finset.mul_sum _ _ _ ] ; refine Finset.sum_congr rfl fun i hi => ?_ ; rw [ show ( 2 : ENNReal ) ^ S = ( 2 : ENNReal ) ^ ( i + 1 ) * ( 2 : ENNReal ) ^ ( S / 2 ) * ( 2 : ENNReal ) ^ ( S - ( i + 1 ) - S / 2 ) from _ ] ; ring_nf;
  · simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ENNReal.mul_inv, ENNReal.inv_pow ];
    simp +decide [ ← mul_assoc ];
    simp +decide [ mul_assoc, ← mul_pow ];
    rw [ ENNReal.mul_inv_cancel ] <;> norm_num;
  · rw [ ← pow_add, ← pow_add ] ; congr 1 ; norm_num at * ; omega;

end Kolmogorov
