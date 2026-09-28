import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Rat.Denumerable
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import Mathlib.Computability.Halting
import KolmogorovMathlib.Prefix.ExtensionTheorem
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots.Part02

/-!
# Solovay's theorem relating plain and prefix complexity: the construction

The machinery for `C(x) = K(x) - K(K(x)) + O(1)`: the computable helper maps
(`solovayFst`, `solovaySnd`, `solovayCtx`, `solovayPairMap`), the arithmetic relating the
numerical values `kVal`, `cVal` and `kNatVal`, and the two halves of the equality
(`solovay_plain_eq_prefix_sub_prefix_prefix`,
`solovay_prefix_plain_eq_add_condK_add`).

SUV Theorem 72, p. 148.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.ComputableReals

/-- The first context component of the Solovay construction: the sum of the two decoded numbers. -/
def solovayFst (p : (BitString × BitString) × ℕ) : ℕ :=
  decodeBits p.1.1 + decodeBits p.1.2

/-- The first context component is primitive recursive. -/
theorem solovayFst_primrec : Primrec solovayFst :=
  Primrec.nat_add.comp
    (primrec_decodeBits.comp (Primrec.fst.comp Primrec.fst))
    (primrec_decodeBits.comp (Primrec.snd.comp Primrec.fst))

/-- The first context component is computable. -/
theorem solovayFst_computable : Computable solovayFst :=
  solovayFst_primrec.to_comp

attribute [irreducible] solovayFst

/-- The second context component of the Solovay construction: the second decoded number. -/
def solovaySnd (p : (BitString × BitString) × ℕ) : ℕ :=
  decodeBits p.1.2

/-- The second context component is primitive recursive. -/
theorem solovaySnd_primrec : Primrec solovaySnd :=
  primrec_decodeBits.comp (Primrec.snd.comp Primrec.fst)

/-- The second context component is computable. -/
theorem solovaySnd_computable : Computable solovaySnd :=
  solovaySnd_primrec.to_comp

attribute [irreducible] solovaySnd

/-- The context of the Solovay construction: the pair of its two components, the first in binary
and the second in unary. -/
def solovayCtxFun (p : (BitString × BitString) × ℕ) : BitString :=
  pairCode (natBits (solovayFst p)) (natCode (solovaySnd p))

/-- The context function is primitive recursive. -/
theorem solovayCtxFun_primrec : Primrec solovayCtxFun :=
  Primrec₂.comp CodedFiniteDistribution.pairCode_primrec
    (primrec_natBits.comp solovayFst_primrec)
    (Kolmogorov.primrec_natCode.comp solovaySnd_primrec)

/-- The context function is computable. -/
theorem solovayCtxFun_computable : Computable solovayCtxFun :=
  solovayCtxFun_primrec.to_comp

/-- The context function with its three arguments given separately. -/
def solovayCtx (i bs : BitString) (plen : ℕ) : BitString :=
  solovayCtxFun ((i, bs), plen)

/-- The context is computable in its three arguments. -/
lemma solovayCtx_computable : Computable (fun (p : (BitString × BitString) × ℕ) =>
    solovayCtx p.1.1 p.1.2 p.2) :=
  solovayCtxFun_computable

attribute [irreducible] solovayCtxFun solovayCtx

/-- Re-encoding: from the unary code of a number to its binary digits. -/
def natCodeToNatBitsMap (p : BitString) : BitString :=
  natBits (CodedFiniteDistribution.decodeNatCode p)

/-- The re-encoding from unary to binary is computable. -/
lemma natCodeToNatBitsMap_computable : Computable natCodeToNatBitsMap :=
  (primrec_natBits.comp CodedFiniteDistribution.decodeNatCode_primrec).to_comp

/-- Re-encoding of a pair code: the first component is converted from unary to binary, the second
is kept. -/
def solovayPairMap (p : BitString) : BitString :=
  pairCode (natCodeToNatBitsMap (decodeFirst p)) (decodeSecond p)

/-- The pair re-encoding is primitive recursive. -/
theorem solovayPairMap_primrec : Primrec solovayPairMap :=
  Primrec₂.comp CodedFiniteDistribution.pairCode_primrec
    (primrec_natBits.comp (CodedFiniteDistribution.decodeNatCode_primrec.comp
      CodedFiniteDistribution.decodeFirst_primrec))
    CodedFiniteDistribution.decodeSecond_primrec

/-- The pair re-encoding is computable. -/
theorem solovayPairMap_computable : Computable solovayPairMap :=
  solovayPairMap_primrec.to_comp

attribute [irreducible] solovayPairMap

/-- The natural-valued shadow of the plain prefix complexity agrees with it for an optimal prefix
machine. -/
lemma kVal_eq_coe (U : Map) (hU : IsOptimalPrefixConditional U) (x : BitString) :
    (kVal U x : ENat) = KPPlain U x :=
  ENat.coe_toNat (KPPlain_ne_top_of_optimal U hU x)

/-- The natural-valued shadow of the plain complexity agrees with it for an optimal conditional
machine. -/
lemma cVal_eq_coe (U V : Map) (hU : IsOptimalPrefixConditional U)
    (hV : isOptimalConditional V) (x : BitString) :
    (cVal V x : ENat) = plainK V x := by
  have hne : plainK V x ≠ ⊤ := by
    obtain ⟨c1, hc1⟩ := plain_le_prefix V U hV hU.isPrefixDecompressor
    obtain ⟨c2, hc2⟩ := KPPlain_le_two_mul_length U hU
    have h1 : plainK V x ≤ ((2 * x.length + c2 + c1 : ℕ) : ENat) := by
      calc plainK V x ≤ KPPlain U x + (c1 : ENat) := hc1 x
      _ ≤ 2 * x.length + (c2 : ENat) + (c1 : ENat) := by gcongr; exact hc2 x
      _ = ((2 * x.length + c2 + c1 : ℕ) : ENat) := by push_cast; ring
    exact ne_top_of_le_ne_top (ENat.coe_ne_top _) h1
  dsimp [cVal]
  exact ENat.coe_toNat hne

/-- The natural-valued shadow of the prefix complexity of a number agrees with the prefix
complexity of its binary digits. -/
lemma kNatVal_eq_coe (U : Map) (hU : IsOptimalPrefixConditional U) (n : ℕ) :
    (kNatVal U n : ENat) = KPPlain U (natBits n) :=
  kVal_eq_coe U hU (natBits n)

/-- Bounding the difference between truncated natural subtraction `Kx - KKx` and integer
subtraction `Kx - KKx`. -/
private lemma solovay_i_diff_le (U : Map) (Kx KKx M_Kx c_two C_bound : ℕ)
    (hM_Kx : ∀ n, M_Kx ≤ n → 1 * (2 * (Nat.bits n).length + c_two) ≤ n)
    (hc_two : ∀ x, KPPlain U x ≤ 2 * x.length + c_two)
    (h_kk_coe : KPPlain U (natBits Kx) = (KKx : ENat))
    (hC : c_two + 2 * M_Kx ≤ C_bound) :
    |((Kx - KKx : ℕ) : ℤ) - ((Kx : ℤ) - (KKx : ℤ))| ≤ (C_bound : ℤ) := by
  by_cases h_ge : KKx ≤ Kx
  · have h_eq_i : ((Kx - KKx : ℕ) : ℤ) = (Kx : ℤ) - (KKx : ℤ) := by zify [h_ge]
    rw [h_eq_i, sub_self, abs_zero]
    have : 0 ≤ (C_bound : ℤ) := Int.natCast_nonneg _
    linarith
  · have hi0 : Kx - KKx = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h_i_zero : ((Kx - KKx : ℕ) : ℤ) = 0 := by exact_mod_cast hi0
    have h_Kx_le_M : Kx ≤ M_Kx := by
      by_contra h_gt
      have h_gt' : M_Kx ≤ Kx := le_of_not_ge h_gt
      have h_dom := hM_Kx Kx h_gt'
      have h_kk_le : KKx ≤ 2 * (Nat.bits Kx).length + c_two := by
        have h_spec := hc_two (natBits Kx)
        rw [h_kk_coe] at h_spec
        exact_mod_cast h_spec
      have h_len_le : (Nat.bits Kx).length ≤ Kx := length_natBits_le Kx
      have h_not_ge : KKx ≤ Kx := by omega
      exact h_ge h_not_ge
    have h_kk_le : KKx ≤ 2 * (Nat.bits Kx).length + c_two := by
      have h_spec := hc_two (natBits Kx)
      rw [h_kk_coe] at h_spec
      exact_mod_cast h_spec
    have h_len_le : (Nat.bits Kx).length ≤ Kx := length_natBits_le Kx
    have h_kk_bound_z : (KKx : ℤ) ≤ (C_bound : ℤ) := by
      have h_kk_nat : KKx ≤ C_bound := by omega
      exact_mod_cast h_kk_nat
    have h_kx_bound_z : (Kx : ℤ) ≤ (C_bound : ℤ) := by
      have h_kx_nat : Kx ≤ C_bound := by omega
      exact_mod_cast h_kx_nat
    have h_kx_nonneg : 0 ≤ (Kx : ℤ) := Int.natCast_nonneg _
    have h_kk_nonneg : 0 ≤ (KKx : ℤ) := Int.natCast_nonneg _
    rw [h_i_zero]
    have h_ring : (0 : ℤ) - ((Kx : ℤ) - (KKx : ℤ)) = (KKx : ℤ) - (Kx : ℤ) := by ring
    rw [h_ring, abs_le]
    constructor <;> linarith

/-- Linear arithmetic bound for scaling the Solovay constant. -/
private lemma solovay_linear_bound (c_stab C_bound R : ℕ) (hc : c_stab ≤ C_bound) :
    (c_stab : ℤ) * ((R : ℤ) + (C_bound : ℤ) + 1) + (C_bound : ℤ) ≤
      ((C_bound * (C_bound + 1) + C_bound : ℕ) : ℤ) * ((R : ℤ) + 1) := by
  have hR_nonneg : 0 ≤ (R : ℤ) := Int.natCast_nonneg _
  have h1 : (c_stab : ℤ) * ((R : ℤ) + (C_bound : ℤ) + 1) + (C_bound : ℤ) ≤
      (C_bound : ℤ) * ((R : ℤ) + (C_bound : ℤ) + 1) + (C_bound : ℤ) := by gcongr
  have h2 : (C_bound : ℤ) * ((R : ℤ) + (C_bound : ℤ) + 1) + (C_bound : ℤ) ≤
      ((C_bound : ℤ) * ((C_bound : ℤ) + 1) + (C_bound : ℤ)) * ((R : ℤ) + 1) := by
    calc (C_bound : ℤ) * ((R : ℤ) + (C_bound : ℤ) + 1) + (C_bound : ℤ)
        = (C_bound : ℤ) * (R : ℤ) + (C_bound : ℤ) * (C_bound : ℤ) + 2 * (C_bound : ℤ) := by ring
      _ ≤ ((C_bound : ℤ) * (C_bound : ℤ) + 2 * (C_bound : ℤ)) * (R : ℤ) +
          ((C_bound : ℤ) * (C_bound : ℤ) + 2 * (C_bound : ℤ)) := by
          have h_c_pos : 0 ≤ (C_bound : ℤ) := Int.natCast_nonneg _
          nlinarith
      _ = ((C_bound : ℤ) * ((C_bound : ℤ) + 1) + (C_bound : ℤ)) * ((R : ℤ) + 1) := by ring
  have h3 : ((C_bound : ℤ) * ((C_bound : ℤ) + 1) + (C_bound : ℤ)) * ((R : ℤ) + 1) =
      ((C_bound * (C_bound + 1) + C_bound : ℕ) : ℤ) * ((R : ℤ) + 1) := by push_cast; rfl
  linarith [h1, h2, h3]

/-- Upper bound on the conditional complexity of `x` given the difference `K(x) - K(K(x))`.

The hypotheses `hc_drop`, `hc_self`, `hc_swap`, `hc_map_pair`, `hc_chain`, `hc_inv`,
`hc_m2` and `hc_two` are interface assumptions about an arbitrary optimal conditional
prefix machine `U`: each is one machine-invariance estimate with its own named constant. -/
private lemma solovay_kp_diff_upper_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    (x : BitString) (Kx KKx R : ℕ)
    (c_drop c_self c_swap c_map_pair c_chain c_inv c_m2 c_two M_Kx C_bound : ℕ)
    (h_kx_coe : KPPlain U x = (Kx : ENat))
    (h_kk_coe : KPPlain U (natBits Kx) = (KKx : ENat))
    (h_R_coe : KPPlain U (natBits KKx) = (R : ENat))
    (hc_drop : ∀ y z, KP U y z ≤ KPPlain U y + (c_drop : ENat))
    (hc_self : ∀ (x : BitString) (kx : ℕ), HasPrefixComplexityValue U x kx →
      KPPair U x (natCode kx) ≤ (kx : ENat) + (c_self : ENat))
    (hc_swap : ∀ (x y : BitString), KPPair U y x ≤ KPPair U x y + (c_swap : ENat))
    (hc_map_pair : ∀ z, KPPlain U (solovayPairMap z) ≤ KPPlain U z + (c_map_pair : ENat))
    (hc_chain : ∀ x y n, HasPrefixComplexityValue U x n →
      KPPlain U x + KP U y (prefixComplexityContext x n) ≤ KPPair U x y + (c_chain : ENat))
    (hc_inv : ∀ y z, KP U y z ≤ KP (condTwoStagePairBuilder U solovayCtx) y z + (c_inv : ENat))
    (hc_m2 : ∀ y z, KP U (decodeSecond y) z ≤ KP U y z + (c_m2 : ENat))
    (hc_two : ∀ z, KPPlain U z ≤ 2 * z.length + c_two)
    (hM_Kx : ∀ n, M_Kx ≤ n → 1 * (2 * (Nat.bits n).length + c_two) ≤ n)
    (hC_bound_sum : c_drop + c_self + c_swap + c_map_pair + c_chain + c_inv + c_m2 ≤ C_bound)
    (hC_bound_M : c_drop + M_Kx ≤ C_bound) :
    KP U x (natBits (Kx - KKx)) ≤ ((Kx - KKx + R + C_bound : ℕ) : ENat) := by
  set i := Kx - KKx with hi
  have h_nc_eval : natCodeToNatBitsMap (natCode Kx) = natBits Kx := by
    dsimp [natCodeToNatBitsMap]; rw [CodedFiniteDistribution.decodeNatCode_natCode]
  by_cases h_ge : KKx ≤ Kx
  · have h_p_ne : KP U (natBits KKx) (natBits i) ≠ ⊤ := by
      have h1 : KP U (natBits KKx) (natBits i) ≤ (R : ENat) + (c_drop : ENat) := by
        calc KP U (natBits KKx) (natBits i)
          _ ≤ KPPlain U (natBits KKx) + (c_drop : ENat) := hc_drop _ _
          _ = (R : ENat) + (c_drop : ENat) := by rw [h_R_coe]
      exact ne_top_of_le_ne_top (ENat.coe_ne_top _) h1
    obtain ⟨p, hp_prod, hp_len⟩ := exists_program_of_KP_ne_top (M := U) (x := natBits KKx)
      (y := natBits i) h_p_ne
    have h_ctx_eval : solovayCtx (natBits i) (natBits KKx) p.length =
        prefixComplexityContext (natBits Kx) KKx := by
      unfold solovayCtx solovayCtxFun solovayFst solovaySnd prefixComplexityContext
      dsimp [natBits]
      rw [decodeBits_natBits, decodeBits_natBits, hi, Nat.sub_add_cancel h_ge]
    have h_kk_has : HasPrefixComplexityValue U (natBits Kx) KKx := h_kk_coe.symm
    have h_ch := hc_chain (natBits Kx) x KKx h_kk_has
    have h_ch_bound : KP U x (prefixComplexityContext (natBits Kx) KKx) ≤
        ((i + c_self + c_swap + c_map_pair + c_chain : ℕ) : ENat) := by
      have h_kk_ne : (KKx : ENat) ≠ ⊤ := ENat.coe_ne_top _
      have h_pair_upper : KPPair U (natBits Kx) x ≤
          (Kx : ENat) + (c_self + c_swap + c_map_pair : ENat) := by
        have h1 : KPPair U (natBits Kx) x = KPPlain U (pairCode (natBits Kx) x) := rfl
        have h2 : KPPlain U (pairCode (natBits Kx) x) ≤
            KPPlain U (pairCode (natCode Kx) x) + (c_map_pair : ENat) := by
          have h_eval_p := hc_map_pair (pairCode (natCode Kx) x)
          have h_eq_pair : solovayPairMap (pairCode (natCode Kx) x) = pairCode (natBits Kx) x := by
            unfold solovayPairMap natCodeToNatBitsMap
            rw [decodeFirst_pairCode, decodeSecond_pairCode,
              CodedFiniteDistribution.decodeNatCode_natCode]
          rw [h_eq_pair] at h_eval_p; exact h_eval_p
        have h3 : KPPair U (natCode Kx) x ≤ KPPair U x (natCode Kx) + (c_swap : ENat) :=
          hc_swap x (natCode Kx)
        have h4 : KPPair U x (natCode Kx) ≤ (Kx : ENat) + (c_self : ENat) :=
          hc_self x Kx h_kx_coe.symm
        calc KPPair U (natBits Kx) x
            = KPPlain U (pairCode (natBits Kx) x) := h1
          _ ≤ KPPlain U (pairCode (natCode Kx) x) + (c_map_pair : ENat) := h2
          _ = KPPair U (natCode Kx) x + (c_map_pair : ENat) := rfl
          _ ≤ KPPair U x (natCode Kx) + (c_swap : ENat) + (c_map_pair : ENat) := by gcongr
          _ ≤ (Kx : ENat) + (c_self : ENat) + (c_swap : ENat) + (c_map_pair : ENat) := by gcongr
          _ = (Kx : ENat) + (c_self + c_swap + c_map_pair : ENat) := by ring
      have h_Kx_eq : (Kx : ENat) = (KKx : ENat) + (i : ENat) := by
        have h_add_nat : Kx = KKx + i := by rw [hi]; exact (Nat.add_sub_cancel' h_ge).symm
        rw [h_add_nat]; push_cast; rfl
      have h_add : (KKx : ENat) + KP U x (prefixComplexityContext (natBits Kx) KKx) ≤
          (KKx : ENat) + ((i + c_self + c_swap + c_map_pair + c_chain : ℕ) : ENat) := by
        calc (KKx : ENat) + KP U x (prefixComplexityContext (natBits Kx) KKx)
            = KPPlain U (natBits Kx) + KP U x (prefixComplexityContext (natBits Kx) KKx) := by
              rw [h_kk_coe]
          _ ≤ KPPair U (natBits Kx) x + (c_chain : ENat) := h_ch
          _ ≤ (Kx : ENat) + (c_self + c_swap + c_map_pair : ENat) + (c_chain : ENat) := by gcongr
          _ = (KKx : ENat) + (i : ENat) + (c_self + c_swap + c_map_pair : ENat) +
              (c_chain : ENat) := by rw [h_Kx_eq]
          _ = (KKx : ENat) + ((i + c_self + c_swap + c_map_pair + c_chain : ℕ) : ENat) := by
            push_cast; ring
      exact WithTop.add_le_add_iff_left h_kk_ne |>.mp h_add
    have h_ne_top : KP U x (prefixComplexityContext (natBits Kx) KKx) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.coe_ne_top _) h_ch_bound
    obtain ⟨q, hq_prod, hq_len⟩ := exists_program_of_KP_ne_top (M := U) (x := x)
      (y := prefixComplexityContext (natBits Kx) KKx) h_ne_top
    have hq_prod' : produces U q (solovayCtx (natBits i) (natBits KKx) p.length) x := by
      rw [h_ctx_eval]; exact hq_prod
    have h_two_stage := KP_condTwoStagePairBuilder_le_of_produces (U := U) (ctx := solovayCtx)
      hU.isPrefixMachine hp_prod hq_prod'
    have h_D_bound : KP U (pairCode (natBits KKx) x) (natBits i) ≤
        KP (condTwoStagePairBuilder U solovayCtx) (pairCode (natBits KKx) x) (natBits i) +
        (c_inv : ENat) := hc_inv _ _
    have h_m2_spec : KP U x (natBits i) ≤
        KP U (pairCode (natBits KKx) x) (natBits i) + (c_m2 : ENat) := by
      have h_m := hc_m2 (pairCode (natBits KKx) x) (natBits i)
      rw [decodeSecond_pairCode] at h_m; exact h_m
    have h_bound_le : i + R + (c_drop + c_self + c_swap + c_map_pair + c_chain + c_inv + c_m2) ≤
        i + R + C_bound := by omega
    calc KP U x (natBits i)
        ≤ KP U (pairCode (natBits KKx) x) (natBits i) + (c_m2 : ENat) := h_m2_spec
      _ ≤ KP (condTwoStagePairBuilder U solovayCtx) (pairCode (natBits KKx) x) (natBits i) +
          (c_inv : ENat) + (c_m2 : ENat) := by gcongr
      _ ≤ ((p.length + q.length : ℕ) : ENat) + (c_inv : ENat) + (c_m2 : ENat) := by gcongr
      _ = KP U (natBits KKx) (natBits i) +
          KP U x (prefixComplexityContext (natBits Kx) KKx) + (c_inv + c_m2 : ENat) := by
          push_cast; rw [hp_len, hq_len]; ring
      _ ≤ (KPPlain U (natBits KKx) + (c_drop : ENat)) +
          ((i + c_self + c_swap + c_map_pair + c_chain : ℕ) : ENat) + (c_inv + c_m2 : ENat) := by
          gcongr; exact hc_drop _ _
      _ = ((i + R + (c_drop + c_self + c_swap + c_map_pair + c_chain + c_inv + c_m2) : ℕ)
          : ENat) := by rw [h_R_coe]; push_cast; ring
      _ ≤ ((i + R + C_bound : ℕ) : ENat) := by exact_mod_cast h_bound_le
  · have hi0 : i = 0 := by rw [hi]; exact Nat.sub_eq_zero_of_le (by omega)
    have h1 := hc_drop x (natBits 0)
    rw [h_kx_coe] at h1
    have h_Kx_le_M : Kx ≤ M_Kx := by
      by_contra h_gt
      have h_gt' : M_Kx ≤ Kx := le_of_not_ge h_gt
      have h_dom := hM_Kx Kx h_gt'
      have h_kk_le : KKx ≤ 2 * (Nat.bits Kx).length + c_two := by
        have h_spec := hc_two (natBits Kx)
        rw [h_kk_coe] at h_spec; exact_mod_cast h_spec
      have h_len_le : (Nat.bits Kx).length ≤ Kx := length_natBits_le Kx
      have h_not_ge : KKx ≤ Kx := by omega
      exact h_ge h_not_ge
    have h_kx_bound : Kx + c_drop ≤ i + R + C_bound := by omega
    calc KP U x (natBits i)
        = KP U x (natBits 0) := by rw [hi0]
      _ ≤ (Kx : ENat) + (c_drop : ENat) := h1
      _ = ((Kx + c_drop : ℕ) : ENat) := by push_cast; rfl
      _ ≤ ((i + R + C_bound : ℕ) : ENat) := by exact_mod_cast h_kx_bound

/-- **Theorem 73 (Solovay).** `C(x) = K(x) - K(K(x)) + O(K⁽³⁾(x))`. -/
theorem solovay_plain_eq_prefix_sub_prefix_prefix (U V : Map)
    (hU : IsOptimalPrefixConditional U) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x : BitString,
      |(cVal V x : ℤ) - ((kVal U x : ℤ) - (kNatVal U (kVal U x) : ℤ))| ≤
        (c : ℤ) * ((kNatVal U (kNatVal U (kVal U x)) : ℤ) + 1) := by
  obtain ⟨c_stab, hc_stab⟩ := plainK_eq_of_condKP_eq_add U V hU hV
  obtain ⟨c_rem, hc_rem⟩ := KP_cond_remove_short_info U hU
  obtain ⟨c_sub, hc_sub⟩ := KPPlain_natBits_sub_self_le U hU
  obtain ⟨c_drop, hc_drop⟩ := KP_le_KPPlain U hU
  obtain ⟨c_m1, hc_m1⟩ := KP_cond_map_le U hU decodeSecond decodeSecond_computable
  obtain ⟨c_m2, hc_m2⟩ := KP_map_le U hU decodeSecond decodeSecond_computable
  obtain ⟨c_self, hc_self⟩ := KPPair_self_complexity_le U hU
  obtain ⟨c_right, hc_right⟩ := KPPlain_right_le_KPPair U hU
  obtain ⟨c_swap, hc_swap⟩ := KPPair_swap_le U hU
  obtain ⟨c_map_nc, hc_map_nc⟩ :=
    KPPlain_map_le U hU natCodeToNatBitsMap natCodeToNatBitsMap_computable
  obtain ⟨c_map_pair, hc_map_pair⟩ := KPPlain_map_le U hU solovayPairMap solovayPairMap_computable
  obtain ⟨c_chain, hc_chain⟩ := KPPair_chain_lower U hU
  obtain ⟨c_two, hc_two⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨M_Kx, hM_Kx⟩ := exists_bits_linear_domination 1 2 c_two
  let D_solovay := condTwoStagePairBuilder U solovayCtx
  have hD_solovay : IsPrefixDecompressor D_solovay := ⟨
    condTwoStagePairBuilder_isDecompressor hU.isDecompressor hU.isPrefixMachine
      solovayCtx_computable,
    condTwoStagePairBuilder_isPrefixMachine hU.isPrefixMachine⟩
  obtain ⟨c_inv, hc_inv⟩ := hU.invariance hD_solovay
  set C_bound := c_stab + c_rem + c_sub + c_drop + c_m1 + c_m2 + c_self + c_right + c_swap +
    c_map_nc + c_map_pair + c_chain + c_inv + c_two + 2 * M_Kx + 10000 with hC_bound_def
  refine ⟨C_bound * (C_bound + 1) + C_bound, fun x => ?_⟩
  set Kx := kVal U x
  set KKx := kNatVal U Kx
  set R := kNatVal U KKx
  set i := Kx - KKx
  set d : ℤ := (kCondVal U x (natBits i) : ℤ) - (i : ℤ)
  have hd_eq : (kCondVal U x (natBits i) : ℤ) = (i : ℤ) + d := by ring
  have h_stab := hc_stab x i d hd_eq
  have h_kx_coe : KPPlain U x = (Kx : ENat) := (kVal_eq_coe U hU x).symm
  have h_kk_coe : KPPlain U (natBits Kx) = (KKx : ENat) := (kNatVal_eq_coe U hU Kx).symm
  have h_R_coe : KPPlain U (natBits KKx) = (R : ENat) := (kNatVal_eq_coe U hU KKx).symm
  have h_top_ne : (i : ENat) + (R : ENat) + (C_bound : ENat) ≠ ⊤ := ENat.coe_ne_top _
  have h_le_kp := solovay_kp_diff_upper_bound U hU x Kx KKx R c_drop c_self c_swap
    c_map_pair c_chain c_inv c_m2 c_two M_Kx C_bound h_kx_coe h_kk_coe h_R_coe hc_drop
    hc_self hc_swap hc_map_pair hc_chain hc_inv hc_m2 hc_two hM_Kx
    (by rw [hC_bound_def]; omega)
    (by rw [hC_bound_def]; omega)
  have h_nat_le : kCondVal U x (natBits i) ≤ i + R + C_bound :=
    ENat.toNat_le_toNat h_le_kp h_top_ne
  have h_sub_spec := hc_sub Kx KKx (h_kk_coe.symm)
  have h_pair_sub : KPPlain U (natBits i) ≤ (KKx : ENat) + (c_sub : ENat) := h_sub_spec
  have h_pair_empty : KP U x [] = (Kx : ENat) := h_kx_coe
  have h_top_ne2 : (kCondVal U x (natBits i) : ENat) + (c_m1 : ENat) + (KKx : ENat)
      + (c_sub : ENat) + (c_rem : ENat) ≠ ⊤ := ENat.coe_ne_top _
  have h_eq : decodeSecond (pairCode [] (natBits i)) = natBits i := decodeSecond_pairCode _ _
  have h_map := hc_m1 x (pairCode [] (natBits i))
  rw [h_eq] at h_map
  have h_cond_coe : KP U x (natBits i) = (kCondVal U x (natBits i) : ENat) := by
    dsimp [kCondVal]
    have h_ne : KP U x (natBits i) ≠ ⊤ := by
      have h1 := hc_drop x (natBits i)
      rw [h_kx_coe] at h1
      exact ne_top_of_le_ne_top (ENat.coe_ne_top _) h1
    exact (ENat.coe_toNat h_ne).symm
  have h_le_kx : (Kx : ENat) ≤ ((kCondVal U x (natBits i) + c_m1 + KKx + c_sub + c_rem : ℕ)
      : ENat) := by
    have h_step1 : (Kx : ENat) ≤ KP U x (pairCode [] (natBits i)) +
        KPPlain U (natBits i) + (c_rem : ENat) := by
      rw [← h_pair_empty]
      exact hc_rem x [] (natBits i)
    have h_step2 : KP U x (pairCode [] (natBits i)) ≤
        KP U x (natBits i) + (c_m1 : ENat) := h_map
    have h_step3 : KPPlain U (natBits i) ≤ ((KKx + c_sub : ℕ) : ENat) := h_pair_sub
    calc (Kx : ENat)
        ≤ KP U x (pairCode [] (natBits i)) + KPPlain U (natBits i) + (c_rem : ENat) := h_step1
      _ ≤ (KP U x (natBits i) + (c_m1 : ENat)) + KPPlain U (natBits i) + (c_rem : ENat) := by
          gcongr
      _ = KP U x (natBits i) + (c_m1 : ENat) + KPPlain U (natBits i) + (c_rem : ENat) := by ring
      _ ≤ (kCondVal U x (natBits i) : ENat) + (c_m1 : ENat) +
          ((KKx + c_sub : ℕ) : ENat) + (c_rem : ENat) := by
          rw [h_cond_coe]
          gcongr
      _ = ((kCondVal U x (natBits i) + c_m1 + KKx + c_sub + c_rem : ℕ) : ENat) := by
          push_cast; ring
  have h_nat_kx : Kx ≤ kCondVal U x (natBits i) + c_m1 + KKx + c_sub + c_rem :=
    ENat.toNat_le_toNat h_le_kx h_top_ne2
  have h_d_up : d ≤ (R : ℤ) + (C_bound : ℤ) := by
    have : (c_drop : ℤ) ≤ (C_bound : ℤ) := by rw [hC_bound_def]; omega
    linarith
  have h_d_low : -(R : ℤ) - (C_bound : ℤ) ≤ d := by
    dsimp [d]
    have hR_nonneg : 0 ≤ (R : ℤ) := Int.natCast_nonneg _
    have hC_nonneg : 0 ≤ (C_bound : ℤ) := Int.natCast_nonneg _
    have h_cond_nonneg : 0 ≤ (kCondVal U x (natBits i) : ℤ) := Int.natCast_nonneg _
    have h_C_sum_nat : c_m1 + c_sub + c_rem ≤ C_bound := by rw [hC_bound_def]; omega
    by_cases h_ge : KKx ≤ Kx
    · have h_kx_z : (Kx : ℤ) ≤ (kCondVal U x (natBits i) : ℤ) + (c_m1 : ℤ) + (KKx : ℤ) +
          (c_sub : ℤ) + (c_rem : ℤ) := by
        exact_mod_cast h_nat_kx
      have h_C_z : (c_m1 : ℤ) + (c_sub : ℤ) + (c_rem : ℤ) ≤ (C_bound : ℤ) := by
        exact_mod_cast h_C_sum_nat
      have h_i_z : (i : ℤ) = (Kx : ℤ) - (KKx : ℤ) := by dsimp [i]; zify [h_ge]
      linarith [h_kx_z, h_C_z, h_i_z, hR_nonneg]
    · have hi0 : i = 0 := Nat.sub_eq_zero_of_le (by omega)
      have h_i0_z : (i : ℤ) = 0 := by exact_mod_cast hi0
      linarith [h_i0_z, h_cond_nonneg, hR_nonneg, hC_nonneg]
  have hd_abs : (d.natAbs : ℤ) ≤ (R : ℤ) + (C_bound : ℤ) := by
    dsimp [d] at h_d_up h_d_low
    cases le_total 0 d with
    | inl hpos =>
      have h1 : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hpos
      linarith
    | inr hneg =>
      have h1 : (d.natAbs : ℤ) = -d := Int.ofNat_natAbs_of_nonpos hneg
      linarith
  have h_bound_d : (c_stab : ℤ) * ((d.natAbs : ℤ) + 1) ≤
      (c_stab : ℤ) * ((R : ℤ) + (C_bound : ℤ) + 1) := by
    nlinarith [hd_abs, Int.natCast_nonneg c_stab]
  have h_tri : |(cVal V x : ℤ) - ((Kx : ℤ) - (KKx : ℤ))| ≤
      |(cVal V x : ℤ) - (i : ℤ)| + |(i : ℤ) - ((Kx : ℤ) - (KKx : ℤ))| := by
    have h_ring : (cVal V x : ℤ) - ((Kx : ℤ) - (KKx : ℤ)) =
        ((cVal V x : ℤ) - (i : ℤ)) + ((i : ℤ) - ((Kx : ℤ) - (KKx : ℤ))) := by ring
    rw [h_ring]
    exact abs_add_le _ _
  have h_i_diff : |(i : ℤ) - ((Kx : ℤ) - (KKx : ℤ))| ≤ (C_bound : ℤ) :=
    solovay_i_diff_le U Kx KKx M_Kx c_two C_bound hM_Kx hc_two h_kk_coe
      (by rw [hC_bound_def]; omega)
  have h_main_le : |(cVal V x : ℤ) - ((Kx : ℤ) - (KKx : ℤ))| ≤
      (c_stab : ℤ) * ((R : ℤ) + (C_bound : ℤ) + 1) + (C_bound : ℤ) := by
    have h1 : |(cVal V x : ℤ) - (i : ℤ)| ≤ (c_stab : ℤ) * (d.natAbs + 1) := h_stab
    have h2 : (c_stab : ℤ) * (d.natAbs + 1) ≤ (c_stab : ℤ) * ((R : ℤ) + (C_bound : ℤ) + 1) :=
      h_bound_d
    have h3 : |(cVal V x : ℤ) - (i : ℤ)| ≤ (c_stab : ℤ) * ((R : ℤ) + (C_bound : ℤ) + 1) :=
      le_trans h1 h2
    linarith [h_tri, h3, h_i_diff]
  have h_linear := solovay_linear_bound c_stab C_bound R (by rw [hC_bound_def]; omega)
  exact le_trans h_main_le h_linear

/-! ### Auxiliary material for Theorem 74 (Solovay, inverse form) -/

/-- Decode a pair code and return the binary encoding of the **sum** of the two
components.  This is the additive companion of `subPairBits`. -/
def addPairBits (z : BitString) : BitString :=
  natBits (bitsToNat (decodeFirst z) + bitsToNat (decodeSecond z))

/-- Adding the two components of a pair code is computable. -/
lemma addPairBits_computable : Computable addPairBits := by
  have h1 : Primrec (fun z => decodeFirst z) := CodedFiniteDistribution.decodeFirst_primrec
  have h2 : Primrec (fun z => decodeSecond z) := CodedFiniteDistribution.decodeSecond_primrec
  have hu : Primrec (fun z => bitsToNat (decodeFirst z)) := bitsToNat_primrec.comp h1
  have hv : Primrec (fun z => bitsToNat (decodeSecond z)) := bitsToNat_primrec.comp h2
  have hadd : Primrec (fun z => bitsToNat (decodeFirst z) + bitsToNat (decodeSecond z)) :=
    Primrec.nat_add.comp hu hv
  have hbits :
      Primrec (fun z => natBits (bitsToNat (decodeFirst z) + bitsToNat (decodeSecond z))) :=
    primrec_natBits.comp hadd
  exact hbits.to_comp

/-- On the pair code of `n` and `k`, the addition map returns the binary digits of `n + k`. -/
lemma addPairBits_eval (n k' : ℕ) :
    addPairBits (pairCode (natBits n) (natBits k')) = natBits (n + k') := by
  dsimp [addPairBits, natBits]
  rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits, bitsToNat_bits]

/-! #### Elementary logarithmic estimates

The proof of Theorem 74 needs a *self-improving* bound for `K⁽³⁾(x)`: the
inequality obtained for it has `K⁽³⁾(x)` again on the right-hand side, but only
inside a logarithm.  The following lemmas turn such an inequality into a genuine
bound; the point is the factor `4` (rather than `2`), which leaves a spare
half of `n` on the right. -/

/-- The estimate `4 * k ≤ 2 ^ k + 4`. -/
lemma four_mul_le_two_pow_add (k : ℕ) : 4 * k ≤ 2 ^ k + 4 := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    have hsucc : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by
      rw [pow_succ]; ring
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hcase : n = 0 ∨ n = 1 := by omega
      rcases hcase with rfl | rfl <;> norm_num
    · have h2 : (4 : ℕ) ≤ 2 ^ n := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega

/-- The estimate `4 * log₂ (m + 2) ≤ m + 6`. -/
lemma four_mul_log2_le (m : ℕ) : 4 * Nat.log 2 (m + 2) ≤ m + 6 := by
  have h1 := four_mul_le_two_pow_add (Nat.log 2 (m + 2))
  have h2 : 2 ^ Nat.log 2 (m + 2) ≤ m + 2 := Nat.pow_log_le_self 2 (by omega)
  omega

/-- The binary logarithm of a product is at most the sum of the shifted logarithms plus one. -/
lemma log2_mul_le (u v : ℕ) :
    Nat.log 2 (u * v) ≤ Nat.log 2 (u + 2) + Nat.log 2 (v + 2) + 1 := by
  rcases Nat.eq_zero_or_pos (u * v) with h0 | hpos
  · rw [h0]
    simp
  · have hu : u + 2 < 2 ^ (Nat.log 2 (u + 2) + 1) :=
      Nat.lt_pow_succ_log_self (by decide) (u + 2)
    have hv : v + 2 < 2 ^ (Nat.log 2 (v + 2) + 1) :=
      Nat.lt_pow_succ_log_self (by decide) (v + 2)
    have hu' : u + 1 ≤ 2 ^ (Nat.log 2 (u + 2) + 1) := by omega
    have hv' : v + 1 ≤ 2 ^ (Nat.log 2 (v + 2) + 1) := by omega
    have key : (u + 1) * (v + 1) ≤
        2 ^ (Nat.log 2 (u + 2) + 1) * 2 ^ (Nat.log 2 (v + 2) + 1) := Nat.mul_le_mul hu' hv'
    have hpow : 2 ^ (Nat.log 2 (u + 2) + 1) * 2 ^ (Nat.log 2 (v + 2) + 1) =
        2 ^ (Nat.log 2 (u + 2) + Nat.log 2 (v + 2) + 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hstrict : u * v < (u + 1) * (v + 1) := by
      have hexp : (u + 1) * (v + 1) = u * v + (u + v + 1) := by ring
      rw [hexp]
      exact Nat.lt_add_of_pos_right (by omega)
    have hlt : u * v < 2 ^ (Nat.log 2 (u + 2) + Nat.log 2 (v + 2) + 2) := by
      calc u * v < (u + 1) * (v + 1) := hstrict
        _ ≤ 2 ^ (Nat.log 2 (u + 2) + 1) * 2 ^ (Nat.log 2 (v + 2) + 1) := key
        _ = 2 ^ (Nat.log 2 (u + 2) + Nat.log 2 (v + 2) + 2) := hpow
    have hfin := Nat.log_lt_of_lt_pow (b := 2) (Nat.ne_of_gt hpos) hlt
    omega

/-- The estimate `4 * log₂ (a * n + b + 2) ≤ n + a + b + 19`, the self-improving step of the
proof of Theorem 74. -/
lemma four_mul_log2_affine_le (a b n : ℕ) :
    4 * Nat.log 2 (a * n + b + 2) ≤ n + a + b + 19 := by
  have hle : a * n + b + 2 ≤ (a + b + 2) * (n + 1) := by
    have hexp : (a + b + 2) * (n + 1) = a * n + b * n + 2 * n + a + b + 2 := by ring
    omega
  have h1 : Nat.log 2 (a * n + b + 2) ≤ Nat.log 2 ((a + b + 2) * (n + 1)) :=
    Nat.log_mono_right hle
  have h2 : Nat.log 2 ((a + b + 2) * (n + 1)) ≤
      Nat.log 2 (a + b + 2 + 2) + Nat.log 2 (n + 1 + 2) + 1 := log2_mul_le _ _
  have h3 : 4 * Nat.log 2 (a + b + 2 + 2) ≤ a + b + 2 + 6 := four_mul_log2_le (a + b + 2)
  have h4 : 4 * Nat.log 2 (n + 1 + 2) ≤ n + 1 + 6 := four_mul_log2_le (n + 1)
  omega

/-! #### Numeric forms of the basic complexity inequalities -/

/-- **Theorem 65 in numeric form:** `K(x) ≤ C(x) + K(C(x)) + O(1)`. -/
lemma kVal_le_cVal_add (U V : Map) (hU : IsOptimalPrefixConditional U)
    (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x : BitString, kVal U x ≤ cVal V x + kNatVal U (cVal V x) + c := by
  obtain ⟨c_KP, hc_KP⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  refine ⟨c_KP, fun x => ?_⟩
  have hx : plainK V x = ((cVal V x : ℕ) : ENat) :=
    (ENat.coe_toNat (plainK_ne_top V hV x)).symm
  have h1 : KPPlain U x ≤
      ((cVal V x : ℕ) : ENat) + KPPlain U (natBits (cVal V x)) + (c_KP : ENat) :=
    hc_KP x (cVal V x) hx
  rw [← kNatVal_eq_coe U hU (cVal V x), ← kVal_eq_coe U hU x] at h1
  have h2 : ((kVal U x : ℕ) : ENat) ≤
      ((cVal V x + kNatVal U (cVal V x) + c_KP : ℕ) : ENat) := by
    push_cast
    exact h1
  exact_mod_cast h2

/-- Plain complexity is below prefix complexity: `C(x) ≤ K(x) + O(1)`. -/
lemma cVal_le_kVal_add (U V : Map) (hU : IsOptimalPrefixConditional U)
    (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ y : BitString, cVal V y ≤ kVal U y + c := by
  obtain ⟨c_plain, hc_plain⟩ := plain_le_prefix V U hV hU.isPrefixDecompressor
  refine ⟨c_plain, fun y => ?_⟩
  have hy : plainK V y = ((cVal V y : ℕ) : ENat) :=
    (ENat.coe_toNat (plainK_ne_top V hV y)).symm
  have h1 : plainK V y ≤ KPPlain U y + (c_plain : ENat) := hc_plain y
  rw [hy, ← kVal_eq_coe U hU y] at h1
  have h2 : ((cVal V y : ℕ) : ENat) ≤ ((kVal U y + c_plain : ℕ) : ENat) := by
    push_cast
    exact h1
  exact_mod_cast h2

/-- Crude length bound for the prefix complexity of a number: `K(d) ≤ 2d + O(1)`. -/
lemma kNatVal_le_two_mul_self (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ d : ℕ, kNatVal U d ≤ 2 * d + c := by
  obtain ⟨c_two, hc_two⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c_two, fun d => ?_⟩
  have h_raw := hc_two (natBits d)
  have h1 : KPPlain U (natBits d) ≤ ((2 * d + c_two : ℕ) : ENat) := by
    calc KPPlain U (natBits d)
      _ ≤ ((2 * (natBits d).length : ℕ) : ENat) + (c_two : ENat) := h_raw
      _ ≤ ((2 * d : ℕ) : ENat) + (c_two : ENat) := by
        gcongr
        dsimp [natBits]
        exact length_natBits_le d
      _ = ((2 * d + c_two : ℕ) : ENat) := by push_cast; rfl
  rw [← kNatVal_eq_coe U hU d] at h1
  exact_mod_cast h1

/-- Logarithmic length bound: `K(d) ≤ 2 log₂ d + O(1)`. -/
lemma kNatVal_le_log_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ d : ℕ, kNatVal U d ≤ 2 * Nat.log 2 (d + 2) + c := by
  obtain ⟨c_two, hc_two⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c_two + 2, fun d => ?_⟩
  have h_raw := hc_two (natBits d)
  have h1 : KPPlain U (natBits d) ≤ ((2 * Nat.log 2 (d + 2) + (c_two + 2) : ℕ) : ENat) := by
    calc KPPlain U (natBits d)
      _ ≤ ((2 * (natBits d).length : ℕ) : ENat) + (c_two : ENat) := h_raw
      _ ≤ ((2 * (Nat.log 2 (d + 2) + 1) : ℕ) : ENat) + (c_two : ENat) := by
        gcongr
        dsimp [natBits]
        exact bits_len_le_log2_add_two d
      _ = ((2 * Nat.log 2 (d + 2) + (c_two + 2) : ℕ) : ENat) := by push_cast; ring
  rw [← kNatVal_eq_coe U hU d] at h1
  exact_mod_cast h1

/-- **The key "difference" step.**  If two numbers differ by `d`, then their
prefix complexities differ by at most `K(d) + O(1)`: from a shortest program for
`n` and one for `d` we can compute `m` in either direction (`addPairBits` for
`m = n + d`, `subPairBits` for `n = m + d`). -/
lemma kNatVal_diff_step (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ m n d : ℕ, (m = n + d ∨ n = m + d) →
      kNatVal U m ≤ kNatVal U n + kNatVal U d + c := by
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_add, hc_add⟩ := KPPlain_map_le U hU addPairBits addPairBits_computable
  obtain ⟨c_sub, hc_sub⟩ := KPPlain_map_le U hU subPairBits subPairBits_computable
  refine ⟨c_pair + c_add + c_sub, fun m n d hmn => ?_⟩
  have hcode : KPPlain U (natBits m) ≤
      KPPlain U (pairCode (natBits n) (natBits d)) + ((c_add + c_sub : ℕ) : ENat) := by
    rcases hmn with h | h
    · have hev : addPairBits (pairCode (natBits n) (natBits d)) = natBits m := by
        rw [addPairBits_eval, ← h]
      calc KPPlain U (natBits m)
          = KPPlain U (addPairBits (pairCode (natBits n) (natBits d))) := by rw [hev]
        _ ≤ KPPlain U (pairCode (natBits n) (natBits d)) + (c_add : ENat) := hc_add _
        _ ≤ KPPlain U (pairCode (natBits n) (natBits d)) +
              ((c_add + c_sub : ℕ) : ENat) := by
            gcongr
            exact_mod_cast Nat.le_add_right c_add c_sub
    · have hev : subPairBits (pairCode (natBits n) (natBits d)) = natBits m := by
        rw [subPairBits_eval]
        congr 1
        omega
      calc KPPlain U (natBits m)
          = KPPlain U (subPairBits (pairCode (natBits n) (natBits d))) := by rw [hev]
        _ ≤ KPPlain U (pairCode (natBits n) (natBits d)) + (c_sub : ENat) := hc_sub _
        _ ≤ KPPlain U (pairCode (natBits n) (natBits d)) +
              ((c_add + c_sub : ℕ) : ENat) := by
            gcongr
            exact_mod_cast Nat.le_add_left c_sub c_add
  have hpair : KPPlain U (pairCode (natBits n) (natBits d)) ≤
      KPPlain U (natBits n) + KPPlain U (natBits d) + (c_pair : ENat) :=
    hc_pair (natBits n) (natBits d)
  have hfin : KPPlain U (natBits m) ≤
      KPPlain U (natBits n) + KPPlain U (natBits d) +
        ((c_pair + c_add + c_sub : ℕ) : ENat) := by
    calc KPPlain U (natBits m)
        ≤ KPPlain U (pairCode (natBits n) (natBits d)) +
            ((c_add + c_sub : ℕ) : ENat) := hcode
      _ ≤ (KPPlain U (natBits n) + KPPlain U (natBits d) + (c_pair : ENat)) +
            ((c_add + c_sub : ℕ) : ENat) := by gcongr
      _ = KPPlain U (natBits n) + KPPlain U (natBits d) +
            ((c_pair + c_add + c_sub : ℕ) : ENat) := by push_cast; ring
  rw [← kNatVal_eq_coe U hU m, ← kNatVal_eq_coe U hU n, ← kNatVal_eq_coe U hU d] at hfin
  have hcast : ((kNatVal U m : ℕ) : ENat) ≤
      ((kNatVal U n + kNatVal U d + (c_pair + c_add + c_sub) : ℕ) : ENat) := by
    push_cast
    exact hfin
  exact_mod_cast hcast

/-- Bounding the prefix complexity of `m` by that of `n` plus twice their absolute difference. -/
private lemma kNatVal_le_kNatVal_add_two_mul_diff (U : Map) (c_two cD : ℕ)
    (hc2m : ∀ d, kNatVal U d ≤ 2 * d + c_two)
    (hstep : ∀ m n d, (m = n + d ∨ n = m + d) → kNatVal U m ≤ kNatVal U n + kNatVal U d + cD)
    (m n : ℕ) :
    kNatVal U m ≤ kNatVal U n + 2 * (m - n) + 2 * (n - m) + c_two + cD := by
  rcases le_total n m with h | h
  · have h1 := hstep m n (m - n) (Or.inl (by omega))
    have h2 := hc2m (m - n)
    omega
  · have h1 := hstep m n (n - m) (Or.inr (by omega))
    have h2 := hc2m (n - m)
    omega

/-- Bounding the prefix complexity of `m` by that of `n` plus logarithmic difference. -/
private lemma kNatVal_le_kNatVal_add_log_diff (U : Map) (c_log cD : ℕ)
    (hclog : ∀ d, kNatVal U d ≤ 2 * Nat.log 2 (d + 2) + c_log)
    (hstep : ∀ m n d, (m = n + d ∨ n = m + d) → kNatVal U m ≤ kNatVal U n + kNatVal U d + cD)
    (m n : ℕ) :
    kNatVal U m ≤ kNatVal U n + 2 * Nat.log 2 (m - n + (n - m) + 2) + c_log + cD := by
  rcases le_total n m with h | h
  · have hz : n - m = 0 := by omega
    rw [hz, Nat.add_zero]
    have h1 := hstep m n (m - n) (Or.inl (by omega))
    have h2 := hclog (m - n)
    omega
  · have hz : m - n = 0 := by omega
    rw [hz, Nat.zero_add]
    have h1 := hstep m n (n - m) (Or.inr (by omega))
    have h2 := hclog (n - m)
    omega

/-- **Theorem 74 (Solovay, inverse form).** `K(x) = C(x) + C(C(x)) + O(C⁽³⁾(x))`. -/
theorem solovay_prefix_plain_eq_add_condK_add (U V : Map)
    (hU : IsOptimalPrefixConditional U) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x : BitString,
      |(kVal U x : ℤ) - ((cVal V x : ℤ) + (cNatVal V (cVal V x) : ℤ))| ≤
        (c : ℤ) * ((cNatVal V (cNatVal V (cVal V x)) : ℤ) + 1) := by
  obtain ⟨c73, hc73⟩ := solovay_plain_eq_prefix_sub_prefix_prefix U V hU hV
  obtain ⟨c_KP, hc65⟩ := kVal_le_cVal_add U V hU hV
  obtain ⟨c_plain, hcp⟩ := cVal_le_kVal_add U V hU hV
  obtain ⟨c_two, hc2m⟩ := kNatVal_le_two_mul_self U hU
  obtain ⟨c_log, hclog⟩ := kNatVal_le_log_bound U hU
  obtain ⟨cD, hstep⟩ := kNatVal_diff_step U hU
  have hstep2 := kNatVal_le_kNatVal_add_two_mul_diff U c_two cD hc2m hstep
  have hstepL := kNatVal_le_kNatVal_add_log_diff U c_log cD hclog hstep
  set S : ℕ := c73 + c_KP + c_plain + c_two + c_log + cD + 1 with hSdef
  refine ⟨(12 * S + 1) * (18 + 66 * S), fun x => ?_⟩
  set c1 := cVal V x with hc1def
  set c2 := cNatVal V c1 with hc2def
  set c3 := cNatVal V c2 with hc3def
  set K1 := kVal U x with hK1def
  set K2 := kNatVal U K1 with hK2def
  set K3 := kNatVal U K2 with hK3def
  set P := kNatVal U c1 with hPdef
  set A := kNatVal U P with hAdef
  set T : ℕ := c73 * (K3 + 1) with hTdef
  have h73 : |(c1 : ℤ) - ((K1 : ℤ) - (K2 : ℤ))| ≤ (T : ℤ) := by
    have hTc : (T : ℤ) = (c73 : ℤ) * ((K3 : ℤ) + 1) := by
      rw [hTdef]; push_cast; ring
    rw [hTc]
    exact hc73 x
  have hT1 : c1 + K2 ≤ K1 + T := by
    have h := (abs_le.mp h73).2
    zify; linarith
  have hT2 : K1 ≤ c1 + K2 + T := by
    have h := (abs_le.mp h73).1
    zify; linarith
  have e1 : K1 ≤ c1 + P + c_KP := hc65 x
  have e2 : P ≤ c2 + kNatVal U c2 + c_KP := hc65 (natBits c1)
  have e3 : kNatVal U c2 ≤ c3 + kNatVal U c3 + c_KP := hc65 (natBits c2)
  have e4 : kNatVal U c3 ≤ 2 * c3 + c_two := hc2m c3
  have e5 : c2 ≤ P + c_plain := hcp (natBits c1)
  have e6 : c1 ≤ K1 + c_plain := hcp x
  have g1 : kNatVal U c2 ≤ 3 * c3 + c_two + c_KP := by omega
  have g2 : P ≤ c2 + 3 * c3 + c_two + 2 * c_KP := by omega
  have g3 : A ≤ kNatVal U c2 + 2 * (P - c2) + 2 * (c2 - P) + c_two + cD := hstep2 P c2
  have g4 : A ≤ 9 * c3 + 12 * S := by omega
  have g5 : P ≤ K2 + kNatVal U (K1 - c1) + kNatVal U (c1 - K1) + cD := by
    rcases le_total c1 K1 with h | h
    · have h1 := hstep c1 K1 (K1 - c1) (Or.inr (by omega))
      have h2 : 0 ≤ kNatVal U (c1 - K1) := Nat.zero_le _
      omega
    · have h1 := hstep c1 K1 (c1 - K1) (Or.inl (by omega))
      have h2 : 0 ≤ kNatVal U (K1 - c1) := Nat.zero_le _
      omega
  have g6 : kNatVal U (c1 - K1) ≤ 2 * c_plain + c_two := by
    have h := hc2m (c1 - K1)
    omega
  have g7 : K2 ≤ K1 - c1 + T := by omega
  have g8 : K1 - c1 ≤ K2 + T := by omega
  have g9 : kNatVal U (K1 - c1) ≤
      K3 + 2 * (K1 - c1 - K2) + 2 * (K2 - (K1 - c1)) + c_two + cD := hstep2 (K1 - c1) K2
  have g10 : kNatVal U (K1 - c1) ≤ K3 + 4 * T + c_two + cD := by omega
  have g11 : P ≤ K2 + K3 + 4 * T + 6 * S := by omega
  have g12 : K2 ≤ P + c_KP + T := by omega
  have g13 : K3 ≤ A + 2 * Nat.log 2 (K2 - P + (P - K2) + 2) + c_log + cD := hstepL K2 P
  have g15 : K2 - P + (P - K2) ≤ (1 + 5 * c73) * K3 + (5 * c73 + 7 * S) := by
    have habT : (1 + 5 * c73) * K3 + (5 * c73 + 7 * S) = K3 + 5 * T + 7 * S := by
      rw [hTdef]; ring
    omega
  have g16 : Nat.log 2 (K2 - P + (P - K2) + 2) ≤
      Nat.log 2 ((1 + 5 * c73) * K3 + (5 * c73 + 7 * S) + 2) :=
    Nat.log_mono_right (by omega)
  have g17 : 4 * Nat.log 2 ((1 + 5 * c73) * K3 + (5 * c73 + 7 * S) + 2) ≤
      K3 + (1 + 5 * c73) + (5 * c73 + 7 * S) + 19 :=
    four_mul_log2_affine_le (1 + 5 * c73) (5 * c73 + 7 * S) K3
  have g18 : K3 ≤ 2 * A + 41 * S := by omega
  have g19 : K3 ≤ 18 * c3 + 65 * S := by omega
  have g20 : T ≤ c73 * (18 * c3 + 65 * S + 1) := by
    rw [hTdef]
    exact Nat.mul_le_mul (le_refl c73) (by omega)
  have hup : K1 ≤ c1 + c2 + (3 * c3 + 4 * S) := by omega
  have hlo : c1 + c2 ≤ K1 + (5 * T + K3 + 7 * S) := by omega
  have hQ1 : 18 * c3 + 65 * S + 1 ≤ (18 + 66 * S) * (c3 + 1) := by
    have hexp : (18 + 66 * S) * (c3 + 1) = 18 * c3 + 18 + 66 * (S * c3) + 66 * S := by ring
    omega
  have hSQ : S ≤ S * (18 * c3 + 65 * S + 1) := by
    have h1 : S * 1 ≤ S * (18 * c3 + 65 * S + 1) := Nat.mul_le_mul (le_refl S) (by omega)
    simpa using h1
  have hTS : T ≤ S * (18 * c3 + 65 * S + 1) := by
    have h2 : c73 * (18 * c3 + 65 * S + 1) ≤ S * (18 * c3 + 65 * S + 1) :=
      Nat.mul_le_mul (by omega) (le_refl _)
    omega
  have hstepA : 5 * T + K3 + 7 * S ≤ (12 * S + 1) * (18 * c3 + 65 * S + 1) := by
    have hexp : (12 * S + 1) * (18 * c3 + 65 * S + 1) =
        12 * (S * (18 * c3 + 65 * S + 1)) + (18 * c3 + 65 * S + 1) := by ring
    omega
  have hstepB : (12 * S + 1) * (18 * c3 + 65 * S + 1) ≤
      (12 * S + 1) * ((18 + 66 * S) * (c3 + 1)) := Nat.mul_le_mul (le_refl _) hQ1
  have hstepC : (12 * S + 1) * ((18 + 66 * S) * (c3 + 1)) =
      (12 * S + 1) * (18 + 66 * S) * (c3 + 1) := by ring
  have hbound : 5 * T + K3 + 7 * S ≤ (12 * S + 1) * (18 + 66 * S) * (c3 + 1) :=
    hstepA.trans (hstepB.trans (le_of_eq hstepC))
  have hsmall : 3 * c3 + 4 * S ≤ (12 * S + 1) * (18 + 66 * S) * (c3 + 1) := by
    have h1 : (3 + 4 * S) * (c3 + 1) ≤ (12 * S + 1) * (18 + 66 * S) * (c3 + 1) := by
      refine Nat.mul_le_mul ?_ (le_refl _)
      have hexp : (12 * S + 1) * (18 + 66 * S) = 792 * (S * S) + 282 * S + 18 := by ring
      omega
    have h2 : 3 * c3 + 4 * S ≤ (3 + 4 * S) * (c3 + 1) := by
      have hexp : (3 + 4 * S) * (c3 + 1) = 3 * c3 + 3 + 4 * (S * c3) + 4 * S := by ring
      omega
    omega
  have hlo2 : c1 + c2 ≤ K1 + (12 * S + 1) * (18 + 66 * S) * (c3 + 1) := by omega
  have hup2 : K1 ≤ c1 + c2 + (12 * S + 1) * (18 + 66 * S) * (c3 + 1) := by omega
  rw [abs_le]
  constructor
  · have h := hlo2
    zify at h
    push_cast at h ⊢
    linarith
  · have h := hup2
    zify at h
    push_cast at h ⊢
    linarith

end Kolmogorov
