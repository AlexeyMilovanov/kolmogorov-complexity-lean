/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Class.Relative
import KolmogorovMathlib.MDLPrediction.Class.Mixture
import KolmogorovMathlib.MDLPrediction.Class.Replay
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Prefix descriptions and mixture bounds for complete blocks

The code consists of self-delimiting level and block-size data, a fixed-width
ordinal, and a partial replay program that halts on complete blocks.
Blueprint nodes: `enum:block-code`, `enum:block-prefixcode`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- The ceiling of the binary logarithm used to encode a complexity level.
Blueprint node `enum:block-prefixcode`. -/
noncomputable def levelLog (a : ℕ) : ℕ :=
  Nat.ceil (Real.logb 2 (a + 2 : ℝ))

/-- A complete block ordinal fits the finite complexity-layer bound. -/
private theorem blockOrdinal_lt
    (U : Map) (hU : IsOptimalPrefixConditional U) (a r j : ℕ) (G : List ℕ)
    (hr : r ≤ a)
    (hG : IsCompleteBlock U hU a r j G) :
    j < 2 ^ (a - r + 1) := by
  obtain ⟨n, hGeq, hlen⟩ := hG
  have hstream : IsDiscoveryStream U (discoveryStream U hU) := Classical.choose_spec
    (enum_indices_ce U hU)
  have hnodup := (hstream.2 a).1 n
  have hmem : ∀ i ∈ (List.range n).filterMap (discoveryStream U hU a), KPNat U i ≤ a := by
    intro i hi
    obtain ⟨k, _, hk2⟩ := List.mem_filterMap.mp hi
    exact ((hstream.2 a).2 i).mpr ⟨k, hk2⟩
  obtain ⟨hfin, hcard⟩ := base_program_count U a
  have hlen_La : ((List.range n).filterMap (discoveryStream U hU a)).length ≤ (Set.ncard {i : ℕ
    | KPNat U i ≤ a}) := by
    rw [← List.toFinset_card_of_nodup hnodup]
    rw [Set.ncard_eq_toFinset_card _ hfin]
    apply Finset.card_le_card
    intro i hi
    rw [Set.Finite.mem_toFinset]
    rw [List.mem_toFinset] at hi
    exact hmem i hi
  rw [hGeq, ordinalBlock, List.length_take, List.length_drop] at hlen
  have hslice := min_le_right (2 ^ r) (((List.range n).filterMap (discoveryStream U hU
    a)).length - j * 2 ^ r)
  rw [hlen] at hslice
  have hpow : 2 ^ (a + 1) = 2 ^ (a - r + 1) * 2 ^ r := by
    rw [← pow_add]
    congr 1
    omega
  have hpos : 0 < 2 ^ r := by positivity
  have hmul : (j + 1) * 2 ^ r < 2 ^ (a - r + 1) * 2 ^ r := by
    rw [add_mul, one_mul, ← hpow]
    omega
  have := Nat.lt_of_mul_lt_mul_right hmul
  omega

/-- Padding a bit encoding with zeroes preserves its decoded value. -/
private lemma decodeBits_pad (l : List Bool) (k : Nat) :
    decodeBits (l ++ List.replicate k false) = decodeBits l := by
  induction l with
  | nil =>
    simp only [List.nil_append]
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, decodeBits, ih]
  | cons b l ih =>
    cases b <;> simp [decodeBits, ih]

/-- The binary level code has enough bits to encode the level. -/
private lemma levelLog_pow_le (a : Nat) :
    a + 2 ≤ 2 ^ levelLog a := by
  unfold levelLog
  have h0 : (0 : ℝ) < a + 2 := by positivity
  have h1 : Real.logb 2 (a + 2 : ℝ) ≤ (Nat.ceil (Real.logb 2 (a + 2 : ℝ)) : ℝ) := Nat.le_ceil _
  have h2 : (a + 2 : ℝ) ≤ (2 : ℝ) ^ (Nat.ceil (Real.logb 2 (a + 2 : ℝ)) : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num) h0).mp h1
  rw [Real.rpow_natCast] at h2
  exact_mod_cast h2

/-- A bounded replay gives each complete block mixture a short prefix code. -/
private theorem blockReplay_prefixcode_bound
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : ℕ × ℕ × ℕ → Part ℕ) (hf : Partrec f) :
    ∃ c : ℕ, ∀ a r j y, 2 ≤ a → r ≤ a →
      j < 2 ^ (a - r + 1) → y ∈ f (a, r, j) →
      KPNat U y ≤ (a - r + c * levelLog a + c : ℕ) := by
  let A := fun s : BitString => decodeBits (decodeFirst (decodeFirst s))
  let N := fun s : BitString => decodeBits (decodeSecond (decodeFirst s))
  let J := fun s : BitString => decodeBits (decodeSecond s)
  let g := fun s : BitString => (f (A s, A s + 1 - N s, J s)).map natToBitString
  have hA : Computable A := decodeBits_computable.comp (decodeFirst_computable.comp
    decodeFirst_computable)
  have hN : Computable N := decodeBits_computable.comp (decodeSecond_computable.comp
    decodeFirst_computable)
  have hJ : Computable J := decodeBits_computable.comp decodeSecond_computable
  have hA1 : Computable (fun s => A s + 1) := Primrec.nat_add.to_comp.comp hA (Computable.const 1)
  have hR : Computable (fun s => A s + 1 - N s) := Primrec.nat_sub.to_comp.comp hA1 hN
  have hdec : Computable (fun s => (A s, A s + 1 - N s, J s)) := hA.pair (hR.pair hJ)
  have hg : Partrec g := (hf.comp hdec).map (computable_natToBitString.comp Computable.snd).to₂
  obtain ⟨c1, hc1⟩ := KPPlain_partrec_map_le U hU g hg
  obtain ⟨c2, hc2⟩ := KPPair_chain_upper_weak U hU
  obtain ⟨c3, hc3⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨c4, hc4⟩ := KP_cond_map_le U hU decodeSecond decodeSecond_computable
  obtain ⟨c5, hc5⟩ := KP_le_length_given_natBits_length U hU
  let c := c1 + c2 + c3 + c4 + c5 + 9
  use c
  intro a r j y _ha hr hj hy
  let ctx := pairCode (Nat.bits a) (Nat.bits (a - r + 1))
  let w := Nat.bits j ++ List.replicate (a - r + 1 - (Nat.bits j).length) false
  have hwlen : w.length = a - r + 1 := by
    dsimp [w]
    rw [List.length_append, List.length_replicate]
    have hbsize : (Nat.bits j).length ≤ a - r + 1 := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr hj
    omega
  have hr' : a + 1 - (a - r + 1) = r := by omega
  have hctx : decodeFirst (pairCode ctx w) = ctx := decodeFirst_pairCode ctx w
  have hw : decodeSecond (pairCode ctx w) = w := decodeSecond_pairCode ctx w
  have hy2 : natToBitString y ∈ g (pairCode ctx w) := by
    dsimp [g, A, N, J]
    rw [hctx, hw]
    rw [decodeFirst_pairCode (Nat.bits a) (Nat.bits (a - r + 1))]
    rw [decodeSecond_pairCode (Nat.bits a) (Nat.bits (a - r + 1))]
    rw [decodeBits_natBits, decodeBits_natBits]
    rw [decodeBits_pad, decodeBits_natBits]
    rw [hr']
    exact Part.mem_map natToBitString hy
  have h0 : KPNat U y = KPPlain U (natToBitString y) := rfl
  have h1 : KPPlain U (natToBitString y) ≤ KPPlain U (pairCode ctx w) + c1 := hc1 (pairCode ctx
    w) (natToBitString y) hy2
  have h2 : KPPlain U (pairCode ctx w) = KPPair U ctx w := rfl
  have h3 : KPPair U ctx w ≤ KPPlain U ctx + KP U w ctx + c2 := hc2 ctx w
  have h4 : KPPlain U ctx ≤ 2 * ctx.length + c3 := hc3 ctx
  have h5 : KP U w ctx ≤ KP U w (Nat.bits (a - r + 1)) + c4 := by
    have H := hc4 w ctx
    have H2 : decodeSecond ctx = Nat.bits (a - r + 1) := decodeSecond_pairCode _ _
    rw [H2] at H
    exact H
  have h6 : KP U w (Nat.bits (a - r + 1)) ≤ (a - r + 1 : ENat) + c5 := by
    have H := hc5 w
    rw [hwlen] at H
    exact H
  have hKP : KPNat U y ≤ (2 * ctx.length + c3) + ((a - r + 1) + c5 + c4) + c2 + c1 := by
    calc
      KPNat U y = KPPlain U (natToBitString y) := rfl
      _ ≤ KPPair U ctx w + c1 := by
        rw [← h2]
        exact h1
      _ ≤ KPPlain U ctx + KP U w ctx + c2 + c1 := by
        have H1 : KPPair U ctx w + (c1 : ENat) ≤ KPPlain U ctx + KP U w ctx + (c2 : ENat) + (c1
          : ENat) := by gcongr
        exact H1
      _ ≤ (2 * ctx.length + c3) + (KP U w (Nat.bits (a - r + 1)) + c4) + c2 + c1 := by
        have H1 : KPPlain U ctx + KP U w ctx ≤ (2 * ctx.length + c3 : ENat) + (KP U w (Nat.bits
          (a - r + 1)) + c4) := add_le_add h4 h5
        have H2 : KPPlain U ctx + KP U w ctx + (c2 : ENat) + (c1 : ENat) ≤ (2 * ctx.length + c3
          : ENat) + (KP U w (Nat.bits (a - r + 1)) + c4) + (c2 : ENat) + (c1 : ENat) := by gcongr
        exact H2
      _ ≤ (2 * ctx.length + c3) + ((a - r + 1 : ENat) + c5 + c4) + c2 + c1 := by
        have H1 : KP U w (Nat.bits (a - r + 1)) + (c4 : ENat) ≤ (a - r + 1 : ENat) + c5 + c4 :=
          by gcongr
        have H2 : (2 * ctx.length + c3 : ENat) + (KP U w (Nat.bits (a - r + 1)) + (c4 : ENat))
          + (c2 : ENat) + (c1 : ENat) ≤ (2 * ctx.length + c3 : ENat) + ((a - r + 1 : ENat) + c5
            + c4) + (c2 : ENat) + (c1 : ENat) := by gcongr
        exact H2
  have h_len_a : (Nat.bits a).length ≤ levelLog a := by
    rw [Nat.size_eq_bits_len]
    have := levelLog_pow_le a
    have : a < 2 ^ levelLog a := by omega
    exact Nat.size_le.mpr this
  have h_len_m : (Nat.bits (a - r + 1)).length ≤ levelLog a := by
    rw [Nat.size_eq_bits_len]
    have := levelLog_pow_le a
    have : a - r + 1 < 2 ^ levelLog a := by omega
    exact Nat.size_le.mpr this
  have h_ctx_len : ctx.length ≤ 3 * levelLog a + 1 := by
    dsimp [ctx]
    rw [length_pairCode]
    omega
  refine hKP.trans (Nat.cast_le.mpr ?_)
  have h_c_mul : 6 * levelLog a ≤ c * levelLog a := Nat.mul_le_mul_right _ (by omega)
  push_cast
  omega

/-- A complete block mixture has a prefix description using its short ordinal.
Blueprint node `enum:block-prefixcode`. -/
theorem enum_block_prefixcode (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    ∃ cA : ℕ, ∀ a r j G, 2 ≤ a → r ≤ a →
      IsCompleteBlock U hU a r j G →
        KPNat U (A.mix G) ≤ (a - r + cA * levelLog a + cA : ℕ) := by
  have ⟨hf, hf_spec⟩ := enum_block_replay U hU A
  have ⟨cA, hcA⟩ := blockReplay_prefixcode_bound U hU
    (fun p : ℕ × ℕ × ℕ => blockReplay U hU A p.1 p.2.1 p.2.2) hf
  use cA
  intro a r j G ha hr hG
  have hj := blockOrdinal_lt U hU a r j G hr hG
  have hy := hf_spec a r j G hG
  exact hcA a r j (A.mix G) ha hr hj hy

/-! ## Mixture bounds -/

/-- A complete block mixture has a short prefix description. -/
private lemma blockMixture_code_bound (U : Map)
    (hU : IsOptimalPrefixConditional U) (A : EffectiveMixtureClass U hU) :
    ∃ cA : ℕ, ∀ a r j G, 2 ≤ a → r ≤ a → IsCompleteBlock U hU a r j G →
      classComplexity U hU A (A.model (A.mix G)) ≤ a - r + cA * levelLog a + cA := by
  obtain ⟨cA, hcA⟩ := enum_block_prefixcode U hU A
  use cA
  intro a r j G ha hr hG
  have h1 := hcA a r j G ha hr hG
  have h2 : classComplexity U hU A (A.model (A.mix G)) ≤ (KPNat U (A.mix G)).toNat := by
    have H : classComplexityENat U hU A (A.model (A.mix G)) ≤ KPNat U (A.mix G) := by
      dsimp [classComplexityENat]
      exact iInf_le (fun (j : {j : ℕ // A.model j = A.model (A.mix G)}) =>
        (KPNat U ↑j : ENat)) (⟨A.mix G, rfl⟩ : {j : ℕ // A.model j = A.model (A.mix G)})
    dsimp [classComplexity]
    apply ENat.toNat_le_toNat H
    have H2 : KPNat U (A.mix G) ≤ (a - r + cA * levelLog a + cA : ENat) := h1
    intro h3
    rw [h3] at H2
    exact WithTop.not_top_le_coe _ H2
  have h3 : (KPNat U (A.mix G)).toNat ≤ a - r + cA * levelLog a + cA := by
    have H2 : KPNat U (A.mix G) ≤ (a - r + cA * levelLog a + cA : ENat) := h1
    have H4 := ENat.toNat_le_toNat H2
    have H5 : (a - r + cA * levelLog a + cA : ENat) ≠ ⊤ :=
      WithTop.coe_ne_top
    exact H4 H5
  omega

/-- The block mixture retains a fixed share of every member mass. -/
private lemma blockMixture_member_mass (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    ∀ a r j G, 2 ≤ a → r ≤ a →
      IsCompleteBlock U hU a r j G →
        ∀ i ∈ G, ∀ x : BitString,
          (2 : ℝ≥0∞)⁻¹ ^ r * cantorMass (A.model i) x ≤
            cantorMass (A.model (A.mix G)) x := by
  intro a r j G ha hr hG i hi x
  rcases hG with ⟨n, rfl, hlen⟩
  have hG_ne : ordinalBlock ((List.range n).filterMap (discoveryStream U hU a)) r j ≠ [] := by
    intro h
    rw [h] at hlen
    simp only [List.length_nil] at hlen
    have : 0 < 2 ^ r := by positivity
    omega
  have H := enum_mix_mass U hU A
    (ordinalBlock ((List.range n).filterMap (discoveryStream U hU a)) r j) hG_ne i hi x
  rw [hlen] at H
  have H2 : (((2 ^ r : ℕ) : ℝ≥0∞)⁻¹) = (2 : ℝ≥0∞)⁻¹ ^ r := by
    push_cast
    rw [ENNReal.inv_pow]
  rw [H2] at H
  exact H

/-- Every member of a complete block contributes mass, and the mixture has a
short relative description. Blueprint node `enum:block-code`. -/
theorem blockMixture_complexity_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    ∃ cA : ℕ, ∀ a r j G, 2 ≤ a → r ≤ a →
      IsCompleteBlock U hU a r j G →
        A.model (A.mix G) ∈ A.carrier ∧
        classComplexity U hU A (A.model (A.mix G)) ≤
          a - r + cA * levelLog a + cA ∧
        ∀ i ∈ G, ∀ x : BitString,
          (2 : ℝ≥0∞)⁻¹ ^ r * cantorMass (A.model i) x ≤
            cantorMass (A.model (A.mix G)) x := by
  obtain ⟨cA, hcA⟩ := blockMixture_code_bound U hU A
  use cA
  intro a r j G ha hr hG
  have h1 : A.model (A.mix G) ∈ A.carrier := ⟨A.mix G, rfl⟩
  refine ⟨h1, ?_, ?_⟩
  · exact hcA a r j G ha hr hG
  · exact blockMixture_member_mass U hU A a r j G ha hr hG
end Kolmogorov.MDLPrediction
