/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Oracle.Universal
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Prefix.CountableKraft
import Mathlib.Analysis.SpecialFunctions.Log.Base
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun

/-!
# Oracle prefix complexity and its basic bounds

This module turns the optimal oracle prefix machine `optimalOraclePrefix A` of
`KolmogorovMathlib.Oracle.Universal` into the complexity functions used by the oracle-relative
point-to-set principles (blueprint nodes `oracle:complexity`, `oracle:kraft`, `oracle:monotone`
and `oracle:tuple`).

It defines the conditional prefix complexity `oraclePrefixComplexity A x y` with values in `ℕ∞`,
its natural-number shadow `oraclePrefixComplexityNat` (finite by
`exists_optimalOraclePrefix_finite`), the unconditional complexity `oracleComplexity` of a string,
the complexities `oracleNatComplexity` and `oraclePairComplexity` of natural numbers and pairs of
natural numbers (through the injective encodings `natBits` and `pairCode`), and the complexity
`oracleSetComplexity` of a set of strings.

The main results are:

* `oracle_kraft` and `oracle_kraft_finite_sublevels`: the Kraft sum over natural numbers is at
  most one, so every complexity sublevel set is finite;
* `oracle_tuple_bounds`, `oracle_tuple_bounds_overhead` and `oracle_tuple_bounds_composition`:
  projection, tuple overhead and effective composition bounds, each up to a constant depending
  only on the oracle (and the operation);
* `oracle_monotonicity`: strengthening the oracle changes complexity by a bounded constant.

These estimates are used by the threshold-set lemmas of
`KolmogorovMathlib.Oracle.PrefixComplexity.MonotonicityThreshold` and by the point-to-set
principles of `KolmogorovMathlib.PointToSet`.
-/

namespace Kolmogorov.PointToSet

open scoped ENNReal Computability

/-- Conditional prefix complexity for the fixed optimal oracle machine, before taking
its finite natural shadow. Blueprint node `oracle:complexity`. -/
noncomputable def oraclePrefixComplexity (A : Set ℕ) (x y : BitString) : ENat :=
  KP (optimalOraclePrefix A) x y

/-- The natural shadow of conditional prefix complexity; finiteness was established by
`exists_optimalOraclePrefix_finite`. Blueprint node `oracle:complexity`. -/
noncomputable def oraclePrefixComplexityNat (A : Set ℕ) (x y : BitString) : ℕ :=
  (oraclePrefixComplexity A x y).toNat

/-- Unconditional relative prefix complexity uses the empty conditional context.
Blueprint node `oracle:complexity`. -/
noncomputable def oracleComplexity (A : Set ℕ) (x : BitString) : ℕ :=
  oraclePrefixComplexityNat A x []

/-- Natural-number complexity uses the existing injective binary encoding.
Blueprint node `oracle:complexity`. -/
noncomputable def oracleNatComplexity (A : Set ℕ) (i : ℕ) : ℕ :=
  oracleComplexity A (natBits i)

/-- Complexity of a pair of naturals uses the existing `pairCode` infrastructure.
Blueprint node `oracle:complexity`. -/
noncomputable def oraclePairComplexity (A : Set ℕ) (i n : ℕ) : ℕ :=
  oracleComplexity A (pairCode (natBits i) (natBits n))

/-- Complexity of a set of strings is an indexed infimum, with value infinity on the
empty set. Blueprint node `oracle:complexity`. -/
noncomputable def oracleSetComplexity (A : Set ℕ) (S : Set BitString) : ENat :=
  ⨅ x ∈ S, oraclePrefixComplexity A x []

/-- The natural shadow agrees with the original extended natural complexity.
Blueprint node `oracle:complexity`. -/
theorem oraclePrefixComplexity_coe (A : Set ℕ) (x y : BitString) :
    (oraclePrefixComplexityNat A x y : ENat) = oraclePrefixComplexity A x y := by
  rw [oraclePrefixComplexityNat]
  exact ENat.natCast_toNat (exists_optimalOraclePrefix_finite A x y)

/-- Kraft's inequality for the injectively encoded natural outputs of the oracle machine.
Blueprint node `oracle:kraft`. -/
theorem oracle_kraft (A : Set ℕ) :
    (∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i) ≤ 1 := by
  let U := optimalOraclePrefix A
  have hU_spec := exists_optimalOraclePrefix_spec A
  have hU_prefix : IsPrefixMachine U := hU_spec.2.1
  have h_str_apriori : (∑' x : BitString, aprioriMeasure U x []) ≤ 1 :=
    tsum_aprioriMeasure_le_one U [] hU_prefix
  have h_le_apriori : ∀ x, complexityWeight (KP U x []) ≤ aprioriMeasure U x [] :=
    fun x => complexityWeight_KP_le_aprioriMeasure U x []
  have h_str : (∑' x : BitString, complexityWeight (KP U x [])) ≤ 1 :=
    (ENNReal.tsum_le_tsum h_le_apriori).trans h_str_apriori
  have h_inj : Function.Injective natBits := natBits_injective
  have h_eq : ∀ i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i =
      complexityWeight (KP U (natBits i) []) := by
    intro i
    rw [oracleNatComplexity, oracleComplexity, oraclePrefixComplexityNat,
      oraclePrefixComplexity]
    have h2 : KP U (natBits i) [] ≠ ⊤ := by
      exact exists_optimalOraclePrefix_finite A (natBits i) []
    have h3 : (↑((KP U (natBits i) []).toNat) : ENat) = KP U (natBits i) [] := by
      exact ENat.natCast_toNat h2
    rw [←complexityWeight_coe, h3]
  have h_sum_eq : (∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i) =
      (∑' i : ℕ, complexityWeight (KP U (natBits i) [])) := by
    apply tsum_congr
    intro b
    exact h_eq b
  rw [h_sum_eq]
  have h_le := ENNReal.tsum_comp_le_tsum_of_injective h_inj
    (fun x => complexityWeight (KP U x []))
  exact le_trans h_le h_str

/-- Each finite natural complexity sublevel contains only finitely many ideal indices.
Blueprint node `oracle:kraft`. -/
theorem oracle_kraft_finite_sublevels (A : Set ℕ) (b : ℕ) :
    {i : ℕ | oracleNatComplexity A i ≤ b}.Finite := by
  let S := {i : ℕ | oracleNatComplexity A i ≤ b}
  by_cases h_fin : S.Finite
  · exact h_fin
  · have h_inf : Infinite S := Set.Infinite.to_subtype h_fin
    have h_kraft := oracle_kraft A
    have hc : ((2 : ℝ≥0∞)⁻¹) ^ b ≠ 0 := by
      have h2 : (2 : ℝ≥0∞)⁻¹ ≠ 0 := by norm_num
      exact pow_ne_zero b h2
    have h_tsum_S : ∑' (x : S), ((2 : ℝ≥0∞)⁻¹) ^ b = ∞ :=
      ENNReal.tsum_const_eq_top_of_ne_zero hc
    have h_pow_le : ∀ (x : S),
        ((2 : ℝ≥0∞)⁻¹) ^ b ≤ ((2 : ℝ≥0∞)⁻¹) ^ (oracleNatComplexity A x) := by
      intro ⟨i, hi⟩
      have h_le : oracleNatComplexity A i ≤ b := hi
      have h1 : (2 : ℝ≥0∞)⁻¹ ≤ 1 := by norm_num
      have h2 : ((2 : ℝ≥0∞)⁻¹⁻¹) ^ (oracleNatComplexity A i) ≤ ((2 : ℝ≥0∞)⁻¹⁻¹) ^ b := by
        apply pow_le_pow_right₀
        · exact ENNReal.one_le_inv.mpr h1
        · exact h_le
      have h3 : ((2 : ℝ≥0∞)⁻¹) ^ (oracleNatComplexity A i)
          = (((2 : ℝ≥0∞)⁻¹⁻¹) ^ (oracleNatComplexity A i))⁻¹ := by
        rw [← ENNReal.inv_pow, inv_inv]
      have h4 : ((2 : ℝ≥0∞)⁻¹) ^ b = (((2 : ℝ≥0∞)⁻¹⁻¹) ^ b)⁻¹ := by
        rw [← ENNReal.inv_pow, inv_inv]
      rw [h3, h4]
      exact ENNReal.inv_le_inv.mpr h2
    have h_tsum_le : ∑' (x : S), ((2 : ℝ≥0∞)⁻¹) ^ b
        ≤ ∑' (x : S), ((2 : ℝ≥0∞)⁻¹) ^ (oracleNatComplexity A x) :=
      ENNReal.tsum_le_tsum h_pow_le
    have h_tsum_subtype_le : ∑' (x : S), ((2 : ℝ≥0∞)⁻¹) ^ (oracleNatComplexity A x)
        ≤ ∑' (i : ℕ), ((2 : ℝ≥0∞)⁻¹) ^ (oracleNatComplexity A i) := by
      classical
      have h_ind : ∑' (x : S), ((2 : ℝ≥0∞)⁻¹) ^ (oracleNatComplexity A (x : ℕ))
          = ∑' i, Set.indicator S (fun i => ((2 : ℝ≥0∞)⁻¹) ^ (oracleNatComplexity A i)) i :=
        tsum_subtype S fun i => (2⁻¹ : ℝ≥0∞) ^ oracleNatComplexity A i
      rw [h_ind]
      apply ENNReal.tsum_le_tsum
      intro i
      unfold Set.indicator
      by_cases h : i ∈ S <;> simp [h]
    have h_infty_le_one : (∞ : ℝ≥0∞) ≤ 1 := by
      calc
        ∞ = ∑' (x : S), ((2 : ℝ≥0∞)⁻¹) ^ b := h_tsum_S.symm
        _ ≤ ∑' (x : S), ((2 : ℝ≥0∞)⁻¹) ^ (oracleNatComplexity A x) := h_tsum_le
        _ ≤ ∑' (i : ℕ), ((2 : ℝ≥0∞)⁻¹) ^ (oracleNatComplexity A i) := h_tsum_subtype_le
        _ ≤ 1 := h_kraft
    exact False.elim (lt_irrefl _ (lt_of_le_of_lt h_infty_le_one ENNReal.one_lt_top))

/-- Taking the first component of an encoded pair costs a uniform additive constant in prefix
complexity for the fixed optimal oracle machine: the machine that applies `decodeFirst` to the
outputs of `optimalOraclePrefix A` is again an `A`-decompressor with a prefix-free domain. -/
private theorem exists_kp_decodeFirst_le (A : Set ℕ) :
    ∃ c : ℕ, ∀ x y,
      KP (optimalOraclePrefix A) (decodeFirst x) y ≤
        KP (optimalOraclePrefix A) x y + (c : ENat) := by
  let U := optimalOraclePrefix A
  let D : Map := fun p => (U p).map decodeFirst
  have hU_spec := exists_optimalOraclePrefix_spec A
  have hU_decomp : IsDecompressorIn (charOracle A) U := hU_spec.1
  have hU_prefix : IsPrefixMachine U := hU_spec.2.1
  have hD_decomp : IsDecompressorIn (charOracle A) D := by
    have h1 : PartrecIn {charOracle A} (mapToNatFun U) := hU_decomp
    let g : ℕ → ℕ → ℕ := fun _ n =>
      Encodable.encode (decodeFirst ((Encodable.decode n : Option BitString).getD []))
    have hg_comp : ComputableIn₂ {charOracle A} g := by
      have hc : Computable₂ g := by
        apply Computable.comp Computable.encode
        apply Computable.comp CodedFiniteDistribution.decodeFirst_primrec.to_comp
        apply Computable.comp (Computable.option_getD (Computable.decode) (Computable.const []))
        exact Computable.snd
      exact hc.computableIn.to₂
    have h2 : PartrecIn {charOracle A} (fun a => (mapToNatFun U a).map (g a)) := by
      exact PartrecIn.map h1 hg_comp
    have h3 : ∀ a, (mapToNatFun U a).map (g a) = mapToNatFun D a := by
      intro a
      unfold mapToNatFun D g
      ext n
      simp only [Part.mem_map_iff, Part.mem_bind_iff]
      constructor
      · rintro ⟨y, ⟨w, hw1, hw2⟩, rfl⟩
        use w
        constructor
        · exact hw1
        · obtain ⟨bs, hbs1, hbs2⟩ := hw2
          use decodeFirst bs
          constructor
          · use bs
          · have eq1 : Encodable.decode y = some bs := by
              rw [← hbs2, Encodable.encodek]
            rw [eq1, Option.getD_some]
      · rintro ⟨w, hw1, ⟨bs, ⟨bs_orig, hbs_orig1, hbs_orig2⟩, hbs_eq⟩⟩
        use Encodable.encode bs_orig
        constructor
        · use w
          constructor
          · exact hw1
          · use bs_orig
        · rw [Encodable.encodek, Option.getD_some, hbs_orig2, hbs_eq]
    exact PartrecIn.of_eq h2 h3
  have hD_prefix : IsPrefixMachine D := by
    intro y p hp q hq hpre
    change (U (p, y)).Dom at hp
    change (U (q, y)).Dom at hq
    exact hU_prefix y hp hq hpre
  have H := hU_spec.2.2 D hD_decomp hD_prefix
  obtain ⟨c, hc⟩ := H
  use c
  intro x y
  calc
    KP U (decodeFirst x) y ≤ KP D (decodeFirst x) y + c := hc (decodeFirst x) y
    _ ≤ KP U x y + c := by
      gcongr
      apply sInf_le_sInf
      rintro n ⟨p, ⟨h_dom, h_eq⟩, rfl⟩
      exact ⟨p, ⟨h_dom, congrArg decodeFirst h_eq⟩, rfl⟩

/-- Projection from an encoded pair costs one constant independent of both entries.
Blueprint node `oracle:tuple`. -/
theorem oracle_tuple_bounds (A : Set ℕ) :
    ∃ c : ℕ, ∀ i n, oracleNatComplexity A i ≤ oraclePairComplexity A i n + c := by
  obtain ⟨c, hc⟩ := exists_kp_decodeFirst_le A
  use c
  intro i n
  have h1 := hc (pairCode (natBits i) (natBits n)) []
  have h2 : decodeFirst (pairCode (natBits i) (natBits n)) = natBits i := decodeFirst_pairCode _ _
  rw [h2] at h1
  unfold oracleNatComplexity oraclePairComplexity oracleComplexity
  have H2 : ((oraclePrefixComplexityNat A (natBits i) []) : ENat) ≤
      ((oraclePrefixComplexityNat A (pairCode (natBits i) (natBits n)) []) : ENat) +
        (c : ENat) := by
    have eq1 := oraclePrefixComplexity_coe A (natBits i) []
    have eq2 := oraclePrefixComplexity_coe A (pairCode (natBits i) (natBits n)) []
    rw [eq1, eq2]
    exact h1
  exact ENat.natCast_le_natCast.mp (by
    have H3 : (((oraclePrefixComplexityNat A (pairCode (natBits i) (natBits n)) []) + c : ℕ) :
        ENat) = ((oraclePrefixComplexityNat A (pairCode (natBits i) (natBits n)) []) : ENat) +
          (c : ENat) := by
      simp only [ENat.natCast_add]
    rw [← H3] at H2
    exact H2
  )

/-- The numerical and typed formulations of relative decompressor computability agree. -/
lemma isDecompressorIn_iff_partrecIn (O : ℕ →. ℕ) (D : Map) :
    IsDecompressorIn O D ↔ PartrecIn {O} D := by
  unfold IsDecompressorIn
  rw [RecursiveIn.iff_nat]
  rfl

/-- Read a self-delimiting string followed by a `U`-program, run that program, and
append the supplied string to its output as an encoded pair. Reject malformed headers. -/
private def headerDecoder (U : Map) : Map := fun pr =>
  if pr.1 = pairCode (decodeFirst pr.1) (decodeSecond pr.1) then
    (U (decodeSecond pr.1, pr.2)).map (fun x => pairCode x (decodeFirst pr.1))
  else Part.none

/-- Prefix-comparable pair codes have identical first components and
prefix-comparable remainders. -/
private lemma eq_and_prefix_of_pairCode_prefix {x z p q : BitString}
    (h : pairCode x p <+: pairCode z q) : x = z ∧ p <+: q := by
  obtain ⟨r, hr⟩ := h
  have hn := natCode_append_inj (by simpa [pairCode, List.append_assoc] using hr)
  obtain ⟨hx, hpq⟩ := List.append_inj hn.2 hn.1
  exact ⟨hx, ⟨r, hpq⟩⟩

/-- A valid header followed by a producing program gives the claimed pair output. -/
private lemma headerDecoder_produces (U : Map)
    (x p y z : BitString) (h : produces U p y x) :
    produces (headerDecoder U) (pairCode z p) y (pairCode x z) := by
  change _ ∈ (if pairCode z p =
      pairCode (decodeFirst (pairCode z p)) (decodeSecond (pairCode z p)) then
    (U (decodeSecond (pairCode z p), y)).map
      (fun x => pairCode x (decodeFirst (pairCode z p))) else Part.none)
  rw [decodeFirst_pairCode, decodeSecond_pairCode, ite_eq_left rfl]
  rw [Part.mem_map_iff]
  exact ⟨x, h, rfl⟩

/-- The self-delimiting header preserves prefix-freeness of the program domain. -/
private lemma headerDecoder_isPrefixMachine (U : Map)
    (hU : IsPrefixMachine U) :
    IsPrefixMachine (headerDecoder U) := by
  intro y p hp q hq hpre
  change (headerDecoder U (p, y)).Dom at hp
  change (headerDecoder U (q, y)).Dom at hq
  dsimp [headerDecoder] at hp hq
  split_ifs at hp with hpvalid
  · split_ifs at hq with hqvalid
    · have hparsed : decodeFirst p = decodeFirst q ∧ decodeSecond p <+: decodeSecond q :=
        eq_and_prefix_of_pairCode_prefix (by rwa [← hpvalid, ← hqvalid])
      have hsuffix : decodeSecond p = decodeSecond q := hU y hp hq hparsed.2
      rw [hpvalid, hqvalid, hparsed.1, hsuffix]
    · exact False.elim hq
  · exact False.elim hp

/-- Parsing the header and pairing the output preserve computability in the same oracle. -/
private lemma headerDecoder_isDecompressorIn (O : ℕ →. ℕ) (U : Map)
    (hU : IsDecompressorIn O U) :
    IsDecompressorIn O (headerDecoder U) := by
  rw [isDecompressorIn_iff_partrecIn] at hU ⊢
  have hfirst : Primrec (fun pr : BitString × BitString => decodeFirst pr.1) :=
    CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.fst
  have hsecond : Primrec (fun pr : BitString × BitString => decodeSecond pr.1) :=
    CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.fst
  have hpair : Primrec (fun pr : BitString × BitString =>
      pairCode (decodeFirst pr.1) (decodeSecond pr.1)) :=
    CodedFiniteDistribution.pairCode_primrec.comp hfirst hsecond
  have hguard : Computable (fun pr : BitString × BitString =>
      decide (pr.1 = pairCode (decodeFirst pr.1) (decodeSecond pr.1))) :=
    (PrimrecPred.decide (Primrec.eq.comp Primrec.fst hpair)).to_comp
  have hrun : PartrecIn {O} (fun pr : BitString × BitString =>
      U (decodeSecond pr.1, pr.2)) :=
    hU.comp (hsecond.to_comp.pair Computable.snd).computableIn
  have hpost : Computable₂ (fun (pr : BitString × BitString) (x : BitString) =>
      pairCode x (decodeFirst pr.1)) :=
    (CodedFiniteDistribution.pairCode_primrec.comp Primrec.snd
      (hfirst.comp Primrec.fst)).to_comp.to₂
  exact (PartrecIn.cond hguard.computableIn (hrun.map hpost.computableIn₂)
    PartrecIn.none).of_eq (fun pr => by
      dsimp [headerDecoder]
      simp only [Bool.cond_decide])

/-- The binary length estimate also holds at zero because the logarithm uses `n + 1`. -/
theorem length_bits_le_logb_add_one (n : ℕ) :
    ((Nat.bits n).length : ℝ) ≤ Real.logb 2 (n + 1) + 1 := by
  have hlen : (Nat.bits n).length ≤ Nat.log 2 (n + 1) + 1 := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr ((Nat.lt_succ_self n).trans
      (Nat.lt_pow_succ_log_self (by decide) (n + 1)))
  have hcast : ((Nat.bits n).length : ℝ) ≤ (Nat.log 2 (n + 1) : ℝ) + 1 := by
    exact_mod_cast hlen
  have hlog := Real.natLog_le_logb (n + 1) 2
  push_cast at hlog
  linarith

/-- Supplying a natural second entry costs at most twice its binary logarithm and a
constant, uniformly in both entries. Blueprint node `oracle:tuple`. -/
theorem oracle_tuple_bounds_overhead (A : Set ℕ) :
    ∃ c : ℕ, ∀ i n, (oraclePairComplexity A i n : ℝ) ≤
      oracleNatComplexity A i + 2 * Real.logb 2 (n + 1) + c := by
  let U := optimalOraclePrefix A
  have hU := exists_optimalOraclePrefix_spec A
  obtain ⟨c, hc⟩ := hU.2.2 (headerDecoder U)
    (headerDecoder_isDecompressorIn _ U hU.1)
    (headerDecoder_isPrefixMachine U hU.2.1)
  refine ⟨c + 3, ?_⟩
  intro i n
  obtain ⟨p, hp, hlen⟩ := exists_program_of_KP_ne_top
    (exists_optimalOraclePrefix_finite A (natBits i) [])
  have hlenNat : p.length = oracleNatComplexity A i := by
    apply ENat.natCast_inj.mp
    exact hlen.trans (oraclePrefixComplexity_coe A (natBits i) []).symm
  have hprod := headerDecoder_produces U
    (natBits i) p [] (natBits n) hp
  have hbound : (oraclePairComplexity A i n : ENat) ≤
      ((oracleNatComplexity A i + 2 * (Nat.bits n).length + 1 + c : ℕ) : ENat) := by
    calc
      (oraclePairComplexity A i n : ENat) =
          KP U (pairCode (natBits i) (natBits n)) [] :=
        oraclePrefixComplexity_coe A _ []
      _ ≤ KP (headerDecoder U)
          (pairCode (natBits i) (natBits n)) [] + c := hc _ []
      _ ≤ ((pairCode (natBits n) p).length : ENat) + c := by
        gcongr
        exact KP_le_programLength_of_produces hprod
      _ = ((oracleNatComplexity A i + 2 * (Nat.bits n).length + 1 + c : ℕ) : ENat) := by
        rw [length_pairCode, hlenNat]
        dsimp [natBits]
        push_cast
        ring
  have hreal : (oraclePairComplexity A i n : ℝ) ≤
      (oracleNatComplexity A i : ℝ) + 2 * ((Nat.bits n).length : ℝ) + 1 + c := by
    exact_mod_cast ENat.natCast_le_natCast.mp hbound
  have hlog := length_bits_le_logb_add_one n
  push_cast
  linarith

/-- A relative partial operation on strings costs one constant in complexity: every output
`x ∈ G w` has complexity at most that of the input `w` plus a constant depending only on `G`
and the oracle. -/
private theorem exists_oracleComplexity_le_of_partrecIn
    (A : Set ℕ) (G : BitString →. BitString)
    (hG : PartrecIn {charOracle A} G) :
    ∃ c : ℕ, ∀ w x, x ∈ G w →
      oracleComplexity A x ≤ oracleComplexity A w + c := by
  let U := optimalOraclePrefix A
  let D : Map := fun pair => (U pair).bind G
  have hU_spec := exists_optimalOraclePrefix_spec A
  have hU_decomp : IsDecompressorIn (charOracle A) U := hU_spec.1
  have hU_prefix : IsPrefixMachine U := hU_spec.2.1
  have hD_decomp : IsDecompressorIn (charOracle A) D := by
    rw [isDecompressorIn_iff_partrecIn]
    have hU_rec : PartrecIn {charOracle A} U := by
      rw [← isDecompressorIn_iff_partrecIn]
      exact hU_decomp
    exact relative_closure_comp A U G hU_rec hG
  have hD_prefix : IsPrefixMachine D := by
    intro y p hp q hq hpre
    have hp' : (U (p, y)).Dom := by
      have h := hp
      simp only [D] at h
      exact h.1
    have hq' : (U (q, y)).Dom := by
      have h := hq
      simp only [D] at h
      exact h.1
    exact hU_prefix y hp' hq' hpre
  obtain ⟨c, hc⟩ := hU_spec.2.2 D hD_decomp hD_prefix
  use c
  intro w x h_prod
  have h_w_fin : oraclePrefixComplexity A w [] ≠ ⊤ := by
    exact exists_optimalOraclePrefix_finite A w []
  obtain ⟨p, hp_prod, hp_len⟩ := exists_program_of_KP_ne_top h_w_fin
  have h_D_prod : x ∈ D (p, []) := by
    change x ∈ (U (p, [])).bind G
    have hw_U : w ∈ U (p, []) := hp_prod
    exact Part.mem_bind_iff.mpr ⟨w, hw_U, h_prod⟩
  have hc_bound := hc x []
  have hlenNat : p.length = oracleComplexity A w := by
    apply ENat.natCast_inj.mp
    exact hp_len.trans (oraclePrefixComplexity_coe A w []).symm
  have hbound : (oracleComplexity A x : ENat) ≤
      ((oracleComplexity A w + c : ℕ) : ENat) := by
    calc
      (oracleComplexity A x : ENat) = KP U x [] := oraclePrefixComplexity_coe A x []
      _ ≤ KP D x [] + c := hc x []
      _ ≤ (p.length : ENat) + c := by
        gcongr
        exact KP_le_programLength_of_produces h_D_prod
      _ = ((oracleComplexity A w + c : ℕ) : ENat) := by
        rw [hlenNat, ENat.natCast_add]
  exact ENat.natCast_le_natCast.mp hbound

/-- `IsConcatParse U k w xs` says that the string `w` is the concatenation of `k` programs
whose outputs for `U` in the empty context are exactly the entries of `xs`. -/
private def IsConcatParse
    (U : Map) (k : ℕ) (w : BitString) (xs : List BitString) : Prop :=
  ∃ ps : List BitString, ps.length = k ∧ ps.flatten = w ∧
    List.Forall₂ (fun p x => produces U p [] x) ps xs

/-- The machine that is defined on a string exactly when it is a concatenation of `k`
halting `U`-programs, and then outputs the code of the list of their outputs. -/
private noncomputable def concatDecoder
    (U : Map) (k : ℕ) : Map := fun pr =>
  Part.mk
    (∃ xs, IsConcatParse U k pr.1 xs)
    (fun h => listCode (Classical.choose h))

/-- For a prefix machine `U`, two prefix-comparable strings that parse as concatenations of
`k` programs are equal and have the same list of outputs. -/
private theorem IsConcatParse.eq_of_prefix
    (U : Map) (hU : IsPrefixMachine U) (k : ℕ)
    (w v : BitString) (xs ys : List BitString)
    (hw : IsConcatParse U k w xs)
    (hv : IsConcatParse U k v ys)
    (hpre : w <+: v) : w = v ∧ xs = ys := by
  induction k generalizing w v xs ys with
  | zero =>
      rcases hw with ⟨ps, hps, rfl, hxs⟩
      rcases hv with ⟨qs, hqs, rfl, hys⟩
      have ep : ps = [] := List.length_eq_zero_iff.mp hps
      have eq : qs = [] := List.length_eq_zero_iff.mp hqs
      subst ps
      subst qs
      cases hxs
      cases hys
      exact ⟨rfl, rfl⟩
  | succ k ih =>
      rcases hw with ⟨ps, hps, rfl, hxs⟩
      rcases hv with ⟨qs, hqs, rfl, hys⟩
      cases ps with
      | nil => simp at hps
      | cons p ps =>
          cases qs with
          | nil => simp at hqs
          | cons q qs =>
              rcases List.forall₂_cons_left_iff.mp hxs with
                ⟨x, xt, hp, hpt, rfl⟩
              rcases List.forall₂_cons_left_iff.mp hys with
                ⟨y, yt, hq, hqt, rfl⟩
              change p ++ ps.flatten <+: q ++ qs.flatten at hpre
              have epq : p = q := by
                rcases List.prefix_or_prefix_of_prefix
                    ((List.prefix_append p ps.flatten).trans hpre)
                    (List.prefix_append q qs.flatten) with h | h
                · exact IsPrefixMachine.eq_of_prefix hU hp hq h
                · exact (IsPrefixMachine.eq_of_prefix hU hq hp h).symm
              subst q
              have exy : x = y := Part.mem_unique hp hq
              subst y
              have ht : ps.flatten <+: qs.flatten :=
                (List.prefix_append_right_inj p).mp hpre
              have hlp : ps.length = k := Nat.succ.inj hps
              have hlq : qs.length = k := Nat.succ.inj hqs
              obtain ⟨ef, eo⟩ := ih ps.flatten qs.flatten xt yt
                ⟨ps, hlp, rfl, hpt⟩
                ⟨qs, hlq, rfl, hqt⟩ ht
              constructor
              · change p ++ ps.flatten = p ++ qs.flatten
                rw [ef]
              · rw [eo]

/-- Running a list of exactly `k` programs is relatively partial computable, with precisely
the componentwise production relation as its graph. -/
private theorem exists_partrecIn_runList
    (A : Set ℕ) (U : Map) (k : ℕ)
    (hU : IsDecompressorIn (charOracle A) U) :
    ∃ V : List BitString →. List BitString,
      PartrecIn {charOracle A} V ∧
      ∀ ps xs, xs ∈ V ps ↔ ps.length = k ∧
        List.Forall₂ (fun p x => produces U p [] x) ps xs := by
  rw [isDecompressorIn_iff_partrecIn] at hU
  induction k with
  | zero =>
      let V : List BitString →. List BitString := fun ps =>
        if ps = [] then Part.some [] else Part.none
      refine ⟨V, ?_, ?_⟩
      · have hg : Computable (fun ps : List BitString => decide (ps = [])) :=
          (Primrec.eq.comp Primrec.id (Primrec.const [])).decide.to_comp
        exact (PartrecIn.cond hg.computableIn (ComputableIn.const []).partrecIn
          PartrecIn.none).of_eq fun ps => by
            simp only [V, Bool.cond_decide, PFun.coe_val]
      · intro ps xs
        cases ps <;> simp [V]
  | succ k ih =>
      obtain ⟨V, hV, hspec⟩ := ih
      let W : List BitString →. List BitString := fun ps =>
        if ps = [] then Part.none else
          (U (ps.headI, [])).bind fun x => (V ps.tail).map fun xs => x :: xs
      have hhead : Computable (fun ps : List BitString => (ps.headI, ([] : BitString))) :=
        Primrec.list_headI.to_comp.pair (Computable.const [])
      have hrun := hU.comp hhead.computableIn
      have htail := hV.comp Primrec.list_tail.to_comp.computableIn
      have htail' : PartrecIn₂ {charOracle A}
          (fun (ps : List BitString) (x : BitString) =>
            (V ps.tail).map fun xs => x :: xs) := by
        have hc : ComputableIn₂ {charOracle A}
            (fun (q : List BitString × BitString) (xs : List BitString) => q.2 :: xs) :=
          (Computable.list_cons.comp (Computable.snd.comp Computable.fst)
            Computable.snd).computableIn.to₂
        exact (htail.comp ComputableIn.fst).map hc
      refine ⟨W, ?_, ?_⟩
      · have hg : Computable (fun ps : List BitString => decide (ps = [])) :=
          (Primrec.eq.comp Primrec.id (Primrec.const [])).decide.to_comp
        exact (PartrecIn.cond hg.computableIn PartrecIn.none
          (hrun.bind htail')).of_eq fun ps => by
            simp only [W, Bool.cond_decide]
      · intro ps xs
        cases ps with
        | nil => simp [W]
        | cons p ps =>
            simp only [W, List.cons_ne_nil, reduceIte, List.headI_cons, List.tail_cons,
              Part.mem_bind_iff, Part.mem_map_iff]
            constructor
            · rintro ⟨x, hx, ys, hys, rfl⟩
              obtain ⟨hlen, hprod⟩ := (hspec ps ys).mp hys
              exact ⟨congrArg Nat.succ hlen, List.Forall₂.cons hx hprod⟩
            · rintro ⟨hlen, hprod⟩
              obtain ⟨x, ys, hx, hys, rfl⟩ := List.forall₂_cons_left_iff.mp hprod
              exact ⟨x, hx, ys, (hspec ps ys).mpr ⟨Nat.succ.inj hlen, hys⟩, rfl⟩

/-- Enumerate the halting inputs of a relative list computation and search for a split
with the prescribed concatenation. The search returns a halting split and has exactly
the domain on which such a split exists. -/
private theorem exists_partrecIn_findSplit
    (A : Set ℕ) (V : List BitString →. List BitString)
    (hV : PartrecIn {charOracle A} V) :
    ∃ S : BitString →. List BitString,
      PartrecIn {charOracle A} S ∧
      (∀ w ps, ps ∈ S w → ps.flatten = w ∧ (V ps).Dom) ∧
      (∀ w, (S w).Dom ↔ ∃ ps, ps.flatten = w ∧ (V ps).Dom) := by
  have hRE : IsREIn A (fun ps => (V ps).Dom) :=
    ⟨fun ps => (V ps).map (fun _ => 0), hV.map (ComputableIn.const 0),
      fun _ => Iff.rfl⟩
  obtain ⟨e, he, henum⟩ := (relative_enumeration A _).mp hRE
  let test (w : BitString) (t : ℕ) : Option (List BitString) :=
    (e t).bind fun ps => if ps.flatten = w then some ps else none
  let S : BitString →. List BitString := fun w => Nat.rfindOpt (test w)
  have hlocal : Computable (fun q : BitString × Option (List BitString) =>
      q.2.bind fun ps => if ps.flatten = q.1 then some ps else none) := by
    have hg : Computable (fun q : BitString × List BitString =>
        decide (q.2.flatten = q.1)) :=
      (Primrec.eq.comp (Primrec.list_flatten.comp Primrec.snd) Primrec.fst).decide.to_comp
    have hm : Computable (fun q : BitString × List BitString =>
        if q.2.flatten = q.1 then some q.2 else none) :=
      (Computable.cond hg (Computable.option_some.comp Computable.snd)
        (Computable.const none)).of_eq fun _ => by simp only [Bool.cond_decide]
    exact Computable.option_bind Computable.snd
      (hm.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂
  have htest : ComputableIn₂ {charOracle A} test :=
    (hlocal.computableIn.comp
      (ComputableIn.fst.pair (he.comp ComputableIn.snd))).to₂
  have hmem (w : BitString) (ps : List BitString) (t : ℕ) :
      ps ∈ test w t ↔ e t = some ps ∧ ps.flatten = w := by
    simp only [test, Option.mem_def, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨qs, hqs, h⟩
      split_ifs at h with hflat
      · cases Option.some.inj h
        exact ⟨hqs, hflat⟩
    · rintro ⟨hps, hflat⟩
      exact ⟨ps, hps, by simp [hflat]⟩
  have hsound (w : BitString) (ps : List BitString) (hps : ps ∈ S w) :
      ps.flatten = w ∧ (V ps).Dom := by
    obtain ⟨t, ht⟩ := Nat.rfindOpt_spec hps
    obtain ⟨heps, hflat⟩ := (hmem w ps t).mp ht
    exact ⟨hflat, (henum ps).mpr ⟨t, heps⟩⟩
  refine ⟨S, PartrecIn.rfindOpt htest, hsound, ?_⟩
  intro w
  constructor
  · intro h
    obtain ⟨ps, hps⟩ := Part.dom_iff_mem.mp h
    exact ⟨ps, hsound w ps hps⟩
  · rintro ⟨ps, hflat, hps⟩
    obtain ⟨t, ht⟩ := (henum ps).mp hps
    exact Nat.rfindOpt_dom.mpr ⟨t, ps, (hmem w ps t).mpr ⟨ht, hflat⟩⟩

/-- The decoder of concatenated `k`-program parses is relatively partial computable. -/
private theorem concatDecoder_isDecompressorIn
    (A : Set ℕ) (U : Map) (k : ℕ)
    (hU : IsDecompressorIn (charOracle A) U)
    (hp : IsPrefixMachine U) :
    IsDecompressorIn (charOracle A) (concatDecoder U k) := by
  obtain ⟨V, hV, hVspec⟩ := exists_partrecIn_runList A U k hU
  obtain ⟨S, hS, hSout, hSdom⟩ := exists_partrecIn_findSplit A V hV
  have hparse (w : BitString) (ps xs : List BitString)
      (hps : ps ∈ S w) (hxs : xs ∈ V ps) :
      IsConcatParse U k w xs := by
    obtain ⟨hlen, hprod⟩ := (hVspec ps xs).mp hxs
    exact ⟨ps, hlen, (hSout w ps hps).1, hprod⟩
  have hgraph (w : BitString) (xs : List BitString) :
      xs ∈ (S w).bind V ↔ IsConcatParse U k w xs := by
    constructor
    · intro h
      obtain ⟨_, hps, hxs⟩ := Part.mem_bind_iff.mp h
      exact hparse w _ xs hps hxs
    · intro hx
      obtain ⟨ps, hlen, hflat, hprod⟩ := hx
      have hps : xs ∈ V ps := (hVspec ps xs).mpr ⟨hlen, hprod⟩
      have hdom : (S w).Dom := (hSdom w).mpr ⟨ps, hflat, hps.1⟩
      obtain ⟨qs, hqs⟩ := Part.dom_iff_mem.mp hdom
      obtain ⟨ys, hys⟩ := Part.dom_iff_mem.mp (hSout w qs hqs).2
      have heq : ys = xs :=
        (IsConcatParse.eq_of_prefix
          U hp k w w ys xs (hparse w qs ys hqs hys)
          ⟨ps, hlen, hflat, hprod⟩ List.prefix_rfl).2
      exact Part.mem_bind hqs (heq ▸ hys)
  have hrun : PartrecIn {charOracle A} (fun w => (S w).bind V) :=
    relative_closure_comp A S V hS hV
  have hcode : ComputableIn₂ {charOracle A}
      (fun (_ : BitString × BitString) (xs : List BitString) => listCode xs) :=
    (listCode_computable.comp Computable.snd).computableIn.to₂
  have hdecoder : PartrecIn {charOracle A}
      (fun pr : BitString × BitString => ((S pr.1).bind V).map listCode) :=
    (hrun.comp ComputableIn.fst).map hcode
  rw [isDecompressorIn_iff_partrecIn]
  refine hdecoder.of_eq fun pr => ?_
  apply Part.ext
  intro z
  change z ∈ ((S pr.1).bind V).map listCode ↔
    z ∈ Part.mk (∃ xs, IsConcatParse U k pr.1 xs)
      (fun h => listCode (Classical.choose h))
  rw [Part.mem_map_iff, Part.mem_mk_iff]
  constructor
  · rintro ⟨xs, hxs, hz⟩
    have hx := (hgraph pr.1 xs).mp hxs
    refine ⟨⟨xs, hx⟩, ?_⟩
    have heq : Classical.choose ⟨xs, hx⟩ = xs :=
      (IsConcatParse.eq_of_prefix
        U hp k pr.1 pr.1 (Classical.choose ⟨xs, hx⟩) xs
        (Classical.choose_spec ⟨xs, hx⟩) hx List.prefix_rfl).2
    simpa only [heq] using hz
  · rintro ⟨h, hz⟩
    exact ⟨Classical.choose h, (hgraph pr.1 _).mpr (Classical.choose_spec h), hz⟩

/-- The decoder of concatenated `k`-program parses has a prefix-free domain. -/
private theorem concatDecoder_isPrefixMachine
    (U : Map) (k : ℕ) (hU : IsPrefixMachine U) :
    IsPrefixMachine (concatDecoder U k) := by
  intro y p hp_mem q hq_mem hpre
  change (concatDecoder U k (p, y)).Dom at hp_mem
  change (concatDecoder U k (q, y)).Dom at hq_mem
  change (∃ xs, IsConcatParse U k p xs) at hp_mem
  change (∃ ys, IsConcatParse U k q ys) at hq_mem
  obtain ⟨xs, hx⟩ := hp_mem
  obtain ⟨ys, hy⟩ := hq_mem
  exact (IsConcatParse.eq_of_prefix U hU k p q xs ys hx hy hpre).1

/-- The concatenation of programs for the entries of `xs` is a program for `listCode xs`
on the decoder of concatenated parses. -/
private theorem concatDecoder_produces
    (U : Map) (k : ℕ) (hU : IsPrefixMachine U)
    (ps xs : List BitString) (hlen : ps.length = k)
    (hprod : List.Forall₂ (fun p x => produces U p [] x) ps xs) :
    produces (concatDecoder U k) ps.flatten [] (listCode xs) := by
  unfold produces
  dsimp [concatDecoder]
  rw [Part.mem_mk_iff]
  have hparse : IsConcatParse U k ps.flatten xs := ⟨ps, hlen, rfl, hprod⟩
  refine ⟨⟨xs, hparse⟩, ?_⟩
  have eq_xs : Classical.choose ⟨xs, hparse⟩ = xs := by
    have h_choose := Classical.choose_spec ⟨xs, hparse⟩
    exact (IsConcatParse.eq_of_prefix U hU k ps.flatten ps.flatten
      (Classical.choose ⟨xs, hparse⟩) xs h_choose hparse List.prefix_rfl).2
  rw [eq_xs]

/-- Every list of strings has a list of shortest programs for its entries, of lengths equal
to the entries' oracle complexities. -/
private theorem exists_shortest_programs
    (A : Set ℕ) (xs : List BitString) :
    ∃ ps : List BitString,
      List.Forall₂ (fun p x =>
        produces (optimalOraclePrefix A) p [] x ∧
        p.length = oracleComplexity A x) ps xs := by
  induction xs with
  | nil =>
    exact ⟨[], List.Forall₂.nil⟩
  | cons x xs ih =>
    obtain ⟨ps, hps⟩ := ih
    have hkp_ne_top : KP (optimalOraclePrefix A) x [] ≠ ⊤ := by
      exact exists_optimalOraclePrefix_finite A x []
    obtain ⟨p, hp_prod, hp_len⟩ := exists_program_of_KP_ne_top hkp_ne_top
    refine ⟨p :: ps, ?_⟩
    apply List.Forall₂.cons
    · refine ⟨hp_prod, ?_⟩
      apply ENat.natCast_inj.mp
      exact hp_len.trans (oraclePrefixComplexity_coe A x []).symm
    · exact hps

/-- The code of a list of fixed length `k` has complexity at most the sum of the complexities
of its entries plus a constant depending only on `A` and `k`. -/
private theorem exists_oracleComplexity_listCode_le
    (A : Set ℕ) (k : ℕ) :
    ∃ c : ℕ, ∀ xs, xs.length = k →
      oracleComplexity A (listCode xs) ≤
        (xs.map (oracleComplexity A)).sum + c := by
  let U := optimalOraclePrefix A
  let D := concatDecoder U k
  have hU := exists_optimalOraclePrefix_spec A
  have hD : IsDecompressorIn (charOracle A) D :=
    concatDecoder_isDecompressorIn A U k hU.1 hU.2.1
  have hpD : IsPrefixMachine D := concatDecoder_isPrefixMachine U k hU.2.1
  obtain ⟨c, hc⟩ := hU.2.2 D hD hpD
  refine ⟨c, ?_⟩
  intro xs hlen
  obtain ⟨ps, hps⟩ := exists_shortest_programs A xs
  have hl : ps.length = k := hps.length_eq.trans hlen
  have hout : produces D ps.flatten [] (listCode xs) :=
    concatDecoder_produces U k hU.2.1 ps xs hl (hps.imp (fun _ _ h => h.1))
  have hsum : ∀ (ps xs : List BitString),
      List.Forall₂ (fun p x =>
        produces (optimalOraclePrefix A) p [] x ∧
        p.length = oracleComplexity A x) ps xs →
      ps.flatten.length = (xs.map (oracleComplexity A)).sum := by
    intro ps xs h
    induction h with
    | nil => simp
    | cons h ht ih => simp [h.2, ih]
  have hs : ps.flatten.length =
      (xs.map (oracleComplexity A)).sum := hsum ps xs hps
  have hb : KP U (listCode xs) [] ≤
      (ps.flatten.length : ENat) + (c : ENat) :=
    (hc (listCode xs) []).trans
      (add_le_add (KP_le_programLength_of_produces hout) (le_refl _))
  have hn : (oracleComplexity A (listCode xs) : ENat) ≤
      ((ps.flatten.length + c : ℕ) : ENat) := by
    calc
      (oracleComplexity A (listCode xs) : ENat) =
          KP U (listCode xs) [] :=
        oraclePrefixComplexity_coe A (listCode xs) []
      _ ≤ (ps.flatten.length : ENat) + (c : ENat) := hb
      _ = ((ps.flatten.length + c : ℕ) : ENat) :=
        (ENat.natCast_add _ _).symm
  have hn' := ENat.natCast_le_natCast.mp hn
  simpa only [hs] using hn'

/-- A fixed relative partial operation on a fixed number of inputs costs at most the sum
of their prefix complexities and one constant whenever it halts.
Blueprint node `oracle:tuple`. -/
theorem oracle_tuple_bounds_composition (A : Set ℕ) (k : ℕ)
    (F : List BitString →. BitString) (hF : PartrecIn {charOracle A} F) :
    ∃ c : ℕ, ∀ xs x, xs.length = k → x ∈ F xs →
      oracleComplexity A x ≤ (xs.map (oracleComplexity A)).sum + c := by
  let G := fun w => F (decodeListCode w)
  have hG : PartrecIn {charOracle A} G :=
    hF.comp decodeListCode_computable.computableIn
  obtain ⟨c1, hc1⟩ := exists_oracleComplexity_le_of_partrecIn A G hG
  obtain ⟨c2, hc2⟩ := exists_oracleComplexity_listCode_le A k
  use c1 + c2
  intro xs x hlen hx
  have hG_eval : x ∈ G (listCode xs) := by
    simp only [G, decodeListCode_listCode]
    exact hx
  have h1 := hc1 (listCode xs) x hG_eval
  have h2 := hc2 xs hlen
  omega

/-- Strengthening an oracle decreases every string complexity up to one uniform constant.
Blueprint node `oracle:monotone`. -/
theorem oracle_monotonicity (A B : Set ℕ) (hAB : charOracle A ≤ᵀ charOracle B) :
    ∃ c : ℕ, ∀ w, oracleComplexity B w ≤ oracleComplexity A w + c := by
  have hU_A := exists_optimalOraclePrefix_spec A
  have hU_B := exists_optimalOraclePrefix_spec B
  have h_decomp_A_in_B : IsDecompressorIn (charOracle B) (optimalOraclePrefix A) := by
    unfold IsDecompressorIn
    apply RecursiveIn.subst hU_A.1
    intro g hg
    simp only [Set.mem_singleton_iff] at hg
    subst hg
    exact hAB
  rcases hU_B.2.2 (optimalOraclePrefix A) h_decomp_A_in_B hU_A.2.1 with ⟨c, hc⟩
  use c
  intro w
  have h_ineq := hc w []
  unfold oracleComplexity oraclePrefixComplexityNat oraclePrefixComplexity
  have h_A_fin := exists_optimalOraclePrefix_finite A w []
  have h_B_fin := exists_optimalOraclePrefix_finite B w []
  have h_A_coe := ENat.natCast_toNat h_A_fin
  have h_B_coe := ENat.natCast_toNat h_B_fin
  rw [← ENat.natCast_le_natCast]
  push_cast
  rw [h_A_coe, h_B_coe]
  exact h_ineq

end Kolmogorov.PointToSet
