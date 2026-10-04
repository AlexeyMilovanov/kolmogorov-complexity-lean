/-
Copyright (c) 2024 Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author
-/
import KolmogorovMathlib.AlgorithmicRandomness.ComputableMeasure
import KolmogorovMathlib.MonotoneComplexity.SharedCoding
import Mathlib.Computability.PartrecCode
import KolmogorovMathlib.AlgorithmicProbability.OptimalCoding

/-!
# Indices and prefix complexity of computable measures

A computable measure on Cantor space is a finite object: a program that, given a string `x` and a
precision `s`, returns a dyadic approximation of the cylinder mass `μ(Ω_x)` within `2^{-s}`. This
module names such programs — `IsComputableMeasureIndex μ e` says that the partial recursive code
with number `e` is one — and defines the prefix complexity of a measure,
`computableMeasureComplexity U μ = min {K(e) : e an index of μ}`, the `K(μ)` of Li–Vitányi and
Hutter, where `K(e) = KPNat U e` is the prefix complexity of the number `e`.

### Outline

* `IsComputableMeasureIndex μ e`: the code `e` halts on every input `encode (x, s)` with a
  numerator `a` such that `a / 2^s` lies within `2^{-s}` of `μ(Ω_x)` on both sides — exactly the
  approximation required by `IsComputableMeasure`, now carried by a named program;
* `isComputableMeasure_iff_exists_index`: a measure is computable exactly when it has an index, and
  `IsComputableMeasureIndex.measure_eq`: an index determines the probability measure;
* `computableMeasureComplexity U μ`, equal to `⊤` for a measure without an index, finite for a
  computable measure and an optimal prefix decompressor (`computableMeasureComplexity_ne_top`), and
  attained by some index (`exists_index_KPNat_eq_computableMeasureComplexity`).

Sources: Li–Vitányi (3rd ed.) §4.5 and §5.2 (`K(μ)`, the prefix complexity of a computable
measure), Hutter (2005) §2.4 (`K(ν)`, the length of a shortest program for `ν`), SUV §3.1
(computable measures on Cantor space).
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-- `e` is an index of the computable measure `μ`: the partial recursive code with number `e`
(`Denumerable.ofNat Nat.Partrec.Code e`) halts on every input `encode (x, s)` with an output `a`
such that `a / 2^s ≤ μ(Ω_x) + 2^{-s}` and `μ(Ω_x) ≤ a / 2^s + 2^{-s}` — the two-sided dyadic
approximation of `IsComputableMeasure`, carried by one program. Item SOL-I-INDEX;
Li–Vitányi (3rd ed.) §4.5 (index of a computable measure), SUV §3.1. -/
def IsComputableMeasureIndex (μ : Measure CantorSeq) (e : ℕ) : Prop :=
  ∀ (x : BitString) (s : ℕ),
    ∃ a ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode (x, s)),
      dyadicValue a s ≤ cantorMass μ x + dyadicValue 1 s ∧
        cantorMass μ x ≤ dyadicValue a s + dyadicValue 1 s

/-- A measure on Cantor space is computable exactly when it has an index. Item SOL-I-IFF; the
bridge between `IsComputableMeasure` and `IsComputableMeasureIndex`. -/
theorem isComputableMeasure_iff_exists_index (μ : Measure CantorSeq) :
    IsComputableMeasure μ ↔ ∃ e, IsComputableMeasureIndex μ e := by
  constructor
  · rintro ⟨a, hcomp, hbound⟩
    have hc : Computable (fun (n : ℕ) =>
        a ((Encodable.decode n : Option (BitString × ℕ)).getD ([], 0)).1
        ((Encodable.decode n : Option (BitString × ℕ)).getD ([], 0)).2) := by
      have hd : Computable (fun (n : ℕ)
          => (Encodable.decode n : Option (BitString × ℕ)).getD ([], 0)) :=
        Computable.option_getD Computable.decode (Computable.const ([], 0))
      have hc1 :
        Computable (fun n => ((Encodable.decode n : Option (BitString × ℕ)).getD ([], 0)).1) :=
        Computable.comp Computable.fst hd
      have hc2 :
        Computable (fun n => ((Encodable.decode n : Option (BitString × ℕ)).getD ([], 0)).2) :=
        Computable.comp Computable.snd hd
      exact hcomp.comp hc1 hc2
    rcases Nat.Partrec.Code.exists_code.mp hc.partrec with ⟨e, he⟩
    use Encodable.encode e
    intro x s
    have he2 := congr_fun he (Encodable.encode (x, s))
    use a x s
    constructor
    · have heq : Denumerable.ofNat Nat.Partrec.Code (Encodable.encode e) = e := by
        exact Denumerable.ofNat_encode e
      rw [heq]
      have h_eval : e.eval (Encodable.encode (x, s)) = Part.some (a x s) := by
        rw [he2]
        have h_bind : (Part.some (Encodable.encode (x, s))).bind
          (fun a_1 => Part.some (a ((Encodable.decode a_1 : Option (BitString × ℕ)).getD ([], 0)).1
            ((Encodable.decode a_1 : Option (BitString × ℕ)).getD ([], 0)).2)) =
            Part.some (a x s) := by
          simp only [Part.bind_some]
          have hd2 : (Encodable.decode (Encodable.encode (x, s)) :
            Option (BitString × ℕ)).getD ([], 0) = (x, s) := by
            rw [Encodable.encodek]
            rfl
          rw [hd2]
        exact h_bind
      rw [h_eval]
      exact Part.mem_some _
    · exact hbound x s
  · rintro ⟨e, he⟩
    have h1 : ∃ a : BitString × ℕ → ℕ, Computable a ∧
        ∀ (p : BitString × ℕ),
          a p ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode p) := by
      have hc_partrec : Partrec (fun (p : BitString × ℕ) =>
          (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode p)) := by
        have h_code : Partrec (Denumerable.ofNat Nat.Partrec.Code e).eval :=
          Partrec.nat_iff.mpr
          (Nat.Partrec.Code.exists_code.mpr ⟨Denumerable.ofNat Nat.Partrec.Code e, rfl⟩)
        exact Partrec.comp h_code Computable.encode
      have htot : ∀ (p : BitString × ℕ),
          ((Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode p)).Dom := by
        intro p
        rcases he p.1 p.2 with ⟨a', ha', _⟩
        exact Part.dom_iff_mem.mpr ⟨a', ha'⟩
      have hc : Computable (fun (p : BitString × ℕ) =>
          ((Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode p)).get (htot p)) := by
        apply Partrec.of_eq_tot hc_partrec
        intro p
        exact Part.get_mem (htot p)
      use fun (p : BitString × ℕ) =>
          ((Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode p)).get (htot p)
      constructor
      · exact hc
      · intro p
        exact Part.get_mem _
    rcases h1 with ⟨a, hcomp, hbound_a⟩
    use fun x s => a (x, s)
    constructor
    · exact hcomp.to₂
    · intro x s
      rcases he x s with ⟨a', ha', hbound'⟩
      have heq : a (x, s) = a' := Part.mem_unique (hbound_a (x, s)) ha'
      rw [heq]
      exact hbound'
/-- An index determines the probability measure it approximates: two probability measures with a
common index are equal. Item SOL-I-DET; with `cantorMeasure_unique`. -/
theorem IsComputableMeasureIndex.measure_eq {μ ν : Measure CantorSeq} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {e : ℕ} (hμ : IsComputableMeasureIndex μ e)
    (hν : IsComputableMeasureIndex ν e) : μ = ν := by
  apply cantorMeasure_unique
  intro x
  apply le_antisymm
  · have h1 : ∀ s : ℕ, cantorMass μ x ≤ cantorMass ν x + (dyadicValue 1 s) * 2 := by
      intro s
      rcases hμ x s with ⟨a, ha_mem, hμ_le, hμ_ge⟩
      rcases hν x s with ⟨b, hb_mem, hν_le, hν_ge⟩
      have heq : a = b := Part.mem_unique ha_mem hb_mem
      rw [heq] at hμ_le hμ_ge
      have h_add1 : cantorMass μ x + dyadicValue 1 s ≤
          dyadicValue b s + dyadicValue 1 s + dyadicValue 1 s := by
        exact add_le_add hμ_ge (le_refl _)
      have h_add2 : dyadicValue b s + dyadicValue 1 s + dyadicValue 1 s ≤
          cantorMass ν x + dyadicValue 1 s + dyadicValue 1 s + dyadicValue 1 s := by
        have h_add2_inner : dyadicValue b s + dyadicValue 1 s ≤
            cantorMass ν x + dyadicValue 1 s + dyadicValue 1 s := by
          exact add_le_add hν_le (le_refl _)
        exact add_le_add h_add2_inner (le_refl _)
      have h_comb : cantorMass μ x + dyadicValue 1 s ≤
          cantorMass ν x + dyadicValue 1 s + dyadicValue 1 s + dyadicValue 1 s :=
        le_trans h_add1 h_add2
      have h_cancel : cantorMass μ x ≤ cantorMass ν x + dyadicValue 1 s + dyadicValue 1 s := by
        have h_ne_top : dyadicValue 1 s ≠ ⊤ := by
          unfold dyadicValue
          apply ENNReal.mul_ne_top ENNReal.coe_ne_top
          apply ENNReal.inv_ne_top.mpr
          simp
        have h_comb2 : cantorMass μ x + dyadicValue 1 s ≤
            (cantorMass ν x + dyadicValue 1 s + dyadicValue 1 s) + dyadicValue 1 s := by
          calc cantorMass μ x + dyadicValue 1 s
            _ ≤ cantorMass ν x + dyadicValue 1 s + dyadicValue 1 s + dyadicValue 1 s := h_comb
            _ = (cantorMass ν x + dyadicValue 1 s + dyadicValue 1 s) + dyadicValue 1 s := rfl
        exact (ENNReal.add_le_add_iff_right h_ne_top).mp h_comb2
      have h_rearrange : cantorMass ν x + dyadicValue 1 s + dyadicValue 1 s =
          cantorMass ν x + (dyadicValue 1 s) * 2 := by
        rw [mul_two, ← add_assoc]
      rw [← h_rearrange]
      exact h_cancel
    have h_inf : iInf (fun s => cantorMass ν x + (dyadicValue 1 s) * 2) = cantorMass ν x := by
      have h_inf2 : (⨅ s, ((2 : ℝ≥0∞)⁻¹) ^ s) = 0 := by
        have h_tendsto : Filter.Tendsto (fun s => ((2 : ℝ≥0∞)⁻¹) ^ s)
            Filter.atTop (nhds 0) := by
          exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simp)
        have h_anti : Antitone (fun (s : ℕ) => ((2 : ℝ≥0∞)⁻¹) ^ s) := by
          intro i j hij
          exact pow_le_pow_of_le_one zero_le (by simp) hij
        have h_tendsto2 : Filter.Tendsto (fun s => ((2 : ℝ≥0∞)⁻¹) ^ s)
            Filter.atTop (nhds (⨅ s, ((2 : ℝ≥0∞)⁻¹) ^ s)) :=
          tendsto_atTop_iInf h_anti
        exact tendsto_nhds_unique h_tendsto2 h_tendsto
      have h_inf_add : iInf (fun s => cantorMass ν x + (dyadicValue 1 s) * 2) =
          cantorMass ν x + iInf (fun s => (dyadicValue 1 s) * 2) := by
        exact ENNReal.add_iInf.symm
      have h_val : ∀ s, (dyadicValue 1 s) = ((2 : ℝ≥0∞)⁻¹) ^ s := by
        intro s
        unfold dyadicValue
        simp [ENNReal.inv_pow]
      have h_inf3 : iInf (fun s => (dyadicValue 1 s) * 2) = 0 := by
        have h_eq : iInf (fun s => (dyadicValue 1 s) * 2) = (⨅ s, dyadicValue 1 s) * 2 := by
          exact (ENNReal.iInf_mul (by simp)).symm
        rw [h_eq]
        have h_eq2 : (⨅ s, dyadicValue 1 s) = 0 := by
          have h_eq3 : (⨅ s, dyadicValue 1 s) = ⨅ s, ((2 : ℝ≥0∞)⁻¹) ^ s := by
            apply iInf_congr
            intro s
            exact h_val s
          rw [h_eq3, h_inf2]
        rw [h_eq2, zero_mul]
      rw [h_inf_add, h_inf3, add_zero]
    have h_le_inf : cantorMass μ x ≤ iInf (fun s => cantorMass ν x + (dyadicValue 1 s) * 2) :=
      le_iInf h1
    rwa [h_inf] at h_le_inf
  · have h1 : ∀ s : ℕ, cantorMass ν x ≤ cantorMass μ x + (dyadicValue 1 s) * 2 := by
      intro s
      rcases hμ x s with ⟨a, ha_mem, hμ_le, hμ_ge⟩
      rcases hν x s with ⟨b, hb_mem, hν_le, hν_ge⟩
      have heq : b = a := (Part.mem_unique ha_mem hb_mem).symm
      rw [heq] at hν_le hν_ge
      have h_add1 : cantorMass ν x + dyadicValue 1 s ≤
          dyadicValue a s + dyadicValue 1 s + dyadicValue 1 s := by
        exact add_le_add hν_ge (le_refl _)
      have h_add2 : dyadicValue a s + dyadicValue 1 s + dyadicValue 1 s ≤
          cantorMass μ x + dyadicValue 1 s + dyadicValue 1 s + dyadicValue 1 s := by
        have h_add2_inner : dyadicValue a s + dyadicValue 1 s ≤
            cantorMass μ x + dyadicValue 1 s + dyadicValue 1 s := by
          exact add_le_add hμ_le (le_refl _)
        exact add_le_add h_add2_inner (le_refl _)
      have h_comb : cantorMass ν x + dyadicValue 1 s ≤
          cantorMass μ x + dyadicValue 1 s + dyadicValue 1 s + dyadicValue 1 s :=
        le_trans h_add1 h_add2
      have h_cancel : cantorMass ν x ≤ cantorMass μ x + dyadicValue 1 s + dyadicValue 1 s := by
        have h_ne_top : dyadicValue 1 s ≠ ⊤ := by
          unfold dyadicValue
          apply ENNReal.mul_ne_top ENNReal.coe_ne_top
          apply ENNReal.inv_ne_top.mpr
          simp
        have h_comb2 : cantorMass ν x + dyadicValue 1 s ≤
            (cantorMass μ x + dyadicValue 1 s + dyadicValue 1 s) + dyadicValue 1 s := by
          calc cantorMass ν x + dyadicValue 1 s
            _ ≤ cantorMass μ x + dyadicValue 1 s + dyadicValue 1 s + dyadicValue 1 s := h_comb
            _ = (cantorMass μ x + dyadicValue 1 s + dyadicValue 1 s) + dyadicValue 1 s := rfl
        exact (ENNReal.add_le_add_iff_right h_ne_top).mp h_comb2
      have h_rearrange : cantorMass μ x + dyadicValue 1 s + dyadicValue 1 s =
          cantorMass μ x + (dyadicValue 1 s) * 2 := by
        rw [mul_two, ← add_assoc]
      rw [← h_rearrange]
      exact h_cancel
    have h_inf : iInf (fun s => cantorMass μ x + (dyadicValue 1 s) * 2) = cantorMass μ x := by
      have h_inf2 : (⨅ s, ((2 : ℝ≥0∞)⁻¹) ^ s) = 0 := by
        have h_tendsto : Filter.Tendsto (fun s => ((2 : ℝ≥0∞)⁻¹) ^ s)
            Filter.atTop (nhds 0) := by
          exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simp)
        have h_anti : Antitone (fun (s : ℕ) => ((2 : ℝ≥0∞)⁻¹) ^ s) := by
          intro i j hij
          exact pow_le_pow_of_le_one zero_le (by simp) hij
        have h_tendsto2 : Filter.Tendsto (fun s => ((2 : ℝ≥0∞)⁻¹) ^ s)
            Filter.atTop (nhds (⨅ s, ((2 : ℝ≥0∞)⁻¹) ^ s)) :=
          tendsto_atTop_iInf h_anti
        exact tendsto_nhds_unique h_tendsto2 h_tendsto
      have h_inf_add : iInf (fun s => cantorMass μ x + (dyadicValue 1 s) * 2) =
          cantorMass μ x + iInf (fun s => (dyadicValue 1 s) * 2) := by
        exact ENNReal.add_iInf.symm
      have h_val : ∀ s, (dyadicValue 1 s) = ((2 : ℝ≥0∞)⁻¹) ^ s := by
        intro s
        unfold dyadicValue
        simp [ENNReal.inv_pow]
      have h_inf3 : iInf (fun s => (dyadicValue 1 s) * 2) = 0 := by
        have h_eq : iInf (fun s => (dyadicValue 1 s) * 2) = (⨅ s, dyadicValue 1 s) * 2 := by
          exact (ENNReal.iInf_mul (by simp)).symm
        rw [h_eq]
        have h_eq2 : (⨅ s, dyadicValue 1 s) = 0 := by
          have h_eq3 : (⨅ s, dyadicValue 1 s) = ⨅ s, ((2 : ℝ≥0∞)⁻¹) ^ s := by
            apply iInf_congr
            intro s
            exact h_val s
          rw [h_eq3, h_inf2]
        rw [h_eq2, zero_mul]
      rw [h_inf_add, h_inf3, add_zero]
    have h_le_inf : cantorMass ν x ≤ iInf (fun s => cantorMass μ x + (dyadicValue 1 s) * 2) :=
      le_iInf h1
    rwa [h_inf] at h_le_inf
/-- The prefix complexity `K(μ)` of a measure on Cantor space: the least prefix complexity
`K(e) = KPNat U e` of an index `e` of `μ`, and `⊤` when `μ` has no index (is not computable).
Item SOL-I-K; Li–Vitányi (3rd ed.) §5.2 (`K(μ)`), Hutter (2005) §2.4 (`K(ν)`). -/
noncomputable def computableMeasureComplexity (U : Map) (μ : Measure CantorSeq) : ℕ∞ :=
  ⨅ (e : ℕ) (_ : IsComputableMeasureIndex μ e), KPNat U e

/-- The complexity of a measure is at most the prefix complexity of any of its indices.
Item SOL-I-LE. -/
theorem computableMeasureComplexity_le (U : Map) {μ : Measure CantorSeq} {e : ℕ}
    (he : IsComputableMeasureIndex μ e) : computableMeasureComplexity U μ ≤ KPNat U e := by
  refine iInf_le_of_le e ?_
  exact iInf_le_of_le he le_rfl

/-- The complexity of a computable measure is attained: some index has prefix complexity exactly
`K(μ)`. Item SOL-I-ATTAIN. -/
theorem exists_index_KPNat_eq_computableMeasureComplexity (U : Map) {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) :
    ∃ e, IsComputableMeasureIndex μ e ∧ KPNat U e = computableMeasureComplexity U μ := by
  have ⟨e₀, he₀⟩ := (isComputableMeasure_iff_exists_index μ).mp hμ
  let S := {e // IsComputableMeasureIndex μ e}
  have hne : Nonempty S := ⟨⟨e₀, he₀⟩⟩
  have heq : computableMeasureComplexity U μ = ⨅ (e : S), KPNat U e.1 := by
    unfold computableMeasureComplexity
    exact (iInf_subtype (p := fun e => IsComputableMeasureIndex μ e)
      (f := fun (e : S) => KPNat U e.val)).symm
  have h_range : (⨅ (e : S), KPNat U e.val) ∈ Set.range (fun (e : S) => KPNat U e.val) := by
    exact ciInf_mem (fun (e : S) => KPNat U e.val)
  rcases h_range with ⟨⟨e, he⟩, eq2⟩
  use e, he
  rw [heq, ←eq2]

/-- For an optimal prefix decompressor the complexity of a computable measure is finite, so its
`toNat` is its value. Item SOL-I-FIN. -/
theorem computableMeasureComplexity_ne_top (U : Map) (hU : IsOptimalPrefixConditional U)
    {μ : Measure CantorSeq} (hμ : IsComputableMeasure μ) :
    computableMeasureComplexity U μ ≠ ⊤ := by
  have ⟨e, _, he_eq⟩ := exists_index_KPNat_eq_computableMeasureComplexity U hμ
  rw [← he_eq]
  obtain ⟨c, hc⟩ := KPPlain_le_length_add_log U hU
  have h := hc (natToBitString e)
  have h_ne : ((natToBitString e).length + 2 * (Nat.bits (natToBitString e).length).length
    + (c : ENat) : ENat) ≠ ⊤ := by
    exact ENat.natCast_ne_top _
  exact ne_top_of_le_ne_top h_ne h

end Kolmogorov
