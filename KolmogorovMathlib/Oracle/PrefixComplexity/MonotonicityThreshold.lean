/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Oracle.PrefixComplexity.Basic

/-!
# Oracle monotonicity threshold

For an oracle `A` and a uniformly `A`-lower-semicomputable function `g` on bit strings, the set
`{w | K^A(w) < g w}` is `A`-computably enumerable
(`Kolmogorov.PointToSet.oracle_monotonicity_threshold`).
This is the first half of the blueprint node `oracle:monotone`.

The proof dovetails halting programs of the optimal oracle prefix machine with rational lower
bounds `q` for `g w` and emits `w` as soon as a halting program of length `< q` produces it.
It rests on two closure properties of `A`-enumerable predicates (`IsREIn.and` and
`IsREIn.exists`) and on the enumerability of the relation `K^A(w) < q` on bit strings and
rationals (`isREIn_oracleComplexity_lt`), which the pressure and dimension modules use too.

The statement is used in the point-to-set principle for Barreira-Schmeling dimension to turn
semicomputable thresholds into `A`-enumerable sets of strings.
-/

namespace Kolmogorov.PointToSet
open scoped ENNReal Computability

/-- The relation "the optimal oracle prefix machine produces `y` from the program `p` with empty
context" is `A`-enumerable. -/
theorem isREIn_produces_optimalOraclePrefix (A : Set ℕ) :
    IsREIn A (fun pw : BitString × BitString =>
      produces (optimalOraclePrefix A) pw.1 [] pw.2) := by
  have hU : PartrecIn {charOracle A} (optimalOraclePrefix A) :=
    (isDecompressorIn_iff_partrecIn _ _).mp (exists_optimalOraclePrefix_spec A).1
  refine ⟨fun pw => ((optimalOraclePrefix A) (pw.1, [])).bind fun x =>
    cond (decide (x = pw.2)) (Part.some 0) Part.none, ?_, fun pw ↦ ?_⟩
  · have hpair : ComputableIn {charOracle A}
        (fun pw : BitString × BitString => (pw.1, ([] : BitString))) :=
      (Computable.pair Computable.fst (Computable.const [])).computableIn
    have hguard : ComputableIn {charOracle A}
        (fun p : (BitString × BitString) × BitString => decide (p.2 = p.1.2)) :=
      ((PrimrecRel.decide Primrec.eq).to_comp.comp Computable.snd
        (Computable.snd.comp Computable.fst)).computableIn
    exact PartrecIn.bind (PartrecIn.comp hU hpair)
      (PartrecIn.cond hguard (ComputableIn.const 0).partrecIn PartrecIn.none)
  · rw [Part.dom_iff_mem]
    constructor
    · intro h
      exact ⟨0, Part.mem_bind_iff.mpr ⟨pw.2, h, by simp⟩⟩
    · rintro ⟨v, hv⟩
      obtain ⟨x, hx, hcond⟩ := Part.mem_bind_iff.mp hv
      by_cases hxy : x = pw.2
      · rwa [hxy] at hx
      · simp [hxy] at hcond

/-- A bit string has oracle complexity below a rational `q` exactly when some program of length
below `q` makes the optimal oracle prefix machine produce it. -/
theorem oracleComplexity_lt_iff_exists_program (A : Set ℕ) (w : BitString) (q : ℚ) :
    (oracleComplexity A w : ℝ) < q ↔
      ∃ p, produces (optimalOraclePrefix A) p [] w ∧ (p.length : ℚ) < q := by
  constructor
  · intro hlt
    obtain ⟨p, hp, hlen⟩ := exists_program_of_KP_ne_top (exists_optimalOraclePrefix_finite A w [])
    have hn : p.length = oracleComplexity A w :=
      ENat.natCast_inj.mp (hlen.trans (oraclePrefixComplexity_coe A w []).symm)
    exact ⟨p, hp, by rw [hn]; exact_mod_cast hlt⟩
  · rintro ⟨p, hp, hlt⟩
    have hle : oracleComplexity A w ≤ p.length := by
      refine ENat.natCast_le_natCast.mp ?_
      rw [oracleComplexity, oraclePrefixComplexity_coe A w []]
      exact KP_le_programLength_of_produces hp
    have h1 : (oracleComplexity A w : ℝ) ≤ p.length := by exact_mod_cast hle
    have h2 : (p.length : ℝ) < q := by exact_mod_cast hlt
    exact h1.trans_lt h2

/-- The relation `K^A(w) < q` on bit strings and rationals is relatively enumerable. -/
theorem isREIn_oracleComplexity_lt (A : Set ℕ) :
    IsREIn A (fun iq : BitString × ℚ ↦ (oracleComplexity A iq.1 : ℝ) < (iq.2 : ℝ)) := by
  have hproduces : IsREIn A (fun t : (BitString × ℚ) × BitString ↦
      produces (optimalOraclePrefix A) t.2 [] t.1.1) :=
    (isREIn_produces_optimalOraclePrefix A).comp
      (f := fun t : (BitString × ℚ) × BitString ↦ (t.2, t.1.1))
      (Computable.snd.pair (Computable.fst.comp Computable.fst)).computableIn
  have hlength : Computable (fun t : (BitString × ℚ) × BitString ↦
      decide ((t.2.length : ℚ) < t.1.2)) :=
    computable₂_ratLt.comp
      (computable_nat_to_rat.comp (Primrec.list_length.comp Primrec.snd).to_comp)
      (Computable.snd.comp Computable.fst)
  have heq : (fun iq : BitString × ℚ ↦ (oracleComplexity A iq.1 : ℝ) < (iq.2 : ℝ)) =
      (fun iq ↦ ∃ p, produces (optimalOraclePrefix A) p [] iq.1 ∧ (p.length : ℚ) < iq.2) :=
    funext fun iq ↦ propext (oracleComplexity_lt_iff_exists_program A iq.1 iq.2)
  rw [heq]
  exact (hproduces.and (isREIn_of_computable_decide hlength)).exists

/-- The relation `K^A(i) < q` on natural numbers and rationals is relatively enumerable. -/
theorem isREIn_oracleNatComplexity_lt (A : Set ℕ) :
    IsREIn A (fun iq : ℕ × ℚ ↦ (oracleNatComplexity A iq.1 : ℝ) < (iq.2 : ℝ)) :=
  (isREIn_oracleComplexity_lt A).comp (f := fun iq : ℕ × ℚ ↦ (natBits iq.1, iq.2))
    ((natBits_computable.comp Computable.fst).pair Computable.snd).computableIn

/-- Strict comparison of complexity with a uniform relative lower semicomputable real
threshold is a relative enumerable predicate. Blueprint node `oracle:monotone`. -/
theorem oracle_monotonicity_threshold (A : Set ℕ) (g : BitString → ℝ)
    (hg : IsLowerSemicomputableIn A g) :
    IsREIn A (fun w => (oracleComplexity A w : ℝ) < g w) := by
  have H : (fun w => (oracleComplexity A w : ℝ) < g w) =
      fun w => ∃ q : ℚ, (oracleComplexity A w : ℝ) < (q : ℝ) ∧ (q : ℝ) < g w := by
    funext w
    refine propext ⟨fun h ↦ ?_, fun ⟨q, h1, h2⟩ ↦ h1.trans h2⟩
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn h
    exact ⟨q, h1, h2⟩
  rw [H]
  exact ((isREIn_oracleComplexity_lt A).and hg).exists

end Kolmogorov.PointToSet
