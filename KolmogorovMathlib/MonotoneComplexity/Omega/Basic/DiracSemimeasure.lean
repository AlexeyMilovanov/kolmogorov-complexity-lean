import KolmogorovMathlib.MonotoneComplexity.Omega.Basic.Part01
import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveReal
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.MonotoneComplexity.SharedCoding
import KolmogorovMathlib.Prefix.OptimalExistence
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria
import KolmogorovMathlib.MonotoneComplexity.Omega.LscBasic
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaPrefixCore
import KolmogorovMathlib.MonotoneComplexity.Omega.UniversalCover
import KolmogorovMathlib.MonotoneComplexity.Omega.PrefixTransfer

/-!
# Chaitin's number and the randomness of its binary expansion

The Dirac semimeasure on the naturals, with its computable stage approximations
(`computable_diracApprox`, `isLowerSemicomputableSemimeasureNat_diracNat`), is used to pin the
mass of a single value; from it `Ω` is defined as `omegaSum = ∑ₙ m(n)`, the halting probability
of the universal prefix machine, with `omegaReal` its real value and `IsOmegaNumber` the property
of being the sum of some maximal lower semicomputable semimeasure. The sum is finite
(`omegaSum_ne_top`) and lower semicomputable (`isLowerSemicomputableReal_omegaReal`). The main
result is `omega_binary_isMartinLofRandom`: the binary expansion of `Ω` is Martin-Löf random for
the uniform measure, obtained from the complexity bound
`exists_const_le_KPPlain_cantorPrefix_omega` on its prefixes.

Source: SUV §5.7, pp. 157 and 160, Theorem 100.
-/

namespace Kolmogorov

open ComputableReals
open MeasureTheory ENNReal

/-- The stage approximations of the Dirac semimeasure are computable. -/
theorem computable_diracApprox :
    Computable (fun p : ℕ × BitString × BitString => diracApprox p.1 p.2.1) := by
  have hnat : Primrec (fun n : ℕ => 2 ^ n) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id
  exact Computable.nat_casesOn
    (primrec_bitStringToNat.to_comp.comp (Computable.fst.comp Computable.snd))
    (hnat.to_comp.comp Computable.fst) (Computable.const 0)

/-- The Dirac semimeasure on the naturals is lower semicomputable. -/
theorem isLowerSemicomputableSemimeasureNat_diracNat :
    IsLowerSemicomputableSemimeasureNat diracNat := by
  constructor
  · change (∑' x : BitString, diracNat (bitStringToNat x)) ≤ 1
    rw [tsum_comp_bitStringToNat]
    have hone : (∑' n : ℕ, diracNat n) = 1 := by simp [diracNat]
    rw [hone]
  · refine ⟨fun s x _ => diracApprox s x, ?_, ?_, computable_diracApprox⟩
    · intro s x _
      by_cases h : bitStringToNat x = 0
      · simp [diracApprox_eq, h, dyadicValue_two_pow_self]
      · simp [diracApprox_eq, h, dyadicValue_zero]
    · intro x _
      by_cases h : bitStringToNat x = 0
      · simp [diracApprox_eq, h, dyadicValue_two_pow_self, diracNat]
      · simp [diracApprox_eq, h, diracNat, dyadicValue_zero]

/-! ### Chaitin's number `Ω` (SUV pp. 157, 160) -/

/-- **SUV p. 157.** Chaitin's number `Ω = ∑ₙ m(n)`: the halting probability of the
universal probabilistic machine, i.e. the sum of the maximal lower semicomputable
series. -/
noncomputable def omegaSum (m : ℕ → ℝ≥0∞) : ℝ≥0∞ := ∑' n, m n

/-- `Ω` as a real number. It is finite because `m` is a semimeasure. -/
noncomputable def omegaReal (m : ℕ → ℝ≥0∞) : ℝ := (omegaSum m).toReal

/-- **SUV p. 160.** An `Ω`-*number* is the sum of some maximal lower semicomputable
semimeasure on `ℕ`. The book stresses that different maximal semimeasures lead to
different numbers, so the class — not a single value — is the object of study. -/
def IsOmegaNumber (α : ℝ) : Prop :=
  ∃ m : ℕ → ℝ≥0∞, IsUniversalSemimeasureNat m ∧ omegaReal m = α

/-- The sum of a maximal lower semicomputable semimeasure is finite: it is at most
`1` by the semimeasure condition.  Proved from the transported interface. -/
theorem omegaSum_ne_top {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m) :
    omegaSum m ≠ ⊤ := by
  have h : omegaSum m ≤ 1 := hm.tsum_le_one
  exact ne_top_of_le_ne_top one_ne_top h

/-- The sum of a maximal lower semicomputable semimeasure is at most `1` — this, and
*only* this, is what the semimeasure axiom gives; see `omegaReal_lt_one` for the
strict bound. -/
theorem omegaReal_le_one {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m) :
    omegaReal m ≤ 1 := by
  have h : omegaSum m ≤ 1 := hm.tsum_le_one
  simpa [omegaReal] using (ENNReal.toReal_le_toReal (omegaSum_ne_top hm) one_ne_top).2 h

/-- **SUV p. 160** (presupposed by Theorems 102–103, which speak of Solovay complete
reals *in `(0,1)`*): the sum of a maximal lower semicomputable semimeasure is strictly
positive. -/
theorem omegaReal_pos {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m) :
    0 < omegaReal m := by
  obtain ⟨c, hc, hdom⟩ := hm.dominates isLowerSemicomputableSemimeasureNat_diracNat
  have h0 : c ≤ m 0 := by simpa [diracNat] using hdom 0
  have hpos : 0 < m 0 := lt_of_lt_of_le hc h0
  have hle : m 0 ≤ omegaSum m := ENNReal.le_tsum 0
  exact ENNReal.toReal_pos (lt_of_lt_of_le hpos hle).ne' (omegaSum_ne_top hm)

/-- The `Ω`-numbers are lower semicomputable (SUV p. 157: `Ω` is the sum of the
maximal lower semicomputable series). -/
theorem isLowerSemicomputableReal_omegaReal {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) : IsLowerSemicomputableReal (omegaReal m) := by
  obtain ⟨A, Amono, Asup, Acomp⟩ := hm.isLowerSemicomputableSemimeasureNat.2
  set g : ℕ → ℕ → ℕ := fun s n => A s (natToBitString n) [] with hg
  have hgc : Computable (fun p : ℕ × ℕ => g p.1 p.2) :=
    Acomp.comp (Computable.pair Computable.fst
      (Computable.pair (computable_natToBitString.comp Computable.snd) (Computable.const [])))
  set N : ℕ → ℕ := fun s => natRangeSum g s s with hN
  have hNc : Computable N := computable_natRangeSum_diag hgc
  have hdsum : ∀ s, dyadicValue (N s) s = ∑ n ∈ Finset.range s, dyadicValue (g s n) s := by
    intro s
    rw [hN]
    simp only [natRangeSum_eq]
    exact dyadicValue_sum _ _ _
  have hmn : ∀ n : ℕ, ⨆ s, dyadicValue (g s n) s = m n := by
    intro n
    simpa [hg] using Asup (natToBitString n) []
  have hgle : ∀ s n, dyadicValue (g s n) s ≤ m n := by
    intro s n
    rw [← hmn n]
    exact le_iSup (fun t => dyadicValue (g t n) t) s
  have hgmono : ∀ n, Monotone (fun s => dyadicValue (g s n) s) := by
    intro n
    refine monotone_nat_of_le_succ (fun s => ?_)
    simpa [hg] using Amono s (natToBitString n) []
  have hdmono : ∀ s, dyadicValue (N s) s ≤ dyadicValue (N (s + 1)) (s + 1) := by
    intro s
    rw [hdsum s, hdsum (s + 1)]
    refine le_trans (Finset.sum_le_sum (fun n _ => hgmono n (Nat.le_succ s))) ?_
    exact Finset.sum_le_sum_of_subset (by simp)
  have hdle : ∀ s, dyadicValue (N s) s ≤ omegaSum m := by
    intro s
    rw [hdsum s]
    refine le_trans (Finset.sum_le_sum (fun n _ => hgle s n)) ?_
    exact ENNReal.sum_le_tsum _
  have hfin : ∀ s, dyadicValue (N s) s ≠ ⊤ := fun s =>
    ne_top_of_le_ne_top (omegaSum_ne_top hm) (hdle s)
  have hdlt : ∀ y : ℝ≥0∞, y < omegaSum m → ∃ s, y < dyadicValue (N s) s := by
    intro y hy
    rw [omegaSum, ENNReal.tsum_eq_iSup_nat] at hy
    obtain ⟨K, hK⟩ := lt_iSup_iff.mp hy
    have key : ∀ K : ℕ, ∑ n ∈ Finset.range K, m n
        = ⨆ s, ∑ n ∈ Finset.range K, dyadicValue (g s n) s := by
      intro K
      induction K with
      | zero => simp
      | succ K ih =>
          have hmonoS : Monotone (fun s => ∑ n ∈ Finset.range K, dyadicValue (g s n) s) :=
            fun i j hij => Finset.sum_le_sum (fun n _ => hgmono n hij)
          rw [Finset.sum_range_succ, ih, ← hmn K,
            ENNReal.iSup_add_iSup_of_monotone hmonoS (hgmono K)]
          exact iSup_congr (fun s => (Finset.sum_range_succ _ _).symm)
    rw [key K] at hK
    obtain ⟨s, hs⟩ := lt_iSup_iff.mp hK
    refine ⟨max s K, lt_of_lt_of_le hs ?_⟩
    rw [hdsum (max s K)]
    refine le_trans (Finset.sum_le_sum (fun n _ => hgmono n (le_max_left s K))) ?_
    exact Finset.sum_le_sum_of_subset (by simp)
  set a : ℕ → ℚ := fun s => (N s : ℚ) / 2 ^ s with ha
  have hac : Computable a := by
    refine computable_of_num_den (f := a) (N := fun s => ((N s : ℕ) : ℤ))
      (D := fun s => 2 ^ s) (ComputableReals.primrec_natCastInt.to_comp.comp hNc)
      (((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id).to_comp)
      (fun s => by positivity) (fun s => ?_)
    rw [ha]
    push_cast
    ring
  have hcast : ∀ s : ℕ, ((a s : ℚ) : ℝ) = (dyadicValue (N s) s).toReal := by
    intro s
    rw [dyadicValue, ENNReal.toReal_div, ha]
    push_cast
    simp
  have hble : ∀ s, ((a s : ℚ) : ℝ) ≤ omegaReal m := by
    intro s
    rw [hcast s, omegaReal]
    exact ENNReal.toReal_mono (omegaSum_ne_top hm) (hdle s)
  have hmonoR : Monotone (fun s => ((a s : ℚ) : ℝ)) := by
    refine monotone_nat_of_le_succ (fun s => ?_)
    rw [hcast s, hcast (s + 1)]
    exact ENNReal.toReal_mono (hfin (s + 1)) (hdmono s)
  have hbddAbove : BddAbove (Set.range (fun s => ((a s : ℚ) : ℝ))) := by
    refine ⟨omegaReal m, ?_⟩
    rintro y ⟨s, rfl⟩
    exact hble s
  have ha0 : ((a 0 : ℚ) : ℝ) = 0 := by
    rw [ha]
    norm_num [hN, natRangeSum]
  have hsup : (⨆ s, ((a s : ℚ) : ℝ)) = omegaReal m := by
    refine le_antisymm (ciSup_le hble) ?_
    by_contra hcon
    push Not at hcon
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hcon
    have h0 : (0 : ℝ) ≤ ⨆ s, ((a s : ℚ) : ℝ) := by
      have hle0 := le_ciSup hbddAbove 0
      rwa [ha0] at hle0
    have hrpos : (0 : ℝ) ≤ ((r : ℚ) : ℝ) := le_of_lt (lt_of_le_of_lt h0 hr1)
    have hlt : ENNReal.ofReal ((r : ℚ) : ℝ) < omegaSum m := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal hrpos (omegaSum_ne_top hm)]
      exact hr2
    obtain ⟨s, hs⟩ := hdlt _ hlt
    have hrs : ((r : ℚ) : ℝ) < ((a s : ℚ) : ℝ) := by
      rw [hcast s, ← ENNReal.ofReal_lt_iff_lt_toReal hrpos (hfin s)]
      exact hs
    have hle2 : ((a s : ℚ) : ℝ) ≤ ⨆ t, ((a t : ℚ) : ℝ) := le_ciSup hbddAbove s
    linarith
  refine ⟨a, hac, ?_, ?_⟩
  · intro i j hij
    have hij2 : ((a i : ℚ) : ℝ) ≤ ((a j : ℚ) : ℝ) := hmonoR hij
    exact_mod_cast hij2
  · rw [← hsup]
    exact tendsto_atTop_ciSup hmonoR hbddAbove

/-! ### Theorem 100 -/

/-- The quantitative core of the proof of Theorem 100 (SUV p. 157): from the first
`n` binary digits of `Ω` one can compute a finite list of integers containing every
`i` with `K(i) < n - c`, hence the `n`-bit prefix of `Ω` has prefix complexity at
least `n - c'` for a constant `c'` uniform in `n`. -/
theorem exists_const_le_KPPlain_cantorPrefix_omega {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {U : Map} (hU : IsOptimalPrefixConditional U)
    {w : CantorSeq} (hw : cantorReal w = omegaReal m) :
    ∃ c : ℕ, ∀ n : ℕ, (n : ENat) ≤ KPPlain U (cantorPrefix w n) + (c : ENat) := by
  classical
  -- the `ℕ`-indexed dyadic approximation of `m`
  obtain ⟨approx, hstepB, hsupB, hcompB⟩ := hm.1.2
  set A : ℕ → ℕ → ℕ := fun s i => approx s (natToBitString i) [] with hAdef
  have hAstep : ∀ s i, dyadicValue (A s i) s ≤ dyadicValue (A (s + 1) i) (s + 1) :=
    fun s i => hstepB s (natToBitString i) []
  have hAsup : ∀ i, ⨆ s, dyadicValue (A s i) s = m i := by
    intro i
    have h := hsupB (natToBitString i) []
    simpa [hAdef, bitStringToNat_natToBitString] using h
  have hAle : ∀ s i, dyadicValue (A s i) s ≤ m i := by
    intro s i
    rw [← hAsup i]
    exact le_iSup (fun t => dyadicValue (A t i) t) s
  have hAcomp : Computable (fun p : ℕ × ℕ => A p.1 p.2) := by
    have h1 : Computable (fun p : ℕ × ℕ => (p.1, natToBitString p.2, ([] : BitString))) :=
      Computable.fst.pair ((computable_natToBitString.comp Computable.snd).pair
        (Computable.const []))
    have h2 := hcompB.comp h1
    exact h2.of_eq (fun p => rfl)
  have hmass : (∑' k, m k) ≤ 1 := hm.tsum_le_one
  have hne : omegaSum m ≠ ⊤ := omegaSum_ne_top hm
  have hoR : ENNReal.ofReal (omegaReal m) = omegaSum m := ENNReal.ofReal_toReal hne
  obtain ⟨c₁, hc₁⟩ := KPNat_partial_map_le U hU (omegaSearch A) (partrec_omegaSearch hAcomp)
  obtain ⟨_cc1, cc2, _hcc1, hcc2, _hfwd, hbwd⟩ := exists_const_KPNat_aprioriNat_equiv hm hU
  obtain ⟨c₀, hc₀⟩ := exists_const_le_of_weight hcc2
  refine ⟨c₀ + c₁, fun n => ?_⟩
  have hxlen : (cantorPrefix w n).length = n := cantorPrefix_length w n
  have hΩ : cantorReal w = ∑' k : ℕ, (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0) := rfl
  have hlow : ((bitsValue (cantorPrefix w n) : ℚ) : ℝ) ≤ omegaReal m := by
    rw [← hw, hΩ]
    exact bitsValue_cantorPrefix_le w n
  have hhigh : omegaReal m
      ≤ ((bitsValue (cantorPrefix w n) : ℚ) : ℝ)
        + (1 : ℝ) / 2 ^ (cantorPrefix w n).length := by
    rw [← hw, hΩ, hxlen]
    exact le_bitsValue_cantorPrefix_add w n
  have hhighE : (∑' k, m k)
      ≤ ENNReal.ofReal (((bitsValue (cantorPrefix w n) : ℚ) : ℝ)
        + (1 : ℝ) / 2 ^ (cantorPrefix w n).length) := by
    rw [show (∑' k, m k) = omegaSum m from rfl, ← hoR]
    exact ENNReal.ofReal_le_ofReal hhigh
  -- the search terminates on this prefix
  have hppos : (0 : ℝ) < (1 : ℝ) / 2 ^ (cantorPrefix w n).length := by positivity
  have hfire : ∃ s : ℕ,
      ((bitsValue (cantorPrefix w n) : ℚ) : ℝ) - (1 : ℝ) / 2 ^ (cantorPrefix w n).length
        < ((diagSum A s s : ℚ) : ℝ) := by
    refine exists_lt_diagSum hAstep hAsup ?_
    rw [show (∑' k, m k) = omegaSum m from rfl, ← hoR]
    exact (ENNReal.ofReal_lt_ofReal_iff (omegaReal_pos hm)).2 (by linarith)
  obtain ⟨s, hs⟩ := hfire
  have hsQ : bitsValue (cantorPrefix w n) - 1 / 2 ^ (cantorPrefix w n).length
      < diagSum A s s := by
    have : ((bitsValue (cantorPrefix w n) - 1 / 2 ^ (cantorPrefix w n).length : ℚ) : ℝ)
        < ((diagSum A s s : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨i, hi⟩ := omegaSearch_dom hsQ
  have hmi := omegaSearch_mass_le hAle hmass hhighE hi
  have hmi' : m i ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ n := by
    rw [← ofReal_two_mul_inv_pow n, ← hxlen]
    exact hmi
  have hcount : (n : ENat) ≤ KPNat U i + (c₀ : ENat) :=
    hc₀ (KPNat U i) n (le_trans (hbwd i) hmi')
  have htrans : KPNat U i ≤ KPPlain U (cantorPrefix w n) + (c₁ : ENat) :=
    hc₁ (cantorPrefix w n) i hi
  calc (n : ENat) ≤ KPNat U i + (c₀ : ENat) := hcount
    _ ≤ (KPPlain U (cantorPrefix w n) + (c₁ : ENat)) + (c₀ : ENat) :=
        add_le_add htrans le_rfl
    _ = KPPlain U (cantorPrefix w n) + ((c₀ + c₁ : ℕ) : ENat) := by
        push_cast
        ring


/-- The binary representation of `Ω` is ML-random with respect to the uniform distribution. The
hypothesis quantifies over *every* maximal lower semicomputable semimeasure `m`, matching
the book's note that "the value of `Ω` depends on the choice of a maximal lower
semicomputable semimeasure, but the statement remains true for every choice"; `w` is any
binary representation of `Ω`.  SUV Theorem 100 (Section 5.7, p. 157). -/
theorem omega_binary_isMartinLofRandom {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {w : CantorSeq} (hw : cantorReal w = omegaReal m) :
    IsMartinLofRandom uniformMeasure w := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  exact (isMartinLofRandom_uniform_iff_le_KPPlain_cantorPrefix hU w).2
    (exists_const_le_KPPlain_cantorPrefix_omega hm hU hw)

/- `isMartinLofRandomReal_omegaReal`, together with the three statements that are
proved from it (`omegaReal_lt_one`, `omegaReal_mem_Ioo`, `IsOmegaNumber.mem_Ioo`), now
live at the end of `Omega/Solovay.lean`.  Nothing in this file uses them. -/

end Kolmogorov
