/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Complexity.CanonicalObjects.HubEdges
import KolmogorovMathlib.Complexity.ConditionalComplexity
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.IncompressibleStrings
import KolmogorovMathlib.Complexity.InfiniteSequences
import KolmogorovMathlib.Complexity.Information
import KolmogorovMathlib.Complexity.KolmogorovLevin
import KolmogorovMathlib.Complexity.PairComplexity
import KolmogorovMathlib.Complexity.RandomConditions
import KolmogorovMathlib.Complexity.SelfComplexity
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Interface.ComputableReals
import KolmogorovMathlib.Interface.ComputableReals.Part01
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic.Part01
import KolmogorovMathlib.Prefix.CondTwoStage
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Prefix.KPPairSwap
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.TotalCountingBound
import KolmogorovMathlib.Prefix.TwoStage
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Rat.Denumerable

/-!
# Lower semicomputable reals, halting probabilities and semimeasure realization

The halting probability `haltingProbability` of a machine, its dyadic lower approximations
(`lowerApproxPos`, `dyadicNumerator`, `dyadicApprox`), and the two directions of the
correspondence between lower semicomputable reals and halting probabilities:
`haltingProbability_isLSC` and `haltingProbability_of_isLowerSemicomputable`, with the
realization of a lower semicomputable semimeasure by a machine
(`semimeasure_realization`).

Conventions used here and in the modules that grew out of the same material: a randomized
machine without input is modelled by a prefix decompressor, so that the probability of the
output `x` is `aprioriMeasure M x []` and the halting probability is the total mass; `K` is
the prefix complexity `KPPlain U`/`KP U` for an optimal prefix-free conditional
decompressor and `C` the plain complexity `plainK`/`condK`; `O(1)` is an existentially
quantified constant and `O(log n)` uses `Nat.log 2` with an explicit factor.

SUV Theorems 44 and 45, pp. 106-108.
-/

namespace Kolmogorov


open ComputableReals
open scoped ENNReal
open Nat.Partrec (Code)

/-! ### Halting probability of a randomized machine -/

/-- The halting probability of a randomized machine without input, modelled as a
prefix decompressor reading its random bits self-delimitingly: the total mass of
all halting programs. -/
noncomputable def haltingProbability (M : Map) : ℝ≥0∞ :=
  ∑' x : BitString, aprioriMeasure M x []

/-! ### Machinery for Theorem 44 (b) -/

/-- The `Nat`-floor of a nonnegative rational of the form `N / d`. -/
lemma stageFloor_nat_div (N d : ℕ) (hd : 0 < d) :
    ⌊((N : ℚ) / (d : ℚ))⌋₊ = N / d := by
  have hd' : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [le_div_iff₀ hd']
    exact_mod_cast Nat.div_mul_le_self N d
  · rw [div_lt_iff₀ hd']
    have h1 := Nat.div_add_mod N d
    have h2 := Nat.mod_lt N hd
    have : N < (N / d + 1) * d := by nlinarith [Nat.div_add_mod N d]
    exact_mod_cast this

/-- Nat-floor of `r * 2 ^ k` computed from the numerator and denominator. -/
lemma stageFloor_eq (r : ℚ) (hr : 0 ≤ r) (k : ℕ) :
    ⌊(r * 2 ^ k : ℚ)⌋₊ = r.num.toNat * 2 ^ k / r.den := by
  have hnum : (0 : ℤ) ≤ r.num := Rat.num_nonneg.mpr hr
  have hd : 0 < r.den := r.pos
  have hd' : ((r.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have key : (r * 2 ^ k : ℚ) = ((r.num.toNat * 2 ^ k : ℕ) : ℚ) / ((r.den : ℕ) : ℚ) := by
    rw [eq_div_iff hd']
    have h1 : r * (r.den : ℚ) = (r.num : ℚ) := ComputableReals.rat_mul_den r
    have hcast : ((r.num.toNat : ℕ) : ℚ) = (r.num : ℚ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (Int.toNat_of_nonneg hnum)
    push_cast [hcast]
    calc r * 2 ^ k * (r.den : ℚ) = (r * (r.den : ℚ)) * 2 ^ k := by ring
      _ = (r.num : ℚ) * 2 ^ k := by rw [h1]
  rw [key, stageFloor_nat_div _ _ hd]

/-! ### Dyadic numerators of a lower-semicomputable real -/

/-- Truncation of a rational approximation to the nonnegative part. -/
def lowerApproxPos (q : ℕ → ℚ) (s : ℕ) : ℚ := max 0 (q s)

/-- The stage-`s` dyadic numerator `⌊q_s · 2^s⌋` of a lower approximation. -/
def dyadicNumerator (q : ℕ → ℚ) (s : ℕ) : ℕ := ⌊(lowerApproxPos q s) * 2 ^ s⌋₊

/-- The truncated approximation `lowerApproxPos q s = max 0 (q s)` is nonnegative. -/
lemma lowerApproxPos_nonneg (q : ℕ → ℚ) (s : ℕ) : 0 ≤ lowerApproxPos q s := le_max_left _ _

/-- Truncating at `0` preserves monotonicity of the approximating sequence. -/
lemma lowerApproxPos_mono {q : ℕ → ℚ} (hq : Monotone q) : Monotone (lowerApproxPos q) :=
  fun _ _ h => max_le_max le_rfl (hq h)

/-- The stage-`s` dyadic numerator `⌊max 0 (q s) · 2^s⌋` is computable in `s` whenever the
approximating sequence `q` is. -/
lemma dyadicNumerator_computable {q : ℕ → ℚ} (hq : Computable q) :
    Computable (dyadicNumerator q) := by
  have hpos : Computable (lowerApproxPos q) :=
    (ComputableReals.primrec_ratMax.to_comp).comp (Computable.const 0) hq
  have hnum : Computable (fun s => (lowerApproxPos q s).num.toNat) :=
    (ComputableReals.primrec_intToNat.to_comp).comp
      ((ComputableReals.primrec_ratNum.to_comp).comp hpos)
  have hden : Computable (fun s => (lowerApproxPos q s).den) :=
    (ComputableReals.primrec_ratDen.to_comp).comp hpos
  have hpow : Computable (fun s : ℕ => 2 ^ s) := (Kolmogorov.primrec_two_pow_aux).to_comp
  have hmul : Computable (fun s => (lowerApproxPos q s).num.toNat * 2 ^ s) :=
    (Primrec.nat_mul.to_comp).comp hnum hpow
  have hdiv : Computable
      (fun s => (lowerApproxPos q s).num.toNat * 2 ^ s / (lowerApproxPos q s).den) :=
    (Primrec.nat_div.to_comp).comp hmul hden
  exact hdiv.of_eq fun s => (stageFloor_eq _ (lowerApproxPos_nonneg q s) s).symm

/-- The dyadic numerator never overshoots: `⌊max 0 (q s) · 2^s⌋ ≤ max 0 (q s) · 2^s`. -/
lemma dyadicNumerator_le (q : ℕ → ℚ) (s : ℕ) :
    ((dyadicNumerator q s : ℚ)) ≤ lowerApproxPos q s * 2 ^ s :=
  Nat.floor_le (mul_nonneg (lowerApproxPos_nonneg q s) (by positivity))

/-- The dyadic numerator is off by less than one: `max 0 (q s) · 2^s < ⌊·⌋ + 1`. -/
lemma dyadicNumerator_lt (q : ℕ → ℚ) (s : ℕ) :
    lowerApproxPos q s * 2 ^ s < (dyadicNumerator q s : ℚ) + 1 :=
  Nat.lt_floor_add_one _

/-- Along a monotone approximation the dyadic numerators at least double from one stage to
the next, so the dyadic approximations are non-decreasing. -/
lemma dyadicNumerator_two_mul_le {q : ℕ → ℚ} (hq : Monotone q) (s : ℕ) :
    2 * dyadicNumerator q s ≤ dyadicNumerator q (s + 1) := by
  rw [dyadicNumerator]
  refine Nat.le_floor ?_
  push_cast
  have h1 : ((dyadicNumerator q s : ℚ)) ≤ lowerApproxPos q s * 2 ^ s := dyadicNumerator_le q s
  have h2 : lowerApproxPos q s ≤ lowerApproxPos q (s + 1) := lowerApproxPos_mono hq (Nat.le_succ s)
  have hpow : (0 : ℚ) < 2 ^ s := by positivity
  calc (2 : ℚ) * (dyadicNumerator q s : ℚ) ≤ 2 * (lowerApproxPos q s * 2 ^ s) := by linarith
    _ = lowerApproxPos q s * 2 ^ (s + 1) := by ring
    _ ≤ lowerApproxPos q (s + 1) * 2 ^ (s + 1) := by
        have : (0 : ℚ) < 2 ^ (s + 1) := by positivity
        nlinarith

/-- Real value of the stage-`s` dyadic approximation. -/
noncomputable def dyadicApprox (q : ℕ → ℚ) (s : ℕ) : ℝ := (dyadicNumerator q s : ℝ) / 2 ^ s

/-- The stage-`s` dyadic approximation lies below the truncated rational approximation. -/
lemma dyadicApprox_le (q : ℕ → ℚ) (s : ℕ) : dyadicApprox q s ≤ ((lowerApproxPos q s : ℚ) : ℝ) := by
  have h : ((dyadicNumerator q s : ℚ)) ≤ lowerApproxPos q s * 2 ^ s := dyadicNumerator_le q s
  have h' : ((dyadicNumerator q s : ℝ)) ≤ ((lowerApproxPos q s : ℚ) : ℝ) * 2 ^ s := by
    exact_mod_cast h
  have hpow : (0 : ℝ) < 2 ^ s := by positivity
  rw [dyadicApprox, div_le_iff₀ hpow]
  exact h'

/-- The stage-`s` dyadic approximation is within `2^{-s}` below the truncated rational
approximation. -/
lemma dyadicApprox_ge (q : ℕ → ℚ) (s : ℕ) :
    ((lowerApproxPos q s : ℚ) : ℝ) - (1 / 2) ^ s ≤ dyadicApprox q s := by
  have h : lowerApproxPos q s * 2 ^ s < (dyadicNumerator q s : ℚ) + 1 := dyadicNumerator_lt q s
  have h' : ((lowerApproxPos q s : ℚ) : ℝ) * 2 ^ s < (dyadicNumerator q s : ℝ) + 1 := by
    exact_mod_cast h
  have hpow : (0 : ℝ) < 2 ^ s := by positivity
  rw [dyadicApprox, le_div_iff₀ hpow, sub_mul]
  have : ((1 : ℝ) / 2) ^ s * 2 ^ s = 1 := by
    rw [← mul_pow]; norm_num
  nlinarith

/-- The dyadic approximations of a monotone rational approximation are non-decreasing. -/
lemma dyadicApprox_mono {q : ℕ → ℚ} (hq : Monotone q) : Monotone (dyadicApprox q) := by
  refine monotone_nat_of_le_succ fun s => ?_
  have h : 2 * dyadicNumerator q s ≤ dyadicNumerator q (s + 1) := dyadicNumerator_two_mul_le hq s
  have h' : (2 : ℝ) * (dyadicNumerator q s : ℝ) ≤ (dyadicNumerator q (s + 1) : ℝ) := by
    exact_mod_cast h
  have hp : (0 : ℝ) < 2 ^ s := by positivity
  have hp1 : (0 : ℝ) < 2 ^ (s + 1) := by positivity
  rw [dyadicApprox, dyadicApprox, div_le_div_iff₀ hp hp1]
  have : (2 : ℝ) ^ (s + 1) = 2 ^ s * 2 := by ring
  rw [this]
  nlinarith

/-- Truncating at `0` does not change the limit of an approximation of a nonnegative real. -/
lemma lowerApproxPos_tendsto {q : ℕ → ℚ} {a : ℝ} (h0 : 0 ≤ a)
    (hq : Filter.Tendsto (fun n => ((q n : ℚ) : ℝ)) Filter.atTop (nhds a)) :
    Filter.Tendsto (fun s => ((lowerApproxPos q s : ℚ) : ℝ)) Filter.atTop (nhds a) := by
  have hcont : Filter.Tendsto (fun s => max (0 : ℝ) ((q s : ℚ) : ℝ)) Filter.atTop
      (nhds (max (0 : ℝ) a)) := (continuous_const.max continuous_id).continuousAt.tendsto.comp hq
  rw [max_eq_right h0] at hcont
  refine hcont.congr fun s => ?_
  simp [lowerApproxPos]

/-- The dyadic approximations converge to the same nonnegative real as the rational ones. -/
lemma dyadicApprox_tendsto {q : ℕ → ℚ} {a : ℝ} (h0 : 0 ≤ a)
    (hq : Filter.Tendsto (fun n => ((q n : ℚ) : ℝ)) Filter.atTop (nhds a)) :
    Filter.Tendsto (dyadicApprox q) Filter.atTop (nhds a) := by
  have hup := lowerApproxPos_tendsto h0 hq
  have hhalf : Filter.Tendsto (fun s : ℕ => ((1 : ℝ) / 2) ^ s) Filter.atTop (nhds 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one <;> norm_num
  have hlow : Filter.Tendsto (fun s => ((lowerApproxPos q s : ℚ) : ℝ) - (1 / 2) ^ s)
      Filter.atTop (nhds (a - 0)) := hup.sub hhalf
  rw [sub_zero] at hlow
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup
    (fun s => dyadicApprox_ge q s) (fun s => dyadicApprox_le q s)

/-- The `ℝ≥0∞`-valued dyadic value of the stage-`s` numerator is the dyadic approximation. -/
lemma stageDyadicValue_eq (q : ℕ → ℚ) (s : ℕ) :
    dyadicValue (dyadicNumerator q s) s = ENNReal.ofReal (dyadicApprox q s) := by
  rw [dyadicValue, dyadicApprox, ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  · simp
  · rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num

/-- The supremum of the dyadic stage values of a monotone approximation of `a ≥ 0` is `a`. -/
lemma stageApprox_iSup_eq {q : ℕ → ℚ} {a : ℝ} (h0 : 0 ≤ a) (hmono : Monotone q)
    (hq : Filter.Tendsto (fun n => ((q n : ℚ) : ℝ)) Filter.atTop (nhds a)) :
    (⨆ s, dyadicValue (dyadicNumerator q s) s) = ENNReal.ofReal a := by
  have hm : Monotone (fun s => dyadicValue (dyadicNumerator q s) s) := by
    intro i j hij
    simp only [stageDyadicValue_eq]
    exact ENNReal.ofReal_le_ofReal (dyadicApprox_mono hmono hij)
  have h1 := tendsto_atTop_iSup hm
  have h2 : Filter.Tendsto (fun s => dyadicValue (dyadicNumerator q s) s) Filter.atTop
      (nhds (ENNReal.ofReal a)) := by
    have := ENNReal.tendsto_ofReal (dyadicApprox_tendsto h0 hq)
    exact this.congr fun s => (stageDyadicValue_eq q s).symm
  exact tendsto_nhds_unique h1 h2

/-- The point mass at the empty string with total weight `a`. -/
noncomputable def emptyStringPointMass (a : ℝ) : BitString → ℝ≥0∞ :=
  fun x => if x = ([] : BitString) then ENNReal.ofReal a else 0

/-- The point mass of a nonnegative lower semicomputable real `a` at the empty string is a
lower semicomputable semimeasure: its dyadic numerators enumerate it from below. -/
lemma haltingProbability_isLSC (a : ℝ) (h0 : 0 ≤ a) (ha : IsLowerSemicomputableReal a) :
    IsLSC (fun x _ => emptyStringPointMass a x) := by
  obtain ⟨q, hqc, hqm, hqt⟩ := ha
  refine ⟨fun s out _ => if out = ([] : BitString) then dyadicNumerator q s else 0, ?_, ?_, ?_⟩
  · intro s out ctx
    by_cases hout : out = ([] : BitString)
    · simp only [hout]
      have hm : Monotone (fun s => dyadicValue (dyadicNumerator q s) s) := by
        intro i j hij
        simp only [stageDyadicValue_eq]
        exact ENNReal.ofReal_le_ofReal (dyadicApprox_mono hqm hij)
      exact hm (Nat.le_succ s)
    · simp only [if_neg hout, dyadicValue_zero, le_refl]
  · intro out ctx
    by_cases hout : out = ([] : BitString)
    · subst hout
      simp only [emptyStringPointMass]
      exact stageApprox_iSup_eq h0 hqm hqt
    · simp only [emptyStringPointMass, if_neg hout, dyadicValue_zero]
      simp
  · have hc : Computable
        (fun p : ℕ × BitString × BitString => decide (p.2.1 = ([] : BitString))) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp
        (Computable.fst.comp Computable.snd) (Computable.const [])
    have hA : Computable (fun p : ℕ × BitString × BitString => dyadicNumerator q p.1) :=
      (dyadicNumerator_computable hqc).comp Computable.fst
    have := Computable.cond hc hA (Computable.const 0)
    refine this.of_eq fun p => ?_
    by_cases hout : p.2.1 = ([] : BitString) <;> simp [hout]

/-- The point mass at the empty string with weight `a ≤ 1` is a semimeasure. -/
lemma emptyStringPointMass_isSemimeasure (a : ℝ) (h1 : a ≤ 1) :
    IsSemimeasure (emptyStringPointMass a) := by
  classical
  have : (∑' x : BitString, emptyStringPointMass a x) = ENNReal.ofReal a := by
    simp only [emptyStringPointMass]
    exact tsum_ite_eq ([] : BitString) (fun _ => ENNReal.ofReal a)
  rw [IsSemimeasure, this]
  simpa using ENNReal.ofReal_le_ofReal h1

/-- The machine realizing a stream of Kraft–Chaitin requests: on input `p` it searches for a
stage `n` at which the allocator hands out exactly the code `p` for a pending request, and
then outputs the requested string. -/
def requestMachine (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString) : Map :=
  fun p =>
    (Nat.rfind fun n => Part.some
      (decide (alloc p.2 n = some p.1 ∧ (req p.2 n).isSome = true))) >>=
      fun n => Part.ofOption ((req p.2 n).map Prod.fst)

/-- A computable request stream whose allocator never issues one code as a prefix of another
turns `requestMachine` into a prefix decompressor. -/
lemma requestMachine_isPrefixDecompressor (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (hreqcomp : Computable (fun p : BitString × ℕ => req p.1 p.2))
    (hcomp : Computable (fun p : BitString × ℕ => alloc p.1 p.2))
    (hprefix : ∀ ctx n m cn cm, alloc ctx n = some cn → alloc ctx m = some cm →
      n ≠ m → ¬ List.IsPrefix cn cm) :
    IsPrefixDecompressor (requestMachine req alloc) := by
  constructor
  · refine Partrec.bind ?_ ?_
    · exact (Partrec.rfind (Partrec.of_eq (Computable.partrec
        (construct_pred_computable req alloc hreqcomp hcomp)) (fun _ => rfl)))
    · exact (Partrec.of_eq (construct_out_partrec req hreqcomp) (fun _ => rfl))
  · intro ctx p hp q hq hpre
    simp_all only [requestMachine, Bool.decide_and, Bool.decide_eq_true,
      Option.isSome_map, Part.bind_dom, Part.bind_eq_bind, Part.ofOption_dom,
      Set.mem_ofPred_eq, domainAt, ne_eq]
    obtain ⟨n, hn_dom, _⟩ := hp.1
    obtain ⟨m, hm_dom, _⟩ := hq.1
    have hn_bool : alloc ctx n = some p ∧ (req ctx n).isSome = true := by
      have hn_mem : true ∈ Part.some (decide (alloc ctx n = some p) && (req ctx n).isSome) := hn_dom
      rw [Part.mem_some_iff] at hn_mem
      have h1 : (decide (alloc ctx n = some p) && (req ctx n).isSome) = true := hn_mem.symm
      simpa using h1
    have hm_bool : alloc ctx m = some q ∧ (req ctx m).isSome = true := by
      have hm_mem : true ∈ Part.some (decide (alloc ctx m = some q) && (req ctx m).isSome) := hm_dom
      rw [Part.mem_some_iff] at hm_mem
      have h1 : (decide (alloc ctx m = some q) && (req ctx m).isSome) = true := hm_mem.symm
      simpa using h1
    have hn₁ := hn_bool.1
    have hm₁ := hm_bool.1
    by_cases hnm : n = m
    · cases hnm; rw [hn₁] at hm₁; cases hm₁; rfl
    · exact (hprefix ctx n m p q hn₁ hm₁ hnm hpre).elim

/-- The machine outputs `x` on the code `p` exactly when some stage requests `x` and the
allocator answers that request with `p`. -/
lemma requestMachine_eq_some (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (hprefix : ∀ ctx n m cn cm, alloc ctx n = some cn → alloc ctx m = some cm →
      n ≠ m → ¬ List.IsPrefix cn cm) (p ctx x : BitString) :
    requestMachine req alloc (p, ctx) = Part.some x ↔
      ∃ n l, req ctx n = some (x, l) ∧ alloc ctx n = some p := by
  constructor
  · intro h
    dsimp [requestMachine] at h
    rw [Part.eq_some_iff, Part.mem_bind_iff] at h
    rcases h with ⟨n, hn, hout⟩
    have hn2 : n ∈ Nat.rfind (show ℕ →. Bool from fun n =>
        Part.some (decide (alloc ctx n = some p ∧ (req ctx n).isSome = true))) := hn
    rw [Nat.mem_rfind] at hn2
    have hn_bool : alloc ctx n = some p ∧ (req ctx n).isSome = true := by
      simpa using hn2.1
    have hreq_some : (req ctx n).isSome = true := hn_bool.2
    obtain ⟨⟨o, l⟩, hreq⟩ := Option.ne_none_iff_exists'.mp (Option.isSome_iff_ne_none.mp hreq_some)
    have ho : o = x := by
      simpa [hreq] using Part.mem_ofOption.mp hout
    subst ho
    exact ⟨n, l, hreq, hn_bool.1⟩
  · rintro ⟨n, l, hreq, halloc⟩
    dsimp [requestMachine]
    rw [Part.eq_some_iff, Part.mem_bind_iff]
    refine ⟨n, ?_, ?_⟩
    · have hn : n ∈ Nat.rfind (show ℕ →. Bool from fun n =>
          Part.some (decide (alloc ctx n = some p ∧ (req ctx n).isSome = true))) := by
        rw [Nat.mem_rfind]
        refine ⟨by simp [halloc, hreq], fun {m} hm => ?_⟩
        simp only [Part.mem_some_iff]
        rw [eq_comm, decide_eq_false_iff_not, not_and]
        intro hm_alloc _
        have hneq : m ≠ n := Nat.ne_of_lt hm
        exact absurd (List.prefix_refl p)
          (hprefix ctx n m p p halloc hm_alloc hneq.symm)
      exact hn
    · simp [hreq]

/-- The weight `2^{-l}` that stage `n` contributes to `x`, or `0` when that stage requests
nothing or requests another string. -/
noncomputable def allocatedWeight (req : BitString → ℕ → Option (BitString × ℕ))
    (ctx x : BitString) (n : ℕ) : ℝ≥0∞ :=
  match req ctx n with
  | some (o, l) => if o = x then (2 : ℝ≥0∞)⁻¹ ^ l else 0
  | none => 0

/-- A stage of nonzero weight for `x` is a stage that requests `x`, at some length `l`. -/
lemma allocatedWeight_ne_zero_imp (req : BitString → ℕ → Option (BitString × ℕ))
    (ctx x : BitString) (n : ℕ) (hn : allocatedWeight req ctx x n ≠ 0) :
    ∃ l, req ctx n = some (x, l) := by
  dsimp [allocatedWeight] at hn
  cases hreq : req ctx n with
  | none => rw [hreq] at hn; contradiction
  | some p =>
    cases p with
    | mk o l =>
      rw [hreq] at hn
      dsimp at hn
      split_ifs at hn with ho
      · subst ho
        use l
      · contradiction

/-- The code that the allocator hands out at a stage of nonzero weight for `x`. -/
noncomputable def allocatedString (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (halloc_match : ∀ ctx n o l, req ctx n = some (o, l) →
      ∃ c, alloc ctx n = some c ∧ c.length = l)
    (ctx x : BitString) (n : ℕ) (hn : allocatedWeight req ctx x n ≠ 0) : BitString :=
  let l := (allocatedWeight_ne_zero_imp req ctx x n hn).choose
  let hreq := (allocatedWeight_ne_zero_imp req ctx x n hn).choose_spec
  (halloc_match ctx n x l hreq).choose

/-- The defining property of `allocatedString`: it is the allocator's answer at that stage,
and its length is the requested one. -/
lemma allocatedString_spec (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (halloc_match : ∀ ctx n o l, req ctx n = some (o, l) →
      ∃ c, alloc ctx n = some c ∧ c.length = l)
    (ctx x : BitString) (n : ℕ) (hn : allocatedWeight req ctx x n ≠ 0) :
    ∃ l, req ctx n = some (x, l) ∧
      alloc ctx n = some (allocatedString req alloc halloc_match ctx x n hn) ∧
      (allocatedString req alloc halloc_match ctx x n hn).length = l := by
  set l := (allocatedWeight_ne_zero_imp req ctx x n hn).choose
  set hreq := (allocatedWeight_ne_zero_imp req ctx x n hn).choose_spec
  set spec := (halloc_match ctx n x l hreq).choose_spec
  exact ⟨l, hreq, spec.1, spec.2⟩

/-- Every lower semicomputable semimeasure is the a priori probability of a prefix
decompressor: `m` is realized as `aprioriMeasure M · []` for some prefix machine `M`. -/
theorem semimeasure_realization (m : BitString → ℝ≥0∞)
    (hm : IsLowerSemicomputableSemimeasure m) :
    ∃ M : Map, IsPrefixDecompressor M ∧ ∀ x, aprioriMeasure M x [] = m x := by
  have hf_lsc : IsLSC (fun x _ => m x) := hm.2
  have hf_sum : ∀ ctx : BitString, (∑' out : BitString, m out) ≤ 1 := fun _ => hm.1
  obtain ⟨req, hreqcomp, hreqweight, hreqsum⟩ := extract_request_stream hf_lsc hf_sum
  obtain ⟨alloc, halloccomp, halloc_match, hprefix⟩ :=
    exists_online_prefixFree_family req hreqcomp hreqweight
  have hM_pref := requestMachine_isPrefixDecompressor req alloc hreqcomp halloccomp hprefix
  refine ⟨requestMachine req alloc, hM_pref, fun x => ?_⟩
  rw [aprioriMeasure]
  have h_sum := hreqsum [] x
  rw [← h_sum]
  have h_prod (p : BitString) : produces (requestMachine req alloc) p [] x ↔
      ∃ n l, req [] n = some (x, l) ∧ alloc [] n = some p := by
    dsimp [produces]
    rw [Part.eq_some_iff.symm]
    exact requestMachine_eq_some req alloc hprefix p [] x
  open Classical in
  let f : BitString → ℝ≥0∞ := fun p =>
    if produces (requestMachine req alloc) p [] x then progWeight p else 0
  let g : ℕ → ℝ≥0∞ := allocatedWeight req [] x
  have h_fg : (∑' p : BitString, f p) = ∑' n : ℕ, g n := by
    let i : ↑(Function.support g) → BitString := fun ⟨n, hn⟩ =>
      allocatedString req alloc halloc_match [] x n hn
    have hi : Function.Injective i := by
      rintro ⟨n1, hn1⟩ ⟨n2, hn2⟩ h_eq
      dsimp [i] at h_eq
      obtain ⟨l1, hreq1, halloc1, _⟩ := allocatedString_spec req alloc halloc_match [] x n1 hn1
      obtain ⟨l2, hreq2, halloc2, _⟩ := allocatedString_spec req alloc halloc_match [] x n2 hn2
      by_cases hneq : n1 = n2
      · exact Subtype.ext hneq
      · exfalso
        have halloc2' := halloc2
        rw [← h_eq] at halloc2'
        exact hprefix [] n1 n2 (i ⟨n1, hn1⟩) (i ⟨n1, hn1⟩) halloc1 halloc2' hneq
          (List.prefix_refl (i ⟨n1, hn1⟩))
    have hf_supp : Function.support f ⊆ Set.range i := by
      intro p hp
      dsimp [Function.support, f] at hp
      split_ifs at hp with hM
      · rw [h_prod] at hM
        rcases hM with ⟨n, l, hreq, halloc⟩
        have hn_supp : g n ≠ 0 := by
          dsimp [g, allocatedWeight]
          rw [hreq]
          simp only [if_true]
          exact ENNReal.pow_ne_zero (ENNReal.inv_ne_zero.mpr (by norm_num)) _
        refine ⟨⟨n, hn_supp⟩, ?_⟩
        dsimp [i]
        obtain ⟨l', hreq', halloc', _⟩ :=
          allocatedString_spec req alloc halloc_match [] x n hn_supp
        rw [hreq] at hreq'
        cases Option.some.inj hreq'
        exact Option.some.inj (halloc'.symm.trans halloc)
      · contradiction
    have hfg : ∀ n_sub : ↑(Function.support g), f (i n_sub) = g n_sub.1 := by
      rintro ⟨n, hn⟩
      dsimp [f]
      obtain ⟨l, hreq, halloc, hlen⟩ := allocatedString_spec req alloc halloc_match [] x n hn
      have hM : produces (requestMachine req alloc) (i ⟨n, hn⟩) [] x := by
        rw [h_prod]
        exact ⟨n, l, hreq, halloc⟩
      rw [if_pos hM]
      dsimp [progWeight, programLength, g, allocatedWeight]
      rw [hreq, hlen]
      dsimp
      rw [if_pos rfl]
    exact tsum_eq_tsum_of_ne_zero_bij i hi hf_supp hfg
  exact h_fg

/-- Every lower semicomputable real in `[0, 1]` is the halting probability of some prefix
decompressor. -/
theorem haltingProbability_of_isLowerSemicomputable (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1)
    (ha : IsLowerSemicomputableReal a) :
    ∃ M : Map, IsPrefixDecompressor M ∧ haltingProbability M = ENNReal.ofReal a := by
  obtain ⟨M, hM, hval⟩ :=
    semimeasure_realization (emptyStringPointMass a)
      ⟨emptyStringPointMass_isSemimeasure a h1, haltingProbability_isLSC a h0 ha⟩
  refine ⟨M, hM, ?_⟩
  rw [haltingProbability, tsum_congr hval]
  simp only [emptyStringPointMass]
  exact tsum_ite_eq ([] : BitString) (fun _ => ENNReal.ofReal a)

/-! ### Machinery for Theorem 44 (a)

The halting probability of a randomized machine is approximated from below by the
probability that it halts *within `n` steps*, using only the first `n` random bits.
Fixing a code `c` for the machine, that quantity is the finite sum of `2^{-|p|}` over
the programs `p` of length at most `n` on which `c` halts within `n` steps.  It is a
rational multiple of `2^{-n}`, computable by simulation (`qApp`, `qApp_computable`), and
its supremum is the total halting mass (`wSum_le`, `domainWeight_le_iSup`). -/

namespace StageHaltingMass

open Nat.Partrec (Code)

/-! #### The rational stage approximation -/

/-- Summing a mapped list is folding addition along it. -/
private lemma sumMap_eq_foldr {α : Type*} (f : α → ℕ) :
    ∀ l : List α, (l.map f).sum = l.foldr (fun a s => f a + s) 0
  | [] => rfl
  | a :: l => by simp [sumMap_eq_foldr f l]

/-- The `2^n`-scaled weight `2^{n-|p|}` of a program halting within `n` steps. -/
private def nTerm (c : Code) (n : ℕ) (p : BitString) : ℕ :=
  bif haltsWithin c n p then 2 ^ (n - p.length) else 0

/-- The `2^n`-scaled mass of the programs of length `≤ n` halting within `n` steps. -/
private def nSum (c : Code) (n : ℕ) : ℕ :=
  ((boundedPrograms n).map (nTerm c n)).sum

private theorem nTerm_primrec (c : Code) :
    Primrec₂ (fun (n : ℕ) (p : BitString) => nTerm c n p) := by
  have hpow : Primrec (fun q : ℕ × BitString => 2 ^ (q.1 - q.2.length)) :=
    primrec_two_pow_aux.comp
      (Primrec.nat_sub.comp Primrec.fst (Primrec.list_length.comp Primrec.snd))
  have h := Primrec.cond (haltsWithin_primrec₂ c) hpow (Primrec.const 0)
  exact h.of_eq (fun _ => rfl)

private theorem nSum_primrec (c : Code) : Primrec (nSum c) := by
  have hstep : Primrec₂ (fun (n : ℕ) (q : BitString × ℕ) => nTerm c n q.1 + q.2) :=
    (Primrec.nat_add.comp
      ((nTerm_primrec c).comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr primrec_boundedPrograms (Primrec.const (0 : ℕ)) hstep
  exact h.of_eq (fun n => (sumMap_eq_foldr (nTerm c n) (boundedPrograms n)).symm)

/-- The probability that the machine coded by `c` halts within `n` steps, as a rational
multiple of `2^{-n}`. -/
private def qApp (c : Code) (n : ℕ) : ℚ := (nSum c n : ℚ) / 2 ^ n

/-- Cross-multiplication recognises the stage approximation among the rationals. -/
private lemma qApp_spec (c : Code) (n : ℕ) (q : ℚ) :
    (q.num * ((2 ^ n : ℕ) : ℤ) = (nSum c n : ℤ) * (q.den : ℤ)) ↔ q = qApp c n := by
  have hden : ((q.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
  have hpow : ((2 : ℚ) ^ n) ≠ 0 := by positivity
  have hmuld : q * (q.den : ℚ) = (q.num : ℚ) := ComputableReals.rat_mul_den q
  rw [qApp, eq_div_iff hpow]
  constructor
  · intro h
    have h' : ((q.num : ℚ)) * ((2 : ℚ) ^ n) = (nSum c n : ℚ) * (q.den : ℚ) := by
      exact_mod_cast h
    refine mul_right_cancel₀ hden ?_
    calc q * (2 : ℚ) ^ n * (q.den : ℚ) = (q * (q.den : ℚ)) * (2 : ℚ) ^ n := by ring
      _ = (q.num : ℚ) * (2 : ℚ) ^ n := by rw [hmuld]
      _ = (nSum c n : ℚ) * (q.den : ℚ) := h'
  · intro h
    have h' : ((q.num : ℚ)) * ((2 : ℚ) ^ n) = (nSum c n : ℚ) * (q.den : ℚ) := by
      calc (q.num : ℚ) * (2 : ℚ) ^ n = (q * (q.den : ℚ)) * (2 : ℚ) ^ n := by rw [hmuld]
        _ = (q * (2 : ℚ) ^ n) * (q.den : ℚ) := by ring
        _ = (nSum c n : ℚ) * (q.den : ℚ) := by rw [h]
    exact_mod_cast h'

/-- **Simulation is effective.**  The stage approximation is a computable sequence of
rationals. -/
private theorem qApp_computable (c : Code) : Computable (qApp c) := by
  have hnum : Primrec (fun z : ℕ × ℚ => z.2.num) :=
    ComputableReals.primrec_ratNum.comp Primrec.snd
  have hden : Primrec (fun z : ℕ × ℚ => ((z.2.den : ℤ))) :=
    ComputableReals.primrec_natCastInt.comp (ComputableReals.primrec_ratDen.comp Primrec.snd)
  have hpow : Primrec (fun z : ℕ × ℚ => (((2 ^ z.1 : ℕ)) : ℤ)) :=
    ComputableReals.primrec_natCastInt.comp (primrec_two_pow_aux.comp Primrec.fst)
  have hN : Primrec (fun z : ℕ × ℚ => ((nSum c z.1 : ℕ) : ℤ)) :=
    ComputableReals.primrec_natCastInt.comp ((nSum_primrec c).comp Primrec.fst)
  have hver : Primrec (fun z : ℕ × ℚ =>
      decide (z.2.num * ((2 ^ z.1 : ℕ) : ℤ) = (nSum c z.1 : ℤ) * (z.2.den : ℤ))) :=
    (PrimrecRel.comp Primrec.eq (ComputableReals.primrec_intMul.comp hnum hpow)
      (ComputableReals.primrec_intMul.comp hN hden)).decide
  refine ComputableReals.computable_of_verifier
    (p := fun (n : ℕ) (q : ℚ) =>
      decide (q.num * ((2 ^ n : ℕ) : ℤ) = (nSum c n : ℤ) * (q.den : ℤ)))
    hver.to_comp.to₂ (fun n q => ?_)
  simp only [decide_eq_true_eq]
  exact qApp_spec c n q

/-! #### The same approximation, as an extended real -/

/-- The stage-`n` contribution of a program to the halting probability. -/
private noncomputable def wTerm (c : Code) (n : ℕ) (p : BitString) : ℝ≥0∞ :=
  bif haltsWithin c n p then progWeight p else 0

/-- The programs of length at most `n`, as a finset. -/
private def bpFinset (n : ℕ) : Finset BitString := (boundedPrograms n).toFinset

private lemma mem_bpFinset {n : ℕ} {p : BitString} : p ∈ bpFinset n ↔ p.length ≤ n := by
  rw [bpFinset, List.mem_toFinset, mem_boundedPrograms_iff]

/-- The probability that the machine coded by `c` halts within `n` steps. -/
private noncomputable def wSum (c : Code) (n : ℕ) : ℝ≥0∞ :=
  ∑ p ∈ bpFinset n, wTerm c n p

private lemma nSum_cast (c : Code) (n : ℕ) :
    ((nSum c n : ℕ) : ℝ≥0∞) = ∑ p ∈ bpFinset n, ((nTerm c n p : ℕ) : ℝ≥0∞) := by
  rw [bpFinset, List.sum_toFinset _ (boundedPrograms_nodup n), nSum, Nat.cast_list_sum,
    List.map_map]
  rfl

private lemma wTerm_mul_pow (c : Code) {n : ℕ} {p : BitString} (hp : p.length ≤ n) :
    wTerm c n p * 2 ^ n = ((nTerm c n p : ℕ) : ℝ≥0∞) := by
  have h2 : (2 : ℝ≥0∞) ^ n = 2 ^ p.length * 2 ^ (n - p.length) := by
    rw [← pow_add]
    congr 1
    omega
  cases hb : haltsWithin c n p with
  | false => simp [wTerm, nTerm, hb]
  | true =>
      have h0 : ((2 : ℝ≥0∞) ^ p.length) ≠ 0 := pow_ne_zero _ (by norm_num)
      have ht : ((2 : ℝ≥0∞) ^ p.length) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
      simp only [wTerm, nTerm, hb, cond_true, progWeight, programLength]
      rw [← ENNReal.inv_pow, h2, ← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
      push_cast
      rfl

/-- The stage approximation, scaled by `2^n`, is the natural number computed by `nSum`. -/
private lemma wSum_mul_pow (c : Code) (n : ℕ) :
    wSum c n * 2 ^ n = ((nSum c n : ℕ) : ℝ≥0∞) := by
  rw [wSum, Finset.sum_mul, nSum_cast]
  exact Finset.sum_congr rfl (fun p hp => wTerm_mul_pow c (mem_bpFinset.mp hp))

/-- The two readings of the stage approximation agree. -/
private lemma wSum_toReal (c : Code) (n : ℕ) :
    (wSum c n).toReal = ((qApp c n : ℚ) : ℝ) := by
  have h := congrArg ENNReal.toReal (wSum_mul_pow c n)
  rw [ENNReal.toReal_mul] at h
  have h2 : (((2 : ℝ≥0∞) ^ n)).toReal = (2 : ℝ) ^ n := by
    rw [ENNReal.toReal_pow]
    norm_num
  have h3 : (((nSum c n : ℕ) : ℝ≥0∞)).toReal = (nSum c n : ℝ) := by simp
  rw [h2, h3] at h
  have hpow : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  rw [qApp]
  push_cast
  rw [eq_div_iff hpow]
  exact h

private lemma wTerm_mono (c : Code) {n m : ℕ} (h : n ≤ m) (p : BitString) :
    wTerm c n p ≤ wTerm c m p := by
  cases hb : haltsWithin c n p with
  | false => simp [wTerm, hb]
  | true =>
      have hb' : haltsWithin c m p = true := haltsWithin_mono c h p hb
      simp [wTerm, hb, hb']

/-- More steps and longer programs can only increase the halting mass found. -/
private lemma wSum_mono (c : Code) : Monotone (wSum c) := by
  intro n m h
  rw [wSum, wSum]
  refine le_trans (Finset.sum_le_sum (fun p _ => wTerm_mono c h p)) ?_
  exact Finset.sum_le_sum_of_subset
    (fun p hp => mem_bpFinset.mpr (le_trans (mem_bpFinset.mp hp) h))

/-! #### The stage approximations converge to the halting probability -/

/-- A program is in the halting domain exactly when the simulation stops on it. -/
private lemma dom_iff_exists_halts {c : Code} {M : Map} (hc : IsCodeFor c M) (p : BitString) :
    p ∈ domainAt M [] ↔ ∃ t, haltsWithin c t p = true := by
  constructor
  · intro hp
    obtain ⟨out, hout⟩ := Part.dom_iff_mem.mp hp
    obtain ⟨t, ht⟩ := runOut_complete hc hout
    refine ⟨t, ?_⟩
    rw [runOut, Option.bind_eq_some_iff] at ht
    obtain ⟨a, ha, -⟩ := ht
    rw [haltsWithin, ha]
    rfl
  · rintro ⟨t, ht⟩
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp ht
    have hsound : r ∈ Code.eval c
        (Encodable.encode ((p, ([] : BitString)) : BitString × BitString)) :=
      Code.evaln_sound (Option.mem_def.mpr hr)
    rw [hc] at hsound
    simp only [Part.mem_bind_iff] at hsound
    obtain ⟨a, hamem, hr2⟩ := hsound
    have h1 : a ∈ (Encodable.decode (α := BitString × BitString)
        (Encodable.encode ((p, ([] : BitString)) : BitString × BitString))) :=
      Part.mem_ofOption.mp hamem
    rw [Encodable.encodek] at h1
    have ha : (p, ([] : BitString)) = a := by simpa using h1
    subst ha
    obtain ⟨w, hw, -⟩ := (Part.mem_map_iff _).mp hr2
    exact Part.dom_iff_mem.mpr ⟨w, hw⟩

/-- Every stage approximation is a lower bound for the halting probability. -/
private lemma wSum_le {c : Code} {M : Map} (hc : IsCodeFor c M) (n : ℕ) :
    wSum c n ≤ domainWeight M [] := by
  classical
  rw [wSum, domainWeight]
  refine le_trans ?_ (ENNReal.sum_le_tsum (bpFinset n))
  refine Finset.sum_le_sum (fun p _ => ?_)
  cases hb : haltsWithin c n p with
  | false => simp [wTerm, hb]
  | true =>
      have hd : p ∈ domainAt M [] := (dom_iff_exists_halts hc p).mpr ⟨n, hb⟩
      simp [wTerm, hb, hd]

/-- Finitely many halting programs are all caught by some common stage. -/
private lemma exists_stage {c : Code} {M : Map} (hc : IsCodeFor c M) (s : Finset BitString) :
    ∃ n, ∀ p ∈ s, p.length ≤ n ∧ (p ∈ domainAt M [] → haltsWithin c n p = true) := by
  classical
  refine ⟨s.sup (fun p => max p.length (sInf {t | haltsWithin c t p = true})), fun p hp => ?_⟩
  have hle := Finset.le_sup
    (f := fun p : BitString => max p.length (sInf {t | haltsWithin c t p = true})) hp
  refine ⟨le_trans (le_max_left _ _) hle, fun hd => ?_⟩
  have hex : ∃ t, haltsWithin c t p = true := (dom_iff_exists_halts hc p).mp hd
  have hmem : haltsWithin c (sInf {t | haltsWithin c t p = true}) p = true := Nat.sInf_mem hex
  exact haltsWithin_mono c (le_trans (le_max_right _ _) hle) p hmem

/-- Nothing is lost in the limit: the stage approximations exhaust the halting mass. -/
private lemma domainWeight_le_iSup {c : Code} {M : Map} (hc : IsCodeFor c M) :
    domainWeight M [] ≤ ⨆ n, wSum c n := by
  classical
  rw [domainWeight, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun s => ?_)
  obtain ⟨n, hn⟩ := exists_stage hc s
  refine le_trans ?_ (le_iSup (fun n => wSum c n) n)
  rw [wSum]
  have hsub : s ⊆ bpFinset n := fun p hp => mem_bpFinset.mpr (hn p hp).1
  refine le_trans (Finset.sum_le_sum (fun p hp => ?_)) (Finset.sum_le_sum_of_subset hsub)
  by_cases hd : p ∈ domainAt M []
  · rw [if_pos hd]
    have hh := (hn p hp).2 hd
    simp [wTerm, hh]
  · rw [if_neg hd]
    exact zero_le

/-- The stage approximations converge to the halting probability. -/
private lemma tendsto_wSum_toReal {c : Code} {M : Map} (hc : IsCodeFor c M)
    (hM : IsPrefixDecompressor M) :
    Filter.Tendsto (fun n => (wSum c n).toReal) Filter.atTop
      (nhds (domainWeight M []).toReal) := by
  have hAtop : domainWeight M [] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (domainWeight_le_one M [] hM.2)
  have hsup : (⨆ n, wSum c n) = domainWeight M [] :=
    le_antisymm (iSup_le (fun n => wSum_le hc n)) (domainWeight_le_iSup hc)
  have h1 := tendsto_atTop_iSup (wSum_mono c)
  rw [hsup] at h1
  exact (ENNReal.tendsto_toReal hAtop).comp h1

end StageHaltingMass

/-- **Theorem 44 (a).** The halting probability of a randomized machine without
input is a lower semicomputable real. -/
theorem haltingProbability_isLowerSemicomputable (M : Map) (hM : IsPrefixDecompressor M) :
    IsLowerSemicomputableReal (haltingProbability M).toReal := by
  obtain ⟨c, hc⟩ : ∃ c : Nat.Partrec.Code, IsCodeFor c M :=
    Nat.Partrec.Code.exists_code.mp hM.1
  have hAtop : domainWeight M [] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (domainWeight_le_one M [] hM.2)
  have key : ComputableReals.IsLowerSemicomputableReal (domainWeight M []).toReal := by
    refine ComputableReals.isLowerSemicomputableReal_of_tendsto_le
      (StageHaltingMass.qApp_computable c) (fun n => ?_) ?_
    · rw [← StageHaltingMass.wSum_toReal c n]
      exact ENNReal.toReal_mono hAtop (StageHaltingMass.wSum_le hc n)
    · exact (StageHaltingMass.tendsto_wSum_toReal hc hM).congr
        (fun n => StageHaltingMass.wSum_toReal c n)
  rw [haltingProbability, tsum_aprioriMeasure_eq_domainWeight M []]
  exact key

end Kolmogorov
