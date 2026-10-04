/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctionDyadic
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealApi

/-!
# The capped scaling of SUV p. 167

The hard direction of SUV Theorem 112 rests on one construction (p. 167):

> For some constant `c` we may let `m̃(i,j)` be `c·aᵢⱼ` while this does not violate the
> property `∑ⱼ m̃(i,j) ≤ m(i)`.  (As `m(i)` increases, we let `m̃(i,j)` increase when
> possible.) … It remains to perform this construction for all `c = 2^{2n}` and combine the
> resulting `m̃` with coefficients `2^{-n}`.

This module carries it out.  The greedy cap is

  `capTerm s n i j = 2ⁿ·aᵢⱼ` if `2^{2n+1}·(∑_{j' ≤ j} aᵢⱼ') < mₛ(i)`, and `0` otherwise,

where `mₛ` is the stage-`s` rational approximation of `m` supplied by lower
semicomputability; the strict comparison of two *rationals* is what makes the condition
decidable at each stage and monotone in `s`.  Summing over `n < s` gives a computable
rational `capApprox s k` that is non-decreasing in `s`, and

  `cappedScaling k = ⨆ s, ofReal (capApprox s k)`

is lower semicomputable by `isLSC_iSup_of_monotone`, has total mass at most `1` (the
`n`-th layer contributes at most `2^{-(n+1)}·∑ᵢ m(i)`), and dominates `2ⁿ·aᵢⱼ` on every
group with `2^{2n+1}·Aᵢ < m(i)`.
-/

namespace Kolmogorov

open ENNReal

/-! ### Lower semicomputability from a monotone computable rational approximation -/

/-- **An `IsLSC` witness from a monotone computable rational approximation.**  The dyadic
floors of a stagewise non-decreasing computable rational sequence are exactly the
numerators `IsLSC` asks for. -/
theorem isLSC_iSup_of_monotone {g : ℕ → ℕ → ℚ} (hg : Computable₂ g)
    (hgm : ∀ s n, g s n ≤ g (s + 1) n) :
    IsLSC (fun (x _ : BitString) => ⨆ s, ENNReal.ofReal ((g s (bitStringToNat x) : ℚ) : ℝ)) := by
  refine ⟨fun s x _ => ratDyadicFloor (g s (bitStringToNat x)) s, ?_, ?_, ?_⟩
  · intro s x _
    exact dyadicValue_ratDyadicFloor_mono_of_le (hgm s (bitStringToNat x)) s
  · intro x _
    exact iSup_dyadicValue_ratDyadicFloor
      (monotone_nat_of_le_succ (fun s => hgm s (bitStringToNat x)))
  · exact computable_ratDyadicFloor.comp
      (hg.comp Computable.fst (computable_bitStringToNat.comp
        (Computable.fst.comp Computable.snd))) Computable.fst

/-! ### The stage approximation of a lower semicomputable semimeasure -/

/-- The stage-`s` rational lower approximation of an `ℕ`-indexed lower semicomputable
function, extracted from its `IsLSC` witness. -/
noncomputable def lscRatApprox (A : ℕ → BitString → BitString → ℕ) (s i : ℕ) : ℚ :=
  (A s (natToBitString i) [] : ℚ) / 2 ^ s

/-- The extended-nonnegative value of the stage-`s` rational approximation is the dyadic mass the
enumeration has put on the index by stage `s`. -/
theorem ofReal_lscRatApprox (A : ℕ → BitString → BitString → ℕ) (s i : ℕ) :
    ENNReal.ofReal ((lscRatApprox A s i : ℚ) : ℝ) = dyadicValue (A s (natToBitString i) []) s := by
  rw [lscRatApprox, dyadicValue]
  have hcast : (((A s (natToBitString i) [] : ℕ) : ℚ) / 2 ^ s : ℚ)
      = ((A s (natToBitString i) [] : ℕ) : ℚ) / ((2 ^ s : ℕ) : ℚ) := by push_cast; ring
  rw [hcast]
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  · exact ENNReal.ofReal_natCast _
  · rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- The stage approximations are nonnegative. -/
theorem lscRatApprox_nonneg (A : ℕ → BitString → BitString → ℕ) (s i : ℕ) :
    0 ≤ lscRatApprox A s i := by
  rw [lscRatApprox]
  positivity

/-- The stage approximations of a computable mass enumeration are computable in the stage and the
index. -/
theorem computable_lscRatApprox {A : ℕ → BitString → BitString → ℕ}
    (hA : Computable (fun p : ℕ × BitString × BitString => A p.1 p.2.1 p.2.2)) :
    Computable₂ (lscRatApprox A) := by
  have hnum : Computable (fun p : ℕ × ℕ => A p.1 (natToBitString p.2) []) :=
    hA.comp (Computable.pair Computable.fst
      (Computable.pair (computable_natToBitString.comp Computable.snd) (Computable.const [])))
  refine computable_of_num_den (N := fun p : ℕ × ℕ => (A p.1 (natToBitString p.2) [] : ℤ))
    (D := fun p : ℕ × ℕ => 2 ^ p.1) ?_ ?_ (fun p => pow_pos (by norm_num) _) (fun p => ?_)
  · exact ComputableReals.primrec_natCastInt.to_comp.comp hnum
  · exact Computable.pow2.comp Computable.fst
  · rw [lscRatApprox]
    push_cast
    ring

/-! ### The capped scaling -/

/-- `∑_{j' < t} aᵢⱼ'`, in the recursive shape `Computable.nat_rec` accepts. -/
def groupSum (a : ℕ → ℕ → ℚ) (i t : ℕ) : ℚ :=
  Nat.rec (motive := fun _ => ℚ) 0 (fun t' acc => acc + a i t') t

/-- The recursive group sum agrees with the sum over `Finset.range`. -/
theorem groupSum_eq (a : ℕ → ℕ → ℚ) (i t : ℕ) :
    groupSum a i t = ∑ j ∈ Finset.range t, a i j := by
  induction t with
  | zero => simp [groupSum]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

/-- `∑_{j' ≤ j} aᵢⱼ'`, the running total inside a group. -/
def groupPartial (a : ℕ → ℕ → ℚ) (i j : ℕ) : ℚ := groupSum a i (j + 1)

/-- The running total inside a group is the sum of the first `j + 1` entries. -/
theorem groupPartial_eq (a : ℕ → ℕ → ℚ) (i j : ℕ) :
    groupPartial a i j = ∑ j' ∈ Finset.range (j + 1), a i j' := groupSum_eq a i (j + 1)

/-- One layer of the greedy cap at stage `s`: the value `2ⁿ·aᵢⱼ`, kept as long as the
running total scaled by `2^{2n+1}` is still below the stage-`s` approximation of `m(i)`. -/
noncomputable def capTerm (a : ℕ → ℕ → ℚ) (A : ℕ → BitString → BitString → ℕ)
    (s n i j : ℕ) : ℚ :=
  if (2 : ℚ) ^ (2 * n + 1) * groupPartial a i j < lscRatApprox A s i then (2 : ℚ) ^ n * a i j
  else 0

/-- The stage-`s` approximation of the capped scaling: the first `s` layers. -/
noncomputable def capApprox (a : ℕ → ℕ → ℚ) (A : ℕ → BitString → BitString → ℕ)
    (s k : ℕ) : ℚ :=
  Nat.rec (motive := fun _ => ℚ) 0
    (fun n acc => acc + capTerm a A s n k.unpair.1 k.unpair.2) s

/-- The capped scaling at `k`: the supremum over stages `s` of the stage-`s` approximation
`capApprox a A s k`. -/
noncomputable def cappedScaling (a : ℕ → ℕ → ℚ) (A : ℕ → BitString → BitString → ℕ)
    (k : ℕ) : ℝ≥0∞ :=
  ⨆ s, ENNReal.ofReal ((capApprox a A s k : ℚ) : ℝ)

/-- The recursion defining the capped approximation computes the sum of its layers. -/
theorem capRec_eq_sum (a : ℕ → ℕ → ℚ) (A : ℕ → BitString → BitString → ℕ) (s i j : ℕ) :
    ∀ t : ℕ, Nat.rec (motive := fun _ => ℚ) 0
        (fun n acc => acc + capTerm a A s n i j) t
      = ∑ n ∈ Finset.range t, capTerm a A s n i j := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih]

/-- The stage-`s` capped approximation is the sum of its first `s` layers. -/
theorem capApprox_eq_sum (a : ℕ → ℕ → ℚ) (A : ℕ → BitString → BitString → ℕ) (s k : ℕ) :
    capApprox a A s k = ∑ n ∈ Finset.range s, capTerm a A s n k.unpair.1 k.unpair.2 :=
  capRec_eq_sum a A s k.unpair.1 k.unpair.2 s

/-- The layers of the capped scaling are nonnegative. -/
theorem capTerm_nonneg {a : ℕ → ℕ → ℚ} (h0 : ∀ i j, 0 ≤ a i j)
    (A : ℕ → BitString → BitString → ℕ) (s n i j : ℕ) : 0 ≤ capTerm a A s n i j := by
  rw [capTerm]
  split
  · exact mul_nonneg (by positivity) (h0 i j)
  · exact le_rfl

/-- The capped approximation is nonnegative. -/
theorem capApprox_nonneg {a : ℕ → ℕ → ℚ} (h0 : ∀ i j, 0 ≤ a i j)
    (A : ℕ → BitString → BitString → ℕ) (s k : ℕ) : 0 ≤ capApprox a A s k := by
  rw [capApprox_eq_sum]
  exact Finset.sum_nonneg fun n _ => capTerm_nonneg h0 A s n _ _

/-- **The layer bound.**  Inside one group the `n`-th layer never exceeds
`mₛ(i)/2^{n+1}`; this is the greedy cap doing its job, and the proof is the one-step
induction "either the cap has bitten, or the whole running total is still admissible". -/
theorem sum_capTerm_le {a : ℕ → ℕ → ℚ} (h0 : ∀ i j, 0 ≤ a i j)
    (A : ℕ → BitString → BitString → ℕ) (s n i : ℕ) (hM : 0 ≤ lscRatApprox A s i) :
    ∀ J : ℕ, ∑ j ∈ Finset.range J, capTerm a A s n i j
      ≤ lscRatApprox A s i / 2 ^ (n + 1) := by
  intro J
  induction J with
  | zero => simpa using div_nonneg hM (by positivity)
  | succ J ih =>
    rw [Finset.sum_range_succ]
    by_cases hc : (2 : ℚ) ^ (2 * n + 1) * groupPartial a i J < lscRatApprox A s i
    · have hterm : capTerm a A s n i J = (2 : ℚ) ^ n * a i J := by rw [capTerm, ite_eq_left hc]
      have hdrop : ∑ j ∈ Finset.range J, capTerm a A s n i j
          ≤ ∑ j ∈ Finset.range J, (2 : ℚ) ^ n * a i j := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [capTerm]
        split
        · exact le_rfl
        · exact mul_nonneg (by positivity) (h0 i j)
      have hgp : ∑ j ∈ Finset.range J, (2 : ℚ) ^ n * a i j + (2 : ℚ) ^ n * a i J
          = (2 : ℚ) ^ n * groupPartial a i J := by
        rw [groupPartial_eq, Finset.sum_range_succ, mul_add, ← Finset.mul_sum]
      have hkey : (2 : ℚ) ^ n * groupPartial a i J ≤ lscRatApprox A s i / 2 ^ (n + 1) := by
        rw [le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ (n + 1))]
        have hpow : (2 : ℚ) ^ n * (2 : ℚ) ^ (n + 1) = (2 : ℚ) ^ (2 * n + 1) := by
          rw [← pow_add]
          congr 1
          omega
        calc (2 : ℚ) ^ n * groupPartial a i J * 2 ^ (n + 1)
            = ((2 : ℚ) ^ n * 2 ^ (n + 1)) * groupPartial a i J := by ring
          _ = (2 : ℚ) ^ (2 * n + 1) * groupPartial a i J := by rw [hpow]
          _ ≤ lscRatApprox A s i := le_of_lt hc
      rw [hterm]
      linarith [hdrop, hgp, hkey]
    · have hterm : capTerm a A s n i J = 0 := by rw [capTerm, ite_eq_right hc]
      rw [hterm, add_zero]
      exact ih

/-! ### Monotonicity in the stage -/

/-- Each layer of the capped scaling is non-decreasing in the stage. -/
theorem capTerm_mono {a : ℕ → ℕ → ℚ} (h0 : ∀ i j, 0 ≤ a i j)
    {A : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s i, lscRatApprox A s i ≤ lscRatApprox A (s + 1) i) (s n i j : ℕ) :
    capTerm a A s n i j ≤ capTerm a A (s + 1) n i j := by
  by_cases hc : (2 : ℚ) ^ (2 * n + 1) * groupPartial a i j < lscRatApprox A s i
  · rw [capTerm, ite_eq_left hc, capTerm, ite_eq_left (lt_of_lt_of_le hc (hmono s i))]
  · rw [capTerm, ite_eq_right hc]
    exact capTerm_nonneg h0 A (s + 1) n i j

/-- The capped approximation is non-decreasing in the stage. -/
theorem capApprox_mono {a : ℕ → ℕ → ℚ} (h0 : ∀ i j, 0 ≤ a i j)
    {A : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s i, lscRatApprox A s i ≤ lscRatApprox A (s + 1) i) (s k : ℕ) :
    capApprox a A s k ≤ capApprox a A (s + 1) k := by
  rw [capApprox_eq_sum, capApprox_eq_sum, Finset.sum_range_succ]
  have h1 : ∑ n ∈ Finset.range s, capTerm a A s n k.unpair.1 k.unpair.2
      ≤ ∑ n ∈ Finset.range s, capTerm a A (s + 1) n k.unpair.1 k.unpair.2 :=
    Finset.sum_le_sum fun n _ => capTerm_mono h0 hmono s n _ _
  have h2 := capTerm_nonneg h0 A (s + 1) s k.unpair.1 k.unpair.2
  linarith

/-! ### Computability -/

/-- Group sums of a computable family are computable in both arguments. -/
theorem computable₂_groupSum {a : ℕ → ℕ → ℚ} (ha : Computable₂ a) :
    Computable₂ (groupSum a) := by
  have hstep : Computable₂ (fun (p : ℕ × ℕ) (z : ℕ × ℚ) => z.2 + a p.1 z.1) := by
    have h1 : Computable (fun q : (ℕ × ℕ) × (ℕ × ℚ) => q.2.2) :=
      Computable.snd.comp Computable.snd
    have h2 : Computable (fun q : (ℕ × ℕ) × (ℕ × ℚ) => a q.1.1 q.2.1) :=
      ha.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)
    exact computable₂_ratAdd.comp h1 h2
  exact Computable.nat_rec Computable.snd (Computable.const 0) hstep

/-- Running totals inside a group are computable in both arguments. -/
theorem computable₂_groupPartial {a : ℕ → ℕ → ℚ} (ha : Computable₂ a) :
    Computable₂ (groupPartial a) :=
  (computable₂_groupSum ha).comp Computable.fst
    (Primrec.nat_add.to_comp.comp Computable.snd (Computable.const 1))

/-- Computability of the capped term along arbitrary computable index maps.  Stating it in
this form avoids composing through nested product types, whose `Primcodable` unification is
what makes the direct route time out. -/
theorem computable_capTerm_comp {a : ℕ → ℕ → ℚ} (ha : Computable₂ a)
    {A : ℕ → BitString → BitString → ℕ} (hA : Computable₂ (lscRatApprox A))
    {α : Type} [Primcodable α] {fs fn fi fj : α → ℕ} (hfs : Computable fs)
    (hfn : Computable fn) (hfi : Computable fi) (hfj : Computable fj) :
    Computable (fun x : α => capTerm a A (fs x) (fn x) (fi x) (fj x)) := by
  have hbig : Computable (fun x : α => (2 : ℚ) ^ (2 * fn x + 1)) :=
    computable_two_pow_rat.comp (Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 2) hfn) (Computable.const 1))
  have hgp : Computable (fun x : α => groupPartial a (fi x) (fj x)) :=
    (computable₂_groupPartial ha).comp hfi hfj
  have hcond : Computable (fun x : α =>
      decide ((2 : ℚ) ^ (2 * fn x + 1) * groupPartial a (fi x) (fj x)
        < lscRatApprox A (fs x) (fi x))) :=
    computable₂_ratLt.comp (computable₂_ratMul.comp hbig hgp) (hA.comp hfs hfi)
  have hval : Computable (fun x : α => (2 : ℚ) ^ fn x * a (fi x) (fj x)) :=
    computable₂_ratMul.comp (computable_two_pow_rat.comp hfn) (ha.comp hfi hfj)
  refine (Computable.cond hcond hval (Computable.const 0)).of_eq fun x => ?_
  rw [capTerm]
  by_cases hc : (2 : ℚ) ^ (2 * fn x + 1) * groupPartial a (fi x) (fj x)
      < lscRatApprox A (fs x) (fi x) <;> simp [hc]

/-- The stage approximation on a single packed index, so that the `Computable.nat_rec`
parameter stays inside `ℕ`. -/
noncomputable def capApproxFlat (a : ℕ → ℕ → ℚ) (A : ℕ → BitString → BitString → ℕ)
    (p : ℕ) : ℚ :=
  Nat.rec (motive := fun _ => ℚ) 0
    (fun n acc => acc + capTerm a A p.unpair.1 n p.unpair.2.unpair.1 p.unpair.2.unpair.2)
    p.unpair.1

/-- The capped approximation agrees with its packed-index form. -/
theorem capApprox_eq_flat (a : ℕ → ℕ → ℚ) (A : ℕ → BitString → BitString → ℕ) (s k : ℕ) :
    capApprox a A s k = capApproxFlat a A (Nat.pair s k) := by
  rw [capApproxFlat, capApprox]
  simp only [Nat.unpair_pair]

/-- The packed form of the capped approximation is computable. -/
theorem computable_capApproxFlat {a : ℕ → ℕ → ℚ} (ha : Computable₂ a)
    {A : ℕ → BitString → BitString → ℕ} (hA : Computable₂ (lscRatApprox A)) :
    Computable (capApproxFlat a A) := by
  have hu1 : Computable (fun q : ℕ × ℕ × ℚ => q.1.unpair.1) :=
    ((Primrec.fst.comp Primrec.unpair).to_comp).comp Computable.fst
  have hu2 : Computable (fun q : ℕ × ℕ × ℚ => q.1.unpair.2.unpair.1) :=
    ((Primrec.fst.comp Primrec.unpair).to_comp).comp
      (((Primrec.snd.comp Primrec.unpair).to_comp).comp Computable.fst)
  have hu3 : Computable (fun q : ℕ × ℕ × ℚ => q.1.unpair.2.unpair.2) :=
    ((Primrec.snd.comp Primrec.unpair).to_comp).comp
      (((Primrec.snd.comp Primrec.unpair).to_comp).comp Computable.fst)
  have hnn : Computable (fun q : ℕ × ℕ × ℚ => q.2.1) := Computable.fst.comp Computable.snd
  have hstep : Computable₂ (fun (p : ℕ) (z : ℕ × ℚ) =>
      z.2 + capTerm a A p.unpair.1 z.1 p.unpair.2.unpair.1 p.unpair.2.unpair.2) := by
    have h1 : Computable (fun q : ℕ × ℕ × ℚ => q.2.2) := Computable.snd.comp Computable.snd
    have h2 : Computable (fun q : ℕ × ℕ × ℚ =>
        capTerm a A q.1.unpair.1 q.2.1 q.1.unpair.2.unpair.1 q.1.unpair.2.unpair.2) :=
      computable_capTerm_comp ha hA hu1 hnn hu2 hu3
    exact computable₂_ratAdd.comp h1 h2
  exact Computable.nat_rec ((Primrec.fst.comp Primrec.unpair).to_comp) (Computable.const 0) hstep

/-- The capped approximation is computable in the stage and the index. -/
theorem computable₂_capApprox {a : ℕ → ℕ → ℚ} (ha : Computable₂ a)
    {A : ℕ → BitString → BitString → ℕ} (hA : Computable₂ (lscRatApprox A)) :
    Computable₂ (capApprox a A) := by
  have hpair : Computable (fun p : ℕ × ℕ => Nat.pair p.1 p.2) := Primrec₂.natPair.to_comp
  refine ((computable_capApproxFlat ha hA).comp hpair).of_eq fun p => ?_
  exact (capApprox_eq_flat a A p.1 p.2).symm

/-! ### The construction -/

/-- Stage approximations `lscRatApprox` are monotone in stage whenever `dyadicValue` stage
approximations are monotone. -/
private theorem lscRatApprox_mono_of_monotone {A : ℕ → BitString → BitString → ℕ}
    (hAmono : ∀ s x y, dyadicValue (A s x y) s ≤ dyadicValue (A (s + 1) x y) (s + 1)) (s i : ℕ) :
    lscRatApprox A s i ≤ lscRatApprox A (s + 1) i := by
  have h1 := hAmono s (natToBitString i) []
  rw [← ofReal_lscRatApprox, ← ofReal_lscRatApprox] at h1
  have hnn : (0 : ℝ) ≤ ((lscRatApprox A (s + 1) i : ℚ) : ℝ) := by
    exact_mod_cast lscRatApprox_nonneg A (s + 1) i
  have h2 := (ENNReal.ofReal_le_ofReal_iff hnn).1 h1
  exact_mod_cast h2

/-- In `ℝ≥0∞`, the sum of `capTerm` over any finite range inside a group is bounded by
`lscRatApprox A s i / 2^{n+1}`. -/
private theorem sum_capTerm_ennreal_le {a : ℕ → ℕ → ℚ} (h0 : ∀ i j, 0 ≤ a i j)
    (A : ℕ → BitString → BitString → ℕ) (s n i N : ℕ) :
    (∑ j ∈ Finset.range N, ENNReal.ofReal ((capTerm a A s n i j : ℚ) : ℝ))
      ≤ ENNReal.ofReal ((lscRatApprox A s i : ℚ) : ℝ) * (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
  have hMnn : (0 : ℚ) ≤ lscRatApprox A s i := lscRatApprox_nonneg A s i
  have hsum := sum_capTerm_le h0 A s n i hMnn N
  have hfin : (∑ j ∈ Finset.range N, ENNReal.ofReal ((capTerm a A s n i j : ℚ) : ℝ))
      = ENNReal.ofReal ((∑ j ∈ Finset.range N, capTerm a A s n i j : ℚ) : ℝ) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by
      exact_mod_cast capTerm_nonneg h0 A s n i j)]
    congr 1
    push_cast
    ring
  rw [hfin]
  have hsum' : ((∑ j ∈ Finset.range N, capTerm a A s n i j : ℚ) : ℝ)
      ≤ ((lscRatApprox A s i / 2 ^ (n + 1) : ℚ) : ℝ) := by exact_mod_cast hsum
  refine le_trans (ENNReal.ofReal_le_ofReal hsum') ?_
  have hcast : (((lscRatApprox A s i / 2 ^ (n + 1) : ℚ)) : ℝ)
      = ((lscRatApprox A s i : ℚ) : ℝ) * ((2 : ℝ)⁻¹) ^ (n + 1) := by
    push_cast
    rw [div_eq_mul_inv, ← inv_pow]
  have hpow : ENNReal.ofReal (((2 : ℝ)⁻¹) ^ (n + 1)) = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
    rw [show ((2 : ℝ)⁻¹) ^ (n + 1) = ((((2 : ℚ)⁻¹) ^ (n + 1) : ℚ) : ℝ) by push_cast; ring]
    exact ofReal_rat_inv_two_pow (n + 1)
  rw [hcast, ENNReal.ofReal_mul (by exact_mod_cast hMnn), hpow]

/-- `A` approximates the semimeasure `m` from below: its rational approximations increase with
the stage, and the dyadic values of stage `s` at the index `i` have supremum `m i`. -/
private def LscApproximates (A : ℕ → BitString → BitString → ℕ) (m : ℕ → ℝ≥0∞) : Prop :=
  (∀ s i : ℕ, lscRatApprox A s i ≤ lscRatApprox A (s + 1) i) ∧
    ∀ i : ℕ, (⨆ s, dyadicValue (A s (natToBitString i) []) s) = m i

/-- Every stage-`s` dyadic value of an approximating enumeration is below the limit. -/
private theorem LscApproximates.le {A : ℕ → BitString → BitString → ℕ} {m : ℕ → ℝ≥0∞}
    (hA : LscApproximates A m) (s i : ℕ) :
    dyadicValue (A s (natToBitString i) []) s ≤ m i := by
  rw [← hA.2 i]
  exact le_iSup (fun t => dyadicValue (A t (natToBitString i) []) t) s

/-- The total mass of `capApprox a A s k` over any finite set `F` is at most `1`, provided the
enumeration `A` is bounded by `m` and `m` has total mass at most `1`. -/
private theorem capApprox_sum_finset_le {a : ℕ → ℕ → ℚ} (h0 : ∀ i j, 0 ≤ a i j)
    (A : ℕ → BitString → BitString → ℕ) {m : ℕ → ℝ≥0∞}
    (hAle : ∀ s i, dyadicValue (A s (natToBitString i) []) s ≤ m i)
    (h_tsum : (∑' i, m i) ≤ 1) (s : ℕ) (F : Finset ℕ) :
    (∑ k ∈ F, ENNReal.ofReal ((capApprox a A s k : ℚ) : ℝ)) ≤ 1 := by
  have hexp : ∀ k : ℕ, ENNReal.ofReal ((capApprox a A s k : ℚ) : ℝ)
      = ∑ n ∈ Finset.range s,
          ENNReal.ofReal ((capTerm a A s n k.unpair.1 k.unpair.2 : ℚ) : ℝ) := by
    intro k
    rw [capApprox_eq_sum, ← ENNReal.ofReal_sum_of_nonneg (fun n _ => by
      exact_mod_cast capTerm_nonneg h0 A s n k.unpair.1 k.unpair.2)]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun k _ => hexp k), Finset.sum_comm]
  have hone : ∀ n : ℕ,
      (∑ k ∈ F, ENNReal.ofReal ((capTerm a A s n k.unpair.1 k.unpair.2 : ℚ) : ℝ))
        ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
    intro n
    set N : ℕ := (F.sup id) + 1 with hN
    have hinj : Set.InjOn Nat.unpair (↑F : Set ℕ) := by
      intro x _ y _ hxy
      have hp := congrArg (fun p : ℕ × ℕ => Nat.pair p.1 p.2) hxy
      simpa [Nat.pair_unpair] using hp
    have himg : F.image Nat.unpair ⊆ Finset.range N ×ˢ Finset.range N := by
      intro p hp
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
      have hklt : k < N := Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
      exact Finset.mem_product.2 ⟨Finset.mem_range.2
        (lt_of_le_of_lt (Nat.unpair_left_le k) hklt),
        Finset.mem_range.2 (lt_of_le_of_lt (Nat.unpair_right_le k) hklt)⟩
    calc (∑ k ∈ F, ENNReal.ofReal ((capTerm a A s n k.unpair.1 k.unpair.2 : ℚ) : ℝ))
        = ∑ p ∈ F.image Nat.unpair,
            ENNReal.ofReal ((capTerm a A s n p.1 p.2 : ℚ) : ℝ) := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ p ∈ Finset.range N ×ˢ Finset.range N,
            ENNReal.ofReal ((capTerm a A s n p.1 p.2 : ℚ) : ℝ) :=
          Finset.sum_le_sum_of_subset himg
      _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            ENNReal.ofReal ((capTerm a A s n i j : ℚ) : ℝ) :=
          Finset.sum_product (Finset.range N) (Finset.range N)
            (fun p => ENNReal.ofReal ((capTerm a A s n p.1 p.2 : ℚ) : ℝ))
      _ ≤ ∑ i ∈ Finset.range N,
            ENNReal.ofReal ((lscRatApprox A s i : ℚ) : ℝ) * (2 : ℝ≥0∞)⁻¹ ^ (n + 1) :=
          Finset.sum_le_sum (fun i _ => sum_capTerm_ennreal_le h0 A s n i N)
      _ = (∑ i ∈ Finset.range N, ENNReal.ofReal ((lscRatApprox A s i : ℚ) : ℝ))
            * (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by rw [Finset.sum_mul]
      _ ≤ 1 * (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
          gcongr
          calc (∑ i ∈ Finset.range N, ENNReal.ofReal ((lscRatApprox A s i : ℚ) : ℝ))
              = ∑ i ∈ Finset.range N, dyadicValue (A s (natToBitString i) []) s :=
                Finset.sum_congr rfl (fun i _ => ofReal_lscRatApprox A s i)
            _ ≤ ∑ i ∈ Finset.range N, m i := Finset.sum_le_sum (fun i _ => hAle s i)
            _ ≤ ∑' i, m i := ENNReal.sum_le_tsum _
            _ ≤ 1 := h_tsum
      _ = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := one_mul _
  calc (∑ n ∈ Finset.range s,
          ∑ k ∈ F, ENNReal.ofReal ((capTerm a A s n k.unpair.1 k.unpair.2 : ℚ) : ℝ))
      ≤ ∑ n ∈ Finset.range s, (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := Finset.sum_le_sum (fun n _ => hone n)
    _ ≤ ∑' n, (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := ENNReal.sum_le_tsum _
    _ = 1 := by
        rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
        exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- On any group `i` where `2^{2n+1} * ∑' j', a i j'` is strictly below `m i`, `cappedScaling`
dominates `2ⁿ * a i j`. -/
private theorem cappedScaling_dominate {m : ℕ → ℝ≥0∞} {a : ℕ → ℕ → ℚ} (h0 : ∀ i j, 0 ≤ a i j)
    (A : ℕ → BitString → BitString → ℕ) (hA : LscApproximates A m) (n i j : ℕ)
    (hlt : (2 : ℝ≥0∞) ^ (2 * n + 1) * (∑' j', ENNReal.ofReal ((a i j' : ℚ) : ℝ)) < m i) :
    (2 : ℝ≥0∞) ^ n * ENNReal.ofReal ((a i j : ℚ) : ℝ) ≤ cappedScaling a A (Nat.pair i j) := by
  obtain ⟨hratmono, hAsup'⟩ := hA
  have hgpnn : (0 : ℚ) ≤ groupPartial a i j := by
    rw [groupPartial_eq]
    exact Finset.sum_nonneg fun j' _ => h0 i j'
  have hgple : ENNReal.ofReal ((groupPartial a i j : ℚ) : ℝ)
      ≤ ∑' j', ENNReal.ofReal ((a i j' : ℚ) : ℝ) := by
    have heq : ENNReal.ofReal ((groupPartial a i j : ℚ) : ℝ)
        = ∑ j' ∈ Finset.range (j + 1), ENNReal.ofReal ((a i j' : ℚ) : ℝ) := by
      rw [groupPartial_eq, ← ENNReal.ofReal_sum_of_nonneg (f := fun j' => ((a i j' : ℚ) : ℝ))
        (fun j' _ => by exact_mod_cast h0 i j')]
      congr 1
      push_cast
      ring
    rw [heq]
    exact ENNReal.sum_le_tsum _
  have hlt' : ENNReal.ofReal (((2 : ℚ) ^ (2 * n + 1) * groupPartial a i j : ℚ) : ℝ) < m i := by
    have hcast : ((((2 : ℚ) ^ (2 * n + 1) * groupPartial a i j : ℚ)) : ℝ)
        = ((2 : ℝ)) ^ (2 * n + 1) * ((groupPartial a i j : ℚ) : ℝ) := by push_cast; ring
    rw [hcast, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
    exact lt_of_le_of_lt (by gcongr) hlt
  rw [← hAsup' i] at hlt'
  obtain ⟨s₀, hs₀⟩ := lt_iSup_iff.1 hlt'
  rw [← ofReal_lscRatApprox] at hs₀
  have hs₀nn : (0 : ℝ) ≤ (((2 : ℚ) ^ (2 * n + 1) * groupPartial a i j : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ (2 : ℚ) ^ (2 * n + 1) * groupPartial a i j :=
      mul_nonneg (by positivity) hgpnn
    exact_mod_cast this
  have hs₀' : (2 : ℚ) ^ (2 * n + 1) * groupPartial a i j < lscRatApprox A s₀ i := by
    exact_mod_cast (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs₀nn).1 hs₀
  set s : ℕ := max s₀ (n + 1)
  have hmonoS : ∀ t u : ℕ, t ≤ u → lscRatApprox A t i ≤ lscRatApprox A u i := by
    intro t u htu
    exact monotone_nat_of_le_succ (fun v => hratmono v i) htu
  have hcond : (2 : ℚ) ^ (2 * n + 1) * groupPartial a i j < lscRatApprox A s i :=
    lt_of_lt_of_le hs₀' (hmonoS s₀ s (le_max_left _ _))
  have hns : n < s := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)
  have hterm : capTerm a A s n i j = (2 : ℚ) ^ n * a i j := by rw [capTerm, ite_eq_left hcond]
  have hle : (2 : ℚ) ^ n * a i j ≤ capApprox a A s (Nat.pair i j) := by
    rw [capApprox_eq_sum]
    simp only [Nat.unpair_pair]
    rw [← hterm]
    refine Finset.single_le_sum (f := fun n' => capTerm a A s n' i j)
      (fun n' _ => capTerm_nonneg h0 A s n' i j) (Finset.mem_range.2 hns)
  calc (2 : ℝ≥0∞) ^ n * ENNReal.ofReal ((a i j : ℚ) : ℝ)
      = ENNReal.ofReal ((((2 : ℚ) ^ n * a i j : ℚ)) : ℝ) := by
        rw [show ((((2 : ℚ) ^ n * a i j : ℚ)) : ℝ) = ((2 : ℝ)) ^ n * ((a i j : ℚ) : ℝ) by
          push_cast; ring, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal ((capApprox a A s (Nat.pair i j) : ℚ) : ℝ) :=
        ENNReal.ofReal_le_ofReal (by exact_mod_cast hle)
    _ ≤ cappedScaling a A (Nat.pair i j) :=
        le_iSup (fun t => ENNReal.ofReal ((capApprox a A t (Nat.pair i j) : ℚ) : ℝ)) s

/-- **SUV pp. 167–168, the mixed capped scaling.**  For a computable double series of
nonnegative rationals there is a lower semicomputable semimeasure on pairs which, on every
group `i` whose total is small compared with `m(i)`, dominates `2ⁿ·aᵢⱼ`. -/
theorem exists_cappedScaling {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    {a : ℕ → ℕ → ℚ} (ha : Computable₂ a) (h0 : ∀ i j, 0 ≤ a i j) :
    ∃ μ : ℕ → ℝ≥0∞, IsLowerSemicomputableSemimeasureNat μ ∧
      ∀ (n i j : ℕ),
        (2 : ℝ≥0∞) ^ (2 * n + 1) * (∑' j', ENNReal.ofReal ((a i j' : ℚ) : ℝ)) < m i →
        (2 : ℝ≥0∞) ^ n * ENNReal.ofReal ((a i j : ℚ) : ℝ) ≤ μ (Nat.pair i j) := by
  classical
  obtain ⟨A, hAmono, hAsup, hAcomp⟩ := hm.1.2
  have hAsup' : ∀ i : ℕ, (⨆ s, dyadicValue (A s (natToBitString i) []) s) = m i := by
    intro i
    have h := hAsup (natToBitString i) []
    simpa [bitStringToNat_natToBitString] using h
  have hratmono : ∀ s i : ℕ, lscRatApprox A s i ≤ lscRatApprox A (s + 1) i :=
    lscRatApprox_mono_of_monotone hAmono
  have hA : LscApproximates A m := ⟨hratmono, hAsup'⟩
  have hAcomp' : Computable₂ (lscRatApprox A) := computable_lscRatApprox hAcomp
  have hcapmono : ∀ s k : ℕ, capApprox a A s k ≤ capApprox a A (s + 1) k :=
    fun s k => capApprox_mono h0 hratmono s k
  have hstage : ∀ (s : ℕ) (F : Finset ℕ),
      (∑ k ∈ F, ENNReal.ofReal ((capApprox a A s k : ℚ) : ℝ)) ≤ 1 :=
    capApprox_sum_finset_le h0 A hA.le hm.tsum_le_one
  have hmass : (∑' k, cappedScaling a A k) ≤ 1 := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    have hmono' : ∀ k : ℕ, Monotone (fun s => ENNReal.ofReal ((capApprox a A s k : ℚ) : ℝ)) := by
      intro k
      refine monotone_nat_of_le_succ fun s => ?_
      exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hcapmono s k)
    have hswap : (∑ k ∈ F, cappedScaling a A k)
        = ⨆ s, ∑ k ∈ F, ENNReal.ofReal ((capApprox a A s k : ℚ) : ℝ) :=
      ENNReal.finsetSum_iSup_of_monotone hmono'
    rw [hswap]
    exact iSup_le fun s => hstage s F
  refine ⟨cappedScaling a A, ⟨?_, ?_⟩, ?_⟩
  · change (∑' x : BitString, cappedScaling a A (bitStringToNat x)) ≤ 1
    rw [tsum_comp_bitStringToNat (fun k => cappedScaling a A k)]
    exact hmass
  · exact isLSC_iSup_of_monotone (computable₂_capApprox ha hAcomp') hcapmono
  · intro n i j hlt
    exact cappedScaling_dominate h0 A hA n i j hlt

end Kolmogorov
