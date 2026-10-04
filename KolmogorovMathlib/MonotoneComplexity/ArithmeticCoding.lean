import KolmogorovMathlib.AlgorithmicProbability.Coding
import KolmogorovMathlib.AlgorithmicRandomness.ComputableMeasure
import KolmogorovMathlib.AlgorithmicRandomness.Cylinders
import KolmogorovMathlib.AlgorithmicRandomness.Measure
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.MonotoneComplexity.BinaryInterval
import KolmogorovMathlib.MonotoneComplexity.ContinuousStreamMap
import KolmogorovMathlib.MonotoneComplexity.MeasureRepresentation
import KolmogorovMathlib.MonotoneComplexity.MonotoneOptimality
import KolmogorovMathlib.MonotoneComplexity.Omega.LscBasic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Arithmetic coding as a monotone decompressor

Arithmetic coding for a computable probability measure `μ` on Cantor space, presented as a
stream relation: `arithmeticCodingLowerGraph` pairs a program `p` with a string `x` when the
dyadic cell of `p` lies inside the interval that `μ` assigns to `x`. The relation is shown to be
a stream lower graph and recursively enumerable
(`arithmeticCodingLowerGraph_isStreamLowerGraph`, `arithmeticCodingLowerGraph_isRE`), with the
computable approximations `treeLeftEndApprox` to the interval endpoints supplying the
enumeration. The coding bound `exists_program_length_le_of_cantorMass` gives a code of length at
most `-log₂ μ[x]` up to a constant, and combining it with optimality yields
`exists_const_cantorMass_mul_le_complexityWeight_KMOf`: monotone complexity is at most
`-log₂ μ[x] + O(1)` for every computable measure.
-/

open Kolmogorov Set MeasureTheory

open scoped ENNReal

namespace Kolmogorov

/-- Inclusion of nondegenerate half-open intervals gives inclusion of their closures. -/
lemma Ico_subset_Ico_imp_Icc_subset_Icc {a b c d : ℝ} (hab : a < b) (h : Ico a b ⊆ Ico c d) :
    Icc a b ⊆ Icc c d := by
  have h1 := h (left_mem_Ico.mpr hab)
  rw [mem_Ico] at h1
  intro x hx
  rw [mem_Icc] at hx ⊢
  constructor
  · exact le_trans h1.1 hx.1
  · by_contra hcd
    push Not at hcd
    have h2 : max a d ∈ Ico a b := by
      rw [mem_Ico]
      constructor
      · exact le_max_left a d
      · exact max_lt hab (lt_of_lt_of_le hcd hx.2)
    have h3 := h h2
    rw [mem_Ico] at h3
    linarith [le_max_right a d, h3.2]

/-- The binary cell of an extension is contained in the cell of the prefix. -/
lemma binaryClosedInterval_subset_of_prefix {p p' : BitString} (h : p <+: p') :
    binaryClosedInterval p' ⊆ binaryClosedInterval p := by
  rw [binaryClosedInterval, binaryClosedInterval]
  apply Ico_subset_Ico_imp_Icc_subset_Icc
  · rw [lt_add_iff_pos_right, lengthMeasure_toReal]
    exact pow_pos (by norm_num) _
  · exact treeIco_prefix_subset lengthMeasure_isContinuousTreeSemimeasure h

/-- The lower graph of arithmetic coding for `μ`: the program `p` codes a real whose cell lies
inside the interval of `x`. -/
def arithmeticCodingLowerGraph (μ : Measure CantorSeq) (p x : BitString) : Prop :=
  x = [] ∨ binaryClosedInterval p ⊆ interior (treeIco (cantorMass μ) x)

/-- The cylinder of the empty string is the whole Cantor space. -/
lemma cantorCylinder_nil : cantorCylinder [] = univ := by
  ext w
  simp [cantorCylinder, IsCantorPrefix]

/-- The cylinder masses of a probability measure form a continuous tree semimeasure. -/
lemma isContinuousTreeSemimeasure_cantorMass (μ : Measure CantorSeq) [IsProbabilityMeasure μ] :
    IsContinuousTreeSemimeasure (cantorMass μ) := by
  constructor
  · rw [cantorMass, cantorCylinder_nil]
    exact measure_univ (μ := μ)
  · intro x
    rw [← cantorMass_add μ x]

/-- The arithmetic coding relation satisfies the lower-graph axioms. -/
lemma arithmeticCodingLowerGraph_isStreamLowerGraph (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] :
    IsStreamLowerGraph (arithmeticCodingLowerGraph μ) := by
  have ha := isContinuousTreeSemimeasure_cantorMass μ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    exact Or.inl rfl
  · intro p x x' h hx
    rcases h with rfl | h
    · exact Or.inl (List.eq_nil_of_prefix_nil hx)
    · by_cases hx'_nil : x' = []
      · exact Or.inl hx'_nil
      · right
        refine Subset.trans h (interior_mono (treeIco_prefix_subset ha hx))
  · intro p p' x h hp
    rcases h with rfl | h
    · exact Or.inl rfl
    · right
      refine Subset.trans (binaryClosedInterval_subset_of_prefix hp) h
  · intro p x x' hx hx'
    rcases hx with rfl | hx
    · exact Or.inl List.nil_prefix
    · rcases hx' with rfl | hx'
      · exact Or.inr List.nil_prefix
      · by_contra h_inc
        push Not at h_inc
        have hp_nonempty : (binaryClosedInterval p).Nonempty := by
          rw [binaryClosedInterval]
          apply nonempty_Icc.mpr
          rw [le_add_iff_nonneg_right, lengthMeasure_toReal]
          exact le_of_lt (pow_pos (by norm_num) _)
        obtain ⟨r, hr⟩ := hp_nonempty
        have hrx := interior_subset (hx hr)
        have hrx' := interior_subset (hx' hr)
        have h_or := prefix_or_prefix_of_mem_treeIco ha hrx hrx'
        rcases h_or with h1 | h1
        · exact h_inc.1 h1
        · exact h_inc.2 h1

/-- The stage-`s` numerator of the left endpoint of the interval of `x`. -/
def treeLeftEndApprox (a : BitString → ℕ → ℕ) (x : BitString) (s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range x.length,
    if x.getD i false then a (x.take i ++ [false]) s else 0

/-- The approximation of the left endpoint is computable. -/
lemma computable_treeLeftEndApprox {a : BitString → ℕ → ℕ} (ha : Computable₂ a) :
    Computable₂ (treeLeftEndApprox a) := by
  have hlen : Computable (fun p : BitString × ℕ => p.1.length) :=
    Computable.list_length.comp Computable.fst
  have hcond : Computable (fun r : (BitString × ℕ) × (ℕ × ℕ) => r.1.1.getD r.2.1 false) :=
    ((Primrec.list_getD false).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)).to_comp
  have hstr : Computable
      (fun r : (BitString × ℕ) × (ℕ × ℕ) => r.1.1.take r.2.1 ++ [false]) :=
    (Primrec.list_append.comp
      (Primrec.list_take.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
      (Primrec.const [false])).to_comp
  have hterm : Computable (fun r : (BitString × ℕ) × (ℕ × ℕ) =>
      if r.1.1.getD r.2.1 false then a (r.1.1.take r.2.1 ++ [false]) r.1.2 else 0) :=
    (Computable.cond hcond (ha.comp hstr (Computable.snd.comp Computable.fst))
      (Computable.const 0)).of_eq (fun r => by cases r.1.1.getD r.2.1 false <;> simp)
  have hh : Computable₂ (fun (p : BitString × ℕ) (q : ℕ × ℕ) =>
      q.2 + if p.1.getD q.1 false then a (p.1.take q.1 ++ [false]) p.2 else 0) :=
    (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd) hterm).to₂
  refine (Computable.nat_rec (σ := ℕ) hlen (Computable.const 0) hh).of_eq ?_
  rintro ⟨x, s⟩
  dsimp [treeLeftEndApprox]
  induction x.length with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ← ih]

/-- The stage-`s` test that the cell of `p` sits inside the interval of `x`. -/
def arithmeticCodingStage (a : BitString → ℕ → ℕ) (s : ℕ) (p x : BitString) : Bool :=
  if x.isEmpty then true else
  if s < p.length then false else
  let p_L := devBitsToNat p * 2 ^ (s - p.length)
  let p_R := (devBitsToNat p + 1) * 2 ^ (s - p.length)
  let l_approx := treeLeftEndApprox a x s
  let r_approx := l_approx + a x s
  (l_approx + x.length < p_L) ∧ (p_R + x.length + 1 < r_approx)

/-- Each stage-`s` approximant of a cylinder mass is within one unit of `2^s` times
the true mass. -/
lemma abs_approx_sub_le_one (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (y : BitString) (s : ℕ) :
    |(a y s : ℝ) - 2 ^ s * (cantorMass μ y).toReal| ≤ 1 := by
  have hmt : cantorMass μ y ≠ ⊤ := measure_ne_top μ _
  have hdt : dyadicValue 1 s ≠ ⊤ := dyadicValue_ne_top 1 s
  have hdt' : dyadicValue (a y s) s ≠ ⊤ := dyadicValue_ne_top _ s
  have h1 := ENNReal.toReal_mono (by finiteness) (ha y s).1
  have h2 := ENNReal.toReal_mono (by finiteness) (ha y s).2
  rw [ENNReal.toReal_add hmt hdt, toReal_dyadicValue, toReal_dyadicValue] at h1
  rw [ENNReal.toReal_add hdt' hdt, toReal_dyadicValue, toReal_dyadicValue] at h2
  have hpos : (0 : ℝ) < 2 ^ s := by positivity
  rw [Nat.cast_one] at h1 h2
  rw [div_le_iff₀ hpos, add_mul, one_div, inv_mul_cancel₀ (ne_of_gt hpos)] at h1
  rw [← add_div, le_div_iff₀ hpos] at h2
  have hc : (2 : ℝ) ^ s * (cantorMass μ y).toReal = (cantorMass μ y).toReal * 2 ^ s :=
    mul_comm _ _
  rw [abs_le]
  constructor <;> linarith

/-- The stage-`s` approximation of the left endpoint of the interval allocated to `x`
is within `|x|` units of `2^s` times the true left endpoint. -/
lemma abs_treeLeftEndApprox_sub_le (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (x : BitString) (s : ℕ) :
    |(treeLeftEndApprox a x s : ℝ) - 2 ^ s * treeLeftEnd (cantorMass μ) x| ≤ x.length := by
  have h1 : ((treeLeftEndApprox a x s : ℕ) : ℝ)
      = ∑ i ∈ Finset.range x.length,
        (if x.getD i false then ((a (x.take i ++ [false]) s : ℕ) : ℝ) else 0) := by
    rw [treeLeftEndApprox]
    push_cast
    exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)
  have h2 : (2 : ℝ) ^ s * treeLeftEnd (cantorMass μ) x
      = ∑ i ∈ Finset.range x.length,
        (if x.getD i false then
          2 ^ s * (cantorMass μ (x.take i ++ [false])).toReal else 0) := by
    rw [treeLeftEnd, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)
  rw [h1, h2, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ Finset.range x.length,
        ((if x.getD i false then ((a (x.take i ++ [false]) s : ℕ) : ℝ) else 0)
          - (if x.getD i false then
              2 ^ s * (cantorMass μ (x.take i ++ [false])).toReal else 0))|
      ≤ ∑ i ∈ Finset.range x.length,
        |((if x.getD i false then ((a (x.take i ++ [false]) s : ℕ) : ℝ) else 0)
          - (if x.getD i false then
              2 ^ s * (cantorMass μ (x.take i ++ [false])).toReal else 0))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range x.length, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        by_cases hb : x.getD i false = true
        · simp only [hb, ite_true]
          exact abs_approx_sub_le_one μ ha _ s
        · simp only [hb, ite_false, Bool.false_eq_true]
          simp
    _ = (x.length : ℝ) := by simp

/-- For a nonempty `x`, membership in the arithmetic coding lower graph is the strict
containment of the dyadic interval endpoints in the measure interval of `x`. -/
lemma arithmeticCodingLowerGraph_iff_endpoints (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (p x : BitString) (hx : x ≠ []) :
    arithmeticCodingLowerGraph μ p x ↔
      treeLeftEnd (cantorMass μ) x < (devBitsToNat p : ℝ) / 2 ^ p.length ∧
      ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length
        < treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal := by
  rw [arithmeticCodingLowerGraph, or_iff_right hx, binaryClosedInterval_eq_Icc,
    treeIco, interior_Ico]
  have hle : (devBitsToNat p : ℝ) / 2 ^ p.length
      ≤ ((devBitsToNat p : ℝ) + 1) / 2 ^ p.length := by
    gcongr
    linarith
  constructor
  · intro h
    exact ⟨(h (Set.left_mem_Icc.mpr hle)).1, (h (Set.right_mem_Icc.mpr hle)).2⟩
  · rintro ⟨h1, h2⟩ y hy
    rw [Set.mem_Icc] at hy
    exact ⟨lt_of_lt_of_le h1 hy.1, lt_of_le_of_lt hy.2 h2⟩

/-- Arithmetic core of the stage characterisation: strict containment of the dyadic
interval `[k/2^n, (k+1)/2^n]` in `(L, L + M)` is witnessed at some finite stage of any
approximation with the stated error bounds. -/
lemma dyadic_endpoints_iff_exists_stage_core (N k n : ℕ) (L M : ℝ) (LA A : ℕ → ℕ)
    (hA : ∀ s, |(LA s : ℝ) - 2 ^ s * L| ≤ (N : ℝ))
    (hB : ∀ s, |((LA s : ℝ) + (A s : ℝ)) - 2 ^ s * (L + M)| ≤ (N : ℝ) + 1) :
    (L < (k : ℝ) / 2 ^ n ∧ ((k : ℝ) + 1) / 2 ^ n < L + M) ↔
      ∃ s, n ≤ s ∧ LA s + N < k * 2 ^ (s - n) ∧
        (k + 1) * 2 ^ (s - n) + N + 1 < LA s + A s := by
  have hpowsplit : ∀ s : ℕ, n ≤ s → (2 : ℝ) ^ s = 2 ^ (s - n) * 2 ^ n := by
    intro s hs
    rw [← pow_add]
    congr 1
    omega
  have hPLmul : ∀ s : ℕ, n ≤ s →
      (2 : ℝ) ^ s * ((k : ℝ) / 2 ^ n) = (k : ℝ) * 2 ^ (s - n) := by
    intro s hs
    rw [hpowsplit s hs]
    field_simp
  have hPRmul : ∀ s : ℕ, n ≤ s →
      (2 : ℝ) ^ s * (((k : ℝ) + 1) / 2 ^ n) = ((k : ℝ) + 1) * 2 ^ (s - n) := by
    intro s hs
    rw [hpowsplit s hs]
    field_simp
  constructor
  · rintro ⟨hL1, hR1⟩
    obtain ⟨s1, hs1⟩ := pow_unbounded_of_one_lt
      (2 * (N : ℝ) / ((k : ℝ) / 2 ^ n - L)) (by norm_num : (1 : ℝ) < 2)
    obtain ⟨s2, hs2⟩ := pow_unbounded_of_one_lt
      ((2 * (N : ℝ) + 2) / (L + M - ((k : ℝ) + 1) / 2 ^ n)) (by norm_num : (1 : ℝ) < 2)
    refine ⟨max n (max s1 s2), le_max_left _ _, ?_⟩
    set s := max n (max s1 s2) with hsdef
    have hsn : n ≤ s := le_max_left _ _
    have hs1' : (2 : ℝ) ^ s1 ≤ 2 ^ s :=
      pow_le_pow_right₀ (by norm_num) (le_trans (le_max_left _ _) (le_max_right _ _))
    have hs2' : (2 : ℝ) ^ s2 ≤ 2 ^ s :=
      pow_le_pow_right₀ (by norm_num) (le_trans (le_max_right _ _) (le_max_right _ _))
    have hd1 : 0 < (k : ℝ) / 2 ^ n - L := by linarith
    have hd2 : 0 < L + M - ((k : ℝ) + 1) / 2 ^ n := by linarith
    have hb1 : 2 * (N : ℝ) < 2 ^ s * ((k : ℝ) / 2 ^ n - L) := by
      have h := lt_of_lt_of_le hs1 hs1'
      rw [div_lt_iff₀ hd1] at h
      nlinarith [h]
    have hb2 : 2 * (N : ℝ) + 2 < 2 ^ s * (L + M - ((k : ℝ) + 1) / 2 ^ n) := by
      have h := lt_of_lt_of_le hs2 hs2'
      rw [div_lt_iff₀ hd2] at h
      nlinarith [h]
    have hAa := hA s
    have hBb := hB s
    rw [abs_le] at hAa hBb
    constructor
    · have hreal : (LA s : ℝ) + (N : ℝ) < (k : ℝ) * 2 ^ (s - n) := by
        rw [← hPLmul s hsn]
        nlinarith [hAa.2, hb1]
      exact_mod_cast hreal
    · have hreal : ((k : ℝ) + 1) * 2 ^ (s - n) + (N : ℝ) + 1 < (LA s : ℝ) + (A s : ℝ) := by
        rw [← hPRmul s hsn]
        nlinarith [hBb.1, hb2]
      exact_mod_cast hreal
  · rintro ⟨s, hsn, C1, C2⟩
    have C1R : (LA s : ℝ) + (N : ℝ) < (k : ℝ) * 2 ^ (s - n) := by exact_mod_cast C1
    have C2R : ((k : ℝ) + 1) * 2 ^ (s - n) + (N : ℝ) + 1 < (LA s : ℝ) + (A s : ℝ) := by
      exact_mod_cast C2
    have hAa := hA s
    have hBb := hB s
    rw [abs_le] at hAa hBb
    have hpos : (0 : ℝ) < 2 ^ s := by positivity
    constructor
    · have h : (2 : ℝ) ^ s * L < 2 ^ s * ((k : ℝ) / 2 ^ n) := by
        rw [hPLmul s hsn]; linarith [hAa.1]
      exact lt_of_mul_lt_mul_left h (le_of_lt hpos)
    · have h : (2 : ℝ) ^ s * (((k : ℝ) + 1) / 2 ^ n) < 2 ^ s * (L + M) := by
        rw [hPRmul s hsn]; linarith [hBb.2]
      exact lt_of_mul_lt_mul_left h (le_of_lt hpos)

/-- With two-sided approximations of the masses, the arithmetic coding relation is the union of
its stage tests. -/
lemma arithmeticCodingLowerGraph_iff_exists_stage (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (a : BitString → ℕ → ℕ)
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (p x : BitString) :
    arithmeticCodingLowerGraph μ p x ↔ ∃ s : ℕ, arithmeticCodingStage a s p x := by
  by_cases hxnil : x = []
  · subst hxnil
    exact ⟨fun _ => ⟨0, by simp [arithmeticCodingStage]⟩, fun _ => Or.inl rfl⟩
  have hxe : ¬ x.isEmpty = true := by simpa using hxnil
  have hstage : ∀ s : ℕ, p.length ≤ s → (arithmeticCodingStage a s p x = true ↔
      (treeLeftEndApprox a x s + x.length < devBitsToNat p * 2 ^ (s - p.length) ∧
       (devBitsToNat p + 1) * 2 ^ (s - p.length) + x.length + 1
         < treeLeftEndApprox a x s + a x s)) := by
    intro s hs
    simp [arithmeticCodingStage, hxe, Nat.not_lt.mpr hs]
  have hB : ∀ s : ℕ, |((treeLeftEndApprox a x s : ℝ) + (a x s : ℝ))
      - 2 ^ s * (treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal)|
      ≤ (x.length : ℝ) + 1 := by
    intro s
    have h1 := abs_treeLeftEndApprox_sub_le μ ha x s
    have h2 := abs_approx_sub_le_one μ ha x s
    have hrw : ((treeLeftEndApprox a x s : ℝ) + (a x s : ℝ))
        - 2 ^ s * (treeLeftEnd (cantorMass μ) x + (cantorMass μ x).toReal)
        = ((treeLeftEndApprox a x s : ℝ) - 2 ^ s * treeLeftEnd (cantorMass μ) x)
          + ((a x s : ℝ) - 2 ^ s * (cantorMass μ x).toReal) := by ring
    rw [hrw]
    exact le_trans (abs_add_le _ _) (by linarith)
  rw [arithmeticCodingLowerGraph_iff_endpoints μ p x hxnil,
    dyadic_endpoints_iff_exists_stage_core x.length (devBitsToNat p) p.length
      (treeLeftEnd (cantorMass μ) x) ((cantorMass μ x).toReal)
      (fun s => treeLeftEndApprox a x s) (fun s => a x s)
      (fun s => abs_treeLeftEndApprox_sub_le μ ha x s) hB]
  constructor
  · rintro ⟨s, hsn, C1, C2⟩
    exact ⟨s, (hstage s hsn).mpr ⟨C1, C2⟩⟩
  · rintro ⟨s, hstg⟩
    have hsn : p.length ≤ s := by
      by_contra hc
      push Not at hc
      simp [arithmeticCodingStage, hxe, Nat.not_le.mpr hc] at hstg
    obtain ⟨C1, C2⟩ := (hstage s hsn).mp hstg
    exact ⟨s, hsn, C1, C2⟩

/-- Folding the binary reading over a string shifts the accumulator by the length of the string. -/
lemma devBitsToNat_foldl (l : BitString) (acc : ℕ) :
    l.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) acc
      = acc * 2 ^ l.length + devBitsToNat l := by
  induction l generalizing acc with
  | nil => simp [devBitsToNat]
  | cons b t ih =>
    simp only [List.foldl_cons, List.length_cons, devBitsToNat, ih, pow_succ]
    ring

/-- Reading a string as a binary numeral is primitive recursive. -/
lemma primrec_devBitsToNat : Primrec devBitsToNat := by
  have hstep : Primrec₂
      (fun (_ : BitString) (q : ℕ × Bool) => 2 * q.1 + (if q.2 then 1 else 0)) := by
    have h1 : Primrec (fun q : BitString × (ℕ × Bool) => 2 * q.2.1) :=
      Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd)
    have h2 : Primrec (fun q : BitString × (ℕ × Bool) => if q.2.2 then 1 else 0) :=
      (Primrec.cond (Primrec.snd.comp Primrec.snd) (Primrec.const 1) (Primrec.const 0)).of_eq
        (fun q => by cases q.2.2 <;> simp)
    exact Primrec₂.mk (Primrec.nat_add.comp h1 h2)
  have key : Primrec (fun l : BitString =>
      l.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0) :=
    Primrec.list_foldl Primrec.id (Primrec.const 0) hstep
  exact key.of_eq (fun l => by simpa using (devBitsToNat_foldl l 0))

/-- Emptiness of a bit string is primitive recursive. -/
lemma primrec_decide_list_isEmpty : Primrec (fun l : BitString => l.isEmpty) := by
  obtain ⟨_, h⟩ := (Primrec.eq (α := ℕ)).comp
    (Primrec.list_length (α := Bool)) (Primrec.const 0)
  exact (h : Primrec fun l : BitString => decide (l.length = 0)).of_eq
    (fun l => by cases l <;> simp)

/-- The stage test of arithmetic coding is computable. -/
lemma computable_arithmeticCodingStage {a : BitString → ℕ → ℕ} (ha : Computable₂ a) :
    Computable (fun r : (BitString × BitString) × ℕ =>
      arithmeticCodingStage a r.2 r.1.1 r.1.2) := by
  have hp : Computable (fun r : (BitString × BitString) × ℕ => r.1.1) :=
    Computable.fst.comp Computable.fst
  have hx : Computable (fun r : (BitString × BitString) × ℕ => r.1.2) :=
    Computable.snd.comp Computable.fst
  have hs : Computable (fun r : (BitString × BitString) × ℕ => r.2) := Computable.snd
  have hplen : Computable (fun r : (BitString × BitString) × ℕ => r.1.1.length) :=
    Computable.list_length.comp hp
  have hxlen : Computable (fun r : (BitString × BitString) × ℕ => r.1.2.length) :=
    Computable.list_length.comp hx
  have hempty : Computable (fun r : (BitString × BitString) × ℕ => r.1.2.isEmpty) :=
    primrec_decide_list_isEmpty.to_comp.comp hx
  have hlt : Computable₂ (fun m n : ℕ => decide (m < n)) := primrec_decide_nat_lt.to_comp
  have hshort : Computable
      (fun r : (BitString × BitString) × ℕ => decide (r.2 < r.1.1.length)) :=
    hlt.comp hs hplen
  have hpow : Computable (fun r : (BitString × BitString) × ℕ => 2 ^ (r.2 - r.1.1.length)) :=
    primrec_two_pow_aux.to_comp.comp (Primrec.nat_sub.to_comp.comp hs hplen)
  have hdev : Computable (fun r : (BitString × BitString) × ℕ => devBitsToNat r.1.1) :=
    primrec_devBitsToNat.to_comp.comp hp
  have hpL : Computable (fun r : (BitString × BitString) × ℕ =>
      devBitsToNat r.1.1 * 2 ^ (r.2 - r.1.1.length)) :=
    Primrec.nat_mul.to_comp.comp hdev hpow
  have hpR : Computable (fun r : (BitString × BitString) × ℕ =>
      (devBitsToNat r.1.1 + 1) * 2 ^ (r.2 - r.1.1.length)) :=
    Primrec.nat_mul.to_comp.comp (Primrec.succ.to_comp.comp hdev) hpow
  have hla : Computable (fun r : (BitString × BitString) × ℕ =>
      treeLeftEndApprox a r.1.2 r.2) := (computable_treeLeftEndApprox ha).comp hx hs
  have hax : Computable (fun r : (BitString × BitString) × ℕ => a r.1.2 r.2) := ha.comp hx hs
  have hc1 := hlt.comp (Primrec.nat_add.to_comp.comp hla hxlen) hpL
  have hc2 := hlt.comp (Primrec.succ.to_comp.comp (Primrec.nat_add.to_comp.comp hpR hxlen))
    (Primrec.nat_add.to_comp.comp hla hax)
  have hbody := Primrec.and.to_comp.comp hc1 hc2
  refine ((Computable.cond hempty (Computable.const true)
    (Computable.cond hshort (Computable.const false) hbody))).of_eq ?_
  rintro ⟨⟨p, x⟩, s⟩
  simp only [arithmeticCodingStage]
  by_cases h1 : x.isEmpty = true
  · simp [h1]
  · by_cases h2 : s < p.length
    · simp [h1, h2]
    · simp [h1, h2, Nat.add_assoc]

/-- For a computable measure the arithmetic coding relation is recursively enumerable. -/
lemma arithmeticCodingLowerGraph_isRE (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (hμ : IsComputableMeasure μ) :
    IsRE (fun q : BitString × BitString => arithmeticCodingLowerGraph μ q.1 q.2) := by
  obtain ⟨a, ha_comp, ha⟩ := hμ
  have hstage : IsRE (fun r : (BitString × BitString) × ℕ =>
      arithmeticCodingStage a r.2 r.1.1 r.1.2 = true) :=
    isRE_of_computable_bool _ (fun r => arithmeticCodingStage a r.2 r.1.1 r.1.2)
      (fun _ => Iff.rfl) (computable_arithmeticCodingStage ha_comp)
  have hex : IsRE (fun q : BitString × BitString => ∃ s : ℕ,
      arithmeticCodingStage a s q.1 q.2 = true) :=
    IsRE.exists_encodable (R := fun (q : BitString × BitString) (s : ℕ) =>
      arithmeticCodingStage a s q.1 q.2 = true) hstage
  exact hex.of_iff (fun q => (arithmeticCodingLowerGraph_iff_exists_stage μ a ha q.1 q.2).symm)

/-- A string of positive mass has an arithmetic code of length at most `-log₂ μ[x] + 2`. -/
lemma exists_program_length_le_of_cantorMass (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (x : BitString)
    (hx : 0 < cantorMass μ x) :
    ∃ p : BitString, arithmeticCodingLowerGraph μ p x ∧
      (2 : ℝ≥0∞)⁻¹ ^ 2 * cantorMass μ x ≤ (2 : ℝ≥0∞)⁻¹ ^ p.length := by
  have ha := isContinuousTreeSemimeasure_cantorMass μ
  let l := treeLeftEnd (cantorMass μ) x
  let r := l + (cantorMass μ x).toReal
  have hl : 0 ≤ l := by
    unfold l treeLeftEnd
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact ENNReal.toReal_nonneg
    · rfl
  have hlr : l < r := by
    have h_pos : 0 < (cantorMass μ x).toReal :=
      ENNReal.toReal_pos (ne_of_gt hx) (measure_ne_top μ _)
    linarith
  have hr : r ≤ 1 := by
    have hsub : treeIco (cantorMass μ) x ⊆ treeIco (cantorMass μ) [] :=
      treeIco_prefix_subset ha List.nil_prefix
    rw [treeIco_nil ha] at hsub
    exact (Set.Ico_subset_Ico_iff hlr).mp hsub |>.2
  obtain ⟨p, hsub, hlen⟩ := exists_binaryClosedInterval_subset_Ioo_pow hl hlr hr
  use p
  constructor
  · rw [arithmeticCodingLowerGraph]
    right
    have h_int : interior (treeIco (cantorMass μ) x) = Ioo l r := interior_Ico
    rw [h_int]
    exact hsub
  · have h_r_l : r - l = (cantorMass μ x).toReal := by ring
    rw [h_r_l] at hlen
    rw [← ENNReal.toReal_le_toReal]
    · have h1 : ((2 : ℝ≥0∞)⁻¹ ^ 2 * cantorMass μ x).toReal =
          (2 : ℝ)⁻¹ ^ 2 * (cantorMass μ x).toReal := by
        simp
      have h2 : ((2 : ℝ≥0∞)⁻¹ ^ p.length).toReal = (2 : ℝ)⁻¹ ^ p.length := by
        simp
      rw [h1, h2]
      linarith
    · exact ENNReal.mul_ne_top (by simp) (measure_ne_top μ _)
    · exact ENNReal.pow_ne_top (by simp)

/-- An optimal monotone decompressor beats every computable stream map up to an additive
constant. -/
lemma KMOf_le_of_isOptimal_of_isComputableStreamMap {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) {f : BitStream → BitStream}
    (hf : IsComputableStreamMap f) :
    ∃ c : ℕ, ∀ x : BitString,
      KMOf D x ≤ KMOf (fun s => f s) x + c := hD.2 f hf

/-- For a computable measure, the monotone complexity of `x` is at most `-log₂ μ[x]` up to an
additive constant: the coding theorem for monotone complexity. -/
theorem exists_const_cantorMass_mul_le_complexityWeight_KMOf
    (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ)
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D) :
    ∃ c : ℕ, ∀ x : BitString,
      (2 : ℝ≥0∞)⁻¹ ^ c * cantorMass μ x ≤ complexityWeight (KMOf D x) := by
  have hR := arithmeticCodingLowerGraph_isStreamLowerGraph μ
  set f := streamMapOfLowerGraph (arithmeticCodingLowerGraph μ) hR with hf_def
  have hfc : IsComputableStreamMap f := by
    refine ⟨streamMapOfLowerGraph_isContinuousStreamMap hR, ?_⟩
    obtain ⟨g, hg, hgd⟩ := arithmeticCodingLowerGraph_isRE μ hμ
    exact ⟨g, hg, fun a =>
      (hgd a).trans (streamMapOfLowerGraph_finite_spec hR a.1 a.2).symm⟩
  obtain ⟨c₀, hc₀⟩ := hD.2 f hfc
  refine ⟨c₀ + 2, fun x => ?_⟩
  by_cases hx : cantorMass μ x = 0
  · simp [hx]
  · obtain ⟨p, hp, hplen⟩ :=
      exists_program_length_le_of_cantorMass μ x (pos_iff_ne_zero.mpr hx)
    have hprod : monotoneProduces f p x :=
      (streamMapOfLowerGraph_finite_spec hR p x).mpr hp
    have h1 : KMOf f x ≤ (p.length : ℕ∞) := KMOf_le_length_of_monotoneProduces hprod
    have h2 : KMOf D x ≤ (p.length : ℕ∞) + (c₀ : ℕ∞) :=
      le_trans (hc₀ x) (add_le_add h1 le_rfl)
    calc (2 : ℝ≥0∞)⁻¹ ^ (c₀ + 2) * cantorMass μ x
        = (2 : ℝ≥0∞)⁻¹ ^ c₀ * ((2 : ℝ≥0∞)⁻¹ ^ 2 * cantorMass μ x) := by
          rw [pow_add, mul_assoc]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c₀ * (2 : ℝ≥0∞)⁻¹ ^ p.length := by gcongr
      _ = complexityWeight ((p.length : ℕ∞) + (c₀ : ℕ∞)) := by
          rw [complexityWeight_add_nat, complexityWeight_coe, mul_comm]
      _ ≤ complexityWeight (KMOf D x) := complexityWeight_le_of_le h2

end Kolmogorov
