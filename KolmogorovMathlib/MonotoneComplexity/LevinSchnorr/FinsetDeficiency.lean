/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Infra
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.FinsetComputable
import KolmogorovMathlib.AlgorithmicRandomness.StageComputable
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure

/-!
# SUV Problem 144: the deficiency set of pairs `(F, w(F))`

SUV p. 149, Problem 144: a Martin-Löf random sequence `w` satisfies
`K(F, w(F)) ≥ -log p_{F,w(F)} - c` for one constant `c` and every finite `F ⊆ ℕ`.

The source hint is the Martin-Löf test whose level `c` is the union of the events
`w(F) = Z` over the pairs `(F, Z)` with `2^c · p_{F,Z} < 2^(-K(F,Z))`: its measure is at
most `2^(-c) · ∑_{(F,Z)} 2^(-K(F,Z)) ≤ 2^(-c)` by the Kraft inequality for the pairs.

This module supplies the measure-theoretic half of that argument:

* `tsum_complexityWeight_KPPair_finsetCode_le_one` — the Kraft bound over pairs `(F, Z)`;
* `measure_prefixHitSet_le_of_finsetBad` — the measure bound for *any* set of strings all of
  whose elements witness a bad pair;
* `problem_144_core` — the resulting criterion, given a uniformly r.e. family of such sets.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ### The Kraft inequality over pairs -/

/-- The prefix complexity of pairs satisfies the Kraft inequality: `∑_{(x,y)} 2^(-K(x,y)) ≤ 1`,
because `pairCode` is injective. -/
theorem tsum_complexityWeight_KPPair_le_one {U : Map} (hU : IsPrefixDecompressor U) :
    (∑' p : BitString × BitString, complexityWeight (KPPair U p.1 p.2)) ≤ 1 := by
  have hinj : Function.Injective fun p : BitString × BitString => pairCode p.1 p.2 :=
    pairCode_injective
  have hle := ENNReal.tsum_comp_le_tsum_of_injective hinj
    fun x : BitString => complexityWeight (KPPlain U x)
  exact le_trans hle (prefixComplexityWeight_isSemimeasure U hU)

/-- SUV p. 149 (the Kraft half of the hint): `∑_{(F,Z)} 2^(-K(F,Z)) ≤ 1`, the sum being over
all pairs of a finite set of indices and a string. -/
theorem tsum_complexityWeight_KPPair_finsetCode_le_one {U : Map} (hU : IsPrefixDecompressor U) :
    (∑' p : Finset ℕ × BitString, complexityWeight (KPPair U (finsetCode p.1) p.2)) ≤ 1 := by
  have hinj : Function.Injective
      fun p : Finset ℕ × BitString => ((finsetCode p.1, p.2) : BitString × BitString) := by
    rintro ⟨F, Z⟩ ⟨F', Z'⟩ h
    have h1 : finsetCode F = finsetCode F' := congrArg Prod.fst h
    have h2 : Z = Z' := congrArg Prod.snd h
    rw [finsetCode_injective h1, h2]
  have hle := ENNReal.tsum_comp_le_tsum_of_injective hinj
    fun p : BitString × BitString => complexityWeight (KPPair U p.1 p.2)
  exact le_trans hle (tsum_complexityWeight_KPPair_le_one hU)

/-! ### The measure of the union of the bad events -/

/-- SUV p. 149 (the measure half of the hint): if every string of `S` witnesses a pair
`(F, x(F))` whose deficiency exceeds `c`, then the set of sequences with a prefix in `S` has
measure at most `2^(-c)`. -/
theorem measure_prefixHitSet_le_of_finsetBad {μ : Measure CantorSeq} {U : Map}
    (hU : IsPrefixDecompressor U) (c : ℕ) (S : Set BitString)
    (hS : ∀ x ∈ S, ∃ F : Finset ℕ, (∀ i ∈ F, i < x.length) ∧
      (2 : ℝ≥0∞) ^ c * finsetEventMass μ F (restrictStr F x)
        < complexityWeight (KPPair U (finsetCode F) (restrictStr F x))) :
    μ (prefixHitSet S) ≤ (2 : ℝ≥0∞)⁻¹ ^ c := by
  classical
  set Bad : Set (Finset ℕ × BitString) :=
    {p | (2 : ℝ≥0∞) ^ c * finsetEventMass μ p.1 p.2
      < complexityWeight (KPPair U (finsetCode p.1) p.2)} with hBaddef
  have hinv : ((2 : ℝ≥0∞)⁻¹) ^ c * (2 : ℝ≥0∞) ^ c = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  have hsub : prefixHitSet S
      ⊆ ⋃ p : Bad, {v : CantorSeq | restrictSeq (p : Finset ℕ × BitString).1 v
        = (p : Finset ℕ × BitString).2} := by
    rintro v ⟨n, hn⟩
    obtain ⟨F, hFn, hbad⟩ := hS _ hn
    have hFn' : ∀ i ∈ F, i < n := by
      intro i hi
      have := hFn i hi
      rwa [cantorPrefix_length] at this
    have hres : restrictSeq F v = restrictStr F (cantorPrefix v n) :=
      restrictSeq_eq_restrictStr hFn'
    have hmem : (F, restrictSeq F v) ∈ Bad := by
      rw [hBaddef]
      simp only [Set.mem_ofPred_eq]
      rw [hres]
      exact hbad
    exact Set.mem_iUnion.2 ⟨⟨(F, restrictSeq F v), hmem⟩, rfl⟩
  have hterm : ∀ p : Bad, finsetEventMass μ (p : Finset ℕ × BitString).1
      (p : Finset ℕ × BitString).2
      ≤ (2 : ℝ≥0∞)⁻¹ ^ c
        * complexityWeight (KPPair U (finsetCode (p : Finset ℕ × BitString).1)
          (p : Finset ℕ × BitString).2) := by
    rintro ⟨p, hp⟩
    have hp' : (2 : ℝ≥0∞) ^ c * finsetEventMass μ p.1 p.2
        < complexityWeight (KPPair U (finsetCode p.1) p.2) := hp
    calc finsetEventMass μ p.1 p.2
        = (2 : ℝ≥0∞)⁻¹ ^ c * ((2 : ℝ≥0∞) ^ c * finsetEventMass μ p.1 p.2) := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c * complexityWeight (KPPair U (finsetCode p.1) p.2) := by
          gcongr
  calc μ (prefixHitSet S)
      ≤ μ (⋃ p : Bad, {v : CantorSeq | restrictSeq (p : Finset ℕ × BitString).1 v
          = (p : Finset ℕ × BitString).2}) := measure_mono hsub
    _ ≤ ∑' p : Bad, μ {v : CantorSeq | restrictSeq (p : Finset ℕ × BitString).1 v
          = (p : Finset ℕ × BitString).2} := measure_iUnion_le _
    _ ≤ ∑' p : Bad, (2 : ℝ≥0∞)⁻¹ ^ c
          * complexityWeight (KPPair U (finsetCode (p : Finset ℕ × BitString).1)
            (p : Finset ℕ × BitString).2) := ENNReal.tsum_le_tsum hterm
    _ = (2 : ℝ≥0∞)⁻¹ ^ c * ∑' p : Bad,
          complexityWeight (KPPair U (finsetCode (p : Finset ℕ × BitString).1)
            (p : Finset ℕ × BitString).2) := ENNReal.tsum_mul_left
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c * ∑' p : Finset ℕ × BitString,
          complexityWeight (KPPair U (finsetCode p.1) p.2) := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c * 1 := by
        gcongr
        exact tsum_complexityWeight_KPPair_finsetCode_le_one hU
    _ = (2 : ℝ≥0∞)⁻¹ ^ c := mul_one _

/-! ### Problem 144 modulo the enumerability of the deficiency set -/

/-- SUV Problem 144 (Section 5.6, p. 149), assembled from a uniformly r.e. family of sets of
strings that is sandwiched between the two halves of the deficiency condition. -/
theorem problem_144_core {μ : Measure CantorSeq} {U : Map} (hU : IsPrefixDecompressor U)
    {S : ℕ → Set BitString}
    (hRE : IsRE fun q : ℕ × BitString => q.2 ∈ S q.1)
    (hbad : ∀ c : ℕ, ∀ x ∈ S c, ∃ F : Finset ℕ, (∀ i ∈ F, i < x.length) ∧
      (2 : ℝ≥0∞) ^ c * finsetEventMass μ F (restrictStr F x)
        < complexityWeight (KPPair U (finsetCode F) (restrictStr F x)))
    (hcover : ∀ (c : ℕ) (F : Finset ℕ) (x : BitString), (∀ i ∈ F, i < x.length) →
      (2 : ℝ≥0∞) ^ c * finsetEventMass μ F (restrictStr F x)
        < complexityWeight (KPPair U (finsetCode F) (restrictStr F x)) → x ∈ S c)
    {w : CantorSeq} (hw : IsMartinLofRandom μ w) :
    ∃ c : ℕ, ∀ F : Finset ℕ,
      complexityWeight (KPPair U (finsetCode F) (restrictSeq F w))
        ≤ (2 : ℝ≥0∞) ^ c * finsetEventMass μ F (restrictSeq F w) := by
  by_contra hcon
  push Not at hcon
  refine hw _ (isMartinLofTest_prefixHitSet hRE
    (fun c => measure_prefixHitSet_le_of_finsetBad hU c (S c) (hbad c)))
    (Set.mem_iInter.2 fun c => ?_)
  obtain ⟨F, hF⟩ := hcon c
  obtain ⟨N, hFN⟩ := Finset.exists_nat_subset_range F
  have hFN' : ∀ i ∈ F, i < N := fun i hi => Finset.mem_range.1 (hFN hi)
  refine ⟨N, hcover c F (cantorPrefix w N) ?_ ?_⟩
  · intro i hi
    rw [cantorPrefix_length]
    exact hFN' i hi
  · rw [← restrictSeq_eq_restrictStr hFN']
    exact hF

/-! ### Dyadic arithmetic -/

/-- `dyadicValue` written multiplicatively. -/
lemma dyadicValue_eq_natCast_mul_inv_pow (m s : ℕ) :
    dyadicValue m s = (m : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ s := by
  rw [dyadicValue, div_eq_mul_inv, ← ENNReal.inv_pow]

/-- `dyadicValue` is strictly monotone in the numerator. -/
lemma dyadicValue_lt_of_lt_nat {j k : ℕ} (h : j < k) (s : ℕ) :
    dyadicValue j s < dyadicValue k s := by
  rw [dyadicValue_eq_natCast_mul_inv_pow, dyadicValue_eq_natCast_mul_inv_pow]
  have h0 : ((2 : ℝ≥0∞)⁻¹) ^ s ≠ 0 := pow_ne_zero _ (by simp)
  have hinf : ((2 : ℝ≥0∞)⁻¹) ^ s ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have hcast : (j : ℝ≥0∞) < (k : ℝ≥0∞) := by exact_mod_cast h
  have hmul := ENNReal.mul_lt_mul_right h0 hinf hcast
  rwa [mul_comm (((2 : ℝ≥0∞)⁻¹) ^ s) (j : ℝ≥0∞),
    mul_comm (((2 : ℝ≥0∞)⁻¹) ^ s) (k : ℝ≥0∞)] at hmul

/-- Scaling the numerator by `2 ^ d` and the precision by `d` leaves `dyadicValue` unchanged. -/
lemma dyadicValue_mul_two_pow (m s d : ℕ) :
    dyadicValue (m * 2 ^ d) (s + d) = dyadicValue m s := by
  rw [dyadicValue_eq_natCast_mul_inv_pow, dyadicValue_eq_natCast_mul_inv_pow, pow_add]
  have hone : ((2 : ℝ≥0∞) ^ d) * (((2 : ℝ≥0∞)⁻¹) ^ d) = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  push_cast
  calc (m : ℝ≥0∞) * (2 : ℝ≥0∞) ^ d * (((2 : ℝ≥0∞)⁻¹) ^ s * ((2 : ℝ≥0∞)⁻¹) ^ d)
      = ((m : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ s) * ((2 : ℝ≥0∞) ^ d * ((2 : ℝ≥0∞)⁻¹) ^ d) := by ring
    _ = (m : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ s := by rw [hone, mul_one]

/-- The decidable arithmetic reformulation of `B / 2^t < 1 / 2^n`. -/
lemma dyadicValue_lt_dyadicValue_one_iff (B t n : ℕ) :
    dyadicValue B t < dyadicValue 1 n ↔ B * 2 ^ n < 2 ^ t := by
  have hB : dyadicValue B t = dyadicValue (B * 2 ^ n) (t + n) :=
    (dyadicValue_mul_two_pow B t n).symm
  have h1 : dyadicValue 1 n = dyadicValue (2 ^ t) (t + n) := by
    have h := (dyadicValue_mul_two_pow 1 n t).symm
    rw [one_mul, add_comm n t] at h
    exact h
  rw [hB, h1]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    exact absurd (dyadicValue_mono_nat hcon (t + n)) (not_le.2 h)
  · intro h
    exact dyadicValue_lt_of_lt_nat h (t + n)

/-- `2 ^ c * dyadicValue A t = dyadicValue (2 ^ c * A) t`. -/
lemma two_pow_mul_dyadicValue (c A t : ℕ) :
    (2 : ℝ≥0∞) ^ c * dyadicValue A t = dyadicValue (2 ^ c * A) t := by
  rw [dyadicValue_eq_natCast_mul_inv_pow, dyadicValue_eq_natCast_mul_inv_pow]
  push_cast
  ring

/-! ### The bounded-index test -/

/-- `allLt l N` tests that every entry of the list `l` is smaller than `N`. -/
def allLt (l : List ℕ) (N : ℕ) : Bool :=
  l.foldr (fun i b => decide (i < N) && b) true

/-- `allLt` decides `∀ i ∈ l, i < N`. -/
lemma allLt_eq_true_iff {l : List ℕ} {N : ℕ} : allLt l N = true ↔ ∀ i ∈ l, i < N := by
  induction l with
  | nil => simp [allLt]
  | cons i t ih =>
    have h : allLt (i :: t) N = (decide (i < N) && allLt t N) := rfl
    rw [h]
    simp [ih]

/-- `allLt` is primitive recursive. -/
lemma primrec_allLt : Primrec fun q : List ℕ × ℕ => allLt q.1 q.2 := by
  have hlt2 : Primrec₂ fun x y : ℕ => decide (x < y) := PrimrecPred.decide Primrec.nat_lt
  have hd : Primrec fun z : (List ℕ × ℕ) × (ℕ × Bool) => decide (z.2.1 < z.1.2) :=
    Primrec₂.comp hlt2 (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
  have hb : Primrec fun z : (List ℕ × ℕ) × (ℕ × Bool) => z.2.2 :=
    Primrec.snd.comp Primrec.snd
  have h : Primrec₂ fun (q : List ℕ × ℕ) (p : ℕ × Bool) => (decide (p.1 < q.2) && p.2) :=
    (Primrec.cond hd hb (Primrec.const false)).of_eq fun z => by
      cases hcase : decide (z.2.1 < z.1.2) <;> simp [hcase]
  exact (Primrec.list_foldr Primrec.fst (Primrec.const true) h).of_eq fun _ => rfl

/-! ### The computable upper approximation of `p_{F,Z}` -/

/-- SUV p. 149: the summand of the level-`N`, precision-`t` upper approximation of `p_{F,Z}`:
the string `x` contributes `a x t + 1` when `x(F) = Z`, and nothing otherwise. -/
def sliceTerm (a : BitString → ℕ → ℕ) (F : Finset ℕ) (Z : BitString) (t : ℕ)
    (x : BitString) : ℕ :=
  if restrictStr F x = Z then a x t + 1 else 0

/-- `sliceTerm` written with `Bool.cond`, the shape `Computable.cond` consumes. -/
lemma sliceTerm_eq_cond (a : BitString → ℕ → ℕ) (F : Finset ℕ) (Z : BitString) (t : ℕ)
    (x : BitString) :
    sliceTerm a F Z t x = cond (decide (restrictStr F x = Z)) (a x t + 1) 0 := by
  by_cases h : restrictStr F x = Z <;> simp [sliceTerm, h]

/-- SUV p. 149: the numerator of the level-`N`, precision-`t` upper approximation of `p_{F,Z}`
built from an approximation `a` of the measure. -/
def sliceApprox (a : BitString → ℕ → ℕ) (F : Finset ℕ) (Z : BitString) (N t : ℕ) : ℕ :=
  ((levelList N).map (sliceTerm a F Z t)).sum

/-- `sliceTerm` is computable in all of its arguments.  The ambient type `α` is kept abstract:
instantiating it at a concrete product containing `Finset ℕ` makes the elaborator unfold the
`Primcodable.ofDenumerable` instance, which is prohibitively expensive. -/
lemma computable_sliceTerm {α : Type} [Primcodable α] {a : BitString → ℕ → ℕ}
    (ha : Computable₂ a) {G : α → Finset ℕ} {Z : α → BitString} {T : α → ℕ}
    (hG : Computable G) (hZ : Computable Z) (hT : Computable T) :
    Computable₂ fun (z : α) (x : BitString) => sliceTerm a (G z) (Z z) (T z) x := by
  have hres : Computable fun p : α × BitString => restrictStr (G p.1) p.2 :=
    Computable₂.comp (computable_restrictStr : Computable₂ restrictStr)
      (hG.comp Computable.fst) Computable.snd
  have hZ' : Computable fun p : α × BitString => Z p.1 := hZ.comp Computable.fst
  have heqC : Computable₂ fun x y : BitString => decide (x = y) :=
    Primrec₂.to_comp
      (PrimrecPred.decide Primrec.eq : Primrec₂ fun x y : BitString => decide (x = y))
  have hchk : Computable fun p : α × BitString =>
      decide (restrictStr (G p.1) p.2 = Z p.1) := Computable₂.comp heqC hres hZ'
  have hval : Computable fun p : α × BitString => a p.2 (T p.1) + 1 :=
    Computable.succ.comp (Computable₂.comp ha Computable.snd (hT.comp Computable.fst))
  have hcond : Computable fun p : α × BitString =>
      cond (decide (restrictStr (G p.1) p.2 = Z p.1)) (a p.2 (T p.1) + 1) 0 :=
    Computable.cond hchk hval (Computable.const 0)
  exact hcond.of_eq fun p => (sliceTerm_eq_cond a (G p.1) (Z p.1) (T p.1) p.2).symm

/-- `sliceApprox` is computable in all of its arguments. -/
lemma computable_sliceApprox {α : Type} [Primcodable α] {a : BitString → ℕ → ℕ}
    (ha : Computable₂ a) {G : α → Finset ℕ} {Z : α → BitString} {N T : α → ℕ}
    (hG : Computable G) (hZ : Computable Z) (hN : Computable N) (hT : Computable T) :
    Computable fun z : α => sliceApprox a (G z) (Z z) (N z) (T z) :=
  computable_list_sum_map (computable_levelList.comp hN) (computable_sliceTerm ha hG hZ hT)

/-- The arithmetic test of the deficiency set is computable, with the ambient type abstract. -/
lemma computable_arithCheck {α : Type} [Primcodable α] {a : BitString → ℕ → ℕ}
    (ha : Computable₂ a) {C : α → ℕ} {G : α → Finset ℕ} {Z : α → BitString} {N T E : α → ℕ}
    (hC : Computable C) (hG : Computable G) (hZ : Computable Z) (hN : Computable N)
    (hT : Computable T) (hE : Computable E) :
    Computable fun z : α =>
      decide (2 ^ C z * sliceApprox a (G z) (Z z) (N z) (T z) * 2 ^ E z < 2 ^ T z) := by
  have hslice : Computable fun z : α => sliceApprox a (G z) (Z z) (N z) (T z) :=
    computable_sliceApprox ha hG hZ hN hT
  have hmul : Computable₂ fun x y : ℕ => x * y := Primrec₂.to_comp Primrec.nat_mul
  have hlt2 : Computable₂ fun x y : ℕ => decide (x < y) :=
    Primrec₂.to_comp (PrimrecPred.decide Primrec.nat_lt : Primrec₂ fun x y : ℕ => decide (x < y))
  have hpow : Computable fun n : ℕ => 2 ^ n := primrec_two_pow_aux.to_comp
  exact Computable₂.comp hlt2
    (Computable₂.comp hmul (Computable₂.comp hmul (hpow.comp hC) hslice) (hpow.comp hE))
    (hpow.comp hT)

/-! ### The approximation is an upper bound converging to `p_{F,Z}` -/

/-- The number of strings of length `n`. -/
lemma length_levelList (n : ℕ) : (levelList n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : levelList (n + 1)
        = (levelList n).map (fun x => x ++ [false])
          ++ (levelList n).map (fun x => x ++ [true]) := rfl
    rw [h, List.length_append, List.length_map, List.length_map, ih, pow_succ]
    ring

/-- `dyadicValue` of a list sum is the sum of the `dyadicValue`s. -/
lemma dyadicValue_listMapSum {ι : Type*} (L : List ι) (g : ι → ℕ) (t : ℕ) :
    dyadicValue ((L.map g).sum) t = (L.map fun x => dyadicValue (g x) t).sum := by
  induction L with
  | nil => simp [dyadicValue]
  | cons x l ih => simp only [List.map_cons, List.sum_cons, dyadicValue_add, ih]

/-- Adding a constant to every summand of a list sum. -/
lemma listSum_map_add_const {ι : Type*} (L : List ι) (f : ι → ℝ≥0∞) (cst : ℝ≥0∞) :
    (L.map fun x => f x + cst).sum = (L.map f).sum + (L.length : ℝ≥0∞) * cst := by
  induction L with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- SUV p. 149: `p_{F,Z}` as a sum over the list of all strings of a level above `F`. -/
lemma finsetEventMass_eq_listSum (μ : Measure CantorSeq) {F : Finset ℕ} {N : ℕ}
    (hF : ∀ i ∈ F, i < N) (Z : BitString) :
    finsetEventMass μ F Z
      = ((levelList N).map fun x => if restrictStr F x = Z then cantorMass μ x else 0).sum := by
  classical
  rw [finsetEventMass_eq_sum μ hF Z, restrictSlice, Finset.sum_filter,
    sum_levelFinset_eq_sum_levelList]

/-- SUV p. 149: `sliceApprox` over-approximates `p_{F,Z}`. -/
lemma finsetEventMass_le_dyadicValue_sliceApprox {μ : Measure CantorSeq}
    {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {F : Finset ℕ} {N : ℕ} (hF : ∀ i ∈ F, i < N) (Z : BitString) (t : ℕ) :
    finsetEventMass μ F Z ≤ dyadicValue (sliceApprox a F Z N t) t := by
  rw [finsetEventMass_eq_listSum μ hF Z, sliceApprox, dyadicValue_listMapSum]
  refine List.sum_le_sum fun x _ => ?_
  by_cases h : restrictStr F x = Z
  · rw [if_pos h, sliceTerm, if_pos h, dyadicValue_add]
    exact (ha x t).2
  · rw [if_neg h, sliceTerm, if_neg h]
    exact bot_le

/-- SUV p. 149: `sliceApprox` over-approximates `p_{F,Z}` by at most `2 · 2^N · 2^(-t)`. -/
lemma dyadicValue_sliceApprox_le {μ : Measure CantorSeq} {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {F : Finset ℕ} {N : ℕ} (hF : ∀ i ∈ F, i < N) (Z : BitString) (t : ℕ) :
    dyadicValue (sliceApprox a F Z N t) t
      ≤ finsetEventMass μ F Z + ((2 ^ N : ℕ) : ℝ≥0∞) * (2 * dyadicValue 1 t) := by
  have hstep : ∀ x ∈ levelList N,
      dyadicValue (sliceTerm a F Z t x) t
        ≤ (if restrictStr F x = Z then cantorMass μ x else 0) + 2 * dyadicValue 1 t := by
    intro x _
    by_cases h : restrictStr F x = Z
    · rw [if_pos h, sliceTerm, if_pos h, dyadicValue_add]
      calc dyadicValue (a x t) t + dyadicValue 1 t
          ≤ (cantorMass μ x + dyadicValue 1 t) + dyadicValue 1 t := by
            gcongr
            exact (ha x t).1
        _ = cantorMass μ x + 2 * dyadicValue 1 t := by rw [add_assoc, two_mul]
    · rw [if_neg h, sliceTerm, if_neg h]
      simp [dyadicValue]
  rw [finsetEventMass_eq_listSum μ hF Z, sliceApprox, dyadicValue_listMapSum]
  calc ((levelList N).map fun x => dyadicValue (sliceTerm a F Z t x) t).sum
      ≤ ((levelList N).map fun x =>
          (if restrictStr F x = Z then cantorMass μ x else 0) + 2 * dyadicValue 1 t).sum :=
        List.sum_le_sum hstep
    _ = ((levelList N).map fun x => if restrictStr F x = Z then cantorMass μ x else 0).sum
          + ((levelList N).length : ℝ≥0∞) * (2 * dyadicValue 1 t) :=
        listSum_map_add_const _ _ _
    _ = ((levelList N).map fun x => if restrictStr F x = Z then cantorMass μ x else 0).sum
          + ((2 ^ N : ℕ) : ℝ≥0∞) * (2 * dyadicValue 1 t) := by
        rw [length_levelList]

/-- SUV p. 149: a large enough precision makes the over-approximation as sharp as required. -/
lemma exists_two_pow_mul_dyadicValue_sliceApprox_lt {μ : Measure CantorSeq}
    {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {F : Finset ℕ} {N : ℕ} (hF : ∀ i ∈ F, i < N) (Z : BitString) {c : ℕ} {v : ℝ≥0∞}
    (hlt : (2 : ℝ≥0∞) ^ c * finsetEventMass μ F Z < v) :
    ∃ t : ℕ, (2 : ℝ≥0∞) ^ c * dyadicValue (sliceApprox a F Z N t) t < v := by
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hlt
  have hrne : ((r : ℝ≥0∞)) ≠ 0 := by
    simpa using hr0.ne'
  obtain ⟨u, hu⟩ := exists_inv_two_pow_lt hrne
  set m : ℕ := c + N + 1 with hm
  have hinv : (2 : ℝ≥0∞) ^ m * ((2 : ℝ≥0∞)⁻¹) ^ m = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  have hCeq : (2 : ℝ≥0∞) ^ c * (((2 ^ N : ℕ) : ℝ≥0∞) * (2 * dyadicValue 1 (m + u)))
      = ((2 : ℝ≥0∞)⁻¹) ^ u := by
    rw [dyadicValue_one_eq_inv_two_pow', pow_add]
    push_cast
    calc (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞) ^ N * (2 * (((2 : ℝ≥0∞)⁻¹) ^ m * ((2 : ℝ≥0∞)⁻¹) ^ u)))
        = ((2 : ℝ≥0∞) ^ m * ((2 : ℝ≥0∞)⁻¹) ^ m) * ((2 : ℝ≥0∞)⁻¹) ^ u := by
          rw [hm, pow_succ, pow_add]
          ring
      _ = ((2 : ℝ≥0∞)⁻¹) ^ u := by rw [hinv, one_mul]
  refine ⟨m + u, ?_⟩
  calc (2 : ℝ≥0∞) ^ c * dyadicValue (sliceApprox a F Z N (m + u)) (m + u)
      ≤ (2 : ℝ≥0∞) ^ c
          * (finsetEventMass μ F Z + ((2 ^ N : ℕ) : ℝ≥0∞) * (2 * dyadicValue 1 (m + u))) := by
        gcongr
        exact dyadicValue_sliceApprox_le ha hF Z (m + u)
    _ = (2 : ℝ≥0∞) ^ c * finsetEventMass μ F Z + ((2 : ℝ≥0∞)⁻¹) ^ u := by
        rw [mul_add, hCeq]
    _ < (2 : ℝ≥0∞) ^ c * finsetEventMass μ F Z + (r : ℝ≥0∞) :=
        ENNReal.add_lt_add_left (ne_top_of_lt hlt) hu
    _ < v := hr

/-! ### The deficiency set and its enumerability -/

/-- SUV p. 149: the deficiency set of Problem 144, in the `Σ₁` form the r.e. machinery consumes.
A string `x` lies in level `c` when some finite `F` below `|x|`, some precision `t` and some
complexity bound `n` witness `2^c · p_{F, x(F)} < 2^(-K(F, x(F)))`. -/
def finsetDeficiencySet (a : BitString → ℕ → ℕ) (U : Map) (c : ℕ) : Set BitString :=
  {x | ∃ p : Finset ℕ × ℕ × ℕ,
      (allLt (p.1.sort (· ≤ ·)) x.length
          && decide (2 ^ c * sliceApprox a p.1 (restrictStr p.1 x) x.length p.2.1 * 2 ^ p.2.2
            < 2 ^ p.2.1)) = true ∧
      KPPair U (finsetCode p.1) (restrictStr p.1 x) < ((p.2.2 + 1 : ℕ) : ℕ∞)}

/-- Every string of the deficiency set witnesses a genuinely bad pair. -/
lemma finsetDeficiencySet_bad {μ : Measure CantorSeq} {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {U : Map} (c : ℕ) {x : BitString} (hx : x ∈ finsetDeficiencySet a U c) :
    ∃ F : Finset ℕ, (∀ i ∈ F, i < x.length) ∧
      (2 : ℝ≥0∞) ^ c * finsetEventMass μ F (restrictStr F x)
        < complexityWeight (KPPair U (finsetCode F) (restrictStr F x)) := by
  obtain ⟨⟨F, t, n⟩, hbool, hK⟩ := hx
  rw [Bool.and_eq_true] at hbool
  obtain ⟨h1, h2⟩ := hbool
  have hF : ∀ i ∈ F, i < x.length := fun i hi =>
    allLt_eq_true_iff.1 h1 i ((Finset.mem_sort (· ≤ ·)).2 hi)
  refine ⟨F, hF, lt_complexityWeight_iff_exists_nat.2 ⟨n, hK, ?_⟩⟩
  have harith : 2 ^ c * sliceApprox a F (restrictStr F x) x.length t * 2 ^ n < 2 ^ t :=
    of_decide_eq_true h2
  calc (2 : ℝ≥0∞) ^ c * finsetEventMass μ F (restrictStr F x)
      ≤ (2 : ℝ≥0∞) ^ c * dyadicValue (sliceApprox a F (restrictStr F x) x.length t) t := by
        gcongr
        exact finsetEventMass_le_dyadicValue_sliceApprox ha hF _ t
    _ = dyadicValue (2 ^ c * sliceApprox a F (restrictStr F x) x.length t) t :=
        two_pow_mul_dyadicValue _ _ _
    _ < dyadicValue 1 n := (dyadicValue_lt_dyadicValue_one_iff _ _ _).2 harith

/-- Every bad pair read off a string is witnessed inside the deficiency set. -/
lemma mem_finsetDeficiencySet {μ : Measure CantorSeq} {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {U : Map} (c : ℕ) (F : Finset ℕ) (x : BitString) (hF : ∀ i ∈ F, i < x.length)
    (hlt : (2 : ℝ≥0∞) ^ c * finsetEventMass μ F (restrictStr F x)
      < complexityWeight (KPPair U (finsetCode F) (restrictStr F x))) :
    x ∈ finsetDeficiencySet a U c := by
  obtain ⟨n, hK, hn⟩ := lt_complexityWeight_iff_exists_nat.1 hlt
  obtain ⟨t, ht⟩ := exists_two_pow_mul_dyadicValue_sliceApprox_lt ha hF (restrictStr F x) hn
  refine ⟨⟨F, t, n⟩, ?_, hK⟩
  rw [Bool.and_eq_true]
  refine ⟨allLt_eq_true_iff.2 fun i hi => hF i ((Finset.mem_sort (· ≤ ·)).1 hi),
    decide_eq_true ?_⟩
  refine (dyadicValue_lt_dyadicValue_one_iff _ _ _).1 ?_
  rw [← two_pow_mul_dyadicValue]
  exact ht

/-- `cond b₁ b₂ false` is `b₁ && b₂`. -/
lemma cond_eq_and (b₁ b₂ : Bool) : cond b₁ b₂ false = (b₁ && b₂) := by
  cases b₁ <;> rfl

/-- The bounded-index half of the deficiency test is primitive recursive. -/
lemma primrec_deficiencyIndexCheck :
    Primrec fun z : (ℕ × BitString) × (Finset ℕ × ℕ × ℕ) =>
      allLt (z.2.1.sort (· ≤ ·)) z.1.2.length := by
  have hsort : Primrec fun z : (ℕ × BitString) × (Finset ℕ × ℕ × ℕ) =>
      z.2.1.sort (· ≤ ·) := primrec_finsetSort.comp (Primrec.fst.comp Primrec.snd)
  have hlen : Primrec fun z : (ℕ × BitString) × (Finset ℕ × ℕ × ℕ) => z.1.2.length :=
    Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)
  exact Primrec₂.comp (primrec_allLt : Primrec₂ allLt) hsort hlen

/-- The arithmetic half of the deficiency test is computable. -/
lemma computable_deficiencyArithCheck {a : BitString → ℕ → ℕ} (ha : Computable₂ a) :
    Computable fun z : (ℕ × BitString) × (Finset ℕ × ℕ × ℕ) =>
      decide (2 ^ z.1.1 * sliceApprox a z.2.1 (restrictStr z.2.1 z.1.2) z.1.2.length z.2.2.1
        * 2 ^ z.2.2.2 < 2 ^ z.2.2.1) := by
  have hC : Computable fun z : (ℕ × BitString) × (Finset ℕ × ℕ × ℕ) => z.1.1 :=
    Computable.fst.comp Computable.fst
  have hG : Computable fun z : (ℕ × BitString) × (Finset ℕ × ℕ × ℕ) => z.2.1 :=
    Computable.fst.comp Computable.snd
  have hZ : Computable fun z : (ℕ × BitString) × (Finset ℕ × ℕ × ℕ) =>
      restrictStr z.2.1 z.1.2 :=
    Computable₂.comp (computable_restrictStr : Computable₂ restrictStr) hG
      (Computable.snd.comp Computable.fst)
  have hN : Computable fun z : (ℕ × BitString) × (Finset ℕ × ℕ × ℕ) => z.1.2.length :=
    Computable.list_length.comp (Computable.snd.comp Computable.fst)
  have hT : Computable fun z : (ℕ × BitString) × (Finset ℕ × ℕ × ℕ) => z.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hE : Computable fun z : (ℕ × BitString) × (Finset ℕ × ℕ × ℕ) => z.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  exact computable_arithCheck ha hC hG hZ hN hT hE

/-- Upper semicomputability of the prefix complexity of a pair, with the ambient type kept
abstract (a concrete product containing `Finset ℕ` makes the elaborator unfold the
`Primcodable.ofDenumerable` instance, which is prohibitively expensive). -/
lemma isRE_KPPair_lt {α : Type} [Primcodable α] {U : Map} (hU : isDecompressor U)
    {X Y : α → BitString} {n : α → ℕ} (hX : Computable X) (hY : Computable Y)
    (hn : Computable n) :
    IsRE fun z : α => KPPair U (X z) (Y z) < ((n z : ℕ) : ℕ∞) := by
  have hmap : Computable fun z : α => ((pairCode (X z) (Y z), n z) : BitString × ℕ) :=
    Computable.pair (Computable₂.comp (pairCode_computable : Computable₂ pairCode) hX hY) hn
  exact (isRE_KPPlain_lt hU).comp_computable hmap

/-- Conjunction of two computable boolean tests, with the ambient type kept abstract. -/
lemma computable_and {α : Type} [Primcodable α] {f g : α → Bool} (hf : Computable f)
    (hg : Computable g) : Computable fun z : α => (f z && g z) :=
  (Computable.cond hf hg (Computable.const false)).of_eq fun _ => cond_eq_and _ _

/-- The complexity half of the deficiency test is recursively enumerable. -/
lemma isRE_deficiencyComplexityBound {U : Map} (hU : isDecompressor U) :
    IsRE fun z : (ℕ × BitString) × (Finset ℕ × ℕ × ℕ) =>
      KPPair U (finsetCode z.2.1) (restrictStr z.2.1 z.1.2) < ((z.2.2.2 + 1 : ℕ) : ℕ∞) := by
  have hcode : Computable fun z : (ℕ × BitString) × (Finset ℕ × ℕ × ℕ) =>
      finsetCode z.2.1 := computable_finsetCode.comp (Computable.fst.comp Computable.snd)
  have hres : Computable fun z : (ℕ × BitString) × (Finset ℕ × ℕ × ℕ) =>
      restrictStr z.2.1 z.1.2 :=
    Computable₂.comp (computable_restrictStr : Computable₂ restrictStr)
      (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.fst)
  have hn : Computable fun z : (ℕ × BitString) × (Finset ℕ × ℕ × ℕ) => z.2.2.2 + 1 :=
    Computable.succ.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  exact isRE_KPPair_lt hU hcode hres hn

/-- SUV p. 149: the deficiency sets of Problem 144 are uniformly enumerable. -/
theorem isRE_finsetDeficiencySet {a : BitString → ℕ → ℕ} (ha : Computable₂ a) {U : Map}
    (hU : isDecompressor U) :
    IsRE fun q : ℕ × BitString => q.2 ∈ finsetDeficiencySet a U q.1 :=
  IsRE.of_iff
    (IsRE.exists_encodable (IsRE.and_computable (isRE_deficiencyComplexityBound hU)
      (computable_and primrec_deficiencyIndexCheck.to_comp
        (computable_deficiencyArithCheck ha))))
    fun _ => Iff.rfl

/-! ### Problem 144 -/

/-- **SUV Problem 144** (Section 5.6, p. 149): if `w` is Martin-Löf random with respect to a
computable measure `μ`, then `K(F, w(F)) ≥ -log p_{F, w(F)} - c` for one constant `c` and every
finite index set `F ⊆ ℕ`. -/
theorem problem_144_le_KPPair_of_isMartinLofRandom' {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {U : Map}
    (hU : IsOptimalPrefixConditional U) {w : CantorSeq} (hw : IsMartinLofRandom μ w) :
    ∃ c : ℕ, ∀ F : Finset ℕ,
      complexityWeight (KPPair U (finsetCode F) (restrictSeq F w))
        ≤ (2 : ℝ≥0∞) ^ c * finsetEventMass μ F (restrictSeq F w) := by
  obtain ⟨a, ha_comp, ha⟩ := hμ
  exact problem_144_core hU.isPrefixDecompressor
    (isRE_finsetDeficiencySet ha_comp hU.isDecompressor)
    (fun c x hx => finsetDeficiencySet_bad ha c hx)
    (fun c F x hFx hlt => mem_finsetDeficiencySet ha c F x hFx hlt) hw

/-! ### Towards Problem 145: initial segments inside an exhaustion

The two lemmas below are the measure-theoretic half of SUV Problem 145 (p. 150).  They are not
enough to prove it: the source proof goes through a computable permutation of the indices that
turns the sets `F i` into initial segments (and transports `μ` along it), which is a genuinely
new construction rather than more plumbing.
-/

/-- SUV p. 150: if `F` contains every index below `n`, then the event `v(F) = w(F)` sits inside
the cylinder of the length-`n` prefix of `w`, so `p_{F, w(F)} ≤ μ(Ω_{(w)_n})`. -/
lemma finsetEventMass_le_cantorMass (μ : Measure CantorSeq) {F : Finset ℕ} {n : ℕ}
    (hF : ∀ k, k < n → k ∈ F) (w : CantorSeq) :
    finsetEventMass μ F (restrictSeq F w) ≤ cantorMass μ (cantorPrefix w n) := by
  rw [finsetEventMass, cantorMass]
  refine measure_mono fun v hv => ?_
  have h : (F.sort (· ≤ ·)).map v = (F.sort (· ≤ ·)).map w := hv
  have hvw : ∀ i ∈ F, v i = w i := fun i hi =>
    List.map_inj_left.1 h i ((Finset.mem_sort (· ≤ ·)).2 hi)
  have hpref : cantorPrefix v n = cantorPrefix w n := by
    refine List.ext_getElem (by simp) fun i h1 _ => ?_
    rw [cantorPrefix_getElem, cantorPrefix_getElem]
    exact hvw i (hF i (by simpa using h1))
  exact (isCantorPrefix_iff_cantorPrefix_eq _ v).2 (by rw [cantorPrefix_length]; exact hpref)

/-- An increasing exhaustion of `ℕ` by finite sets eventually contains every initial
segment. -/
lemma exists_forall_lt_mem_of_exhaustion {F : ℕ → Finset ℕ} (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) (n : ℕ) : ∃ i : ℕ, ∀ k, k < n → k ∈ F i := by
  have hmonoF : Monotone F := monotone_nat_of_le_succ hmono
  induction n with
  | zero => exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ n ih =>
    obtain ⟨i₀, hi₀⟩ := ih
    obtain ⟨i₁, hi₁⟩ := hcover n
    refine ⟨max i₀ i₁, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
    · exact hmonoF (le_max_left i₀ i₁) (hi₀ k h)
    · subst h
      exact hmonoF (le_max_right i₀ i₁) hi₁

/-- If `F` contains the whole block `[m, m+n)` and has no element below `m`, then the first `n`
entries of the increasing enumeration of `F` are `m, m+1, …, m+n-1`. -/
lemma sort_take_eq_range' : ∀ (n m : ℕ) (F : Finset ℕ),
    (∀ k, m ≤ k → k < m + n → k ∈ F) → (∀ b ∈ F, m ≤ b) →
    (F.sort (· ≤ ·)).take n = List.range' m n
  | 0, _, _, _, _ => rfl
  | (n + 1), m, F, hin, hge => by
    classical
    have hmF : m ∈ F := hin m le_rfl (by omega)
    have hm : m ∉ F.erase m := Finset.notMem_erase m F
    have hle : ∀ b ∈ F.erase m, m ≤ b := fun b hb => hge b (Finset.mem_of_mem_erase hb)
    have hsort : F.sort (· ≤ ·) = m :: (F.erase m).sort (· ≤ ·) := by
      conv_lhs => rw [← Finset.insert_erase hmF]
      exact Finset.sort_insert (· ≤ ·) hle hm
    have hin' : ∀ k, m + 1 ≤ k → k < (m + 1) + n → k ∈ F.erase m := by
      intro k h1 h2
      exact Finset.mem_erase.2 ⟨by omega, hin k (by omega) (by omega)⟩
    have hge' : ∀ b ∈ F.erase m, m + 1 ≤ b := by
      intro b hb
      have h1 := hle b hb
      have h2 : b ≠ m := (Finset.mem_erase.1 hb).1
      omega
    rw [hsort, List.take_succ_cons, sort_take_eq_range' n (m + 1) (F.erase m) hin' hge']
    rfl

/-- SUV p. 150: if `F` contains every index below `n`, the first `n` entries of the increasing
enumeration of `F` are `0, 1, …, n-1`. -/
lemma sort_take_eq_range {F : Finset ℕ} {n : ℕ} (hF : ∀ k, k < n → k ∈ F) :
    (F.sort (· ≤ ·)).take n = List.range n := by
  rw [sort_take_eq_range' n 0 F (fun k _ hk => hF k (by omega)) (fun b _ => Nat.zero_le b),
    ← List.range_eq_range']

/-- SUV p. 150: if `F` contains every index below `n`, the first `n` bits of `v(F)` are the
length-`n` prefix of `v`. -/
lemma restrictSeq_take (F : Finset ℕ) {n : ℕ} (hF : ∀ k, k < n → k ∈ F) (v : CantorSeq) :
    (restrictSeq F v).take n = cantorPrefix v n := by
  have hmap : (restrictSeq F v).take n = ((F.sort (· ≤ ·)).take n).map v := by
    rw [restrictSeq, List.map_take]
  rw [hmap, sort_take_eq_range hF]
  refine List.ext_getElem (by simp) fun i hi₁ _ => ?_
  rw [List.getElem_map, List.getElem_range, cantorPrefix_getElem]

/-- The event `v(F) = Z` is measurable. -/
lemma measurableSet_setOf_restrictSeq (F : Finset ℕ) (Z : BitString) :
    MeasurableSet {v : CantorSeq | restrictSeq F v = Z} := by
  obtain ⟨N, hFN⟩ := Finset.exists_nat_subset_range F
  have hF : ∀ i ∈ F, i < N := fun i hi => Finset.mem_range.1 (hFN hi)
  rw [setOf_restrictSeq_eq_biUnion hF Z]
  exact Finset.measurableSet_biUnion _ fun x _ => measurableSet_cantorCylinder x

open scoped Classical in
/-- SUV p. 150, the law of total probability for the `F`-events refining a cylinder: if `F`
contains every index below `n = |x|`, the events `v(F) = Z` with `Z` extending `x` partition
the cylinder `Ω_x`, so `μ(Ω_x) = ∑ p_{F,Z}`.

Together with `finsetEventMass_le_cantorMass` this is the measure-theoretic half of what a
Kraft-Chaitin proof of Problem 145 on the filtration of the sets `F i` needs. -/
theorem cantorMass_eq_sum_finsetEventMass (μ : Measure CantorSeq) {F : Finset ℕ} {n : ℕ}
    (hF : ∀ k, k < n → k ∈ F) {x : BitString} (hx : x.length = n) :
    cantorMass μ x
      = ∑ Z ∈ (levelFinset F.card).filter fun Z => Z.take n = x,
          finsetEventMass μ F Z := by
  have hset : cantorCylinder x
      = ⋃ Z ∈ (levelFinset F.card).filter fun Z => Z.take n = x,
          {v : CantorSeq | restrictSeq F v = Z} := by
    ext v
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_filter, mem_levelFinset, exists_prop]
    constructor
    · intro hv
      have hpref : cantorPrefix v n = x := by
        rw [← hx]
        exact (isCantorPrefix_iff_cantorPrefix_eq x v).1 hv
      exact ⟨restrictSeq F v, ⟨length_restrictSeq F v, by rw [restrictSeq_take F hF v, hpref]⟩,
        rfl⟩
    · rintro ⟨Z, ⟨_, hZx⟩, hvZ⟩
      have hpref : cantorPrefix v n = x := by
        rw [← restrictSeq_take F hF v, hvZ, hZx]
      exact (isCantorPrefix_iff_cantorPrefix_eq x v).2 (by rw [hx]; exact hpref)
  have hdisj : (((levelFinset F.card).filter fun Z => Z.take n = x : Finset BitString) :
      Set BitString).PairwiseDisjoint fun Z => {v : CantorSeq | restrictSeq F v = Z} := by
    intro Z _ Z' _ hne
    refine Set.disjoint_left.mpr fun v hv hv' => ?_
    exact hne (hv.symm.trans hv')
  rw [cantorMass, hset, measure_biUnion_finset hdisj
    fun Z _ => measurableSet_setOf_restrictSeq F Z]
  rfl

end Kolmogorov
