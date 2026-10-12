import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Partition.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalMaps
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Core.Invariance

/-!
# Merging strong sufficient statistics: shared definitions

The common interface of the formalization of the strong-merging note `sublinear-merging.tex`:
the square-root merger of two strong sufficient statistics, its quantitative tradeoff, the
matching Hamming-sphere obstruction, and the negative answer to the formal one-sided Question 1
of Vereshchagin–Shen, *Algorithmic statistics: forty years later*, §7.9.  The module fixes the
shared nodes of the note's appendix "Formalization blueprint".

* **S01, the canonical total interpreter.**  Total conditional complexity `CT` is always taken
  with respect to `T₀ = universalDecompressor`, never an unspecified optimal interpreter.
  `exists_prefix_universalDecompressor_eq` is its structural compiler (one prefix per machine,
  fixed before every program and condition) and
  `isOptimalTotalConditional_universalDecompressor` its total optimality.
* **U00, plain statistics.**  Plain complexity `C` is taken with respect to a plain machine `V`;
  the theorems assume `isOptimalConditional V`.  A finite model `F` is encoded by
  `canonicalFiniteSetCode F`, which on a nonempty set is the code `(codedUniformOn F hF).code`
  of `plainSetComplexity`, `IsSufficientStatistic` and `IsStrongSetModel`
  (`canonicalFiniteSetCode_eq_codedUniformOn_code`).  Complexities enter real inequalities
  through their natural values, which are the genuine values: `plainK V u` is finite for an
  optimal `V` (`plainK_ne_top`) and `totalCondK universalDecompressor u v` always is
  (`totalCondK_universalDecompressor_ne_top`).  Logarithms are real binary logarithms
  `Real.logb 2` and tolerances are real.  At a natural tolerance the real predicates agree with
  the library's ceiling-log ones (`isSufficientModel_natCast_iff`, `isStrongModel_natCast_iff`);
  a real tolerance is rounded explicitly (`isStrongModel_iff_floor`,
  `isSufficientModel_ceil_bridge`).
* **S00, strong-only robust minimality** (`StrongRobustMin`), the one minimality notion of both
  the positive enlarged-window result and the negative answer to Question 1.  Its competitors are
  the strong sufficient models only, so it is not the library's all-model `IsMinimalModel`.

The numerical conventions are `headerLog n = ⌈log₂ (n + 2)⌉`, the base budget
`baseBudget n e = e + ⌈log₂ (n + 2)⌉`, the square-root scale `rootScale n e = √(n · baseBudget n e)`
and the merger budget `mergerBudget` of the lower bound; `IsMergingInstance` and `TradeoffBounds`
bundle the hypotheses and the conclusions of the positive theorems.
-/

namespace Kolmogorov

/-! ### S01: the canonical total interpreter -/

/-- **Structural compiler of the canonical total interpreter** (blueprint node S01).  For every
partial recursive machine `D` there is one prefix `pre`, chosen before any program or condition,
such that `universalDecompressor` runs `pre ++ p` exactly as `D` runs `p`: the two partial
evaluations agree on every program `p` and every condition `y`.  So `p ↦ pre ++ p` preserves
outputs and totality on all conditions, at the cost of `pre.length` bits. -/
theorem exists_prefix_universalDecompressor_eq (D : Map) (hD : isDecompressor D) :
    ∃ pre : BitString, ∀ p y : BitString,
      universalDecompressor (pre ++ p, y) = D (p, y) := by
  obtain ⟨code, hc⟩ := exists_code_of_isDecompressor D hD
  exact ⟨unaryPrefix (Encodable.encode code), fun p y => by rw [universal_simulation, hc]⟩

/-- **The canonical total interpreter is optimal for total conditional complexity** (blueprint
node S01).  This names the interpreter that `exists_isOptimalTotalConditional` only asserts to
exist. -/
theorem isOptimalTotalConditional_universalDecompressor :
    IsOptimalTotalConditional universalDecompressor := by
  refine ⟨isDecompressor_universalDecompressor, fun D hD => ?_⟩
  obtain ⟨code, hc⟩ := exists_code_of_isDecompressor D hD
  exact ⟨(unaryPrefix (Encodable.encode code)).length, fun x y =>
    sInfLeSInfAdd (totalCandidateLengths_universalPrefix D code hc x y)⟩

/-- Total conditional complexity with respect to the canonical total interpreter is finite for
every output and condition. -/
theorem totalCondK_universalDecompressor_ne_top (u v : BitString) :
    totalCondK universalDecompressor u v ≠ ⊤ := by
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  obtain ⟨c, hc⟩ := totalCondK_le_plainK V universalDecompressor hV.1
    isOptimalTotalConditional_universalDecompressor
  obtain ⟨c', hc'⟩ := plainK_le_length V hV
  exact ne_top_of_le_natCast (n := u.length + c' + c) <|
    (hc u v).trans (by push_cast; gcongr; exact hc' u)

namespace StrongMerging

/-! ### U00: model encoding and real-valued complexities -/

/-- On a nonempty finite set the canonical code `canonicalFiniteSetCode` is the uniform-model code
`(codedUniformOn F hF).code` used by `plainSetComplexity`, `IsSufficientStatistic` and
`IsStrongSetModel`. -/
theorem canonicalFiniteSetCode_eq_codedUniformOn_code (F : Finset BitString)
    (hF : F.Nonempty) : canonicalFiniteSetCode F = (codedUniformOn F hF).code := by
  rw [canonicalFiniteSetCode, canonicalUniformCodeOfList_canonicalFinsetList]

/-- The canonical model code is injective: a finite model is recovered from its code. -/
theorem canonicalFiniteSetCode_injective : Function.Injective canonicalFiniteSetCode := by
  intro F G h
  have hlist := congrArg canonicalPointListOfCode h
  rw [canonicalPointListOfCode_canonicalFiniteSetCode,
    canonicalPointListOfCode_canonicalFiniteSetCode] at hlist
  rw [← canonicalFinsetList_toFinset F, ← canonicalFinsetList_toFinset G, hlist]

/-- The plain complexity `C(u)` of a string `u` with respect to the plain machine `V`, as a real
number: the natural value of `plainK V u`.  For an optimal `V` this value is finite
(`plainK_ne_top`), so it is the complexity itself. -/
noncomputable def plainC (V : Map) (u : BitString) : ℝ :=
  ((plainK V u).toNat : ℝ)

/-- The plain complexity `C(F)` of a finite model `F`: the plain complexity of its canonical code
`canonicalFiniteSetCode F`, as a real number.  On nonempty sets it is the natural value of the
library's `plainSetComplexity` (`setC_eq_plainSetComplexity`). -/
noncomputable def setC (V : Map) (F : Finset BitString) : ℝ :=
  plainC V (canonicalFiniteSetCode F)

/-- The total conditional complexity `CT(u | v)` with respect to the canonical total interpreter
`universalDecompressor` (blueprint node S01), as a real number.  It is the natural value of
`totalCondK universalDecompressor u v`, which is always finite
(`totalCondK_universalDecompressor_ne_top`). -/
noncomputable def totalC (u v : BitString) : ℝ :=
  ((totalCondK universalDecompressor u v).toNat : ℝ)

/-- `CT(D | A)`: the total conditional complexity of a finite model `D` given a finite model `A`,
computed on their canonical codes. -/
noncomputable def setTotalC (D A : Finset BitString) : ℝ :=
  totalC (canonicalFiniteSetCode D) (canonicalFiniteSetCode A)

/-- `CT(F | x)`: the total conditional complexity of a finite model `F` given a string `x` (the
point strength of `F` at `x`). -/
noncomputable def pointTotalC (F : Finset BitString) (x : BitString) : ℝ :=
  totalC (canonicalFiniteSetCode F) x

/-- The real two-part score `Score(F, x) = C(F) + log₂ |F| - C(x)` of a finite model `F` for
`x`, with the real binary logarithm and no truncated subtraction. -/
noncomputable def modelScore (V : Map) (F : Finset BitString) (x : BitString) : ℝ :=
  setC V F + Real.logb 2 F.card - plainC V x

/-- `F` is `ε`-strong for `x`: `CT(F | x) ≤ ε`, for a real tolerance `ε`.  As for the library's
`IsStrongSetModel`, this does not assert `x ∈ F`. -/
def IsStrongModel (x : BitString) (F : Finset BitString) (ε : ℝ) : Prop :=
  pointTotalC F x ≤ ε

/-- `F` is an `ε`-sufficient model of `x`: `x ∈ F` and `C(F) + log₂ |F| ≤ C(x) + ε`, with the real
binary logarithm and a real tolerance `ε`. -/
def IsSufficientModel (V : Map) (x : BitString) (F : Finset BitString) (ε : ℝ) : Prop :=
  x ∈ F ∧ setC V F + Real.logb 2 F.card ≤ plainC V x + ε

/-! ### S00: strong-only robust minimality -/

/-- **Strong-only robust minimality** (blueprint node S00, `StrongRobustMin`).  The model `A` is
robustly minimal for `x` at tolerance `t` with gap `δ` when every `t`-strong, `t`-sufficient model
`F` of `x` (so `x ∈ F`, `CT(F | x) ≤ t` and `C(F) + log₂ |F| ≤ C(x) + t`) satisfies the strict
additive cutoff `C(F) + δ > C(A)`; that is, no such competitor has `C(F) ≤ C(A) - δ`
(`strongRobustMin_iff`).  The predicate asserts nothing about `A` itself: `x ∈ A` and the strength
and sufficiency of `A` are separate hypotheses.  Its competitor class differs from that of the
library's all-model `IsMinimalModel`. -/
def StrongRobustMin (V : Map) (x : BitString) (A : Finset BitString) (t δ : ℝ) : Prop :=
  ∀ F : Finset BitString, IsStrongModel x F t → IsSufficientModel V x F t →
    setC V A < setC V F + δ

/-! ### Numerical conventions and bundled hypotheses -/

/-- `headerLog n = ⌈log₂ (n + 2)⌉`, computed as `Nat.clog 2 (n + 2)` (`headerLog_eq_ceil_logb`):
the header length `ℓ(n)` of the positive results and `m = ⌈log₂ (M + 2)⌉` of the lower bound. -/
def headerLog (n : ℕ) : ℕ :=
  Nat.clog 2 (n + 2)

/-- The base budget `H = e + ⌈log₂ (n + 2)⌉` of the merging theorems, for the integer input budget
`e`. -/
def baseBudget (n e : ℕ) : ℕ :=
  e + headerLog n

/-- The square-root scale `S = √(n H)`, with `H = e + ⌈log₂ (n + 2)⌉` (`baseBudget n e`), of the
merging theorems. -/
noncomputable def rootScale (n e : ℕ) : ℝ :=
  Real.sqrt (n * baseBudget n e)

/-- The merger budget `T = ⌊r / 10⁶⌋` with `r = ⌊√(M E)⌋` of the sharp lower bound, computed with
`Nat.sqrt` and natural division (`mergerBudget_eq_floor`). -/
def mergerBudget (M E : ℕ) : ℕ :=
  Nat.sqrt (M * E) / 10 ^ 6

/-- The hypotheses of the merging theorems: `n ≥ 2`, `0 ≤ ε ≤ n`, `x` is a string of length `n`,
and `A`, `B` are `ε`-strong, `ε`-sufficient statistics for `x`. -/
def IsMergingInstance (V : Map) (n : ℕ) (ε : ℝ) (x : BitString) (A B : Finset BitString) :
    Prop :=
  2 ≤ n ∧ 0 ≤ ε ∧ ε ≤ n ∧ x.length = n ∧
    IsStrongModel x A ε ∧ IsSufficientModel V x A ε ∧
    IsStrongModel x B ε ∧ IsSufficientModel V x B ε

/-- The score, endpoint and mass bounds of the quantitative merging tradeoff for a model `D`, at
the shrink exponent `R`, the integer budget `e` and the constant `c`.  With
`H = e + ⌈log₂ (n + 2)⌉` (`baseBudget n e`) and real division:
`C(D) + log₂ |D| - C(x) ≤ c (R + H)`, `CT(D | A) ≤ c (H + n H / R)`, `CT(D | B) ≤ c (H + n H / R)`
and `log₂ |D| ≥ log₂ |A| + log₂ |B| - log₂ |A ∩ B| - c (H + n H / R)`. -/
def TradeoffBounds (V : Map) (n e R c : ℕ) (x : BitString) (A B D : Finset BitString) : Prop :=
  modelScore V D x ≤ c * (R + baseBudget n e) ∧
    setTotalC D A ≤ c * (baseBudget n e + n * baseBudget n e / R) ∧
    setTotalC D B ≤ c * (baseBudget n e + n * baseBudget n e / R) ∧
    Real.logb 2 A.card + Real.logb 2 B.card - Real.logb 2 (A ∩ B).card -
      c * (baseBudget n e + n * baseBudget n e / R) ≤ Real.logb 2 D.card

/-! ### Bridges to the library's predicates and to the manuscript's notation -/

/-- `setC` is the natural value of the library's `plainSetComplexity`. -/
theorem setC_eq_plainSetComplexity (V : Map) (F : Finset BitString) (hF : F.Nonempty) :
    setC V F = ((plainSetComplexity V F hF).toNat : ℝ) := by
  rw [setC, plainC, plainSetComplexity, canonicalFiniteSetCode_eq_codedUniformOn_code F hF]

/-- At a natural tolerance `e`, `IsStrongModel` is the library's `IsStrongSetModel` at the
canonical total interpreter. -/
theorem isStrongModel_natCast_iff (x : BitString) (F : Finset BitString) (hF : F.Nonempty)
    (e : ℕ) : IsStrongModel x F e ↔ IsStrongSetModel universalDecompressor x F hF e := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp
    (totalCondK_universalDecompressor_ne_top (canonicalFiniteSetCode F) x)
  rw [IsStrongModel, pointTotalC, totalC, IsStrongSetModel,
    ← canonicalFiniteSetCode_eq_codedUniformOn_code F hF, ← hk, ENat.toNat_natCast]
  norm_cast

/-- The real binary logarithm of a positive natural `N` is at most a natural `j` exactly when the
ceiling logarithm `Nat.clog 2 N` is. -/
private theorem logb_le_natCast_iff_clog_le {N : ℕ} (hN : 0 < N) (j : ℕ) :
    Real.logb 2 N ≤ j ↔ Nat.clog 2 N ≤ j := by
  rw [Real.logb_le_iff_le_rpow one_lt_two (by exact_mod_cast hN), Real.rpow_natCast,
    Nat.clog_le_iff_le_pow one_lt_two]
  norm_cast

/-- For natural `a, k, e` and positive `N`, the real-log inequality `a + log₂ N ≤ k + e` is the
ceiling-log inequality `a + ⌈log₂ N⌉ ≤ k + e`. -/
private theorem add_logb_le_iff_add_clog_le {a k e N : ℕ} (hN : 0 < N) :
    (a : ℝ) + Real.logb 2 N ≤ k + e ↔ a + Nat.clog 2 N ≤ k + e := by
  have hlog : 0 ≤ Real.logb 2 N := Real.logb_nonneg one_lt_two (by exact_mod_cast hN)
  constructor
  · intro h
    have hak : a ≤ k + e := by
      have : (a : ℝ) ≤ k + e := by linarith
      exact_mod_cast this
    have hj : Real.logb 2 N ≤ ((k + e - a : ℕ) : ℝ) := by
      push_cast [hak]
      linarith
    have := (logb_le_natCast_iff_clog_le hN _).mp hj
    omega
  · intro h
    have hj := (logb_le_natCast_iff_clog_le hN (k + e - a)).mpr (by omega)
    have hak : a ≤ k + e := by omega
    push_cast [hak] at hj
    linarith

/-- **Integer-tolerance bridge.**  At a natural tolerance `e` and for an optimal plain machine,
the real-log sufficiency `C(F) + log₂ |F| ≤ C(x) + e` is exactly the library's ceiling-log
`IsSufficientStatistic`, because both complexities and the cutoff are integers. -/
theorem isSufficientModel_natCast_iff (V : Map) (hV : isOptimalConditional V) (x : BitString)
    (F : Finset BitString) (hF : F.Nonempty) (e : ℕ) :
    IsSufficientModel V x F e ↔ IsSufficientStatistic V x F hF e := by
  obtain ⟨cV, hcV⟩ := plainK_le_length V hV
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_natCast_add (hcV (codedUniformOn F hF).code))
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_natCast_add (hcV x))
  rw [IsSufficientModel, IsSufficientStatistic, setC_eq_plainSetComplexity V F hF, plainC,
    plainSetComplexity, ← ha, ← hk, ENat.toNat_natCast, ENat.toNat_natCast]
  refine and_congr_right fun _ => ?_
  have hE : (a : ℕ∞) + (finiteSetLogCard F : ℕ∞) ≤ (k : ℕ∞) + (e : ℕ∞) ↔
      a + finiteSetLogCard F ≤ k + e := by
    norm_cast
  rw [hE, finiteSetLogCard]
  exact add_logb_le_iff_add_clog_le hF.card_pos

/-- **Real-tolerance strength bridge.**  Total conditional complexity is an integer, so for a real
tolerance `ε ≥ 0` the model `F` is `ε`-strong exactly when it is `⌊ε⌋`-strong in the library's
sense. -/
theorem isStrongModel_iff_floor (x : BitString) (F : Finset BitString) (hF : F.Nonempty) {ε : ℝ}
    (hε : 0 ≤ ε) : IsStrongModel x F ε ↔ IsStrongSetModel universalDecompressor x F hF ⌊ε⌋₊ := by
  rw [← isStrongModel_natCast_iff x F hF, IsStrongModel, IsStrongModel, pointTotalC, totalC,
    Nat.cast_le, Nat.le_floor_iff hε]

/-- **Real-tolerance sufficiency bridge.**  For a real tolerance `ε ≥ 0`, rounding up to the
natural tolerance `⌈ε⌉` costs less than one bit: an `ε`-sufficient model is `⌈ε⌉`-sufficient in
the library's ceiling-log sense, and a `⌈ε⌉`-sufficient one is `(ε + 1)`-sufficient. -/
theorem isSufficientModel_ceil_bridge (V : Map) (hV : isOptimalConditional V) (x : BitString)
    (F : Finset BitString) (hF : F.Nonempty) {ε : ℝ} (hε : 0 ≤ ε) :
    (IsSufficientModel V x F ε → IsSufficientStatistic V x F hF ⌈ε⌉₊) ∧
      (IsSufficientStatistic V x F hF ⌈ε⌉₊ → IsSufficientModel V x F (ε + 1)) := by
  rw [← isSufficientModel_natCast_iff V hV x F hF]
  refine ⟨fun h => ⟨h.1, h.2.trans ?_⟩, fun h => ⟨h.1, h.2.trans ?_⟩⟩
  · linarith [Nat.le_ceil ε]
  · linarith [Nat.ceil_lt_add_one hε]

/-- Sufficiency in score form: `F` is `ε`-sufficient for `x` exactly when `x ∈ F` and
`Score(F, x) = C(F) + log₂ |F| - C(x) ≤ ε`. -/
theorem isSufficientModel_iff_modelScore_le (V : Map) (x : BitString) (F : Finset BitString)
    (ε : ℝ) : IsSufficientModel V x F ε ↔ x ∈ F ∧ modelScore V F x ≤ ε := by
  rw [IsSufficientModel, modelScore, sub_le_iff_le_add']

/-- `StrongRobustMin` in the source's phrasing: no `t`-strong, `t`-sufficient model `F` of `x` has
`C(F) ≤ C(A) - δ`. -/
theorem strongRobustMin_iff (V : Map) (x : BitString) (A : Finset BitString) (t δ : ℝ) :
    StrongRobustMin V x A t δ ↔ ∀ F : Finset BitString, IsStrongModel x F t →
      IsSufficientModel V x F t → ¬ setC V F ≤ setC V A - δ := by
  simp only [StrongRobustMin, not_le, sub_lt_iff_lt_add]

/-- `headerLog n` is the ceiling of the real binary logarithm `⌈log₂ (n + 2)⌉`. -/
theorem headerLog_eq_ceil_logb (n : ℕ) :
    (headerLog n : ℤ) = ⌈Real.logb 2 ((n : ℝ) + 2)⌉ := by
  have h := Real.ceil_logb_natCast (b := 2) (r := ((n + 2 : ℕ) : ℝ)) (by positivity)
  rw [Int.clog_natCast] at h
  push_cast at h
  rw [h, headerLog]

/-- `mergerBudget M E = ⌊⌊√(M E)⌋ / 10⁶⌋`, with the real square root. -/
theorem mergerBudget_eq_floor (M E : ℕ) :
    mergerBudget M E = ⌊(⌊Real.sqrt (M * E)⌋₊ : ℝ) / 10 ^ 6⌋₊ := by
  have h := Real.nat_floor_real_sqrt_eq_nat_sqrt (a := M * E)
  push_cast at h
  rw [h, mergerBudget, ← Nat.floor_div_eq_div (K := ℝ)]
  norm_num

end StrongMerging

end Kolmogorov
