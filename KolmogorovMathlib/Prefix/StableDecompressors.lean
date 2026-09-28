import KolmogorovMathlib.Interface.ComputableReals
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Complexity.PairComplexity
import KolmogorovMathlib.Complexity.ConditionalComplexity
import KolmogorovMathlib.Complexity.KolmogorovLevin
import KolmogorovMathlib.Complexity.RandomConditions
import KolmogorovMathlib.Complexity.SelfComplexity
import KolmogorovMathlib.Complexity.InfiniteSequences
import KolmogorovMathlib.Complexity.IncompressibleStrings
import KolmogorovMathlib.Complexity.Information
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Prefix.TotalCountingBound
import KolmogorovMathlib.Prefix.KPPairSwap
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Prefix.CondTwoStage
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Rat.Denumerable
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import Mathlib.Computability.Halting
import KolmogorovMathlib.Interface.ComputableReals.LowerSemicomputableReals
import KolmogorovMathlib.AlgorithmicProbability.HaltingProbabilityApproximation

/-!
# Prefix-stable decompressors

The prefix-stable variant of prefix complexity: `IsPrefixStableFun`,
`IsPrefixStableMachine`, `IsPrefixStableDecompressor` and `IsOptimalPrefixStable`, together
with the graph machinery (`stabTriple`) used to build an optimal prefix-stable
decompressor.

SUV Theorem 48, p. 111.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.ComputableReals

/-! ### Prefix-stable decompressors -/

/-- A partial function on strings is *prefix stable* if its value propagates to
all extensions of any string where it is defined. -/
def IsPrefixStableFun (f : BitString →. BitString) : Prop :=
  ∀ x y z : BitString, z ∈ f x → x <+: y → z ∈ f y

/-- A map is a *prefix-stable machine* if it is prefix stable in its program
argument, for every fixed condition. -/
def IsPrefixStableMachine (M : Map) : Prop :=
  ∀ c : BitString, IsPrefixStableFun (fun p => M (p, c))

/-- A *prefix-stable decompressor* is a computable prefix-stable map. -/
def IsPrefixStableDecompressor (M : Map) : Prop :=
  isDecompressor M ∧ IsPrefixStableMachine M

/-- Optimality inside the class of prefix-stable decompressors. -/
def IsOptimalPrefixStable (U : Map) : Prop :=
  IsPrefixStableDecompressor U ∧
    ∀ M, IsPrefixStableDecompressor M → ∃ c : ℕ, ∀ x y, condK U x y ≤ condK M x y + (c : ℕ∞)

/-! ### Machinery for Theorem 48 -/

/-- The stage-`n` triple enumerated by a code: the input pair and the output it produces, when the
code halts at that stage. -/
def stabTriple (code : Code) (n : ℕ) : Option ((BitString × BitString) × BitString) :=
  ((Encodable.decode n.unpair.1 : Option (BitString × BitString))).bind fun qy =>
    (Code.evaln n.unpair.2 code (Encodable.encode qy)).bind fun e =>
      (Encodable.decode e : Option BitString).map fun z => (qy, z)

/-- Enumerating the stage-`n` triple of a code is primitive recursive. -/
theorem stabTriple_primrec : Primrec (fun a : Code × ℕ => stabTriple a.1 a.2) := by
  have hdec : Primrec (fun a : Code × ℕ =>
      (Encodable.decode a.2.unpair.1 : Option (BitString × BitString))) :=
    Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have hevaln : Primrec (fun a : (Code × ℕ) × (BitString × BitString) =>
      Code.evaln a.1.2.unpair.2 a.1.1 (Encodable.encode a.2)) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))).pair
        (Primrec.fst.comp Primrec.fst)).pair (Primrec.encode.comp Primrec.snd))
  have hinner : Primrec₂ (fun (a : (Code × ℕ) × (BitString × BitString)) (e : ℕ) =>
      (Encodable.decode e : Option BitString).map (fun z => (a.2, z))) :=
    (Primrec.option_map (Primrec.decode.comp Primrec.snd)
      ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd).to₂).to₂
  exact Primrec.option_bind hdec (Primrec.option_bind hevaln hinner).to₂

/-- Soundness of `stabTriple`: an entry really comes from a halting computation. -/
theorem stabTriple_sound {code : Code} {n : ℕ} {q y z : BitString}
    (h : stabTriple code n = some ((q, y), z)) :
    ∃ e : ℕ, e ∈ Code.eval code (Encodable.encode (q, y)) ∧
      (Encodable.decode e : Option BitString) = some z := by
  unfold stabTriple at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨qy, hqy, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨e, he, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨z', hz', heq⟩ := h
  have hqy_eq : qy = (q, y) := congrArg Prod.fst heq
  have hz_eq : z' = z := congrArg Prod.snd heq
  subst hqy_eq; subst hz_eq
  exact ⟨e, Nat.Partrec.Code.evaln_sound he, hz'⟩

/-- Completeness of `stabTriple`: every halting computation appears as an entry. -/
theorem stabTriple_complete {code : Code} {q y z : BitString}
    (h : Encodable.encode z ∈ Code.eval code (Encodable.encode (q, y))) :
    ∃ n : ℕ, stabTriple code n = some ((q, y), z) := by
  obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp h
  set E : ℕ := Encodable.encode ((q, y) : BitString × BitString) with hE
  refine ⟨Nat.pair E t, ?_⟩
  have hev : Code.evaln t code E = some (Encodable.encode z) := Option.mem_def.mp ht
  have hdec : (Encodable.decode E : Option (BitString × BitString)) = some (q, y) :=
    Encodable.encodek _
  have hunfold : stabTriple code (Nat.pair E t) =
      (Encodable.decode (Nat.pair E t).unpair.1 : Option (BitString × BitString)).bind fun qy =>
        (Code.evaln (Nat.pair E t).unpair.2 code (Encodable.encode qy)).bind fun e =>
          (Encodable.decode e : Option BitString).map fun z => (qy, z) := rfl
  rw [hunfold, Nat.unpair_pair, hdec]
  change ((Code.evaln t code E).bind fun e =>
    (Encodable.decode e : Option BitString).map fun z => ((q, y), z)) = some ((q, y), z)
  rw [hev]
  change ((Encodable.decode (Encodable.encode z) : Option BitString).map
    fun z' => ((q, y), z')) = some ((q, y), z)
  rw [Encodable.encodek]
  rfl

attribute [irreducible] stabTriple

/-- Turn a `PrimrecPred` into a `Primrec` statement about its `decide`. -/
theorem primrec_decide_of_pred {α : Type*} [Primcodable α] {p : α → Prop}
    [DecidablePred p] (h : PrimrecPred p) : Primrec (fun a => decide (p a)) := by
  exact PrimrecPred.decide h

/-- A disjunction of two negations with a conclusion is the two-premise implication. -/
theorem or_not_or_not_iff_imp_imp (A E D : Prop) :
    (¬ A ∨ ¬ E ∨ D) ↔ (A → E → D) := by
  by_cases hA : A <;> by_cases hE : E <;> by_cases hD : D <;> simp [hA, hE, hD]

/-- The Boolean disjunction of two decisions decides the disjunction. -/
theorem bool_or_decide {B C : Prop} [Decidable B] [Decidable C] :
    (decide B || decide C) = decide (B ∨ C) := by
  by_cases hB : B <;> by_cases hC : C <;> simp [hB, hC]

/-- The Boolean form of a two-premise implication decides that implication. -/
theorem bool_or_not_eq_decide_imp {A E D : Prop} [Decidable A] [Decidable E] [Decidable D] :
    ((!decide A) || ((!decide E) || decide D)) = decide (A → E → D) := by
  by_cases hA : A <;> by_cases hE : E <;> by_cases hD : D <;> simp [hA, hE, hD]

/-- Two graph entries are *compatible* if, having the same condition and
comparable programs, they carry the same output. -/
def stabCompat (t₁ t₂ : (BitString × BitString) × BitString) : Bool :=
  decide (t₁.1.2 = t₂.1.2 →
    (t₁.1.1 = t₂.1.1.take t₁.1.1.length ∨ t₂.1.1 = t₁.1.1.take t₂.1.1.length) →
      t₁.2 = t₂.2)

/-- Two enumerated triples are compatible exactly when, at a common condition, their inputs are
comparable and, when one input extends the other, so do the outputs. -/
theorem stabCompat_iff (t₁ t₂ : (BitString × BitString) × BitString) :
    stabCompat t₁ t₂ = true ↔
      (t₁.1.2 = t₂.1.2 → (t₁.1.1 <+: t₂.1.1 ∨ t₂.1.1 <+: t₁.1.1) → t₁.2 = t₂.2) := by
  simp only [stabCompat, decide_eq_true_eq, List.prefix_iff_eq_take]

/-- Compatibility of two triples is primitive recursive in the pair of triples. -/
theorem stabCompat_primrec :
    Primrec₂ (fun (t₁ t₂ : (BitString × BitString) × BitString) => stabCompat t₁ t₂) := by
  have h1 : Primrec (fun a : ((BitString × BitString) × BitString) ×
      ((BitString × BitString) × BitString) => decide (a.1.1.2 = a.2.1.2)) :=
    primrec_decide_of_pred (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have h2 : Primrec (fun a : ((BitString × BitString) × BitString) ×
      ((BitString × BitString) × BitString) =>
        decide (a.1.1.1 = a.2.1.1.take a.1.1.1.length)) :=
    primrec_decide_of_pred
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.list_take.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
  have h3 : Primrec (fun a : ((BitString × BitString) × BitString) ×
      ((BitString × BitString) × BitString) =>
        decide (a.2.1.1 = a.1.1.1.take a.2.1.1.length)) :=
    primrec_decide_of_pred
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.list_take.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))))
  have h4 : Primrec (fun a : ((BitString × BitString) × BitString) ×
      ((BitString × BitString) × BitString) => decide (a.1.2 = a.2.2)) :=
    primrec_decide_of_pred
      (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  have hall : Primrec (fun a : ((BitString × BitString) × BitString) ×
      ((BitString × BitString) × BitString) =>
        ((!decide (a.1.1.2 = a.2.1.2)) ||
          ((!(decide (a.1.1.1 = a.2.1.1.take a.1.1.1.length) ||
            decide (a.2.1.1 = a.1.1.1.take a.2.1.1.length))) ||
              decide (a.1.2 = a.2.2)))) :=
    Primrec.or.comp (Primrec.not.comp h1)
      (Primrec.or.comp (Primrec.not.comp (Primrec.or.comp h2 h3)) h4)
  refine Primrec.of_eq hall (fun a => ?_)
  rw [bool_or_decide, bool_or_not_eq_decide_imp]
  unfold stabCompat
  exact decide_eq_decide.mpr Iff.rfl

attribute [irreducible] stabCompat

/-- Compatibility of the entries at stages `m` and `n` (vacuously true if one of
them does not exist). -/
def stabPairCompat (code : Code) (n m : ℕ) : Bool :=
  (((stabTriple code m).bind fun t₁ =>
    (stabTriple code n).map fun t₂ => stabCompat t₁ t₂)).getD true

/-- Pairwise compatibility of the stages `n` and `m` of a code follows from compatibility of the
two triples those stages enumerate. -/
theorem stabPairCompat_of {code : Code} {n m : ℕ}
    {t₁ t₂ : (BitString × BitString) × BitString}
    (h₁ : stabTriple code m = some t₁) (h₂ : stabTriple code n = some t₂)
    (h : stabPairCompat code n m = true) : stabCompat t₁ t₂ = true := by
  unfold stabPairCompat at h
  rw [h₁, h₂] at h
  simpa using h

/-- Pairwise compatibility of two stages of a code is primitive recursive. -/
theorem stabPairCompat_primrec :
    Primrec (fun a : Code × ℕ × ℕ => stabPairCompat a.1 a.2.1 a.2.2) := by
  have hm : Primrec (fun a : Code × ℕ × ℕ => stabTriple a.1 a.2.2) :=
    stabTriple_primrec.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))
  have hn : Primrec (fun a : (Code × ℕ × ℕ) × ((BitString × BitString) × BitString) =>
      stabTriple a.1.1 a.1.2.1) :=
    stabTriple_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
  have hbody : Primrec (fun a : (Code × ℕ × ℕ) × ((BitString × BitString) × BitString) =>
      ((stabTriple a.1.1 a.1.2.1).map fun t₂ => stabCompat a.2 t₂)) :=
    Primrec.option_map hn (stabCompat_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hb : Primrec (fun a : Code × ℕ × ℕ =>
      ((stabTriple a.1 a.2.2).bind fun t₁ =>
        (stabTriple a.1 a.2.1).map fun t₂ => stabCompat t₁ t₂)) :=
    Primrec.option_bind hm hbody.to₂
  exact Primrec.option_getD.comp hb (Primrec.const true)

/-- Two stages are pairwise compatible as soon as every pair of triples they enumerate is. -/
theorem stabPairCompat_eq_true (code : Code) (n m : ℕ)
    (h : ∀ t₁ t₂, stabTriple code m = some t₁ → stabTriple code n = some t₂ →
      stabCompat t₁ t₂ = true) : stabPairCompat code n m = true := by
  unfold stabPairCompat
  cases h₁ : stabTriple code m with
  | none => rfl
  | some t₁ =>
    cases h₂ : stabTriple code n with
    | none => rfl
    | some t₂ => simpa using h t₁ t₂ h₁ h₂

attribute [irreducible] stabPairCompat

/-- The entry at stage `n` is *accepted* if it is compatible with all earlier
entries. -/
def stabOK (code : Code) (n : ℕ) : Bool :=
  (List.range n).foldr (fun m r => stabPairCompat code n m && r) true

/-- A conjunction folded over a list holds exactly when it holds at every member of the list. -/
theorem foldr_and_eq_true {l : List ℕ} {f : ℕ → Bool} :
    (l.foldr (fun m r => f m && r) true) = true ↔ ∀ m ∈ l, f m = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Bool.and_eq_true, ih]

/-- Stage `n` of a code passes the filter exactly when it is compatible with every earlier stage. -/
theorem stabOK_eq_true_iff (code : Code) (n : ℕ) :
    stabOK code n = true ↔ ∀ m < n, stabPairCompat code n m = true := by
  simp [stabOK, foldr_and_eq_true]

/-- The stage filter `stabOK` is primitive recursive in the code and the stage index. -/
theorem stabOK_primrec : Primrec (fun a : Code × ℕ => stabOK a.1 a.2) := by
  have hrange : Primrec (fun a : Code × ℕ => List.range a.2) :=
    Primrec.list_range.comp Primrec.snd
  have hstep : Primrec₂ (fun (a : Code × ℕ) (p : ℕ × Bool) =>
      stabPairCompat a.1 a.2 p.1 && p.2) :=
    (Primrec.and.comp
      (stabPairCompat_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr hrange (Primrec.const true) hstep

attribute [irreducible] stabOK

/-- The value an entry contributes on the program/condition pair `py`. -/
def stabSelect (py : BitString × BitString) (t : (BitString × BitString) × BitString) :
    Option BitString :=
  cond (decide (t.1.2 = py.2) && decide (t.1.1 = py.1.take t.1.1.length)) (some t.2) none

/-- An enumerated triple contributes the output `z` to the input pair exactly when the conditions
agree, the enumerated input is a prefix of the given one, and the output is `z`. -/
theorem stabSelect_eq_some_iff {py : BitString × BitString}
    {t : (BitString × BitString) × BitString} {z : BitString} :
    stabSelect py t = some z ↔ t.1.2 = py.2 ∧ t.1.1 <+: py.1 ∧ t.2 = z := by
  unfold stabSelect
  by_cases hb : (decide (t.1.2 = py.2) && decide (t.1.1 = py.1.take t.1.1.length)) = true
  · rw [hb]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    simp only [cond_true, Option.some.injEq]
    constructor
    · intro h; exact ⟨hb.1, List.prefix_iff_eq_take.mpr hb.2, h⟩
    · rintro ⟨-, -, h⟩; exact h
  · rw [Bool.not_eq_true] at hb
    rw [hb]
    simp only [cond_false, reduceCtorEq, false_iff]
    rintro ⟨h1, h2, -⟩
    have hb' : (decide (t.1.2 = py.2) && decide (t.1.1 = py.1.take t.1.1.length)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h1, List.prefix_iff_eq_take.mp h2⟩
    rw [hb'] at hb
    exact absurd hb (by simp)

/-- Selecting the contribution of a triple is primitive recursive. -/
theorem stabSelect_primrec : Primrec₂ stabSelect := by
  have h1 : Primrec (fun a : (BitString × BitString) × ((BitString × BitString) × BitString) =>
      decide (a.2.1.2 = a.1.2)) :=
    primrec_decide_of_pred (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst))
  have h2 : Primrec (fun a : (BitString × BitString) × ((BitString × BitString) × BitString) =>
      decide (a.2.1.1 = a.1.1.take a.2.1.1.length)) :=
    primrec_decide_of_pred
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.list_take.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))))
  exact (Primrec.cond (Primrec.and.comp h1 h2)
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)).to₂

/-- The value contributed by stage `n` to the stabilised machine. -/
def stabFind (code : Code) (p y : BitString) (n : ℕ) : Option BitString :=
  cond (stabOK code n) ((stabTriple code n).bind (stabSelect (p, y))) none

/-- The search finds `z` at stage `n` exactly when that stage enumerates a filtered triple whose
input is a prefix of the given one and whose output is `z`. -/
theorem stabFind_eq_some_iff {code : Code} {p y : BitString} {n : ℕ} {z : BitString} :
    stabFind code p y n = some z ↔
      ∃ q : BitString, stabTriple code n = some ((q, y), z) ∧ stabOK code n = true ∧ q <+: p := by
  unfold stabFind
  by_cases hok : stabOK code n = true
  · have hc : (cond (stabOK code n) ((stabTriple code n).bind (stabSelect (p, y)))
        none : Option BitString) = (stabTriple code n).bind (stabSelect (p, y)) := by
      rw [hok]; rfl
    rw [hc]
    constructor
    · intro h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, hsel⟩ := h
      rw [stabSelect_eq_some_iff] at hsel
      obtain ⟨hy, hpre, hz⟩ := hsel
      have hy' : t.1.2 = y := hy
      have hpre' : t.1.1 <+: p := hpre
      refine ⟨t.1.1, ?_, hok, hpre'⟩
      rw [ht]
      have ht' : t = ((t.1.1, y), z) := by rw [← hy', ← hz]
      rw [ht']
    · rintro ⟨q, ht, -, hpre⟩
      rw [Option.bind_eq_some_iff]
      exact ⟨((q, y), z), ht, stabSelect_eq_some_iff.mpr ⟨rfl, hpre, rfl⟩⟩
  · rw [Bool.not_eq_true] at hok
    have hc : (cond (stabOK code n) ((stabTriple code n).bind (stabSelect (p, y)))
        none : Option BitString) = none := by rw [hok]; rfl
    rw [hc]
    simp only [reduceCtorEq, false_iff, not_exists]
    rintro q ⟨-, hok', -⟩
    rw [hok] at hok'
    exact Bool.false_ne_true hok'

/-- The stagewise search is primitive recursive. -/
theorem stabFind_primrec :
    Primrec (fun a : (Code × BitString × BitString) × ℕ =>
      stabFind a.1.1 a.1.2.1 a.1.2.2 a.2) := by
  have htr : Primrec (fun a : (Code × BitString × BitString) × ℕ =>
      stabTriple a.1.1 a.2) :=
    stabTriple_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have hok : Primrec (fun a : (Code × BitString × BitString) × ℕ => stabOK a.1.1 a.2) :=
    stabOK_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have hsel : Primrec₂ (fun (a : (Code × BitString × BitString) × ℕ)
      (t : (BitString × BitString) × BitString) => stabSelect (a.1.2.1, a.1.2.2) t) :=
    (stabSelect_primrec.comp
      (((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))) Primrec.snd).to₂
  exact Primrec.cond hok (Primrec.option_bind htr hsel) (Primrec.const none)

attribute [irreducible] stabFind

/-- The *stabilisation* of the machine with code `code`. -/
def stabMap (code : Code) : Map := fun pr =>
  (Nat.rfind fun n => Part.some (stabFind code pr.1 pr.2 n).isSome).bind fun n =>
    (↑(stabFind code pr.1 pr.2 n) : Part BitString)

/-- The filtered machine of a code is partial computable uniformly in the code. -/
theorem stabMap_partrec_uniform :
    Partrec (fun a : Code × BitString × BitString => stabMap a.1 (a.2.1, a.2.2)) :=
  Partrec.bind
    (Partrec.rfind (Computable.to₂
      ((Primrec.option_isSome.comp stabFind_primrec).to_comp)).partrec₂)
    (Computable.ofOption stabFind_primrec.to_comp).to₂

/-- Two stages of the stabilised machine that both fire on the same program and
condition give the same value. -/
theorem stabFind_unique {code : Code} {p y : BitString} {n₁ n₂ : ℕ} {z₁ z₂ : BitString}
    (h₁ : stabFind code p y n₁ = some z₁) (h₂ : stabFind code p y n₂ = some z₂) :
    z₁ = z₂ := by
  rw [stabFind_eq_some_iff] at h₁ h₂
  obtain ⟨q₁, ht₁, hok₁, hpre₁⟩ := h₁
  obtain ⟨q₂, ht₂, hok₂, hpre₂⟩ := h₂
  have hcomp : q₁ <+: q₂ ∨ q₂ <+: q₁ := List.prefix_or_prefix_of_prefix hpre₁ hpre₂
  rcases lt_trichotomy n₁ n₂ with hlt | heq | hgt
  · have hpc := (stabOK_eq_true_iff code n₂).mp hok₂ n₁ hlt
    have hcc := stabPairCompat_of ht₁ ht₂ hpc
    exact (stabCompat_iff _ _).mp hcc rfl hcomp
  · subst heq
    rw [ht₁] at ht₂
    exact (Prod.mk.injEq _ _ _ _ ▸ Option.some.inj ht₂).2
  · have hpc := (stabOK_eq_true_iff code n₁).mp hok₁ n₂ hgt
    have hcc := stabPairCompat_of ht₂ ht₁ hpc
    exact ((stabCompat_iff _ _).mp hcc rfl hcomp.symm).symm

/-- A value found by the stagewise search is a value of the filtered machine. -/
theorem stabMap_mem_of_find {code : Code} {p y z : BitString} {n : ℕ}
    (h : stabFind code p y n = some z) : z ∈ stabMap code (p, y) := by
  have hcheck : (stabFind code p y n).isSome = true := by rw [h]; rfl
  have hrdom : (Nat.rfind (fun m => Part.some (stabFind code p y m).isSome)).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨n, by rw [Part.mem_some_iff, hcheck], fun {m} _ => Part.some_dom _⟩
  obtain ⟨n', hn'⟩ := Part.dom_iff_mem.mp hrdom
  have hsome : (stabFind code p y n').isSome = true := by
    have h2 := (Nat.mem_rfind.mp hn').1
    rw [Part.mem_some_iff] at h2
    exact h2.symm
  obtain ⟨z', hz'⟩ := Option.isSome_iff_exists.mp hsome
  have hzz : z' = z := stabFind_unique hz' h
  subst hzz
  unfold stabMap
  rw [Part.mem_bind_iff]
  exact ⟨n', hn', by rw [Part.mem_ofOption]; exact Option.mem_def.mpr hz'⟩

/-- Every value of the filtered machine is found by the stagewise search at some stage. -/
theorem stabMap_mem_imp_find {code : Code} {p y z : BitString}
    (h : z ∈ stabMap code (p, y)) : ∃ n : ℕ, stabFind code p y n = some z := by
  unfold stabMap at h
  rw [Part.mem_bind_iff] at h
  obtain ⟨n, -, hn⟩ := h
  rw [Part.mem_ofOption] at hn
  exact ⟨n, Option.mem_def.mp hn⟩

/-- Every stabilised machine is prefix stable. -/
theorem stabMap_isPrefixStableMachine (code : Code) :
    IsPrefixStableMachine (stabMap code) := by
  intro y p p' z hz hpre
  obtain ⟨n, hn⟩ := stabMap_mem_imp_find hz
  rw [stabFind_eq_some_iff] at hn
  obtain ⟨q, htriple, hok, hq⟩ := hn
  exact stabMap_mem_of_find (stabFind_eq_some_iff.mpr ⟨q, htriple, hok, hq.trans hpre⟩)

/-- The entries of a code computing `V` really record computations of `V`. -/
theorem stabTriple_produces {V : Map} {code : Code}
    (hc : code.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (V a)))
    {n : ℕ} {q y z : BitString} (h : stabTriple code n = some ((q, y), z)) :
    produces V q y z := by
  obtain ⟨e, he, hdec⟩ := stabTriple_sound h
  rw [hc, Part.mem_bind_iff] at he
  obtain ⟨a, ha, hmap⟩ := he
  rw [Part.mem_ofOption] at ha
  have ha' : a = (q, y) := by
    apply Option.some.inj
    rw [← Option.mem_def.mp ha, Encodable.encodek]
  subst ha'
  rw [Part.mem_map_iff] at hmap
  obtain ⟨w, hw, hwe⟩ := hmap
  have hwz : w = z := by
    apply Option.some.inj
    rw [← hdec, ← hwe, Encodable.encodek]
  subst hwz
  exact hw

/-- Every computation of `V` appears among the entries of a code computing `V`. -/
theorem exists_stabTriple_of_produces {V : Map} {code : Code}
    (hc : code.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (V a)))
    {q y z : BitString} (h : produces V q y z) :
    ∃ n : ℕ, stabTriple code n = some ((q, y), z) := by
  refine stabTriple_complete ?_
  rw [hc]
  simp only [Part.mem_bind_iff]
  exact ⟨(q, y), by simp, Part.mem_map Encodable.encode h⟩

/-- If the underlying machine is prefix stable, no entry is ever rejected. -/
theorem stabOK_of_prefixStable {V : Map} {code : Code}
    (hc : code.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (V a)))
    (hV : IsPrefixStableMachine V) (n : ℕ) : stabOK code n = true := by
  rw [stabOK_eq_true_iff]
  intro m _
  refine stabPairCompat_eq_true code n m (fun t₁ t₂ h₁ h₂ => ?_)
  rw [stabCompat_iff]
  intro hy hcomp
  obtain ⟨⟨q₁, y₁⟩, z₁⟩ := t₁
  obtain ⟨⟨q₂, y₂⟩, z₂⟩ := t₂
  simp only at hy hcomp ⊢
  subst hy
  have hp₁ := stabTriple_produces hc h₁
  have hp₂ := stabTriple_produces hc h₂
  rcases hcomp with h12 | h21
  · exact Part.mem_unique (hV y₁ q₁ q₂ z₁ hp₁ h12) hp₂
  · exact Part.mem_unique hp₁ (hV y₁ q₂ q₁ z₂ hp₂ h21)

/-- The stabilisation of a prefix-stable machine is at least as good as the
machine itself. -/
theorem condK_stabMap_le {V : Map} {code : Code}
    (hc : code.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (V a)))
    (hV : IsPrefixStableMachine V) (x y : BitString) :
    condK (stabMap code) x y ≤ condK V x y := by
  refine sInf_le_sInf fun n hn => ?_
  obtain ⟨p, hp, rfl⟩ := hn
  obtain ⟨m, htriple⟩ := exists_stabTriple_of_produces hc hp
  have hfind : stabFind code p y m = some x :=
    stabFind_eq_some_iff.mpr ⟨p, htriple, stabOK_of_prefixStable hc hV m, List.prefix_refl p⟩
  exact ⟨p, stabMap_mem_of_find hfind, rfl⟩

/-! #### The universal prefix-stable decompressor -/

/-- The universal prefix-stable decompressor: the program is read as a unary
index (terminated by a `false` bit) followed by the program for the stabilisation
of the machine with that index. -/
def stabUniversal : Map := fun pr =>
  (Part.ofOption (if (pr.1.takeWhile id).length < pr.1.length then
      (Encodable.decode (pr.1.takeWhile id).length : Option Code) else none)).bind
    fun code => stabMap code (pr.1.drop ((pr.1.takeWhile id).length + 1), pr.2)

/-- The universal prefix-stable machine is partial computable. -/
theorem stabUniversal_partrec : Partrec stabUniversal := by
  have hi : Primrec (fun pr : BitString × BitString => (pr.1.takeWhile id).length) :=
    Primrec.list_length.comp ((Primrec.list_takeWhile Primrec.id).comp Primrec.fst)
  have hlen : Primrec (fun pr : BitString × BitString => pr.1.length) :=
    Primrec.list_length.comp Primrec.fst
  have hif : Primrec (fun pr : BitString × BitString =>
      if (pr.1.takeWhile id).length < pr.1.length then
        (Encodable.decode (pr.1.takeWhile id).length : Option Code) else none) :=
    Primrec.ite (Primrec.nat_lt.comp hi hlen) (Primrec.decode.comp hi) (Primrec.const none)
  have harg : Computable (fun a : (BitString × BitString) × Code =>
      (a.2, (a.1.1.drop ((a.1.1.takeWhile id).length + 1), a.1.2))) :=
    (Primrec.snd.pair
      ((Primrec.list_drop.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp (hi.comp Primrec.fst))).pair
          (Primrec.snd.comp Primrec.fst))).to_comp
  exact Partrec.bind (Computable.ofOption hif.to_comp)
    ((stabMap_partrec_uniform.comp harg).to₂)

/-- If the initial run of ones of `l` stops inside `l`, then every extension of `l` has the same
initial run of ones. -/
theorem takeWhile_eq_of_prefix {l l' : BitString} (hpre : l <+: l')
    (h : (l.takeWhile id).length < l.length) :
    l'.takeWhile id = l.takeWhile id := by
  obtain ⟨r, rfl⟩ := hpre
  rw [List.takeWhile_append]
  rw [if_neg (by omega)]

/-- The universal machine is prefix-stable: on comparable inputs with the same condition its
outputs are comparable. -/
theorem stabUniversal_isPrefixStableMachine : IsPrefixStableMachine stabUniversal := by
  intro y p p' z hz hpre
  unfold stabUniversal at hz ⊢
  rw [Part.mem_bind_iff] at hz ⊢
  obtain ⟨code, hcode, hzmem⟩ := hz
  rw [Part.mem_ofOption] at hcode
  by_cases hlt : (p.takeWhile id).length < p.length
  · rw [if_pos hlt] at hcode
    have hsame : p'.takeWhile id = p.takeWhile id := takeWhile_eq_of_prefix hpre hlt
    have hlt' : (p'.takeWhile id).length < p'.length := by
      have hlen : p.length ≤ p'.length := hpre.length_le
      rw [hsame]
      omega
    obtain ⟨r, hr⟩ := hpre
    have hdrop : p'.drop ((p'.takeWhile id).length + 1)
        = p.drop ((p.takeWhile id).length + 1) ++ r := by
      rw [hsame, ← hr]
      exact List.drop_append_of_le_length (by omega)
    refine ⟨code, ?_, ?_⟩
    · rw [Part.mem_ofOption, if_pos hlt', hsame]
      exact hcode
    · rw [hdrop]
      exact stabMap_isPrefixStableMachine code y _ _ z hzmem ⟨r, rfl⟩
  · rw [if_neg hlt] at hcode
    exact absurd hcode (by simp)

/-- On an input prefixed by the unary code of `code`, the universal machine behaves as the
filtered machine of that code. -/
theorem stabUniversal_apply (code : Code) (p y : BitString) :
    stabUniversal (unaryPrefix (Encodable.encode code) ++ p, y) = stabMap code (p, y) := by
  have hlenTake : ((unaryPrefix (Encodable.encode code) ++ p).takeWhile id).length
      = Encodable.encode code := takeWhile_unaryPrefix _ _
  have hlt : ((unaryPrefix (Encodable.encode code) ++ p).takeWhile id).length
      < (unaryPrefix (Encodable.encode code) ++ p).length := by
    rw [hlenTake, List.length_append, length_unaryPrefix]
    omega
  unfold stabUniversal
  simp only [hlenTake, Encodable.encodek, drop_unaryPrefix]
  rw [if_pos (show Encodable.encode code < (unaryPrefix (Encodable.encode code) ++ p).length by
    rw [List.length_append, length_unaryPrefix]; omega)]
  simp

/-- **Theorem 48.** There is an optimal prefix-stable decompressor. -/
theorem exists_optimal_prefixStable_decompressor : ∃ U : Map, IsOptimalPrefixStable U := by
  refine ⟨stabUniversal, ⟨stabUniversal_partrec, stabUniversal_isPrefixStableMachine⟩, ?_⟩
  intro M hM
  obtain ⟨code, hc⟩ := Nat.Partrec.Code.exists_code.mp hM.1
  refine ⟨(unaryPrefix (Encodable.encode code)).length, fun x y => ?_⟩
  have hstep : condK (stabMap code) x y + ((unaryPrefix (Encodable.encode code)).length : ENat)
      ≤ condK M x y + ((unaryPrefix (Encodable.encode code)).length : ENat) := by
    gcongr
    exact condK_stabMap_le hc hM.2 x y
  refine le_trans ?_ hstep
  apply sInfLeSInfAdd
  rintro len_p ⟨p, hp_out, rfl⟩
  refine ⟨(programLength (unaryPrefix (Encodable.encode code) ++ p) : ENat), ?_, ?_⟩
  · refine ⟨unaryPrefix (Encodable.encode code) ++ p, ?_, rfl⟩
    change x ∈ stabUniversal _
    rw [stabUniversal_apply]
    exact hp_out
  · dsimp [programLength]
    rw [List.length_append]
    push_cast
    rw [add_comm]

/-- Candidate output from running `code` on prefixes of `p` at fuel `n.unpair.2`. -/
def prefixExtensionOut (code : Code) (p c : BitString) (n : ℕ) : Option BitString :=
  if decide (n.unpair.1 ≤ p.length) then
    (Code.evaln n.unpair.2 code (Encodable.encode (p.take n.unpair.1, c))).bind
      (fun e => Encodable.decode e)
  else
    none

/-- Halting check for the prefix extension search. -/
def prefixExtensionCheck (code : Code) (p c : BitString) (n : ℕ) : Bool :=
  (prefixExtensionOut code p c n).isSome

/-- The prefix extension decompressor map. -/
def prefixExtensionMap (code : Code) : Map := fun pr =>
  (Nat.rfind (fun n => Part.some (prefixExtensionCheck code pr.1 pr.2 n))).bind
    (fun n => (↑(prefixExtensionOut code pr.1 pr.2 n) : Part BitString))

/-- The stagewise output of the prefix extension of a code is computable. -/
theorem prefixExtensionOut_computable (code : Code) :
    Computable (fun p : (BitString × BitString) × ℕ =>
      prefixExtensionOut code p.1.1 p.1.2 p.2) := by
  have h1 : Computable (fun p : (BitString × BitString) × ℕ =>
      decide (p.2.unpair.1 ≤ p.1.1.length)) := by
    have h1 : Computable (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
      obtain ⟨_, h⟩ := Primrec.nat_le
      exact Computable.of_eq h.to_comp (fun p => by congr)
    convert h1.comp
        ( Computable.fst.comp ( Computable.unpair.comp ( Computable.snd ) ) |> Computable.pair <|
            Computable.list_length.comp ( Computable.fst.comp Computable.fst ) ) using 1
  have h2 : Computable (fun p : (BitString × BitString) × ℕ =>
      (Code.evaln p.2.unpair.2 code (Encodable.encode (p.1.1.take p.2.unpair.1, p.1.2))).bind
        (fun e => (Encodable.decode e : Option BitString))) := by
    have h_take : Computable₂ (fun (w : BitString) (n : ℕ) => w.take n) :=
      primrec_list_take.to_comp
    have h_evaln : Computable₂ (fun (n : ℕ) (m : ℕ) => Code.evaln n code m) :=
      evaln_fixed_computable code
    have h_enc : Computable (fun p : (BitString × BitString) × ℕ =>
        Encodable.encode (p.1.1.take p.2.unpair.1, p.1.2)) := by
      exact Computable.encode.comp
        (Computable.pair
          (h_take.comp (Computable.fst.comp Computable.fst)
            (Computable.fst.comp (Computable.unpair.comp Computable.snd)))
          (Computable.snd.comp Computable.fst))
    have h_eval_call : Computable (fun p : (BitString × BitString) × ℕ =>
        Code.evaln p.2.unpair.2 code (Encodable.encode (p.1.1.take p.2.unpair.1, p.1.2))) := by
      exact h_evaln.comp (Computable.snd.comp (Computable.unpair.comp Computable.snd)) h_enc
    exact Computable.option_bind h_eval_call (Computable.decode.comp Computable.snd)
  convert Computable.cond h1 h2 (Computable.const none) using 1
  exact funext fun p => by
    unfold prefixExtensionOut; cases decide (p.2.unpair.1 ≤ p.1.1.length) <;> rfl

/-- The stagewise admissibility check of the prefix extension is computable. -/
theorem prefixExtensionCheck_computable (code : Code) :
    Computable (fun p : (BitString × BitString) × ℕ =>
      prefixExtensionCheck code p.1.1 p.1.2 p.2) := by
  unfold prefixExtensionCheck
  exact Primrec.to_comp Primrec.option_isSome |> Computable.comp <|
    prefixExtensionOut_computable code

/-- The prefix extension of a code is partial computable. -/
theorem prefixExtensionMap_partrec (code : Code) :
    Partrec (prefixExtensionMap code) := by
  exact Partrec.bind
    (Partrec.rfind (Computable.to₂ (prefixExtensionCheck_computable code)).partrec₂)
    (Computable.ofOption (prefixExtensionOut_computable code)).to₂

/-- Every value of the prefix extension is a value the underlying machine produces on a prefix of
the input. -/
theorem prefixExtensionMap_mem_imp_produces {V : Map} {code : Code}
    (hc : code.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (V a)))
    {p c z : BitString} (hz : z ∈ prefixExtensionMap code (p, c)) :
    ∃ p', p' <+: p ∧ produces V p' c z := by
  obtain ⟨n, hn_rfind, hn_z⟩ : ∃ n,
      n ∈ Nat.rfind (fun n => Part.some (prefixExtensionCheck code p c n)) ∧
      z ∈ (↑(prefixExtensionOut code p c n) : Part BitString) := by
    unfold prefixExtensionMap at hz
    rw [Part.mem_bind_iff] at hz
    exact hz
  have hz1 : prefixExtensionOut code p c n = some z := Part.mem_ofOption.mp hn_z
  unfold prefixExtensionOut at hz1
  by_cases hlen : n.unpair.1 ≤ p.length
  · have hdec : decide (n.unpair.1 ≤ p.length) = true := decide_eq_true hlen
    rw [hdec] at hz1
    simp only [if_true] at hz1
    rw [Option.bind_eq_some_iff] at hz1
    obtain ⟨e, he_eval, he_dec⟩ := hz1
    refine ⟨p.take n.unpair.1, List.take_prefix _ _, ?_⟩
    have h_eval_sound := Nat.Partrec.Code.evaln_sound he_eval
    rw [hc, Part.mem_bind_iff] at h_eval_sound
    obtain ⟨input', hinput, houtput⟩ := h_eval_sound
    rw [Part.mem_ofOption] at hinput
    have hinput_eq : input' = (p.take n.unpair.1, c) := by
      apply Option.some.inj
      rw [← hinput, Encodable.encodek]
    subst input'
    rw [Part.mem_map_iff] at houtput
    obtain ⟨output', hmem, hencode⟩ := houtput
    have houtput_eq : output' = z := by
      apply Option.some.inj
      rw [← he_dec, ← hencode, Encodable.encodek]
    subst output'
    exact hmem
  · have hdec : decide (n.unpair.1 ≤ p.length) = false := decide_eq_false hlen
    rw [hdec] at hz1
    contradiction

/-- The prefix extension of a prefix machine is prefix-stable. -/
theorem prefixExtensionMap_isPrefixStableMachine {V : Map} {code : Code}
    (hc : code.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (V a)))
    (hV : IsPrefixMachine V) :
    IsPrefixStableMachine (prefixExtensionMap code) := by
  intro c p q z hz hpre
  obtain ⟨p', hp'pre, hp'prod⟩ := prefixExtensionMap_mem_imp_produces hc hz
  have hp'q : p' <+: q := hp'pre.trans hpre
  have hmem : Encodable.encode z ∈ code.eval (Encodable.encode (p', c)) := by
    rw [hc]; simp only [Part.mem_bind_iff]
    exact ⟨(p', c), by simp, Part.mem_map Encodable.encode hp'prod⟩
  obtain ⟨t, ht⟩ : ∃ t, Code.evaln t code (Encodable.encode (p', c))
      = some (Encodable.encode z) := by
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
    exact ⟨k, Option.mem_def.mp hk⟩
  have hn_out : prefixExtensionOut code q c (Nat.pair p'.length t) = some z := by
    unfold prefixExtensionOut
    simp only [Nat.unpair_pair]
    have hlen : p'.length ≤ q.length := hp'q.length_le
    have hdec : decide (p'.length ≤ q.length) = true := decide_eq_true hlen
    obtain ⟨r, hr⟩ := hp'q
    subst hr
    rw [hdec]
    simp only [if_true, List.take_left, ht, Option.bind_some, Encodable.encodek]
  have hcheck : prefixExtensionCheck code q c (Nat.pair p'.length t) = true := by
    unfold prefixExtensionCheck
    rw [hn_out]
    rfl
  have hrdom : (Nat.rfind (fun m => Part.some (prefixExtensionCheck code q c m))).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨Nat.pair p'.length t, by rw [Part.mem_some_iff, hcheck], fun {m} _ => Part.some_dom _⟩
  obtain ⟨n', hn'⟩ := Part.dom_iff_mem.mp hrdom
  have hcheck' : prefixExtensionCheck code q c n' = true := by
    have h := (Nat.mem_rfind.mp hn').1
    rw [Part.mem_some_iff] at h
    exact h.symm
  have hsome : (prefixExtensionOut code q c n').isSome = true := hcheck'
  obtain ⟨z', hz'⟩ := Option.isSome_iff_exists.mp hsome
  have hmem_q : z' ∈ prefixExtensionMap code (q, c) := by
    unfold prefixExtensionMap
    rw [Part.mem_bind_iff]
    exact ⟨n', hn', by rw [Part.mem_ofOption]; exact Option.mem_def.mpr hz'⟩
  obtain ⟨p'', hp''q, hp''prod⟩ := prefixExtensionMap_mem_imp_produces hc hmem_q
  have hcomp : p' <+: p'' ∨ p'' <+: p' := by
    rcases List.prefix_or_prefix_of_prefix hp'q hp''q with h1 | h2
    · exact Or.inl h1
    · exact Or.inr h2
  have hp_eq : p' = p'' := by
    rcases hcomp with h1 | h2
    · exact IsPrefixMachine.eq_of_prefix hV hp'prod hp''prod h1
    · exact (IsPrefixMachine.eq_of_prefix hV hp''prod hp'prod h2).symm
  subst hp_eq
  have hz_eq : z = z' := Part.mem_unique hp'prod hp''prod
  subst hz_eq
  exact hmem_q

end Kolmogorov
