/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.OracleComputability
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Interface.ComputableReals.Part01

/-!
# Relative enumerability and computable real families

The oracle is always the existing total `charOracle`. The typed `PartrecIn` and
`ComputableIn` APIs are imported unchanged. Predicates on possibly undecidable domains
remain predicates on their ambient primcodable types.
-/

namespace Kolmogorov.PointToSet

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

/-- A predicate is relatively enumerable when it is the domain of a relative partial
computation. Blueprint node `oracle:ce`. -/
def IsREIn (A : Set ℕ) (F : α → Prop) : Prop :=
  ∃ f : α →. ℕ, PartrecIn {charOracle A} f ∧ ∀ w, F w ↔ (f w).Dom

/-- A total optional enumeration permits empty sets and idle stages.
Blueprint node `oracle:ce`. -/
def IsEnumerationIn (A : Set ℕ) (F : α → Prop) (e : ℕ → Option α) : Prop :=
  ComputableIn {charOracle A} e ∧ ∀ w, F w ↔ ∃ t, e t = some w

/-- Upper semicomputability on a domain is witnessed by enumerable strict rational
upper bounds, sound on that domain and arbitrarily close to each value. The subtype
does not carry a primcodable instance. Blueprint node `oracle:enumeration`. -/
def IsUpperSemicomputableOnIn (A : Set ℕ) (F : α → Prop) (g : Subtype F → ℝ) : Prop :=
  ∃ U : α × ℚ → Prop, IsREIn A U ∧
    (∀ w q, U (w, q) → ∃ h : F w, g ⟨w, h⟩ < (q : ℝ)) ∧
    ∀ w : Subtype F, ∀ ε : ℝ, 0 < ε →
      ∃ q : ℚ, U (w.val, q) ∧ (q : ℝ) < g w + ε

/-- Uniform lower semicomputability is enumerability of the strict rational lower cut.
Blueprint node `oracle:monotone`. -/
def IsLowerSemicomputableIn (A : Set ℕ) (g : α → ℝ) : Prop :=
  IsREIn A (fun w : α × ℚ => (w.2 : ℝ) < g w.1)

/-- A family of real numbers has relative rational approximations with specified dyadic
error, uniformly in the index and precision. Blueprint node `metric:names`. -/
def IsComputableRealFamilyIn (A : Set ℕ) (v : α → ℝ) : Prop :=
  ∃ q : α × ℕ → ℚ, ComputableIn {charOracle A} q ∧
    ∀ i p, |(q (i, p) : ℝ) - v i| < (2 : ℝ)⁻¹ ^ p

/-- Ordinary partial computability implies relative partial computability for every
total characteristic oracle. Blueprint node `oracle:closure`. -/
theorem relative_closure (A : Set ℕ) (f : α →. β) (hf : Partrec f) :
    PartrecIn {charOracle A} f := by
  exact hf.partrecIn

/-- Pairing relative partial computations preserves relative computability.
Blueprint node `oracle:closure`. -/
theorem relative_closure_pair (A : Set ℕ) (f : α →. β) (g : α →. γ)
    (hf : PartrecIn {charOracle A} f) (hg : PartrecIn {charOracle A} g) :
    PartrecIn {charOracle A} (fun a => (f a).bind fun b => (g a).map fun c => (b, c)) := by
  have H : PartrecIn₂ {charOracle A} (fun (a : α) (b : β) => (g a).map (fun c => (b, c))) := by
    have hg' : PartrecIn₂ {charOracle A} (fun (a : α) (b : β) => g a) := hg.comp ComputableIn.fst
    have hc : ComputableIn₂ {charOracle A} (fun (a : α × β) (c : γ) => (a.2, c)) := by
      exact ComputableIn.pair (ComputableIn.snd.comp ComputableIn.fst) ComputableIn.snd
    exact PartrecIn.map hg' hc
  exact PartrecIn.bind hf H

/-- Composition of relative partial computations preserves relative computability.
Blueprint node `oracle:closure`. -/
theorem relative_closure_comp (A : Set ℕ) (f : α →. β) (g : β →. γ)
    (hf : PartrecIn {charOracle A} f) (hg : PartrecIn {charOracle A} g) :
    PartrecIn {charOracle A} (fun a => (f a).bind g) := by
  have hg2 : PartrecIn₂ {charOracle A} (fun (_ : α) (b : β) => g b) :=
    hg.comp Computable.snd.computableIn
  exact PartrecIn.bind hf hg2

/-- Binding a relative partial computation to a relative binary computation is effective.
Blueprint node `oracle:closure`. -/
theorem relative_closure_bind (A : Set ℕ) (f : α →. β) (g : α → β →. γ)
    (hf : PartrecIn {charOracle A} f) (hg : PartrecIn₂ {charOracle A} g) :
    PartrecIn {charOracle A} (fun a => (f a).bind (g a)) := by
  exact hf.bind hg

/-- Mapping a relative total computation over a relative partial result is effective.
Blueprint node `oracle:closure`. -/
theorem relative_closure_map (A : Set ℕ) (f : α →. β) (g : α → β → γ)
    (hf : PartrecIn {charOracle A} f) (hg : ComputableIn₂ {charOracle A} g) :
    PartrecIn {charOracle A} (fun a => (f a).map (g a)) := by
  exact PartrecIn.map hf hg

/-- Natural recursion with relative partial steps is effective.
Blueprint node `oracle:closure`. -/
theorem relative_closure_nat_rec (A : Set ℕ) (f : α → ℕ) (g : α →. β)
    (h : α → ℕ × β →. β) (hf : ComputableIn {charOracle A} f)
    (hg : PartrecIn {charOracle A} g) (hh : PartrecIn₂ {charOracle A} h) :
    PartrecIn {charOracle A} (fun a =>
      Nat.rec (g a) (fun n ih => ih.bind fun b => h a (n, b)) (f a)) := by
  exact PartrecIn.nat_rec hf hg hh

/-- Relative partial Boolean tests admit unbounded search.
Blueprint node `oracle:closure`. -/
theorem relative_closure_rfind (A : Set ℕ) (p : α → ℕ →. Bool)
    (hp : PartrecIn₂ {charOracle A} p) :
    PartrecIn {charOracle A} (fun a => Nat.rfind (p a)) := by
  exact PartrecIn.rfind hp

/-- A relative total optional family admits search for its first defined value.
Blueprint node `oracle:closure`. -/
theorem relative_closure_rfindOpt (A : Set ℕ) (f : α → ℕ → Option β)
    (hf : ComputableIn₂ {charOracle A} f) :
    PartrecIn {charOracle A} (fun a => Nat.rfindOpt (f a)) := by
  exact PartrecIn.rfindOpt hf

/-- A relative total Boolean test can choose between relative partial computations.
Blueprint node `oracle:closure`. -/
theorem relative_closure_cond (A : Set ℕ) (c : α → Bool) (f g : α →. β)
    (hc : ComputableIn {charOracle A} c) (hf : PartrecIn {charOracle A} f)
    (hg : PartrecIn {charOracle A} g) :
    PartrecIn {charOracle A} (fun a => cond (c a) (f a) (g a)) :=
  PartrecIn.cond hc hf hg

/-- Substitution of relative oracle computations preserves typed relative computability.
Blueprint node `oracle:closure`. -/
theorem relative_closure_subst (O O' : Set (ℕ →. ℕ)) (f : α →. β)
    (hf : PartrecIn O f) (hO : ∀ g ∈ O, RecursiveIn O' g) : PartrecIn O' f := by
  exact RecursiveIn.subst hf hO

/-! ### Closure properties of relatively enumerable predicates -/

/-- The empty predicate is relatively enumerable. -/
theorem isREIn_empty (A : Set ℕ) : IsREIn A (∅ : Set α) :=
  ⟨fun _ ↦ Part.none, PartrecIn.none, fun _ ↦ iff_false_intro id⟩

/-- A predicate with a relatively computable decision procedure is relatively enumerable. -/
theorem isREIn_of_computableIn_decide (A : Set ℕ) (P : α → Prop) [DecidablePred P]
    (h_comp : ComputableIn {charOracle A} (fun x ↦ decide (P x))) :
    IsREIn A P := by
  refine ⟨fun x ↦ cond (decide (P x)) (Part.some 0) Part.none,
    PartrecIn.cond h_comp (ComputableIn.const 0).partrecIn PartrecIn.none, fun x ↦ ?_⟩
  by_cases hx : P x <;> simp [hx]

/-- A decidable predicate with a computable decision procedure is relatively enumerable for
every oracle. -/
theorem isREIn_of_computable_decide {A : Set ℕ} {P : α → Prop} [DecidablePred P]
    (h_comp : Computable (fun x ↦ decide (P x))) : IsREIn A P :=
  isREIn_of_computableIn_decide A P h_comp.computableIn

namespace IsREIn

variable {A : Set ℕ}

/-- The conjunction of two relatively enumerable predicates is relatively enumerable. -/
theorem and {F G : α → Prop} (hF : IsREIn A F) (hG : IsREIn A G) :
    IsREIn A (fun x ↦ F x ∧ G x) := by
  obtain ⟨f, hf, hf_dom⟩ := hF
  obtain ⟨g, hg, hg_dom⟩ := hG
  refine ⟨fun x ↦ (f x).bind fun _ ↦ g x, hf.bind (hg.comp ComputableIn.fst), fun x ↦ ?_⟩
  simp only [Part.bind_dom, exists_prop]
  exact and_congr (hf_dom x) (hg_dom x)

/-- Precomposing a relatively enumerable predicate with a relatively computable map gives a
relatively enumerable predicate. -/
theorem comp {F : β → Prop} (hF : IsREIn A F) {f : α → β}
    (hf : ComputableIn {charOracle A} f) : IsREIn A (fun x ↦ F (f x)) := by
  obtain ⟨g, hg, hdom⟩ := hF
  exact ⟨fun x ↦ g (f x), hg.comp hf, fun x ↦ hdom (f x)⟩

/-- Relative enumerability transfers to every Turing-stronger oracle. -/
theorem mono_oracle {B : Set ℕ} {F : α → Prop} (hF : IsREIn A F)
    (hAB : TuringReducible (charOracle A) (charOracle B)) : IsREIn B F := by
  obtain ⟨f, hf, hdom⟩ := hF
  refine ⟨f, RecursiveIn.subst hf fun g hg ↦ ?_, hdom⟩
  obtain rfl := Set.mem_singleton_iff.mp hg
  exact hAB

end IsREIn

/-- Every set is relatively enumerable for the characteristic oracle of the codes of its
members. -/
theorem isREIn_encode_image (E : Set α) : IsREIn (Encodable.encode '' E) E := by
  let A : Set ℕ := Encodable.encode '' E
  let f : α →. ℕ := fun p ↦
    (charOracle A (Encodable.encode p)).bind fun a ↦ cond (a == 1) (Part.some 0) Part.none
  refine ⟨f, ?_, fun p ↦ ?_⟩
  · have h1 : PartrecIn {charOracle A} (fun p : α ↦ charOracle A (Encodable.encode p)) :=
      PartrecIn.comp (PartrecIn.oracle _ (Set.mem_singleton _)) Computable.encode.computableIn
    have hp : Computable (fun a : ℕ ↦ a == 1) :=
      (Primrec.beq.comp Primrec.id (Primrec.const 1)).to_comp
    have h2 : ComputableIn₂ {charOracle A} (fun (_ : α) (a : ℕ) ↦ a == 1) :=
      (hp.comp Computable.snd).computableIn
    have h3 : PartrecIn₂ {charOracle A}
        (fun (_ : α) (a : ℕ) ↦ cond (a == 1) (Part.some (0 : ℕ)) Part.none) :=
      PartrecIn.cond h2 (ComputableIn.const (0 : ℕ)) PartrecIn.none
    exact relative_closure_bind A _ _ h1 h3
  · classical
    have hmem : Encodable.encode p ∈ A ↔ p ∈ E := Encodable.encode_injective.mem_set_image
    have hc : charOracle A (Encodable.encode p) =
        Part.some (if Encodable.encode p ∈ A then 1 else 0) := rfl
    by_cases h : p ∈ E
    · simp only [f, hc, hmem.mpr h, ↓reduceIte, Part.bind_some]
      exact iff_of_true h trivial
    · have hmem' : Encodable.encode p ∉ A := fun h' ↦ h (hmem.mp h')
      simp only [f, hc, hmem', ↓reduceIte, Part.bind_some, cond_eq_ite, beq_iff_eq,
        zero_ne_one]
      exact iff_of_false h id

/-- Every predicate is relatively enumerable for all oracles above a suitable one: the
characteristic oracle of the codes of its members. -/
theorem exists_oracle_isREIn (R : α → Prop) :
    ∃ C : Set ℕ, ∀ A : Set ℕ, TuringReducible (charOracle C) (charOracle A) → IsREIn A R :=
  ⟨Encodable.encode '' {x | R x}, fun _ hCA ↦ (isREIn_encode_image {x | R x}).mono_oracle hCA⟩

end Kolmogorov.PointToSet

