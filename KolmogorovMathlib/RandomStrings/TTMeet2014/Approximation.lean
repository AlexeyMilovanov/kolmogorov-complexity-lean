/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.TruthTable

/-!
# Stage approximations (§4 of the paper: "every `R_{K_U}` is `Δ⁰₂`")

If the complement of an oracle `R` is c.e., it has a monotone primitive recursive enumeration
(`exists_mono_stage`, `IsCoEnum`).  If moreover `X ≤_tt R` through a generator `g`, then evaluating
the table on the stage approximation of the oracle gives a computable approximation of `X`
(`approximation_of_tt`).  The approximation is only used on the actual oracle `R_U`, for the fixed
`U` of the hypothesis.  So the argument for Theorem 4.1 needs only one machine at this point: `X` is
`Δ⁰₂` as soon as it is tt-reducible to some `R_U`.
-/

namespace Kolmogorov.RandomStrings.TTMeet

/-- A monotone primitive recursive enumeration of the complement of the oracle `R`. -/
structure IsCoEnum (f : ℕ → Str → Bool) (R : Set Str) : Prop where
  /-- The stage approximation is primitive recursive. -/
  primrec : Primrec fun p : ℕ × Str => f p.1 p.2
  /-- What has left the oracle does not come back. -/
  mono : ∀ {s s' : ℕ} {z : Str}, s ≤ s' → f s z = true → f s' z = true
  /-- The limit is the complement of the oracle. -/
  spec : ∀ z, z ∉ R ↔ ∃ s, f s z = true

/-- A c.e. predicate has a monotone primitive recursive stage approximation: the code of the
semi-decision procedure halts within `s` steps. -/
theorem exists_mono_stage {β : Type*} [Primcodable β] {P : β → Prop} (hP : REPred P) :
    ∃ f : ℕ → β → Bool, Primrec (fun p : ℕ × β => f p.1 p.2) ∧
      (∀ {s s' : ℕ} {b : β}, s ≤ s' → f s b = true → f s' b = true) ∧
      ∀ b, P b ↔ ∃ s, f s b = true := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hP
  refine ⟨fun s b => (Nat.Partrec.Code.evaln s c (Encodable.encode b)).isSome, ?_, ?_, fun b => ?_⟩
  · exact Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
      ((Primrec.fst.pair (Primrec.const c)).pair (Primrec.encode.comp Primrec.snd)))
  · intro s s' b hs h
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 h
    exact Option.isSome_iff_exists.2 ⟨y, Nat.Partrec.Code.evaln_mono hs hy⟩
  · have key : (Nat.Partrec.Code.eval c (Encodable.encode b)).Dom ↔ P b := by
      rw [hc]
      simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
      exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩
    rw [← key]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.1 (Part.get_mem h)
      exact ⟨k, Option.isSome_iff_exists.2 ⟨_, hk⟩⟩
    · rintro ⟨k, hk⟩
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hk
      exact Part.dom_iff_mem.2 ⟨y, Nat.Partrec.Code.evaln_sound hy⟩

/-- The value of a clause is a right fold over its literals, as used by `holds_primrec`. -/
theorem holds_eq_foldr (c : Clause) (o : Str → Bool) :
    c.holds o = c.foldr (fun l b => (o l.1 == l.2) && b) true := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [Clause.holds, List.all_cons, List.foldr_cons] at ih ⊢
    rw [ih]

/-- The value of a table is a right fold over its clauses, as used by `evalB_primrec`. -/
theorem evalB_eq_foldr (t : TTable) (o : Str → Bool) :
    t.evalB o = t.foldr (fun c b => c.holds o || b) false := by
  induction t with
  | nil => rfl
  | cons c t ih =>
    simp only [TTable.evalB, List.any_cons, List.foldr_cons] at ih ⊢
    rw [ih]

/-- A clause evaluates primitive recursively in a primitive recursive oracle. -/
theorem holds_primrec {γ : Type*} [Primcodable γ] {o : γ → Str → Bool}
    (ho : Primrec fun q : γ × Str => o q.1 q.2) :
    Primrec fun q : γ × Clause => q.2.holds (o q.1) := by
  have h : Primrec fun r : (γ × Clause) × ((Str × Bool) × Bool) =>
      (o r.1.1 r.2.1.1 == r.2.1.2) && r.2.2 :=
    Primrec.and.comp
      (Primrec.beq.comp
        (ho.comp ((Primrec.fst.comp Primrec.fst).pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.snd (Primrec.const true) h.to₂).of_eq fun q =>
    (holds_eq_foldr q.2 (o q.1)).symm

/-- A table evaluates primitive recursively in a primitive recursive oracle. -/
theorem evalB_primrec {γ : Type*} [Primcodable γ] {o : γ → Str → Bool}
    (ho : Primrec fun q : γ × Str => o q.1 q.2) :
    Primrec fun q : γ × TTable => q.2.evalB (o q.1) := by
  have hc : Primrec fun r : (γ × TTable) × (Clause × Bool) => r.2.1.holds (o r.1.1) :=
    (holds_primrec ho).comp
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))
  have h : Primrec fun r : (γ × TTable) × (Clause × Bool) => r.2.1.holds (o r.1.1) || r.2.2 :=
    Primrec.or.comp hc (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.snd (Primrec.const false) h.to₂).of_eq fun q =>
    (evalB_eq_foldr q.2 (o q.1)).symm

/-- At a late stage the approximation is correct on any finite list. -/
theorem exists_stage_correct {f : ℕ → Str → Bool} {R : Set Str} (hf : IsCoEnum f R) (L : List Str) :
    ∃ s₀, ∀ s ≥ s₀, ∀ z ∈ L, (!(f s z)) = chi R z := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons a L ih =>
    obtain ⟨s₁, hs₁⟩ := ih
    have hstage : ∃ s₂, ∀ s ≥ s₂, (!(f s a)) = chi R a := by
      by_cases ha : a ∈ R
      · refine ⟨0, fun s _ => ?_⟩
        have hfa : f s a = false := by
          by_contra hne
          have : f s a = true := by simpa using hne
          exact (hf.spec a).2 ⟨s, this⟩ ha
        rw [hfa, chi_eq_true.2 ha]
        rfl
      · obtain ⟨s₂, hs₂⟩ := (hf.spec a).1 ha
        refine ⟨s₂, fun s hs => ?_⟩
        rw [hf.mono hs hs₂]
        have : chi R a = false := by
          cases h : chi R a
          · rfl
          · exact absurd (chi_eq_true.1 h) ha
        rw [this]
        rfl
    obtain ⟨s₂, hs₂⟩ := hstage
    refine ⟨max s₁ s₂, fun s hs z hz => ?_⟩
    rcases List.mem_cons.1 hz with rfl | h
    · exact hs₂ s ((le_max_right _ _).trans hs)
    · exact hs₁ s ((le_max_left _ _).trans hs) z h

/-- **Approximation.**  If `X ≤_tt R` and the complement of `R` is enumerated, then `X` has a
computable approximation: evaluate the table on the stage approximation of the actual oracle. -/
theorem approximation_of_tt {f : ℕ → Str → Bool} {R : Set Str} {g : Str → TTable} {X : Set Str}
    (hf : IsCoEnum f R) (hg : Computable g) (h : IsTTReduction g X R) :
    (Computable fun p : ℕ × Str => (g p.2).evalB fun z => !(f p.1 z)) ∧
      ∀ x, ∃ s₀, ∀ s ≥ s₀, (((g x).evalB fun z => !(f s z)) = true ↔ x ∈ X) := by
  constructor
  · have ho : Primrec fun q : ℕ × Str => (fun s z => !(f s z)) q.1 q.2 :=
      Primrec.not.comp hf.primrec
    have he := evalB_primrec (o := fun s z => !(f s z)) ho
    exact he.to_comp.comp (Computable.fst.pair (hg.comp Computable.snd))
  · intro x
    obtain ⟨s₀, hs₀⟩ := exists_stage_correct hf (g x).queries
    refine ⟨s₀, fun s hs => ?_⟩
    rw [h x, TTable.Accepts]
    rw [TTable.evalB_congr (o' := chi R) (hs₀ s hs)]

end Kolmogorov.RandomStrings.TTMeet
