import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import Mathlib.Computability.Halting

/-!
# Closure properties of recursively enumerable predicates

The toolkit used whenever a construction needs its acceptance condition to stay enumerable:
transport along a pointwise equivalence (`IsRE.of_iff`), precomposition with a computable
function (`IsRE.comp_computable`), disjunction (`IsRE.or`), conjunction with a decidable
condition and with another RE predicate (`IsRE.and_computable`, `IsRE.and`, whose proof
dovetails the two searches), projection along an encodable existential
(`IsRE.exists_encodable`), and the passage between decidable and enumerable
(`isRE_of_computable_bool`). `IsRE.exists_stageApprox` gives every RE predicate a computable
stage approximation, the form most of the library consumes.
-/

namespace Kolmogorov

/-- A predicate pointwise equivalent to a recursively enumerable one is recursively enumerable. -/
lemma IsRE.of_iff {α : Type*} [Primcodable α] {P Q : α → Prop}
    (hP : IsRE P) (h : ∀ a, P a ↔ Q a) : IsRE Q := by
  obtain ⟨f, hf, hdom⟩ := hP
  exact ⟨f, hf, fun a => (hdom a).trans (h a)⟩

/-- Precomposing a recursively enumerable predicate with a computable function keeps it recursively
enumerable. -/
lemma IsRE.comp_computable {α β : Type*} [Primcodable α] [Primcodable β]
    {R : β → Prop} (hR : IsRE R) {g : α → β} (hg : Computable g) :
    IsRE (fun a => R (g a)) := by
  obtain ⟨f, hf, hdom⟩ := hR
  exact ⟨fun a => f (g a), hf.comp hg, fun a => hdom (g a)⟩

/-- The disjunction of two recursively enumerable predicates is recursively enumerable. -/
lemma IsRE.or {α : Type*} [Primcodable α] {P Q : α → Prop}
    (hP : IsRE P) (hQ : IsRE Q) : IsRE (fun a => P a ∨ Q a) := by
  obtain ⟨f, hf, hf'⟩ := hP
  obtain ⟨g, hg, hg'⟩ := hQ
  obtain ⟨k, hk, hk'⟩ := Partrec.merge' hf hg
  exact ⟨k, hk, fun a => ((hk' a).2).trans (or_congr (hf' a) (hg' a))⟩

/-- Conjoining a recursively enumerable predicate with a decidable condition keeps it recursively
enumerable. -/
lemma IsRE.and_computable {α : Type*} [Primcodable α] {R : α → Prop}
    (hR : IsRE R) {p : α → Bool} (hp : Computable p) :
    IsRE (fun a => p a = true ∧ R a) := by
  obtain ⟨f, hf, hdom⟩ := hR
  refine ⟨fun a => (f a).bind fun _ =>
    (↑(if p a = true then some () else none : Option Unit) : Part Unit), ?_, ?_⟩
  · refine hf.bind ?_
    have h : Computable fun q : α × Unit =>
        (if p q.1 = true then some () else none : Option Unit) :=
      (Computable.cond (hp.comp Computable.fst) (Computable.const (some ()))
        (Computable.const none)).of_eq (fun q => by cases h : p q.1 <;> simp)
    exact (Computable.ofOption h).to₂
  · intro a
    rw [Part.bind_dom]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hpa : p a = true
      · exact ⟨hpa, (hdom a).mp h1⟩
      · rw [ite_eq_right hpa] at h2; simp at h2
    · rintro ⟨hpa, hRa⟩
      exact ⟨(hdom a).mpr hRa, by rw [ite_eq_left hpa]; trivial⟩

private lemma decodeDovetailCheckComputable {α β : Type*} [Primcodable α] [Primcodable β]
    (c : Nat.Partrec.Code) :
    Computable₂ (fun (a : α) (n : ℕ) =>
      match (Encodable.decode (α := β) n.unpair.1) with
      | some b =>
        (Nat.Partrec.Code.evaln (n.unpair.2 + 1) c (Encodable.encode (a, b))).isSome
      | none => false) := by
  have h_lookup : Computable (fun p : α × ℕ => Encodable.decode (α := β) p.2.unpair.1) :=
    Computable.comp Computable.decode
      (Computable.comp Computable.fst (Computable.comp Computable.unpair Computable.snd))
  have h_step : Computable₂ (fun (p : α × ℕ) (b : β) =>
      Nat.Partrec.Code.evaln (p.2.unpair.2 + 1) c (Encodable.encode (p.1, b))) := by
    have h_steps : Computable (fun q : (α × ℕ) × β => q.1.2.unpair.2 + 1) :=
      Primrec.to_comp
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))))
    have h_input : Computable (fun q : (α × ℕ) × β => Encodable.encode (q.1.1, q.2)) :=
      Computable.comp Computable.encode
        (Primrec.to_comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
    exact Computable.comp (evalnCoreComputable c) (Computable.pair h_steps h_input)
  have h_isSome : Computable (fun o : Option ℕ => o.isSome) :=
    Primrec.to_comp Primrec.option_isSome
  have h_full := Computable.comp h_isSome (Computable.option_bind h_lookup h_step)
  exact Computable.of_eq h_full (by
    intro p
    dsimp only
    cases h : (Encodable.decode (α := β) p.2.unpair.1) <;> rfl)

/-- Projection: an RE relation stays RE after existentially quantifying an
encodable argument. -/
lemma IsRE.exists_encodable {α β : Type*} [Primcodable α] [Primcodable β]
    {R : α → β → Prop} (hR : IsRE (fun p : α × β => R p.1 p.2)) :
    IsRE (fun a => ∃ b, R a b) := by
  obtain ⟨g, hg_partrec, hg_dom⟩ := hR
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg_partrec
  let check : α → ℕ → Bool := fun a n =>
    match (Encodable.decode (α := β) n.unpair.1) with
    | some b =>
      (Nat.Partrec.Code.evaln (n.unpair.2 + 1) c (Encodable.encode (a, b))).isSome
    | none => false
  have hcheck : Computable₂ check := decodeDovetailCheckComputable c
  let p (a : α) : ℕ →. Bool := fun n => Part.some (check a n)
  have h_rfind : Partrec (fun a => Nat.rfind (p a)) :=
    Partrec.rfind hcheck.partrec
  refine ⟨fun a => (Nat.rfind (p a)).map (fun _ => ()),
    h_rfind.map (Computable.const ()).to₂, ?_⟩
  intro a
  change (Nat.rfind (p a)).Dom ↔ _
  rw [Nat.rfind_dom]
  dsimp [p]
  simp_rw [Part.mem_some_iff]
  have hrfind_simp : (∃ n, true = check a n ∧ ∀ {m : ℕ}, m < n →
      (Part.some (check a m)).Dom) ↔ (∃ n, check a n = true) := by
    constructor
    · rintro ⟨n, hn, _⟩; exact ⟨n, hn.symm⟩
    · rintro ⟨n, hn⟩; exact ⟨n, hn.symm, fun _ => Part.some_dom _⟩
  rw [hrfind_simp]
  have code_dom := partrecCodeDom g c hc
  constructor
  · rintro ⟨n, hn⟩
    simp only [check] at hn
    generalize n.unpair.1 = i at hn
    generalize n.unpair.2 = k at hn
    cases hget : (Encodable.decode (α := β) i) with
    | none =>
      simp only [hget] at hn
      contradiction
    | some b =>
      simp only [hget] at hn
      exact ⟨b, (hg_dom (a, b)).mp ((code_dom (a, b)).mpr ⟨k + 1, hn⟩)⟩
  · rintro ⟨b, hR_ab⟩
    have hdom : (g (a, b)).Dom := (hg_dom (a, b)).mpr hR_ab
    obtain ⟨k, hk⟩ := (code_dom (a, b)).mp hdom
    refine ⟨Nat.pair (Encodable.encode b) k, ?_⟩
    simp only [check, Nat.unpair_pair, Encodable.encodek]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
    exact Option.isSome_iff_exists.mpr
      ⟨x, Option.mem_def.mp (Nat.Partrec.Code.evaln_mono
        (Nat.le_succ k) (Option.mem_def.mpr hx))⟩

/-- A predicate with a computable boolean test is RE. -/
lemma isRE_of_computable_bool {α : Type*} [Primcodable α] (R : α → Prop)
    (check : α → Bool) (h_iff : ∀ a, check a = true ↔ R a)
    (h_comp : Computable check) : IsRE R := by
  let f : α →. Unit := fun a => (if check a then Part.some () else Part.none : Part Unit)
  have hf : Partrec f := by
    have h : Partrec (fun a => (↑(bif check a then some () else none) : Part Unit)) :=
      Computable.ofOption
        (Computable.cond h_comp (Computable.const (some ())) (Computable.const none))
    apply Partrec.of_eq h
    intro a
    dsimp [f]
    cases h_check : check a <;> simp_all
  refine ⟨f, hf, ?_⟩
  intro a
  dsimp [f]
  split_ifs with h
  · exact iff_of_true trivial (h_iff a |>.mp h)
  · exact iff_of_false (by simp) (fun ha => h (h_iff a |>.mpr ha))

/-- Every RE predicate admits a computable stage approximation: a computable
boolean test `chk a s` which is monotone in the stage `s` and whose union over
all stages is the predicate. -/
lemma IsRE.exists_stageApprox {α : Type*} [Primcodable α] {R : α → Prop} (hR : IsRE R) :
    ∃ chk : α → ℕ → Bool, Computable₂ chk ∧
      (∀ a s t, s ≤ t → chk a s = true → chk a t = true) ∧
      (∀ a, R a ↔ ∃ s, chk a s = true) := by
  obtain ⟨g, hg, hg_dom⟩ := hR
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg
  refine ⟨fun a s => (Nat.Partrec.Code.evaln s c (Encodable.encode a)).isSome, ?_, ?_, ?_⟩
  · have h : Computable
        (fun p : α × ℕ => Nat.Partrec.Code.evaln p.2 c (Encodable.encode p.1)) :=
      (evalnCoreComputable c).comp
        (Computable.pair Computable.snd (Computable.encode.comp Computable.fst))
    exact (Primrec.to_comp Primrec.option_isSome).comp h
  · intro a s t hst h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    exact Option.isSome_iff_exists.mpr ⟨x, Option.mem_def.mp
      (Nat.Partrec.Code.evaln_mono hst (Option.mem_def.mpr hx))⟩
  · intro a
    rw [← hg_dom a]
    exact partrecCodeDom g c hc a

/-- The conjunction of two recursively enumerable predicates is recursively enumerable. -/
lemma IsRE.and {α : Type*} [Primcodable α] {P Q : α → Prop}
    (hP : IsRE P) (hQ : IsRE Q) : IsRE (fun a => P a ∧ Q a) := by
  obtain ⟨f, hf, hf_dom⟩ := hP
  obtain ⟨g, hg, hg_dom⟩ := hQ
  refine ⟨fun a => (f a).bind (fun _ => g a), hf.bind (hg.comp Computable.fst), ?_⟩
  intro a
  simp [Part.bind_dom, hf_dom, hg_dom]

end Kolmogorov
