/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.Position
import KolmogorovMathlib.MonotoneComplexity.StreamGapFill
import KolmogorovMathlib.MonotoneComplexity.StreamRelationEnumeration
import KolmogorovMathlib.Restricted.EffectiveSelection.Part01

/-!
# Consistency sanitizer for enumerable stream relations

An arbitrary recursively enumerable relation between finite inputs and finite outputs
need not be *consistent* in the sense of `IsConsistentStreamRelation`, so it cannot be
fed directly into `streamGapFill`.  This file provides the standard *sanitizer*: given a
uniformly computable stage-by-stage enumeration `A` of a relation, we accept an
enumerated pair only when it is compatible with every pair enumerated strictly earlier
in a fixed linear order on "pair together with its first stage of appearance".

The result, `sanitizedStreamRel`, is

* always consistent (`sanitizedStreamRel_isConsistent`),
* contained in the enumerated relation (`sanitizedStreamRel_le`),
* equal to it whenever the enumerated relation was already consistent
  (`sanitizedStreamRel_eq_of_consistent`),
* recursively enumerable, uniformly in the parameter
  (`sanitizedStreamRel_isRE_uniform`).

Combining the sanitizer with `universalStreamRel` yields a uniformly enumerable family
of *consistent* relations that already contains every consistent enumerable relation
(`sanitizedUniversalStreamRel_complete`), the enumeration step of SUV Theorem 83.
-/

namespace Kolmogorov

/-! ### A bounded-quantifier primitive recursion helper -/

/-! ### Boolean prefix and compatibility tests -/

/-- Boolean test for the prefix relation on bit strings. -/
def prefixCheck (u v : BitString) : Bool := decide (u = v.take u.length)

/-- The Boolean prefix test returns `true` exactly on pairs where the first string is a prefix of
the
second. -/
lemma prefixCheck_eq_true_iff (u v : BitString) : prefixCheck u v = true ↔ u <+: v := by
  rw [prefixCheck, decide_eq_true_iff, ← List.prefix_iff_eq_take]

/-- The Boolean prefix test returns `false` exactly when the first string is not a prefix of the
second. -/
lemma prefixCheck_eq_false_iff (u v : BitString) : prefixCheck u v = false ↔ ¬ (u <+: v) := by
  rw [← prefixCheck_eq_true_iff]; simp

/-- Boolean test: if the two inputs are prefix-comparable then so are the two outputs. -/
def compatCheck (x y x' y' : BitString) : Bool :=
  !(prefixCheck x x' || prefixCheck x' x) || (prefixCheck y y' || prefixCheck y' y)

/-- The compatibility test returns `true` exactly when comparable inputs are required to have
comparable outputs, the monotonicity condition on a stream relation. -/
lemma compatCheck_eq_true_iff (x y x' y' : BitString) :
    compatCheck x y x' y' = true ↔ ((x <+: x' ∨ x' <+: x) → (y <+: y' ∨ y' <+: y)) := by
  simp only [compatCheck, Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    prefixCheck_eq_true_iff, prefixCheck_eq_false_iff]
  tauto

/-- Total decoding of a natural number into a pair of bit strings. -/
def decodePair (n : ℕ) : BitString × BitString :=
  (Encodable.decode (α := BitString × BitString) n).getD ([], [])

/-- Decoding the code of a pair of strings returns that pair. -/
lemma decodePair_encode (x y : BitString) : decodePair (Encodable.encode (x, y)) = (x, y) := by
  simp [decodePair]

/-! ### The sanitizer -/

section Sanitizer

variable {α : Type*} (A : α → BitString → BitString → ℕ → Bool)

/-- `sanStage A a x y k` says that `k` is the first stage at which the pair `(x, y)`
appears in the enumeration `A a`. -/
def sanStage (a : α) (x y : BitString) (k : ℕ) : Bool :=
  A a x y k && (decide (k = 0) || !(A a x y (k - 1)))

/-- The linear order key attached to a pair together with its first stage. -/
def sanKey (x y : BitString) (k : ℕ) : ℕ := Nat.pair k (Encodable.encode (x, y))

/-- The key attached to a triple of input, output and stage determines the triple. -/
lemma sanKey_injective {x₁ y₁ x₂ y₂ : BitString} {k₁ k₂ : ℕ}
    (h : sanKey x₁ y₁ k₁ = sanKey x₂ y₂ k₂) :
    x₁ = x₂ ∧ y₁ = y₂ ∧ k₁ = k₂ := by
  have h' := congrArg Nat.unpair h
  rw [sanKey, sanKey, Nat.unpair_pair, Nat.unpair_pair] at h'
  obtain ⟨hk, he⟩ := Prod.mk.injEq .. ▸ h'
  have := Encodable.encode_injective he
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this, hk⟩

/-- The compatibility test run against everything enumerated strictly earlier. -/
def sanCheck (a : α) (x y : BitString) (k : ℕ) : Bool :=
  (List.range (sanKey x y k)).all fun n =>
    !(sanStage A a (decodePair n.unpair.2).1 (decodePair n.unpair.2).2 n.unpair.1) ||
      compatCheck x y (decodePair n.unpair.2).1 (decodePair n.unpair.2).2

/-- One accepted enumeration step of the sanitized relation. -/
def sanStep (a : α) (x y : BitString) (k : ℕ) : Bool :=
  sanStage A a x y k && sanCheck A a x y k

/-- The sanitized relation: the pairs that survive the compatibility filter. -/
def sanitizedStreamRel (a : α) (x y : BitString) : Prop :=
  ∃ k, sanStep A a x y k = true

/-- Sanitisation only removes pairs: an accepted step was already accepted by the raw stage
relation. -/
lemma sanStep_imp_stage {a : α} {x y : BitString} {k : ℕ} (h : sanStep A a x y k = true) :
    A a x y k = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

/-- The sanitizer only removes pairs. -/
lemma sanitizedStreamRel_le {a : α} {x y : BitString} (h : sanitizedStreamRel A a x y) :
    ∃ k, A a x y k = true := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, sanStep_imp_stage A hk⟩

/-- The sanitized relation is always consistent. -/
theorem sanitizedStreamRel_isConsistent (a : α) :
    IsConsistentStreamRelation (sanitizedStreamRel A a) := by
  rintro x₁ x₂ y₁ y₂ ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ hpre
  obtain ⟨hs₁, hc₁⟩ := Bool.and_eq_true_iff.mp h₁
  obtain ⟨hs₂, hc₂⟩ := Bool.and_eq_true_iff.mp h₂
  rcases lt_trichotomy (sanKey x₁ y₁ k₁) (sanKey x₂ y₂ k₂) with hlt | heq | hgt
  · have hmem : sanKey x₁ y₁ k₁ ∈ List.range (sanKey x₂ y₂ k₂) :=
      List.mem_range.mpr hlt
    have hall := List.all_eq_true.mp hc₂ _ hmem
    rw [sanKey, Nat.unpair_pair] at hall
    simp only [decodePair_encode, hs₁, Bool.not_true, Bool.false_or] at hall
    have := (compatCheck_eq_true_iff x₂ y₂ x₁ y₁).mp hall (hpre.symm)
    exact this.symm
  · obtain ⟨hx, hy, _⟩ := sanKey_injective heq
    subst hy
    exact Or.inl List.prefix_rfl
  · have hmem : sanKey x₂ y₂ k₂ ∈ List.range (sanKey x₁ y₁ k₁) :=
      List.mem_range.mpr hgt
    have hall := List.all_eq_true.mp hc₁ _ hmem
    rw [sanKey, Nat.unpair_pair] at hall
    simp only [decodePair_encode, hs₂, Bool.not_true, Bool.false_or] at hall
    exact (compatCheck_eq_true_iff x₁ y₁ x₂ y₂).mp hall hpre

/-- If the enumerated relation was already consistent, the sanitizer changes nothing. -/
theorem sanitizedStreamRel_eq_of_consistent (a : α)
    (hcons : IsConsistentStreamRelation (fun x y => ∃ k, A a x y k = true)) (x y : BitString) :
    sanitizedStreamRel A a x y ↔ ∃ k, A a x y k = true := by
  classical
  refine ⟨sanitizedStreamRel_le A, fun hR => ?_⟩
  have hk : A a x y (Nat.find hR) = true := Nat.find_spec hR
  refine ⟨Nat.find hR, Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hk, ?_⟩, ?_⟩⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hR) with h0 | hpos
    · simp [h0]
    · have hmin : ¬ A a x y (Nat.find hR - 1) = true := Nat.find_min hR (by omega)
      simp [hmin]
  · refine List.all_eq_true.mpr fun n _ => ?_
    set q := decodePair n.unpair.2 with hq
    by_cases hst : sanStage A a q.1 q.2 n.unpair.1 = true
    · have hRq : ∃ m, A a q.1 q.2 m = true := ⟨n.unpair.1, (Bool.and_eq_true_iff.mp hst).1⟩
      have hcompat := hcons x q.1 y q.2 hR hRq
      simp only [hst, Bool.not_true, Bool.false_or]
      exact (compatCheck_eq_true_iff x y q.1 q.2).mpr hcompat
    · have hfalse : sanStage A a q.1 q.2 n.unpair.1 = false := Bool.eq_false_iff.mpr hst
      simp [hfalse]

end Sanitizer

/-! ### Uniform computability of the sanitizer -/

section Computability

variable {α : Type*} [Primcodable α] {A : α → BitString → BitString → ℕ → Bool}

private lemma primrec_prefixCheck {γ : Type*} [Primcodable γ] {fu fv : γ → BitString}
    (hu : Primrec fu) (hv : Primrec fv) : Primrec fun c => prefixCheck (fu c) (fv c) := by
  obtain ⟨_, h⟩ : PrimrecPred fun c => fu c = (fv c).take (fu c).length :=
    Primrec.eq.comp hu (Primrec.list_take.comp (Primrec.list_length.comp hu) hv)
  exact h.of_eq fun c => by simp only [prefixCheck]; congr

private lemma primrec_compatCheck {γ : Type*} [Primcodable γ] {fx fy fx' fy' : γ → BitString}
    (hx : Primrec fx) (hy : Primrec fy) (hx' : Primrec fx') (hy' : Primrec fy') :
    Primrec fun c => compatCheck (fx c) (fy c) (fx' c) (fy' c) :=
  Primrec.or.comp
    (Primrec.not.comp
      (Primrec.or.comp (primrec_prefixCheck hx hx') (primrec_prefixCheck hx' hx)))
    (Primrec.or.comp (primrec_prefixCheck hy hy') (primrec_prefixCheck hy' hy))

private lemma primrec_decodePair : Primrec decodePair := by
  have h := Primrec.option_casesOn (Primrec.decode (α := BitString × BitString))
    (Primrec.const (([], []) : BitString × BitString)) (Primrec.snd (α := ℕ)).to₂
  refine h.of_eq fun n => ?_
  cases hd : Encodable.decode (α := BitString × BitString) n <;> simp [decodePair, hd]

variable (hA : Primrec fun p : (α × BitString × BitString) × ℕ =>
  A p.1.1 p.1.2.1 p.1.2.2 p.2)

include hA

private lemma primrec_sanStage {γ : Type*} [Primcodable γ] {fa : γ → α}
    {fx fy : γ → BitString} {fk : γ → ℕ}
    (ha : Primrec fa) (hx : Primrec fx) (hy : Primrec fy) (hk : Primrec fk) :
    Primrec fun c => sanStage A (fa c) (fx c) (fy c) (fk c) := by
  have hbase : Primrec fun c => A (fa c) (fx c) (fy c) (fk c) :=
    hA.comp (Primrec.pair (Primrec.pair ha (Primrec.pair hx hy)) hk)
  have hpred : Primrec fun c => A (fa c) (fx c) (fy c) (fk c - 1) :=
    hA.comp (Primrec.pair (Primrec.pair ha (Primrec.pair hx hy)) (Primrec.pred.comp hk))
  obtain ⟨_, hzero⟩ : PrimrecPred fun c => fk c = 0 := Primrec.eq.comp hk (Primrec.const 0)
  have hfinal := Primrec.and.comp hbase (Primrec.or.comp hzero (Primrec.not.comp hpred))
  exact hfinal.of_eq fun c => by simp only [sanStage]; congr

private lemma primrec_sanCheck :
    Primrec fun p : (α × BitString × BitString) × ℕ =>
      sanCheck A p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  have hrange : Primrec fun p : (α × BitString × BitString) × ℕ =>
      List.range (sanKey p.1.2.1 p.1.2.2 p.2) :=
    Primrec.list_range.comp
      (Primrec₂.natPair.comp Primrec.snd
        (Primrec.encode.comp (Primrec.snd.comp Primrec.fst)))
  set Q := ((α × BitString × BitString) × ℕ) × ℕ
  have hn : Primrec fun c : Q => c.2 := Primrec.snd
  have hq : Primrec fun c : Q => decodePair c.2.unpair.2 :=
    primrec_decodePair.comp (Primrec.snd.comp (Primrec.unpair.comp hn))
  have hq1 : Primrec fun c : Q => (decodePair c.2.unpair.2).1 := Primrec.fst.comp hq
  have hq2 : Primrec fun c : Q => (decodePair c.2.unpair.2).2 := Primrec.snd.comp hq
  have hk : Primrec fun c : Q => c.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hn)
  have ha : Primrec fun c : Q => c.1.1.1 := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hx : Primrec fun c : Q => c.1.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hy : Primrec fun c : Q => c.1.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hbody : Primrec₂ fun (p : (α × BitString × BitString) × ℕ) (n : ℕ) =>
      !(sanStage A p.1.1 (decodePair n.unpair.2).1 (decodePair n.unpair.2).2 n.unpair.1) ||
        compatCheck p.1.2.1 p.1.2.2 (decodePair n.unpair.2).1 (decodePair n.unpair.2).2 :=
    Primrec.or.comp
      (Primrec.not.comp (primrec_sanStage hA ha hq1 hq2 hk))
      (primrec_compatCheck hx hy hq1 hq2)
  exact list_all_primrec hrange hbody

/-- The sanitised stage relation is primitive recursive in the parameter, both strings and the
stage. -/
lemma primrec_sanStep : Primrec fun p : (α × BitString × BitString) × ℕ =>
    sanStep A p.1.1 p.1.2.1 p.1.2.2 p.2 :=
  Primrec.and.comp
    (primrec_sanStage hA (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
    (primrec_sanCheck hA)

/-- The sanitized relation is recursively enumerable, uniformly in the parameter. -/
theorem sanitizedStreamRel_isRE_uniform :
    IsRE fun p : α × BitString × BitString => sanitizedStreamRel A p.1 p.2.1 p.2.2 := by
  have hstep : IsRE fun p : (α × BitString × BitString) × ℕ =>
      sanStep A p.1.1 p.1.2.1 p.1.2.2 p.2 = true :=
    isRE_of_computable_bool
      (fun p : (α × BitString × BitString) × ℕ => sanStep A p.1.1 p.1.2.1 p.1.2.2 p.2 = true)
      (fun p => sanStep A p.1.1 p.1.2.1 p.1.2.2 p.2) (fun _ => Iff.rfl)
      (primrec_sanStep hA).to_comp
  have hex := IsRE.exists_encodable
    (R := fun (p : α × BitString × BitString) (k : ℕ) =>
      sanStep A p.1 p.2.1 p.2.2 k = true) hstep
  exact hex.of_iff fun p => Iff.rfl

end Computability

/-! ### The sanitized universal family -/

/-- The Boolean stage predicate underlying `universalStreamRel`. -/
def universalStageBool (i : ℕ) (x y : BitString) (k : ℕ) : Bool :=
  (Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode i) (Encodable.encode (x, y))).isSome

/-- The universal stream relation holds exactly when some finite stage of its Boolean approximation
accepts. -/
lemma universalStreamRel_iff_stageBool (i : ℕ) (x y : BitString) :
    universalStreamRel i x y ↔ ∃ k, universalStageBool i x y k = true := Iff.rfl

/-- The staged Boolean approximation of the universal stream relation is primitive recursive. -/
lemma primrec_universalStageBool :
    Primrec fun p : (ℕ × BitString × BitString) × ℕ =>
      universalStageBool p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  have hcode : Primrec fun p : (ℕ × BitString × BitString) × ℕ =>
      Nat.Partrec.Code.ofNatCode p.1.1 := by
    have h := (Primrec.ofNat Nat.Partrec.Code).comp
      (Primrec.fst.comp (Primrec.fst (β := ℕ) (α := ℕ × BitString × BitString)))
    exact h.of_eq fun p => by rw [Nat.Partrec.Code.ofNatCode_eq]
  have hinput : Primrec fun p : (ℕ × BitString × BitString) × ℕ =>
      Encodable.encode (p.1.2.1, p.1.2.2) :=
    Primrec.encode.comp (Primrec.snd.comp Primrec.fst)
  have hevaln := Nat.Partrec.Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair Primrec.snd hcode) hinput)
  exact (Primrec.option_isSome.comp hevaln)

/-- The sanitized universal family: a uniformly enumerable family of relations, each of
which is consistent. -/
def sanitizedUniversalStreamRel (i : ℕ) (x y : BitString) : Prop :=
  sanitizedStreamRel universalStageBool i x y

/-- Every row of the sanitised universal stream relation is a consistent stream relation. -/
theorem sanitizedUniversalStreamRel_isConsistent (i : ℕ) :
    IsConsistentStreamRelation (sanitizedUniversalStreamRel i) :=
  sanitizedStreamRel_isConsistent universalStageBool i

/-- The sanitised universal stream relation is recursively enumerable uniformly in the row index. -/
theorem sanitizedUniversalStreamRel_isRE_uniform :
    IsRE fun p : ℕ × BitString × BitString => sanitizedUniversalStreamRel p.1 p.2.1 p.2.2 :=
  sanitizedStreamRel_isRE_uniform primrec_universalStageBool

/-- Every consistent recursively enumerable stream relation occurs in the sanitized
universal family. -/
theorem sanitizedUniversalStreamRel_complete {R : BitString → BitString → Prop}
    (hcons : IsConsistentStreamRelation R)
    (hre : IsRE fun p : BitString × BitString => R p.1 p.2) :
    ∃ i, ∀ x y, sanitizedUniversalStreamRel i x y ↔ R x y := by
  obtain ⟨i, hi⟩ := universalStreamRel_complete hre
  refine ⟨i, fun x y => ?_⟩
  have hcons' : IsConsistentStreamRelation
      (fun x y => ∃ k, universalStageBool i x y k = true) := by
    intro x₁ x₂ y₁ y₂ h₁ h₂ hpre
    exact hcons x₁ x₂ y₁ y₂ ((hi x₁ y₁).mp h₁) ((hi x₂ y₂).mp h₂) hpre
  rw [sanitizedUniversalStreamRel,
    sanitizedStreamRel_eq_of_consistent universalStageBool i hcons' x y]
  exact hi x y

/-- Every consistent recursively enumerable stream relation is, after gap filling, the
lower graph of a computable stream map drawn from a single uniformly enumerable family. -/
theorem sanitizedUniversalStreamRel_gapFill_isComputableStreamMap (i : ℕ) :
    IsComputableStreamMap
      (streamMapOfLowerGraph (streamGapFill (sanitizedUniversalStreamRel i))
        (streamGapFill_isStreamLowerGraph (sanitizedUniversalStreamRel_isConsistent i))) := by
  refine streamMapOfLowerGraph_streamGapFill_isComputableStreamMap
    (sanitizedUniversalStreamRel_isConsistent i) ?_
  have huniform := sanitizedUniversalStreamRel_isRE_uniform
  exact huniform.comp_computable
    (Computable.pair (Computable.const i) Computable.id)

end Kolmogorov
