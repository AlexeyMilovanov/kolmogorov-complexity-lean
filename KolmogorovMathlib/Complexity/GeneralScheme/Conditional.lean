import KolmogorovMathlib.Complexity.GeneralScheme.DecisionBasic
import KolmogorovMathlib.Prefix.StableDecompressors

/-!
# Conditional complexities: the eight `(α, β) | γ` classes (SUV Section 6.3)

SUV Theorem 129 (printed p. 200) and Problems 200–202 (printed p. 201). The notation remark of
printed p. 201 identifies `K(=,=)|=` with `C(x | y)` and `K(≍,=)|=` with `K(x | y)`.
-/

namespace Kolmogorov

namespace GeneralScheme

/-- Step 1 of the proof of `exists_isOptimalCondDescriptionMode`: a computable
enumeration of all enumerable sets of triples. There is a computable `E u n : Option (triple)`
such that every enumerable set `A` of triples `(p, x, y)` equals `{t | ∃ n, E u n = some t}` for
some index `u`. (Take `E u n` to decode `n.unpair.1` as a triple `t` and test by `evaln` with
`n.unpair.2` steps whether the `u`-th program accepts `t`; every positive natural number is the
index `decodeBits (u ++ [true])` of a program for a suitable bit string `u`.) -/
private theorem exists_isOptimalCondDescriptionMode_universalEnumeration :
    ∃ E : BitString → ℕ → Option (BitString × BitString × BitString), Computable₂ E ∧
      ∀ A : BitString → BitString → BitString → Prop,
        IsRE (fun q : BitString × BitString × BitString => A q.1 q.2.1 q.2.2) →
        ∃ u, ∀ p x y, A p x y ↔ ∃ n, E u n = some (p, x, y) := by
  classical
  let E : BitString → ℕ → Option (BitString × BitString × BitString) := fun u n =>
    (Encodable.decode (α := BitString × BitString × BitString) n.unpair.1).bind fun t =>
      if (Nat.Partrec.Code.evaln (n.unpair.2 + 1)
        (Denumerable.ofNat Nat.Partrec.Code (decodeBits u)) (Encodable.encode t)).isSome
      then some t else none
  have hE : Computable₂ E := by
    have hdec : Computable (fun p : BitString × ℕ =>
        Encodable.decode (α := BitString × BitString × BitString) p.2.unpair.1) :=
      Computable.decode.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
    have hk : Computable (fun q : (BitString × ℕ) × (BitString × BitString × BitString) =>
        q.1.2.unpair.2 + 1) :=
      Primrec.to_comp (Primrec.succ.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))))
    have hcode : Computable (fun q : (BitString × ℕ) × (BitString × BitString × BitString) =>
        Denumerable.ofNat Nat.Partrec.Code (decodeBits q.1.1)) :=
      (Computable.ofNat Nat.Partrec.Code).comp
        (decodeBits_computable.comp (Computable.fst.comp Computable.fst))
    have hin : Computable (fun q : (BitString × ℕ) × (BitString × BitString × BitString) =>
        Encodable.encode q.2) := Computable.encode.comp Computable.snd
    have hev : Computable (fun q : (BitString × ℕ) × (BitString × BitString × BitString) =>
        (Nat.Partrec.Code.evaln (q.1.2.unpair.2 + 1)
          (Denumerable.ofNat Nat.Partrec.Code (decodeBits q.1.1)) (Encodable.encode q.2)).isSome) :=
      Primrec.option_isSome.to_comp.comp
        ((Nat.Partrec.Code.primrec_evaln.to_comp).comp
          (Computable.pair (Computable.pair hk hcode) hin))
    have hbody : Computable₂ (fun (p : BitString × ℕ) (t : BitString × BitString × BitString) =>
        if (Nat.Partrec.Code.evaln (p.2.unpair.2 + 1)
          (Denumerable.ofNat Nat.Partrec.Code (decodeBits p.1)) (Encodable.encode t)).isSome
        then some t else none) := by
      refine (Computable.cond hev (Computable.option_some.comp Computable.snd)
        (Computable.const none)).of_eq fun q => ?_
      cases hh : (Nat.Partrec.Code.evaln (q.1.2.unpair.2 + 1)
        (Denumerable.ofNat Nat.Partrec.Code (decodeBits q.1.1)) (Encodable.encode q.2)).isSome
        <;> simp only [hh] <;> rfl
    exact Computable.option_bind hdec hbody
  refine ⟨E, hE, fun A hA => ?_⟩
  obtain ⟨g, hg, hdom⟩ := hA
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg
  have hcd := partrecCodeDom g c hc
  refine ⟨Nat.bits (Encodable.encode c), fun p x y => ?_⟩
  have hcode : Denumerable.ofNat Nat.Partrec.Code (decodeBits (Nat.bits (Encodable.encode c))) = c
      := by
    rw [decodeBits_natBits, Denumerable.ofNat_encode]
  rw [show A p x y ↔ _ from (hdom (p, x, y)).symm.trans (hcd (p, x, y))]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
    have hv' := Nat.Partrec.Code.evaln_mono (Nat.le_succ k) (Option.mem_def.mpr hv)
    refine ⟨Nat.pair (Encodable.encode (p, x, y)) k, ?_⟩
    simp only [E, Nat.unpair_pair, Encodable.encodek, Option.bind_some]
    rw [hcode, ite_eq_left (Option.isSome_iff_exists.mpr ⟨v, Option.mem_def.mp hv'⟩)]
  · rintro ⟨n, hn⟩
    simp only [E, Option.bind_eq_some_iff] at hn
    obtain ⟨t, -, hif⟩ := hn
    split_ifs at hif with hs
    · obtain rfl := Option.some.inj hif
      rw [hcode] at hs
      exact ⟨_, hs⟩

/-- Boolean test for the relations `=` and `≍` of `StrRel`. -/
private def exists_isOptimalCondDescriptionMode_trim_isRE_holdsB :
    StrRel → BitString → BitString → Bool
  | .eq, x, y => decide (x = y)
  | .compat, x, y => decide (x = y.take x.length) || decide (y = x.take y.length)

private theorem exists_isOptimalCondDescriptionMode_trim_isRE_holdsB_iff (a : StrRel)
    (x y : BitString) :
    exists_isOptimalCondDescriptionMode_trim_isRE_holdsB a x y = true ↔ a.Holds x y := by
  cases a
  · simp [exists_isOptimalCondDescriptionMode_trim_isRE_holdsB, StrRel.Holds]
  · simp [exists_isOptimalCondDescriptionMode_trim_isRE_holdsB, StrRel.Holds,
      List.prefix_iff_eq_take]

private theorem exists_isOptimalCondDescriptionMode_trim_isRE_holdsB_computable
    (a : StrRel) {X : Type*} [Primcodable X] {f g : X → BitString}
    (hf : Computable f) (hg : Computable g) :
    Computable (fun p => exists_isOptimalCondDescriptionMode_trim_isRE_holdsB a (f p) (g p))
        := by
  cases a
  · exact ((Primrec.eq.decide.to_comp).comp hf hg).of_eq fun p => rfl
  · have h1 : Computable (fun p => (g p).take (f p).length) :=
      (Primrec.list_take.to_comp).comp (Computable.list_length.comp hf) hg
    have h2 : Computable (fun p => (f p).take (g p).length) :=
      (Primrec.list_take.to_comp).comp (Computable.list_length.comp hg) hf
    exact ((Primrec.or.to_comp).comp ((Primrec.eq.decide.to_comp).comp hf h1)
      ((Primrec.eq.decide.to_comp).comp hg h2)).of_eq fun p => rfl

/-- Step 2 of the proof of `exists_isOptimalCondDescriptionMode`: trimming a
computable enumeration `E u` of triples keeps it enumerable. The trimmed set contains a triple `t`
enumerated at time `n` iff no triple `s` enumerated at an earlier time `m < n` contradicts `t`
(`s.1 α t.1`, `s.2.2 γ t.2.2` but not `s.2.1 β t.2.1`). The condition is a bounded quantifier over
`m < n` of a decidable test, so `∃ n, ...` is an enumerable search. -/
private theorem exists_isOptimalCondDescriptionMode_trim_isRE (α β γ : StrRel)
    {E : BitString → ℕ → Option (BitString × BitString × BitString)} (hE : Computable₂ E) :
    IsRE (fun q : BitString × BitString × BitString × BitString =>
      ∃ n, E q.1 n = some (q.2.1, q.2.2.1, q.2.2.2) ∧ ∀ m < n, ∀ s, E q.1 m = some s →
        ¬ (α.Holds s.1 q.2.1 ∧ γ.Holds s.2.2 q.2.2.2 ∧ ¬ β.Holds s.2.1 q.2.2.1)) := by
  classical
  let hB := exists_isOptimalCondDescriptionMode_trim_isRE_holdsB
  have hBiff := exists_isOptimalCondDescriptionMode_trim_isRE_holdsB_iff
  have hBc := exists_isOptimalCondDescriptionMode_trim_isRE_holdsB_computable
  let okB : BitString × BitString × BitString × BitString →
      Option (BitString × BitString × BitString) → Bool := fun q o =>
    match o with
    | none => true
    | some s => !(hB α s.1 q.2.1 && hB γ s.2.2 q.2.2.2 && !hB β s.2.1 q.2.2.1)
  let check : (BitString × BitString × BitString × BitString) × ℕ → Bool := fun r =>
    decide (E r.1.1 r.2 = some (r.1.2.1, r.1.2.2.1, r.1.2.2.2)) &&
      Nat.rec (motive := fun _ => Bool) true (fun m acc => acc && okB r.1 (E r.1.1 m)) r.2
  have hokB : Computable₂ (fun (r : (BitString × BitString × BitString × BitString) × ℕ)
      (mb : ℕ × Bool) => okB r.1 (E r.1.1 mb.1)) := by
    have hEm : Computable (fun p : ((BitString × BitString × BitString × BitString) × ℕ) ×
        (ℕ × Bool) => E p.1.1.1 p.2.1) :=
      hE.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
        (Computable.fst.comp Computable.snd)
    have hq : Computable (fun p : (((BitString × BitString × BitString × BitString) × ℕ) ×
        (ℕ × Bool)) × (BitString × BitString × BitString) => p.1.1.1) :=
      Computable.fst.comp (Computable.fst.comp Computable.fst)
    have hs1 : Computable (fun p : (((BitString × BitString × BitString × BitString) × ℕ) ×
        (ℕ × Bool)) × (BitString × BitString × BitString) => p.2.1) :=
      Computable.fst.comp Computable.snd
    have hs2 : Computable (fun p : (((BitString × BitString × BitString × BitString) × ℕ) ×
        (ℕ × Bool)) × (BitString × BitString × BitString) => p.2.2.1) :=
      Computable.fst.comp (Computable.snd.comp Computable.snd)
    have hs3 : Computable (fun p : (((BitString × BitString × BitString × BitString) × ℕ) ×
        (ℕ × Bool)) × (BitString × BitString × BitString) => p.2.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.snd)
    have hq1 : Computable (fun p : (((BitString × BitString × BitString × BitString) × ℕ) ×
        (ℕ × Bool)) × (BitString × BitString × BitString) => p.1.1.1.2.1) :=
      Computable.fst.comp (Computable.snd.comp hq)
    have hq2 : Computable (fun p : (((BitString × BitString × BitString × BitString) × ℕ) ×
        (ℕ × Bool)) × (BitString × BitString × BitString) => p.1.1.1.2.2.1) :=
      Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hq))
    have hq3 : Computable (fun p : (((BitString × BitString × BitString × BitString) × ℕ) ×
        (ℕ × Bool)) × (BitString × BitString × BitString) => p.1.1.1.2.2.2) :=
      Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hq))
    have hsome : Computable₂ (fun (p : ((BitString × BitString × BitString × BitString) × ℕ) ×
        (ℕ × Bool)) (s : BitString × BitString × BitString) =>
        !(hB α s.1 p.1.1.2.1 && hB γ s.2.2 p.1.1.2.2.2 && !hB β s.2.1 p.1.1.2.2.1)) := by
      have a1 := hBc α hs1 hq1
      have a2 := hBc β hs2 hq2
      have a3 := hBc γ hs3 hq3
      exact (Primrec.not.to_comp.comp ((Primrec.and.to_comp.comp
        (Primrec.and.to_comp.comp a1 a3) (Primrec.not.to_comp.comp a2)))).to₂
    exact (Computable.option_casesOn hEm (Computable.const true) hsome).of_eq fun p => by
      beta_reduce
      cases E p.1.1.1 p.2.1 <;> rfl
  have hcheck : Computable check := by
    have hrec : Computable (fun r : (BitString × BitString × BitString × BitString) × ℕ =>
        Nat.rec (motive := fun _ => Bool) true
          (fun m acc => acc && okB r.1 (E r.1.1 m)) r.2) := by
      refine Computable.nat_rec (h := fun (r : (BitString × BitString × BitString × BitString) × ℕ)
        (mb : ℕ × Bool) => mb.2 && okB r.1 (E r.1.1 mb.1)) Computable.snd
        (Computable.const true) ?_
      exact (Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd) hokB).to₂
    have hdec : Computable (fun r : (BitString × BitString × BitString × BitString) × ℕ =>
        decide (E r.1.1 r.2 = some (r.1.2.1, r.1.2.2.1, r.1.2.2.2))) := by
      refine (Primrec.eq.decide.to_comp).comp
        (hE.comp (Computable.fst.comp Computable.fst) Computable.snd) ?_
      exact Computable.option_some.comp (Computable.pair
        (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (Computable.pair (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
            Computable.fst)))
          (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))))
    exact (Primrec.and.to_comp.comp hdec hrec)
  have hREn : IsRE (fun r : (BitString × BitString × BitString × BitString) × ℕ =>
      E r.1.1 r.2 = some (r.1.2.1, r.1.2.2.1, r.1.2.2.2) ∧ ∀ m < r.2, ∀ s, E r.1.1 m = some s →
        ¬ (α.Holds s.1 r.1.2.1 ∧ γ.Holds s.2.2 r.1.2.2.2 ∧ ¬ β.Holds s.2.1 r.1.2.2.1)) := by
    refine isRE_of_computable_bool _ check (fun r => ?_) hcheck
    obtain ⟨q, n⟩ := r
    have hok : ∀ s, okB q (some s) = true ↔
        ¬ (α.Holds s.1 q.2.1 ∧ γ.Holds s.2.2 q.2.2.2 ∧ ¬ β.Holds s.2.1 q.2.2.1) := by
      intro s
      simp only [okB, hB, Bool.not_eq_true', Bool.and_eq_true, Bool.eq_false_iff, ne_eq,
        hBiff]
      tauto
    have key : ∀ k, (Nat.rec (motive := fun _ => Bool) true
        (fun m acc => acc && okB q (E q.1 m)) k = true) ↔ ∀ m < k, ∀ s, E q.1 m = some s →
        ¬ (α.Holds s.1 q.2.1 ∧ γ.Holds s.2.2 q.2.2.2 ∧ ¬ β.Holds s.2.1 q.2.2.1) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        change (_ && okB q (E q.1 k)) = true ↔ _
        rw [Bool.and_eq_true, ih]
        constructor
        · rintro ⟨h1, h2⟩ m hm s hs
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
          · exact h1 m hm s hs
          · rw [hs] at h2
            exact (hok s).1 h2
        · intro h
          refine ⟨fun m hm => h m (Nat.lt_succ_of_lt hm), ?_⟩
          cases hs : E q.1 k with
          | none => rfl
          | some s => exact (hok s).2 (h k (Nat.lt_succ_self k) s hs)
    simp only [check, Bool.and_eq_true, decide_eq_true_eq, key]
  exact (hREn.exists_encodable (R := fun q n => _)).of_iff fun q => Iff.rfl

/-- Step 3 of the proof of `exists_isOptimalCondDescriptionMode`: a computable
prefix-free (self-delimiting) injective code `u ↦ û` of bit strings, e.g. doubling every bit and
appending `01`. -/
private theorem exists_isOptimalCondDescriptionMode_prefixFreeCode :
    ∃ h : BitString → BitString, Computable h ∧ ∀ u₁ u₂, h u₁ <+: h u₂ → u₁ = u₂ := by
  refine ⟨fun u => u.flatMap (fun b => [b, b]) ++ [false, true], ?_, ?_⟩
  · refine Primrec.to_comp ?_
    refine Primrec.list_append.comp
      (Primrec.list_flatMap Primrec.id
        (Primrec.list_cons.comp Primrec.snd
          (Primrec.list_cons.comp Primrec.snd (Primrec.const [])) |>.to₂))
      (Primrec.const [false, true])
  · intro u₁
    induction u₁ with
    | nil =>
      intro u₂ h
      cases u₂ with
      | nil => rfl
      | cons c u₂' => cases c <;> simp at h
    | cons b u₁' ih =>
      intro u₂ h
      cases u₂ with
      | nil => cases b <;> simp at h
      | cons c u₂' =>
        have hbc : b = c := by
          cases b <;> cases c <;> simp at h ⊢
        subst hbc
        obtain ⟨t, ht⟩ := h
        simp only [List.flatMap_cons, List.cons_append, List.cons.injEq, true_and] at ht
        rw [ih u₂' ⟨t, by simpa using ht⟩]

private lemma exists_isOptimalCondDescriptionMode_holds_symm (α : StrRel) {x y : BitString}
    (h : α.Holds x y) : α.Holds y x := by
  cases α
  · exact h.symm
  · exact Or.symm h

/-- **SUV Theorem 129 (Section 6.3, printed p. 200); SUV Problem 200 (printed p. 201).** In each
of the eight classes of `(α, β) | γ`-decompressors there is an optimal one. Problem 200 asks
for the detailed proof of this theorem.

Proof idea: the same scheme as for plain or prefix conditional complexity. Enumerate the
enumerable sets of triples, trim each one to an `(α, β) | γ`-regular set (drop a triple that
contradicts the triples enumerated before), and prefix descriptions with a self-delimiting code
of the index. The prefix `ẑ` preserves the relation `α` between descriptions. -/
theorem exists_isOptimalCondDescriptionMode (α β γ : StrRel) :
    ∃ S, IsOptimalCondDescriptionMode α β γ S := by
  obtain ⟨E, hE, hEuniv⟩ := exists_isOptimalCondDescriptionMode_universalEnumeration
  obtain ⟨h, hh, hpf⟩ := exists_isOptimalCondDescriptionMode_prefixFreeCode
  have hWre := exists_isOptimalCondDescriptionMode_trim_isRE α β γ hE
  let W : BitString → BitString → BitString → BitString → Prop := fun u p x y =>
    ∃ n, E u n = some (p, x, y) ∧ ∀ m < n, ∀ s, E u m = some s →
      ¬ (α.Holds s.1 p ∧ γ.Holds s.2.2 y ∧ ¬ β.Holds s.2.1 x)
  have hWreg : ∀ u, IsCondRegular α β γ (W u) := by
    intro u p₁ x₁ y₁ p₂ x₂ y₂ ⟨n, hn, hno⟩ ⟨m, hm, hmo⟩ hp hy
    by_contra hb
    rcases lt_trichotomy n m with hlt | rfl | hgt
    · exact hmo n hlt _ hn ⟨hp, hy, hb⟩
    · rw [hn] at hm
      have hm' := Option.some.inj hm
      simp only [Prod.mk.injEq] at hm'
      obtain ⟨-, rfl, -⟩ := hm'
      exact hb (β.holds_refl _)
    · exact hno m hgt _ hm ⟨exists_isOptimalCondDescriptionMode_holds_symm α hp,
        exists_isOptimalCondDescriptionMode_holds_symm γ hy,
        fun h => hb (exists_isOptimalCondDescriptionMode_holds_symm β h)⟩
  have hWeq : ∀ T, IsCondDescriptionMode α β γ T → ∃ u, ∀ p x y, T p x y ↔ W u p x y := by
    intro T hT
    obtain ⟨u, hu⟩ := hEuniv T (by simpa using hT.1)
    refine ⟨u, fun p x y => ⟨fun hp => ?_, fun ⟨n, hn, _⟩ => (hu p x y).2 ⟨n, hn⟩⟩⟩
    obtain ⟨n, hn⟩ := (hu p x y).1 hp
    refine ⟨n, hn, fun m _ s hs ⟨h1, h2, h3⟩ => ?_⟩
    obtain ⟨sp, sx, sy⟩ := s
    obtain ⟨m', hm'⟩ : ∃ m', E u m' = some (sp, sx, sy) := ⟨m, hs⟩
    exact h3 (hT.2 ((hu sp sx sy).2 ⟨m', hm'⟩) hp h1 h2)
  refine ⟨fun p x y => ∃ u v, p = h u ++ v ∧ W u v x y, ⟨?_, ?_⟩, ?_⟩
  · have hR : IsRE (fun r : (BitString × BitString × BitString) × (BitString × BitString) =>
        (decide (r.1.1 = h r.2.1 ++ r.2.2) = true) ∧ W r.2.1 r.2.2 r.1.2.1 r.1.2.2) := by
      refine IsRE.and_computable (R := fun r : (BitString × BitString × BitString) ×
        (BitString × BitString) => W r.2.1 r.2.2 r.1.2.1 r.1.2.2) ?_ ?_
      · exact hWre.comp_computable (g := fun r : (BitString × BitString × BitString) ×
          (BitString × BitString) => (r.2.1, r.2.2, r.1.2.1, r.1.2.2))
          (Computable.pair (Computable.fst.comp Computable.snd)
            (Computable.pair (Computable.snd.comp Computable.snd)
              (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
                (Computable.snd.comp (Computable.snd.comp Computable.fst)))))
      · have h1 : Computable (fun r : (BitString × BitString × BitString) ×
            (BitString × BitString) => r.1.1) := Computable.fst.comp Computable.fst
        have h2 : Computable (fun r : (BitString × BitString × BitString) ×
            (BitString × BitString) => h r.2.1 ++ r.2.2) :=
          Computable.list_append.comp (hh.comp (Computable.fst.comp Computable.snd))
            (Computable.snd.comp Computable.snd)
        exact ((Primrec.to_comp (Primrec.beq (α := BitString))).comp
          (Computable.pair h1 h2)).of_eq fun r => by rw [Bool.eq_iff_iff]; simp
    have := IsRE.exists_encodable (R := fun (q : BitString × BitString × BitString)
      (b : BitString × BitString) => (decide (q.1 = h b.1 ++ b.2) = true) ∧ W b.1 b.2 q.2.1 q.2.2)
          hR
    refine this.of_iff fun q => ?_
    constructor
    · rintro ⟨⟨u, v⟩, hq, hw⟩
      exact ⟨u, v, by simpa using hq, hw⟩
    · rintro ⟨u, v, hq, hw⟩
      exact ⟨(u, v), by simpa using hq, hw⟩
  · intro p₁ x₁ y₁ p₂ x₂ y₂ ⟨u₁, v₁, hp₁, hw₁⟩ ⟨u₂, v₂, hp₂, hw₂⟩ hp hy
    subst hp₁ hp₂
    have hp' : h u₁ ++ v₁ <+: h u₂ ++ v₂ ∨ h u₂ ++ v₂ <+: h u₁ ++ v₁ := by
      cases α
      · exact Or.inl (by change h u₁ ++ v₁ = h u₂ ++ v₂ at hp; rw [hp])
      · exact hp
    have hu : u₁ = u₂ := by
      have key : h u₁ <+: h u₂ ∨ h u₂ <+: h u₁ := by
        rcases hp' with h12 | h12
        · exact List.prefix_or_prefix_of_prefix ((List.prefix_append (h u₁) v₁).trans h12)
            (List.prefix_append (h u₂) v₂)
        · exact List.prefix_or_prefix_of_prefix (List.prefix_append (h u₁) v₁)
            ((List.prefix_append (h u₂) v₂).trans h12)
      rcases key with a | a
      · exact hpf _ _ a
      · exact (hpf _ _ a).symm
    subst hu
    refine hWreg u₁ hw₁ hw₂ ?_ hy
    cases α
    · change h u₁ ++ v₁ = h u₁ ++ v₂ at hp
      exact List.append_cancel_left hp
    · rcases hp' with h12 | h12
      · exact Or.inl ((List.prefix_append_right_inj _).1 h12)
      · exact Or.inr ((List.prefix_append_right_inj _).1 h12)
  · intro T hT
    obtain ⟨u, hu⟩ := hWeq T hT
    refine ⟨(h u).length, fun x y => ?_⟩
    unfold condModeComplexity
    by_cases hne : {l : ℕ∞ | ∃ p, T p x y ∧ l = (p.length : ℕ∞)}.Nonempty
    · obtain ⟨p, hTp, hpl⟩ := csInf_mem hne
      rw [hpl]
      refine le_trans (sInf_le (a := (((h u ++ p).length : ℕ) : ℕ∞))
        ⟨h u ++ p, ⟨u, p, rfl, (hu p x y).1 hTp⟩, rfl⟩) ?_
      rw [List.length_append, add_comm]
      push_cast
      exact le_rfl
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, sInf_empty]
      simp

/-- A functional RE relation is the graph of a partial computable function. -/
private lemma exists_const_condModeComplexity_eq_eq_eq_condK_functional {α β : Type*}
    [Primcodable α] [Primcodable β] {R : α → β → Prop}
    (hR : IsRE (fun q : α × β => R q.1 q.2)) (hfun : ∀ a b b', R a b → R a b' → b = b') :
    ∃ f : α →. β, Partrec f ∧ ∀ a b, b ∈ f a ↔ R a b := by
  obtain ⟨g, hg, hdom⟩ := hR
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg
  let step : α → ℕ → Option β := fun a n =>
    (Encodable.decode (α := β) n.unpair.1).bind fun b =>
      if (Nat.Partrec.Code.evaln (n.unpair.2 + 1) c (Encodable.encode (a, b))).isSome
      then some b else none
  have hstep : Computable₂ step := by
    have hdec : Computable (fun p : α × ℕ => Encodable.decode (α := β) p.2.unpair.1) :=
      Computable.decode.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
    have hk : Computable (fun q : (α × ℕ) × β => q.1.2.unpair.2 + 1) :=
      Primrec.to_comp (Primrec.succ.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))))
    have hin : Computable (fun q : (α × ℕ) × β => Encodable.encode (q.1.1, q.2)) :=
      Computable.comp Computable.encode
        (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
    have hev : Computable (fun q : (α × ℕ) × β =>
        (Nat.Partrec.Code.evaln (q.1.2.unpair.2 + 1) c (Encodable.encode (q.1.1, q.2))).isSome) :=
      Primrec.option_isSome.to_comp.comp
        ((evalnCoreComputable c).comp (Computable.pair hk hin))
    have hbody : Computable₂ (fun (p : α × ℕ) (b : β) =>
        if (Nat.Partrec.Code.evaln (p.2.unpair.2 + 1) c (Encodable.encode (p.1, b))).isSome
        then some b else none) := by
      refine (Computable.cond hev (Computable.option_some.comp Computable.snd)
        (Computable.const none)).of_eq fun q => ?_
      cases hh : (Nat.Partrec.Code.evaln (q.1.2.unpair.2 + 1) c
        (Encodable.encode (q.1.1, q.2))).isSome <;> simp only [hh] <;> rfl
    exact Computable.option_bind hdec hbody
  have hsound : ∀ a b, b ∈ Nat.rfindOpt (step a) → R a b := by
    intro a b hb
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hb
    simp only [step, Option.mem_def, Option.bind_eq_some_iff] at hn
    obtain ⟨b', -, hb'⟩ := hn
    split_ifs at hb' with hsome
    · obtain rfl : b' = b := Option.some.inj hb'
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
      have hx' := Nat.Partrec.Code.evaln_sound hx
      rw [hc] at hx'
      have hd : (g (a, b')).Dom := by
        have := Part.dom_iff_mem.mpr ⟨x, hx'⟩
        simpa [Part.bind_dom] using this
      exact (hdom (a, b')).mp hd
  refine ⟨fun a => Nat.rfindOpt (step a), Partrec.rfindOpt hstep, fun a b => ⟨hsound a b, fun hab =>
      ?_⟩⟩
  have hd : (g (a, b)).Dom := (hdom (a, b)).mpr hab
  have hev : (c.eval (Encodable.encode (a, b))).Dom := by
    rw [hc]
    simpa [Part.bind_dom] using hd
  obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hev
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hx
  have hk' := Nat.Partrec.Code.evaln_mono (Nat.le_succ k) hk
  have hmem : b ∈ step a (Nat.pair (Encodable.encode b) k) := by
    simp only [step, Nat.unpair_pair, Encodable.encodek, Option.mem_def, Option.bind_some]
    rw [ite_eq_left (Option.isSome_iff_exists.mpr ⟨x, hk'⟩)]
  have hdm : (Nat.rfindOpt (step a)).Dom := Nat.rfindOpt_dom.mpr ⟨_, _, hmem⟩
  obtain ⟨b', hb'⟩ := Part.dom_iff_mem.mp hdm
  have hb'' := hsound a b' hb'
  rw [hfun a b' b hb'' hab] at hb'
  exact hb'

/-- **SUV Section 6.3 (printed p. 201), notation remark.** `C(x | y)` is `K(=,=)|=`: the optimal
`(=, =) | =` complexity is plain conditional complexity up to `O(1)`.

Proof idea: `(=, =) | =`-regular enumerable sets of triples are graphs of partial computable
functions of `(p, y)`. -/
theorem exists_const_condModeComplexity_eq_eq_eq_condK
    {S : BitString → BitString → BitString → Prop} (hS : IsOptimalCondDescriptionMode .eq .eq .eq S)
    {U : Map} (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x y,
      condModeComplexity S x y ≤ condK U x y + c ∧ condK U x y ≤ condModeComplexity S x y + c := by
  obtain ⟨⟨hRE, hreg⟩, hopt⟩ := hS
  obtain ⟨hUdec, hUopt⟩ := hU
  -- `S` is the graph of a partial computable function `D`
  have hRE' : IsRE (fun q : (BitString × BitString) × BitString => S q.1.1 q.2 q.1.2) := by
    obtain ⟨f, hf, hd⟩ := hRE
    refine ⟨fun q => f (q.1.1, q.2, q.1.2), ?_, fun q => hd _⟩
    exact hf.comp (Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair Computable.snd (Computable.snd.comp Computable.fst)))
  obtain ⟨D, hD, hDS⟩ := exists_const_condModeComplexity_eq_eq_eq_condK_functional
    (R := fun (a : BitString × BitString) (x : BitString) => S a.1 x a.2) hRE'
    (fun a b b' h h' => hreg h h' rfl rfl)
  obtain ⟨c₁, hc₁⟩ := hUopt D hD
  -- conversely, `U` is itself an `(=, =) | =` decompressor
  let T : BitString → BitString → BitString → Prop := fun p x y => x ∈ U (p, y)
  have hTRE : IsRE (fun q : BitString × BitString × BitString => T q.1 q.2.1 q.2.2) := by
    obtain ⟨f, hf, hd⟩ := Partrec.graphIsRe U hUdec
    refine ⟨fun q => f ((q.1, q.2.2), q.2.1), ?_, fun q => hd _⟩
    exact hf.comp (Computable.pair
      (Computable.pair Computable.fst (Computable.snd.comp Computable.snd))
      (Computable.fst.comp Computable.snd))
  have hTreg : IsCondRegular .eq .eq .eq T := by
    intro p₁ x₁ y₁ p₂ x₂ y₂ h₁ h₂ hp hy
    change p₁ = p₂ at hp
    change y₁ = y₂ at hy
    subst hp hy
    exact Part.mem_unique h₁ h₂
  obtain ⟨c₂, hc₂⟩ := hopt T ⟨hTRE, hTreg⟩
  have hT : ∀ x y, condModeComplexity T x y = condK U x y := by
    intro x y
    unfold condModeComplexity condK
    congr 1
    ext l
    simp only [Set.mem_ofPred_eq, candidateLengths, produces, programLength, T]
    constructor <;> rintro ⟨p, hp, rfl⟩ <;> exact ⟨p, hp, rfl⟩
  have hDK : ∀ x y, condK D x y = condModeComplexity S x y := by
    intro x y
    unfold condModeComplexity condK
    congr 1
    ext l
    simp only [Set.mem_ofPred_eq, candidateLengths, produces, programLength]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, (hDS (p, y) x).mp hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, (hDS (p, y) x).mpr hp, rfl⟩
  refine ⟨max c₁ c₂, fun x y => ⟨?_, ?_⟩⟩
  · calc condModeComplexity S x y ≤ condModeComplexity T x y + c₂ := hc₂ x y
      _ = condK U x y + c₂ := by rw [hT]
      _ ≤ condK U x y + (max c₁ c₂ : ℕ) := by
        gcongr; exact_mod_cast le_max_right _ _
  · calc condK U x y ≤ condK D x y + c₁ := hc₁ x y
      _ = condModeComplexity S x y + c₁ := by rw [hDK]
      _ ≤ condModeComplexity S x y + (max c₁ c₂ : ℕ) := by
        gcongr; exact_mod_cast le_max_left _ _

/-- Step 1 of the proof of `exists_const_condModeComplexity_compat_eq_eq_KP`: the
easy direction. The graph `{(p, x, y) | x ∈ U (p, y)}` of a prefix decompressor `U` is a
`(≍, =) | =`-decompressor, so the optimal `S` is below it, and its complexity is `KP U`. -/
private theorem exists_const_condModeComplexity_compat_eq_eq_KP_le_KP
    {S : BitString → BitString → BitString → Prop}
    (hS : IsOptimalCondDescriptionMode .compat .eq .eq S) {U : Map}
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, condModeComplexity S x y ≤ KP U x y + c := by
  have hT : IsCondDescriptionMode .compat .eq .eq
      (fun p x y => x ∈ U (p, y)) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨g, hg, hdom⟩ := Partrec.graphIsRe U hU.isDecompressor
      refine ⟨fun q => g ((q.1, q.2.2), q.2.1), hg.comp ?_, fun q => hdom _⟩
      exact Computable.pair (Computable.pair Computable.fst (Computable.snd.comp Computable.snd))
        (Computable.fst.comp Computable.snd)
    · intro p₁ x₁ y₁ p₂ x₂ y₂ h₁ h₂ hp hy
      change x₁ = x₂
      subst hy
      have hpp : p₁ = p₂ := by
        rcases hp with hp | hp
        · exact hU.isPrefixMachine.eq_of_prefix h₁ h₂ hp
        · exact (hU.isPrefixMachine.eq_of_prefix h₂ h₁ hp).symm
      subst hpp
      exact Part.mem_unique h₁ h₂
  obtain ⟨c, hc⟩ := hS.2 _ hT
  refine ⟨c, fun x y => (hc x y).trans ?_⟩
  refine add_le_add_left (le_of_eq ?_) _
  unfold condModeComplexity KP condK
  congr 1
  ext l
  constructor <;> rintro ⟨p, h, e⟩ <;> exact ⟨p, h, e.symm⟩

/-- Step 2 of the proof of `exists_const_condModeComplexity_compat_eq_eq_KP`: a
`(≍, =) | =`-decompressor `S` gives a prefix-stable decompressor `M` with
`K_M(x | y) ≤ K_S(x | y)`. Take `M(p, y) = x` iff some prefix `q` of `p` has `S q x y`; this is
well defined by regularity (two comparable `q`'s with the same condition give the same `x`),
enumerable (dovetail over the finitely many prefixes of `p`), and prefix-stable by
construction. -/
private theorem exists_const_condModeComplexity_compat_eq_eq_KP_prefixStable
    {S : BitString → BitString → BitString → Prop}
    (hS : IsCondDescriptionMode .compat .eq .eq S) :
    ∃ M : Map, IsPrefixStableDecompressor M ∧ ∀ x y, condK M x y ≤ condModeComplexity S x y := by
  obtain ⟨hRE, hreg⟩ := hS
  have hpre : IsRE (fun r : ((BitString × BitString) × BitString) × BitString =>
      r.2 <+: r.1.1.1) := by
    have hp : Computable (fun r : ((BitString × BitString) × BitString) × BitString =>
        decide (r.2 <+: r.1.1.1)) := by
      have htake : Primrec (fun p : BitString × BitString => p.1.take p.2.length) :=
        Primrec.list_take.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst
      have hrel : PrimrecPred (fun p : BitString × BitString => p.1.take p.2.length = p.2) :=
        PrimrecRel.comp Primrec.eq htake Primrec.snd
      have hpf : Primrec (fun p : BitString × BitString => decide (p.2 <+: p.1)) := by
        refine hrel.decide.of_eq fun p => ?_
        simp only [decide_eq_decide]
        exact eq_comm.trans List.prefix_iff_eq_take.symm
      exact (hpf.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd)).to_comp
    exact (IsRE_of_computable hp).of_iff fun q => by simp
  have hA : IsRE (fun r : ((BitString × BitString) × BitString) × BitString =>
      r.2 <+: r.1.1.1 ∧ S r.2 r.1.2 r.1.1.2) :=
    hpre.and (hRE.comp_computable
      (g := fun r : ((BitString × BitString) × BitString) × BitString =>
        (r.2, r.1.2, r.1.1.2)) (Computable.pair Computable.snd
        (Computable.pair (Computable.snd.comp Computable.fst)
          (Computable.snd.comp (Computable.fst.comp Computable.fst)))))
  have hQ := IsRE.exists_encodable
    (R := fun (a : (BitString × BitString) × BitString) (b : BitString) =>
      b <+: a.1.1 ∧ S b a.2 a.1.2) hA
  obtain ⟨f, hf, hfQ⟩ := exists_const_condModeComplexity_eq_eq_eq_condK_functional
    (R := fun (a : BitString × BitString) (x : BitString) => ∃ q, q <+: a.1 ∧ S q x a.2)
    (IsRE.of_iff hQ fun _ => by rfl) (by
      rintro ⟨u, y⟩ x x' ⟨p₁, h₁, h₁'⟩ ⟨p₂, h₂, h₂'⟩
      exact hreg h₁' h₂' (List.prefix_or_prefix_of_prefix h₁ h₂) rfl)
  refine ⟨f, ⟨hf, ?_⟩, fun x y => ?_⟩
  · intro c u v z hz huv
    obtain ⟨p', hp', hR'⟩ := (hfQ (u, c) z).1 hz
    exact (hfQ (v, c) z).2 ⟨p', hp'.trans huv, hR'⟩
  · refine le_sInf ?_
    rintro l ⟨p, hp, rfl⟩
    exact sInf_le ⟨p, (hfQ (p, y) x).2 ⟨p, List.prefix_refl p, hp⟩, rfl⟩

/-- The list of all bit strings of a given length is computable. -/
private lemma exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_allStrings :
    Computable allStrings := by
  have h : allStrings = fun s => Nat.rec [[]]
      (fun _ IH => IH.map (fun x => false :: x) ++ IH.map (fun x => true :: x)) s := by
    funext s
    induction s with
    | zero => rfl
    | succ s ih =>
      dsimp [allStrings]
      rw [ih]
  rw [h]
  apply Primrec.to_comp
  apply Primrec.nat_rec₁
  apply Primrec.list_append.comp
  · apply Primrec.list_map Primrec₂.right
    apply Primrec.list_cons.comp (Primrec.const false) Primrec₂.right
  · apply Primrec.list_map Primrec₂.right
    apply Primrec.list_cons.comp (Primrec.const true) Primrec₂.right

/-- The stage-`s` numerator of the semimeasure of a prefix-stable machine: the number of strings
`w` of length `s` with a prefix `w.take k` (`k ≤ s`) on which the stage-`s` check `chk` accepts
the output `x` under the condition `y`. Divided by `2 ^ s`, it is the measure of the union of the
cylinders of these prefixes. -/
private def exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count
    (chk : (BitString × BitString) × BitString → ℕ → Bool) (s : ℕ) (x y : BitString) : ℕ :=
  ((allStrings s).filter fun w =>
    (List.range (s + 1)).any fun k => chk ((w.take k, y), x) s).length

/-- The stage-`s` count is computable when the check `chk` is. -/
private lemma exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count_computable
    {chk : (BitString × BitString) × BitString → ℕ → Bool} (hchk : Computable₂ chk) :
    Computable (fun q : ℕ × BitString × BitString =>
      exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count chk
        q.1 q.2.1 q.2.2) := by
  have hany : Computable₂ (fun (q : ℕ × BitString × BitString) (w : BitString) =>
      (List.range (q.1 + 1)).any fun k => chk ((w.take k, q.2.2), q.2.1) q.1) := by
    have heq : ∀ (l : List ℕ) (g : ℕ → Bool),
        l.any g = l.foldr (fun k acc => g k || acc) false := by
      intro l g
      induction l with
      | nil => rfl
      | cons b t ih => simp [List.any_cons, ih]
    have hrange : Computable (fun r : (ℕ × BitString × BitString) × BitString =>
        List.range (r.1.1 + 1)) :=
      Primrec.to_comp (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.fst)))
    have htake : Computable (fun z : ((ℕ × BitString × BitString) × BitString) × (ℕ × Bool) =>
        z.1.2.take z.2.1) :=
      Primrec.to_comp (Primrec.list_take.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
    have hc : Computable (fun z : ((ℕ × BitString × BitString) × BitString) × (ℕ × Bool) =>
        chk ((z.1.2.take z.2.1, z.1.1.2.2), z.1.1.2.1) z.1.1.1) :=
      hchk.comp (Computable.pair (Computable.pair htake
        (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))))
        (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))))
        (Computable.fst.comp (Computable.fst.comp Computable.fst))
    have hstep : Computable₂ (fun (r : (ℕ × BitString × BitString) × BitString)
        (kb : ℕ × Bool) => chk ((r.2.take kb.1, r.1.2.2), r.1.2.1) r.1.1 || kb.2) :=
      (Primrec.or.to_comp.comp hc (Computable.snd.comp Computable.snd)).to₂
    have hf := Computable.list_foldr hrange (Computable.const false) hstep
    exact hf.of_eq fun r => by dsimp only; exact (heq _ _).symm
  have hcount_eq : ∀ (l : List BitString) (P : BitString → Bool),
      (l.filter P).length = l.foldr (fun w n => bif P w then n.succ else n) 0 := by
    intro l P
    induction l with
    | nil => rfl
    | cons w t ih => cases hw : P w <;> simp [hw, ih]
  have hfold : Computable (fun q : ℕ × BitString × BitString =>
      (allStrings q.1).foldr (fun w n =>
        bif ((List.range (q.1 + 1)).any fun k => chk ((w.take k, q.2.2), q.2.1) q.1)
        then n.succ else n) 0) :=
    Computable.list_foldr
      (exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_allStrings.comp
        Computable.fst) (Computable.const 0)
      (Computable.cond (hany.comp Computable.fst (Computable.fst.comp Computable.snd))
        (Computable.succ.comp (Computable.snd.comp Computable.snd))
        (Computable.snd.comp Computable.snd)).to₂
  refine hfold.of_eq fun q => ?_
  rw [exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count, hcount_eq]

/-- The stage-`s` count as the cardinality of a filtered `stringsOfLength s`. -/
private lemma exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count_eq_card
    (chk : (BitString × BitString) × BitString → ℕ → Bool) (s : ℕ) (x y : BitString) :
    exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count chk s x y =
      ((stringsOfLength s).filter fun w =>
        ((List.range (s + 1)).any fun k => chk ((w.take k, y), x) s) = true).card := by
  unfold exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count
    stringsOfLength
  rw [← List.toFinset_filter, List.toFinset_card_of_nodup ((allStrings_nodup s).filter _)]

/-- Doubling: every accepted string of length `s` has two accepted extensions of length
`s + 1`. -/
private lemma exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count_mono
    {chk : (BitString × BitString) × BitString → ℕ → Bool}
    (hmon : ∀ a s t, s ≤ t → chk a s = true → chk a t = true) (s : ℕ) (x y : BitString) :
    2 * exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count chk s x y ≤
      exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count chk
        (s + 1) x y := by
  rw [exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count_eq_card,
    exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count_eq_card]
  have h := Finset.card_le_card_of_injOn (s := ((stringsOfLength s).filter fun w =>
        ((List.range (s + 1)).any fun k => chk ((w.take k, y), x) s) = true) ×ˢ
      (Finset.univ : Finset Bool))
    (t := (stringsOfLength (s + 1)).filter fun w =>
        ((List.range (s + 1 + 1)).any fun k => chk ((w.take k, y), x) (s + 1)) = true)
    (fun q => q.1 ++ [q.2]) ?_ ?_
  · rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at h
    omega
  · intro q hq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      mem_stringsOfLength, List.any_eq_true, List.mem_range] at hq
    obtain ⟨⟨hlen, k, hk, hck⟩, -⟩ := hq
    simp only [Finset.mem_coe, Finset.mem_filter, mem_stringsOfLength, List.length_append, hlen,
      List.length_singleton, List.any_eq_true, List.mem_range, true_and]
    refine ⟨k, by omega, ?_⟩
    rw [List.take_append_of_le_length (by omega)]
    exact hmon _ _ _ (Nat.le_succ s) hck
  · intro q hq q' hq' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      mem_stringsOfLength] at hq hq'
    obtain ⟨h1, h2⟩ := List.append_inj heq (by rw [hq.1.1, hq'.1.1])
    exact Prod.ext h1 (by simpa using h2)

/-- If `chk` accepts `x` on `p` at stage `s₀`, then at stage `|p| + s₀` all `2 ^ s₀` extensions
of `p` of length `|p| + s₀` are counted. -/
private lemma exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count_lower
    {chk : (BitString × BitString) × BitString → ℕ → Bool}
    (hmon : ∀ a s t, s ≤ t → chk a s = true → chk a t = true) {p x y : BitString} {s₀ : ℕ}
    (h : chk ((p, y), x) s₀ = true) :
    2 ^ s₀ ≤ exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count chk
      (p.length + s₀) x y := by
  rw [exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count_eq_card,
    ← card_stringsOfLength s₀]
  refine Finset.card_le_card_of_injOn (fun v => p ++ v) ?_ ?_
  · intro v hv
    simp only [Finset.mem_coe, mem_stringsOfLength] at hv
    simp only [Finset.mem_coe, Finset.mem_filter, mem_stringsOfLength, List.length_append, hv,
      true_and, List.any_eq_true, List.mem_range]
    refine ⟨p.length, by omega, ?_⟩
    rw [List.take_left]
    exact hmon _ _ _ (Nat.le_add_left _ _) h
  · intro v _ v' _ heq
    exact List.append_cancel_left heq

/-- Disjointness: by prefix stability and single-valuedness, a string of length `s` is counted
for at most one output `x`, so the counts of distinct outputs add up to at most `2 ^ s`. -/
private lemma exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count_sum
    {M : Map} (hM : IsPrefixStableMachine M)
    {chk : (BitString × BitString) × BitString → ℕ → Bool}
    (hsound : ∀ a s, chk a s = true → a.2 ∈ M a.1) (s : ℕ) (y : BitString)
    (F : Finset BitString) :
    ∑ x ∈ F, exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count chk
      s x y ≤ 2 ^ s := by
  rw [Finset.sum_congr rfl fun x _ =>
    exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count_eq_card chk s x
        y,
    ← Finset.card_biUnion, ← card_stringsOfLength s]
  · refine Finset.card_le_card fun w hw => ?_
    simp only [Finset.mem_biUnion, Finset.mem_filter] at hw
    obtain ⟨x, -, hw, -⟩ := hw
    exact hw
  · intro x _ x' _ hxx'
    refine Finset.disjoint_left.mpr fun w hw hw' => hxx' ?_
    simp only [Finset.mem_filter, mem_stringsOfLength, List.any_eq_true, List.mem_range] at hw hw'
    obtain ⟨-, k, -, hc⟩ := hw
    obtain ⟨-, k', -, hc'⟩ := hw'
    have h1 : x ∈ M (w, y) := hM y _ _ _ (hsound _ _ hc) (List.take_prefix k w)
    have h2 : x' ∈ M (w, y) := hM y _ _ _ (hsound _ _ hc') (List.take_prefix k' w)
    exact Part.mem_unique h1 h2

/-- The semimeasure of a prefix-stable machine is lower semicomputable. -/
private lemma exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_isLSC
    {chk : (BitString × BitString) × BitString → ℕ → Bool} (hchk : Computable₂ chk)
    (hmon : ∀ a s t, s ≤ t → chk a s = true → chk a t = true) :
    IsLSC (fun x y => ⨆ s, dyadicValue
      (exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count chk s x y)
      s) := by
  refine ⟨exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count chk,
    fun s x y => ?_, fun _ _ => rfl,
    exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count_computable hchk⟩
  rw [← dyadicValue_two_mul_succ]
  exact monotone_dyadicValue_num _
    (exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count_mono hmon s x y)

/-- The semimeasure of a prefix-stable machine has mass at most `1` for every condition. -/
private lemma exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_tsum_le
    {M : Map} (hM : IsPrefixStableMachine M)
    {chk : (BitString × BitString) × BitString → ℕ → Bool}
    (hmon : ∀ a s t, s ≤ t → chk a s = true → chk a t = true)
    (hsound : ∀ a s, chk a s = true → a.2 ∈ M a.1) (y : BitString) :
    ∑' x, (⨆ s, dyadicValue
      (exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count chk s x y)
      s) ≤ 2 ^ 0 := by
  rw [pow_zero, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  rw [ENNReal.finsetSum_iSup_of_monotone fun x => monotone_nat_of_le_succ fun s => ?_]
  · refine iSup_le fun s => ?_
    have hsum : ∑ x ∈ F, dyadicValue
        (exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count chk s x y)
        s = dyadicValue (∑ x ∈ F,
          exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count chk
            s x y) s := by
      simp only [dyadicValue, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
    rw [hsum]
    calc _ ≤ dyadicValue (2 ^ s) s := monotone_dyadicValue_num s
          (exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count_sum hM
            hsound s y F)
      _ = 1 := by
          unfold dyadicValue
          push_cast
          exact ENNReal.div_self (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top
              ENNReal.ofNat_ne_top)
  · rw [← dyadicValue_two_mul_succ]
    exact monotone_dyadicValue_num _
      (exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count_mono hmon s x
          y)

/-- The semimeasure of a prefix-stable machine `M` is at least `2 ^ (-K_M(x | y))`. -/
private lemma exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_weight_le
    {M : Map} {chk : (BitString × BitString) × BitString → ℕ → Bool}
    (hmon : ∀ a s t, s ≤ t → chk a s = true → chk a t = true)
    (hcomplete : ∀ a, a.2 ∈ M a.1 → ∃ s, chk a s = true) (x y : BitString) :
    complexityWeight (condK M x y) ≤ ⨆ s, dyadicValue
      (exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count chk s x y)
      s := by
  rcases Set.eq_empty_or_nonempty (candidateLengths M x y) with he | hne
  · have htop : condK M x y = ⊤ := by rw [condK, he, sInf_empty]
    rw [htop, complexityWeight_top]
    exact bot_le
  · have hmem : condK M x y ∈ candidateLengths M x y := by
      rw [condK]; exact csInf_mem hne
    obtain ⟨p, hp, hlen⟩ := hmem
    rw [← hlen, complexityWeight_programLength]
    obtain ⟨s₀, hs₀⟩ := hcomplete ((p, y), x) hp
    refine le_trans ?_ (le_iSup _ (p.length + s₀))
    calc progWeight p
        = dyadicValue (2 ^ (p.length + s₀ - p.length)) (p.length + s₀) :=
          (dyadicValue_two_pow_sub (Nat.le_add_right _ _)).symm
      _ ≤ _ := monotone_dyadicValue_num _ (by
          rw [Nat.add_sub_cancel_left]
          exact exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count_lower
            hmon hs₀)

/-- Step 3 of the proof of `exists_const_condModeComplexity_compat_eq_eq_KP`
(SUV Section 4.7: prefix-stable and prefix-free complexities agree up to `O(1)`): an optimal
prefix-free conditional decompressor `U` is below every prefix-stable decompressor `M` up to an
additive constant, `KP U x y ≤ K_M(x | y) + c`. -/
private theorem exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable
    {U : Map} (hU : IsOptimalPrefixConditional U) {M : Map}
    (hM : IsPrefixStableDecompressor M) :
    ∃ c : ℕ, ∀ x y, KP U x y ≤ condK M x y + c := by
  obtain ⟨hMdec, hMst⟩ := hM
  obtain ⟨chk, hchk, hmon, hchk_iff⟩ := IsRE.exists_stageApprox (Partrec.graphIsRe M hMdec)
  have hsound : ∀ a s, chk a s = true → a.2 ∈ M a.1 := fun a s h => (hchk_iff a).2 ⟨s, h⟩
  have hcomplete : ∀ a, a.2 ∈ M a.1 → ∃ s, chk a s = true := fun a h => (hchk_iff a).1 h
  obtain ⟨M', hM', c₀, hc₀⟩ := kraftChaitin_realization_bound
    (exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_isLSC hchk hmon) 0
    (exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_tsum_le hMst hmon
      hsound)
  obtain ⟨c, hc⟩ := complexityWeight_dominates_of_prefix_realization hU hM' hc₀
  refine ⟨c, fun x y => ?_⟩
  by_cases htop : condK M x y = ⊤
  · rw [htop, top_add]
    exact le_top
  · refine le_add_nat_of_complexityWeight_le htop ?_
    calc (2 : ENNReal)⁻¹ ^ c * complexityWeight (condK M x y)
        ≤ (2 : ENNReal)⁻¹ ^ c * ⨆ s, dyadicValue
          (exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_count chk
            s x y) s := by
          gcongr
          exact exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable_weight_le
            hmon hcomplete x y
      _ ≤ complexityWeight (KP U x y) := hc x y

/-- **SUV Section 6.3 (printed p. 201), notation remark.** `K(x | y)` is `K(≍,=)|=`: the optimal
`(≍, =) | =` complexity is conditional prefix complexity up to `O(1)`. `KP U x y` is computed
with an optimal prefix-free conditional decompressor.

Proof idea: `(≍, =) | =`-regular enumerable sets give conditional decompressors that are
prefix-stable in `p`. Prefix-stable and prefix-free conditional complexities agree up to `O(1)`
(Section 4.7). -/
theorem exists_const_condModeComplexity_compat_eq_eq_KP
    {S : BitString → BitString → BitString → Prop}
    (hS : IsOptimalCondDescriptionMode .compat .eq .eq S) {U : Map}
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y,
      condModeComplexity S x y ≤ KP U x y + c ∧ KP U x y ≤ condModeComplexity S x y + c := by
  obtain ⟨c₁, h₁⟩ := exists_const_condModeComplexity_compat_eq_eq_KP_le_KP hS hU
  obtain ⟨M, hM, hMS⟩ := exists_const_condModeComplexity_compat_eq_eq_KP_prefixStable hS.1
  obtain ⟨c₃, h₃⟩ := exists_const_condModeComplexity_compat_eq_eq_KP_KP_le_prefixStable hU hM
  refine ⟨c₁ + c₃, fun x y => ⟨?_, ?_⟩⟩
  · calc condModeComplexity S x y ≤ KP U x y + c₁ := h₁ x y
      _ ≤ KP U x y + ((c₁ + c₃ : ℕ) : ℕ∞) := by
        gcongr; exact_mod_cast Nat.le_add_right _ _
  · calc KP U x y ≤ condK M x y + c₃ := h₃ x y
      _ ≤ condModeComplexity S x y + c₃ := by gcongr; exact hMS x y
      _ ≤ condModeComplexity S x y + ((c₁ + c₃ : ℕ) : ℕ∞) := by
        gcongr; exact_mod_cast Nat.le_add_left _ _

/-- **SUV Problem 201 (Section 6.3, printed p. 201).** Replacing `=` by `≍` in the place of `γ`
can only increase the complexity: `K(α,β)|= ≤ K(α,β)|≍ + O(1)`. Requiring regularity for
compatible conditions is a stronger restriction, so there are fewer decompressors. -/
theorem exists_const_condModeComplexity_eq_le_compat {α β : StrRel}
    {S T : BitString → BitString → BitString → Prop} (hS : IsOptimalCondDescriptionMode α β .eq S)
    (hT : IsOptimalCondDescriptionMode α β .compat T) :
    ∃ c : ℕ, ∀ x y, condModeComplexity S x y ≤ condModeComplexity T x y + c :=
  hS.2 T hT.1.of_compat

/-- Applying a fixed partial recursive map raises plain complexity by at most an additive
constant. -/
private lemma exists_const_plainK_le_condModeComplexity_add_KROf_partrecMap
    (V : Map) (hV : isOptimalConditional V) (f : BitString →. BitString) (hf : Partrec f) :
    ∃ c : ℕ, ∀ x w : BitString, w ∈ f x → plainK V w ≤ plainK V x + (c : ENat) := by
  set D : Map := fun pr ↦ (V pr).bind (fun z ↦ f z) with hDdef
  have hD_decomp : isDecompressor D :=
    Partrec.bind hV.1 (hf.comp Computable.snd)
  obtain ⟨c, hc⟩ := hV.2 D hD_decomp
  refine ⟨c, fun x w hw ↦ ?_⟩
  calc
    plainK V w ≤ plainK D w + (c : ENat) := hc w []
    _ ≤ plainK V x + (c : ENat) := by
      have : plainK D w ≤ plainK V x := by
        unfold plainK condK
        apply le_sInf
        rintro n ⟨p, hp, rfl⟩
        apply sInf_le
        refine ⟨p, ?_, rfl⟩
        simp only [produces, hDdef]
        exact Part.mem_bind_iff.mpr ⟨x, hp, hw⟩
      gcongr

/-- A finite minimum in `ℕ∞` of lengths is attained. -/
private lemma exists_const_plainK_le_condModeComplexity_add_KROf_attained
    {P : BitString → Prop} (h : sInf {l : ℕ∞ | ∃ p, P p ∧ l = p.length} ≠ ⊤) :
    ∃ p, P p ∧ ((p.length : ℕ) : ℕ∞) = sInf {l : ℕ∞ | ∃ p, P p ∧ l = p.length} := by
  have hne : {l : ℕ∞ | ∃ p, P p ∧ l = p.length}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, sInf_empty] at h
    exact h rfl
  obtain ⟨p, hp, hpe⟩ := csInf_mem hne
  exact ⟨p, hp, hpe.symm⟩

/-- The plain machine: from `pairCode (bits |q|) (q ++ p)` it recovers `q` and `p`, then searches
for a triple `(x', y', z')` with `S p x' y'`, `R q z'` and `y' <+: z'`, and outputs `x'`. -/
private lemma exists_const_plainK_le_condModeComplexity_add_KROf_machine
    {S : BitString → BitString → BitString → Prop}
    (hS : IsCondDescriptionMode .eq .eq .compat S) (R : DecisionDecompressor) :
    ∃ f : BitString →. BitString, Partrec f ∧ ∀ p q x y : BitString, S p x y → R.rel q y →
      x ∈ f (pairCode (Nat.bits q.length) (q ++ p)) := by
  obtain ⟨chkS, hchkS, hmonS, hchkS_iff⟩ := IsRE.exists_stageApprox hS.1
  obtain ⟨chkR, hchkR, hmonR, hchkR_iff⟩ := IsRE.exists_stageApprox R.re
  let cand : ℕ → BitString × BitString × BitString := fun t =>
    (Encodable.decode (α := BitString × BitString × BitString) (Nat.unpair t).2).getD ([], [], [])
  have hcand : Computable cand :=
    Computable.option_getD
      (Computable.decode.comp (Primrec.snd.comp Primrec.unpair).to_comp) (Computable.const _)
  let nn : BitString → ℕ := fun z => decodeBits (decodeFirst z)
  have hnn : Computable nn := decodeBits_computable.comp decodeFirst_computable
  let pz : BitString → BitString := fun z => (decodeSecond z).drop (nn z)
  let qz : BitString → BitString := fun z => (decodeSecond z).take (nn z)
  have hpz : Computable pz :=
    (Primrec.list_drop.to_comp.comp hnn decodeSecond_computable)
  have hqz : Computable qz :=
    (Primrec.list_take.to_comp.comp hnn decodeSecond_computable)
  let pred : BitString → ℕ → Bool := fun z t =>
    chkS (pz z, (cand t).1, (cand t).2.1) (Nat.unpair t).1 &&
      chkR (qz z, (cand t).2.2) (Nat.unpair t).1 &&
      decide ((cand t).2.2.take (cand t).2.1.length = (cand t).2.1)
  have hpred : Computable₂ pred := by
    have hc2 : Computable (fun q : BitString × ℕ => cand q.2) := hcand.comp Computable.snd
    have hs1 : Computable (fun q : BitString × ℕ => (Nat.unpair q.2).1) :=
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have hA : Computable₂ (fun (z : BitString) (t : ℕ) =>
        chkS (pz z, (cand t).1, (cand t).2.1) (Nat.unpair t).1) :=
      hchkS.comp (Computable.pair (hpz.comp Computable.fst)
        (Computable.pair (Computable.fst.comp hc2)
          (Computable.fst.comp (Computable.snd.comp hc2)))) hs1
    have hB : Computable₂ (fun (z : BitString) (t : ℕ) =>
        chkR (qz z, (cand t).2.2) (Nat.unpair t).1) :=
      hchkR.comp (Computable.pair (hqz.comp Computable.fst)
        (Computable.snd.comp (Computable.snd.comp hc2))) hs1
    have hdec : Computable (fun q : BitString × BitString => decide (q.1 = q.2)) :=
      Primrec.to_comp (PrimrecPred.decide Primrec.eq)
    have hT : Computable (fun q : BitString × ℕ =>
        (cand q.2).2.2.take (cand q.2).2.1.length) :=
      (Primrec.list_take.to_comp).comp
        (Computable.list_length.comp (Computable.fst.comp (Computable.snd.comp hc2)))
        (Computable.snd.comp (Computable.snd.comp hc2))
    have hC : Computable₂ (fun (z : BitString) (t : ℕ) =>
        decide ((cand t).2.2.take (cand t).2.1.length = (cand t).2.1)) :=
      (hdec.comp (Computable.pair hT (Computable.fst.comp (Computable.snd.comp hc2)))).of_eq
        fun q => rfl
    have hAB : Computable₂ (fun (z : BitString) (t : ℕ) =>
        (chkS (pz z, (cand t).1, (cand t).2.1) (Nat.unpair t).1 &&
          chkR (qz z, (cand t).2.2) (Nat.unpair t).1)) :=
      Primrec.and.to_comp.comp hA hB
    refine (Primrec.and.to_comp.comp hAB hC).of_eq fun q => ?_
    rfl
  let P : BitString → ℕ →. Bool := fun z t => Part.some (pred z t)
  refine ⟨fun z => (Nat.rfind (P z)).map (fun t => (cand t).1), ?_, ?_⟩
  · exact Partrec.map (Partrec.rfind (Computable₂.partrec₂ hpred))
      (Computable.fst.comp (hcand.comp Computable.snd)).to₂
  · intro p q x y hSp hRq
    have hz : pz (pairCode (Nat.bits q.length) (q ++ p)) = p ∧
        qz (pairCode (Nat.bits q.length) (q ++ p)) = q := by
      simp [pz, qz, nn, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
    set z0 := pairCode (Nat.bits q.length) (q ++ p)
    have hdom : (Nat.rfind (P z0)).Dom := by
      rw [Nat.rfind_dom]
      obtain ⟨s₁, hs₁⟩ := (hchkS_iff (p, x, y)).mp hSp
      obtain ⟨s₂, hs₂⟩ := (hchkR_iff (q, y)).mp hRq
      refine ⟨Nat.pair (max s₁ s₂) (Encodable.encode (x, y, y)), ?_, fun {m} _ => trivial⟩
      refine Part.mem_some_iff.mpr ?_
      have h1 := hmonS _ _ _ (le_max_left s₁ s₂) hs₁
      have h2 := hmonR _ _ _ (le_max_right s₁ s₂) hs₂
      simp [pred, cand, hz.1, hz.2, h1, h2]
    have hmem := Part.get_mem hdom
    have hspec := Nat.rfind_spec hmem
    set t0 := (Nat.rfind (P z0)).get hdom
    have ht : pred z0 t0 = true := (Part.mem_some_iff.mp hspec).symm
    simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨⟨h1, h2⟩, h3⟩ := ht
    rw [hz.1] at h1
    rw [hz.2] at h2
    have hS' : S p (cand t0).1 (cand t0).2.1 := (hchkS_iff _).mpr ⟨_, h1⟩
    have hR' : R.rel q (cand t0).2.2 := (hchkR_iff _).mpr ⟨_, h2⟩
    have hpre : (cand t0).2.1 <+: (cand t0).2.2 := List.prefix_iff_eq_take.mpr h3.symm
    have hcomp : (cand t0).2.1 <+: y ∨ y <+: (cand t0).2.1 := by
      rcases R.regular hR' hRq rfl with h | h
      · exact Or.inl (hpre.trans h)
      · exact List.prefix_or_prefix_of_prefix hpre h
    have hxx : x = (cand t0).1 :=
      hS.2 hSp hS' rfl (by rcases hcomp with h | h <;> [exact Or.inr h; exact Or.inl h])
    exact Part.mem_map_iff _ |>.mpr ⟨t0, hmem, hxx.symm⟩

/-- **SUV Problem 202 (Section 6.3, printed p. 201).**
`C(x) ≤ K(=,=)|≍(x | y) + KR(y) + O(log KR(y))`. The `toNat` is harmless because `KROf R y` is
finite (`KROf_ne_top`).

Proof idea: given a description `p` of `x` with condition `y` and a self-delimiting
`KR`-description `q` of `y`, run `R(q)` and enumerate `S` until some triple `(p, x', y')` with
`y'` a prefix of an enumerated prefix of `R(q)` appears. Then `y'` and `y` are compatible, so
`x' = x` by regularity. -/
theorem exists_const_plainK_le_condModeComplexity_add_KROf
    {S : BitString → BitString → BitString → Prop}
    (hS : IsOptimalCondDescriptionMode .eq .eq .compat S) {R : DecisionDecompressor}
    (hR : R.IsOptimal) {U : Map} (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x y, plainK U x ≤ condModeComplexity S x y + KROf R y +
      ((c * Nat.log 2 (KROf R y).toNat + c : ℕ) : ℕ∞) := by
  obtain ⟨f, hf, hfS⟩ := exists_const_plainK_le_condModeComplexity_add_KROf_machine hS.1 R
  obtain ⟨c₁, h₁⟩ :=
    exists_const_plainK_le_condModeComplexity_add_KROf_partrecMap U hU f hf
  obtain ⟨c₂, h₂⟩ := plainK_le_length U hU
  refine ⟨c₁ + c₂ + 5, fun x y => ?_⟩
  by_cases hcm : condModeComplexity S x y = ⊤
  · rw [hcm, top_add, top_add]
    exact le_top
  obtain ⟨p, hpS, hp⟩ :=
    exists_const_plainK_le_condModeComplexity_add_KROf_attained (P := fun p => S p x y) hcm
  obtain ⟨q, hqR, hq⟩ := exists_const_plainK_le_condModeComplexity_add_KROf_attained
    (P := fun q => R.rel q y) (KROf_ne_top hR y)
  have hcm' : condModeComplexity S x y = (p.length : ℕ∞) := hp.symm
  have hkr : KROf R y = (q.length : ℕ∞) := hq.symm
  rw [hcm', hkr, ENat.toNat_natCast]
  have hx := hfS p q x y hpS hqR
  set z0 := pairCode (Nat.bits q.length) (q ++ p) with hz0
  have hlen : z0.length + c₂ + c₁ ≤
      p.length + q.length + ((c₁ + c₂ + 5) * Nat.log 2 q.length + (c₁ + c₂ + 5)) := by
    have hb := length_natBits_le_log q.length
    have h2L : 2 * Nat.log 2 q.length ≤ (c₁ + c₂ + 5) * Nat.log 2 q.length :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [hz0, length_pairCode, List.length_append]
    omega
  calc plainK U x ≤ plainK U z0 + c₁ := h₁ z0 x hx
    _ ≤ ((z0.length : ℕ) : ℕ∞) + c₂ + c₁ := by
        gcongr
        exact h₂ z0
    _ = ((z0.length + c₂ + c₁ : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ ((p.length + q.length + ((c₁ + c₂ + 5) * Nat.log 2 q.length + (c₁ + c₂ + 5)) : ℕ) : ℕ∞) :=
        by exact_mod_cast hlen
    _ = _ := by push_cast; rfl

end GeneralScheme

end Kolmogorov
