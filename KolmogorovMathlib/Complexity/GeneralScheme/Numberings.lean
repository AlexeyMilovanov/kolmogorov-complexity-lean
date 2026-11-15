import KolmogorovMathlib.Complexity.GeneralScheme.Regular

/-!
# Complexity of functions and optimal numberings (SUV Section 6.3)

SUV Problem 203 (printed p. 201): decompressors whose objects are partial functions. Theorem 130
(printed p. 202): Schnorr's optimal numberings exist.

A computable continuous map `T : ℕ⊥ → F` into the space `F` of partial functions is determined
by the enumerable set of pairs `⟨a, f⟩` (`f` finite, `f ⪯ T(a)`). Equivalently, it is
determined by the enumerable graph of `(a, y) ↦ T(a)(y)`, which is functional. We represent `T`
by the predicate `T a x y` ("`T(a)(y) = x`"), i.e. by a `(=, =) | =` description mode. The value
`T(⊥)` is extended by every `T(a)`, and since `⊥` is not a description it plays no role for
complexity.
-/

namespace Kolmogorov

namespace GeneralScheme

/-- The complexity of a finite partial function `f`, given as a finite set of pairs
`(argument, value)`, with respect to a function decompressor `T`: the least length of a
description `a` such that `T(a)` extends `f`. -/
noncomputable def funComplexity (T : BitString → BitString → BitString → Prop)
    (f : Finset (BitString × BitString)) : ℕ∞ :=
  sInf {l : ℕ∞ | ∃ a, (∀ yx ∈ f, T a yx.2 yx.1) ∧ l = a.length}

/-- An optimal function decompressor: minimal complexity of all finite functions up to an
additive constant. The book asks for minimality on every `f ∈ F`, infinite ones included. Here
optimality is required on finite functions only, which is all that SUV Problem 203 (part 2)
uses, so the existence statement is weaker than the book's. -/
def IsOptimalFunDecompressor (T : BitString → BitString → BitString → Prop) : Prop :=
  IsCondDescriptionMode .eq .eq .eq T ∧
    ∀ T', IsCondDescriptionMode .eq .eq .eq T' →
      ∃ c : ℕ, ∀ f, funComplexity T f ≤ funComplexity T' f + c

/-- Step 1 of the proof of `exists_isOptimalFunDecompressor`: the `(=, =) | =`
decompressors can be enumerated by a uniformly enumerable family of regular relations. That is,
there is a family `W z` of triple sets (`W z p x y` meaning "`p` describes `x` given `y` in the
`z`-th set") such that the relation `⟨z, p, x, y⟩ ↦ W z p x y` is enumerable, every `W z` is
`(=, =) | =`-regular, and every `(=, =) | =`-decompressor `T'` equals some `W z`.

Proof idea: enumerate all enumerable sets of triples (via codes of partial recursive functions and
their stage approximations), and trim the `z`-th set: keep a triple `⟨p, x, y⟩` enumerated at
stage `s` unless a triple `⟨p, x', y⟩` with `x' ≠ x` was enumerated at an earlier stage (or at the
same stage with a smaller index). The trimmed set is regular, enumerable uniformly in `z`, and
it equals the original set if that is already regular. -/
private lemma exists_isOptimalFunDecompressor_enumeration :
    ∃ W : ℕ → BitString → BitString → BitString → Prop,
      IsRE (fun q : ℕ × BitString × BitString × BitString => W q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
      (∀ z, IsCondRegular .eq .eq .eq (W z)) ∧
      ∀ T', IsCondDescriptionMode .eq .eq .eq T' → ∃ z, ∀ p x y, W z p x y ↔ T' p x y := by
  classical
  let A : ℕ → ℕ → ℕ → Bool := fun z n s =>
    (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code z) n).isSome
  have hA : Primrec (fun r : (ℕ × ℕ) × ℕ => A r.1.1 r.1.2 r.2) := by
    have h1 : Primrec (fun r : (ℕ × ℕ) × ℕ =>
        ((r.2, Denumerable.ofNat Nat.Partrec.Code r.1.1), r.1.2)) :=
      Primrec.pair (Primrec.pair Primrec.snd ((Primrec.ofNat Nat.Partrec.Code).comp
        (Primrec.fst.comp Primrec.fst))) (Primrec.snd.comp Primrec.fst)
    exact Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp h1)
  have hAmono : ∀ z n s t, s ≤ t → A z n s = true → A z n t = true := by
    intro z n s t hst h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    exact Option.isSome_iff_exists.mpr ⟨x, Option.mem_def.mp
      (Nat.Partrec.Code.evaln_mono hst (Option.mem_def.mpr hx))⟩
  have hAbound : ∀ z n s, A z n s = true → n < s := by
    intro z n s h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    exact Nat.Partrec.Code.evaln_bound (Option.mem_def.mpr hx)
  let chk : ℕ × BitString × BitString × BitString → ℕ → Bool := fun q s =>
    A q.1 (Encodable.encode (q.2.1, q.2.2.1, q.2.2.2)) s &&
      (List.range s).all (fun n =>
        match Encodable.decode (α := BitString) n with
        | none => true
        | some x' => decide (x' = q.2.2.1) || !A q.1 (Encodable.encode (q.2.1, x', q.2.2.2)) s)
  have hchk : Computable₂ chk := by
    have hq : Primrec (fun r : (ℕ × BitString × BitString × BitString) × ℕ => r.1) := Primrec.fst
    have hs : Primrec (fun r : (ℕ × BitString × BitString × BitString) × ℕ => r.2) := Primrec.snd
    have hz : Primrec (fun r : (ℕ × BitString × BitString × BitString) × ℕ => r.1.1) :=
      Primrec.fst.comp Primrec.fst
    have hp : Primrec (fun r : (ℕ × BitString × BitString × BitString) × ℕ => r.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hx : Primrec (fun r : (ℕ × BitString × BitString × BitString) × ℕ => r.1.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    have hy : Primrec (fun r : (ℕ × BitString × BitString × BitString) × ℕ => r.1.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    have h1 : Primrec (fun r : (ℕ × BitString × BitString × BitString) × ℕ =>
        A r.1.1 (Encodable.encode (r.1.2.1, r.1.2.2.1, r.1.2.2.2)) r.2) :=
      hA.comp (Primrec.pair (Primrec.pair hz
        (Primrec.encode.comp (Primrec.pair hp (Primrec.pair hx hy)))) hs)
    have h2 : Primrec (fun r : (ℕ × BitString × BitString × BitString) × ℕ =>
        (List.range r.2).all (fun n =>
          match Encodable.decode (α := BitString) n with
          | none => true
          | some x' => decide (x' = r.1.2.2.1) ||
              !A r.1.1 (Encodable.encode (r.1.2.1, x', r.1.2.2.2)) r.2)) := by
      have hx' : Primrec (fun w : (((ℕ × BitString × BitString × BitString) × ℕ) × ℕ) ×
          BitString => w.2) := Primrec.snd
      have hr : ∀ {γ : Type} [Primcodable γ] (f : (ℕ × BitString × BitString × BitString) × ℕ → γ),
          Primrec f → Primrec (fun w : (((ℕ × BitString × BitString × BitString) × ℕ) × ℕ) ×
            BitString => f w.1.1) := fun f hf => hf.comp (Primrec.fst.comp Primrec.fst)
      have hg1 : Primrec (fun w : (((ℕ × BitString × BitString × BitString) × ℕ) × ℕ) ×
          BitString => decide (w.2 = w.1.1.1.2.2.1)) :=
        (Primrec.eq (α := BitString)).decide.comp hx' (hr (fun r => r.1.2.2.1) hx)
      have hg2 : Primrec (fun w : (((ℕ × BitString × BitString × BitString) × ℕ) × ℕ) ×
          BitString => Encodable.encode (w.1.1.1.2.1, w.2, w.1.1.1.2.2.2)) :=
        Primrec.encode.comp (Primrec.pair (hr (fun r => r.1.2.1) hp)
          (Primrec.pair hx' (hr (fun r => r.1.2.2.2) hy)))
      have hg3 : Primrec (fun w : (((ℕ × BitString × BitString × BitString) × ℕ) × ℕ) ×
          BitString => A w.1.1.1.1 (Encodable.encode (w.1.1.1.2.1, w.2, w.1.1.1.2.2.2)) w.1.1.2) :=
        hA.comp (Primrec.pair (Primrec.pair (hr (fun r => r.1.1) hz) hg2) (hr (fun r => r.2) hs))
      have hg : Primrec₂ (fun (a : ((ℕ × BitString × BitString × BitString) × ℕ) × ℕ)
          (x' : BitString) => decide (x' = a.1.1.2.2.1) ||
              !A a.1.1.1 (Encodable.encode (a.1.1.2.1, x', a.1.1.2.2.2)) a.1.2) :=
        Primrec.or.comp hg1 (Primrec.not.comp hg3)
      refine list_all_primrec (Primrec.list_range.comp hs) ?_
      refine (Primrec.option_casesOn
        (o := fun a : ((ℕ × BitString × BitString × BitString) × ℕ) × ℕ =>
          Encodable.decode (α := BitString) a.2)
        (f := fun _ => true)
        (g := fun a x' => decide (x' = a.1.1.2.2.1) ||
              !A a.1.1.1 (Encodable.encode (a.1.1.2.1, x', a.1.1.2.2.2)) a.1.2)
        ((Primrec.decode (α := BitString)).comp Primrec.snd) (Primrec.const true) hg).of_eq ?_
      intro a
      dsimp only
      cases Encodable.decode (α := BitString) a.2 <;> rfl
    exact (Primrec.and.comp h1 h2).to_comp
  have hle : ∀ (p x y : BitString), Encodable.encode x ≤ Encodable.encode (p, x, y) := by
    intro p x y
    rw [Encodable.encode_prod_val, Encodable.encode_prod_val]
    exact (Nat.left_le_pair _ _).trans (Nat.right_le_pair _ _)
  have key : ∀ z p x y s, chk (z, p, x, y) s = true ↔
      A z (Encodable.encode (p, x, y)) s = true ∧
        ∀ x', x' ≠ x → A z (Encodable.encode (p, x', y)) s = false := by
    intro z p x y s
    simp only [chk, Bool.and_eq_true, List.all_eq_true, List.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun x' hne => ?_⟩
      by_contra hA'
      have hA'' : A z (Encodable.encode (p, x', y)) s = true := by simpa using hA'
      have hlt : Encodable.encode x' < s :=
        lt_of_le_of_lt (hle p x' y) (hAbound _ _ _ hA'')
      have := h2 (Encodable.encode x') hlt
      rw [Encodable.encodek] at this
      rcases Bool.or_eq_true_iff.mp this with h | h
      · exact hne (of_decide_eq_true h)
      · rw [hA''] at h
        exact Bool.noConfusion h
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun n hn => ?_⟩
      cases hd : Encodable.decode (α := BitString) n with
      | none => simp
      | some x' =>
        by_cases hx : x' = x
        · simp [hx]
        · have h3 := h2 x' hx
          simp only [h3, Bool.not_false, Bool.or_true]
  refine ⟨fun z p x y => ∃ s, chk (z, p, x, y) s = true, ?_, ?_, ?_⟩
  · exact IsRE.exists_encodable (R := fun (q : ℕ × BitString × BitString × BitString) (s : ℕ) =>
      chk q s = true)
      (isRE_of_computable_bool (fun r : (ℕ × BitString × BitString × BitString) × ℕ =>
        chk r.1 r.2 = true) (fun r => chk r.1 r.2) (fun _ => Iff.rfl) hchk)
  · intro z p₁ x₁ y₁ p₂ x₂ y₂ ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ hp hy
    have hp' : p₁ = p₂ := hp
    have hy' : y₁ = y₂ := hy
    subst hp' hy'
    by_contra hne
    obtain ⟨a₁, b₁⟩ := (key _ _ _ _ _).1 h₁
    obtain ⟨a₂, b₂⟩ := (key _ _ _ _ _).1 h₂
    rcases le_total s₁ s₂ with hs | hs
    · have := b₂ x₁ hne
      rw [hAmono _ _ _ _ hs a₁] at this
      exact Bool.noConfusion this
    · have := b₁ x₂ (Ne.symm hne)
      rw [hAmono _ _ _ _ hs a₂] at this
      exact Bool.noConfusion this
  · rintro T' ⟨hRE, hreg⟩
    obtain ⟨g, hg, hdom⟩ := hRE
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg
    refine ⟨Encodable.encode c, fun p x y => ?_⟩
    have hdomA : ∀ p x y, T' p x y ↔
        ∃ k, A (Encodable.encode c) (Encodable.encode (p, x, y)) k = true := by
      intro p x y
      have := (hdom (p, x, y)).symm.trans (partrecCodeDom g c hc (p, x, y))
      simpa [A, Denumerable.ofNat_encode] using this
    rw [hdomA]
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨s, ((key _ _ _ _ _).1 hs).1⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, (key _ _ _ _ _).2 ⟨hk, fun x' hne => ?_⟩⟩
      by_contra hA'
      have hA'' : A (Encodable.encode c) (Encodable.encode (p, x', y)) k = true := by simpa using
          hA'
      have h1 : T' p x y := (hdomA p x y).2 ⟨k, hk⟩
      have h2 : T' p x' y := (hdomA p x' y).2 ⟨k, hA''⟩
      exact hne (hreg h2 h1 rfl rfl)

/-- **SUV Problem 203 (Section 6.3, printed p. 201), part 1.** There is an optimal decompressor
for functions.

Proof idea: the universal construction `T(ẑ a) = T_z(a)` over an enumeration of the enumerable
functional sets of triples. It preserves "`T(a)` extends `f`". -/
theorem exists_isOptimalFunDecompressor : ∃ T, IsOptimalFunDecompressor T := by
  classical
  obtain ⟨W, hWre, hWreg, hWuniv⟩ := exists_isOptimalFunDecompressor_enumeration
  let T : BitString → BitString → BitString → Prop := fun a x y =>
    ∃ (z : ℕ) (p : BitString), a = List.replicate z true ++ false :: p ∧ W z p x y
  have hcode : ∀ {z₁ z₂ : ℕ} {p₁ p₂ : BitString},
      List.replicate z₁ true ++ false :: p₁ = List.replicate z₂ true ++ false :: p₂ →
        z₁ = z₂ ∧ p₁ = p₂ := by
    intro z₁
    induction z₁ with
    | zero =>
      intro z₂ p₁ p₂ h
      cases z₂ with
      | zero => simpa using h
      | succ z₂ => simp [List.replicate_succ] at h
    | succ z₁ ih =>
      intro z₂ p₁ p₂ h
      cases z₂ with
      | zero => simp [List.replicate_succ] at h
      | succ z₂ =>
        simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
        obtain ⟨h1, h2⟩ := ih h
        exact ⟨by omega, h2⟩
  have hT : IsCondDescriptionMode .eq .eq .eq T := by
    refine ⟨?_, ?_⟩
    · have hp : Computable (fun r : (BitString × BitString × BitString) × (ℕ × BitString) =>
          decide (r.1.1 = List.replicate r.2.1 true ++ false :: r.2.2)) := by
        have h1 : Computable
            (fun r : (BitString × BitString × BitString) × (ℕ × BitString) => r.1.1) :=
          Computable.fst.comp Computable.fst
        have h2 : Computable
            (fun r : (BitString × BitString × BitString) × (ℕ × BitString) =>
              List.replicate r.2.1 true ++ false :: r.2.2) := by
          refine Primrec.to_comp ?_
          have hs : Primrec (fun r : (BitString × BitString × BitString) × (ℕ × BitString) => r.2.1)
              :=
            Primrec.fst.comp Primrec.snd
          have ht : Primrec (fun r : (BitString × BitString × BitString) × (ℕ × BitString) => r.2.2)
              :=
            Primrec.snd.comp Primrec.snd
          exact Primrec.list_append.comp
            (Primrec.list_replicate.comp hs (Primrec.const true))
            (Primrec.list_cons.comp (Primrec.const false) ht)
        exact Computable₂.comp (Primrec.eq (α := BitString)).decide.to_comp h1 h2
      have hg : Computable (fun r : (BitString × BitString × BitString) × (ℕ × BitString) =>
          (r.2.1, r.2.2, r.1.2.1, r.1.2.2)) :=
        Computable.pair (Computable.fst.comp Computable.snd)
          (Computable.pair (Computable.snd.comp Computable.snd)
            (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
              (Computable.snd.comp (Computable.snd.comp Computable.fst))))
      have h1 := (hWre.comp_computable hg).and_computable hp
      have h2 := IsRE.exists_encodable
        (R := fun (q : BitString × BitString × BitString) (zp : ℕ × BitString) =>
          decide (q.1 = List.replicate zp.1 true ++ false :: zp.2) = true ∧
            W zp.1 zp.2 q.2.1 q.2.2) h1
      refine IsRE.of_iff h2 fun q => ?_
      simp only [decide_eq_true_eq, T]
      constructor
      · rintro ⟨⟨z, p⟩, h, w⟩
        exact ⟨z, p, h, w⟩
      · rintro ⟨z, p, h, w⟩
        exact ⟨⟨z, p⟩, h, w⟩
    · intro p₁ x₁ y₁ p₂ x₂ y₂ h₁ h₂ hp hy
      obtain ⟨z₁, q₁, e₁, w₁⟩ := h₁
      obtain ⟨z₂, q₂, e₂, w₂⟩ := h₂
      have hp' : p₁ = p₂ := hp
      subst hp'
      obtain ⟨hz, hq⟩ := hcode (e₁.symm.trans e₂)
      subst hz hq
      exact hWreg z₁ w₁ w₂ rfl hy
  refine ⟨T, hT, fun T' hT' => ?_⟩
  obtain ⟨z, hz⟩ := hWuniv T' hT'
  refine ⟨z + 1, fun f => ?_⟩
  unfold funComplexity
  by_cases hne : {l : ℕ∞ | ∃ a, (∀ yx ∈ f, T' a yx.2 yx.1) ∧ l = a.length}.Nonempty
  · obtain ⟨a, ha, hl⟩ := csInf_mem hne
    rw [hl]
    refine sInf_le ⟨List.replicate z true ++ false :: a, fun yx hyx => ?_, ?_⟩
    · exact ⟨z, a, rfl, (hz _ _ _).2 (ha yx hyx)⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons]
      push_cast
      ring
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, sInf_empty]
    simp

/-- Step 1 of the proof of `exists_const_funComplexity_singleton_eq_condK`: an
enumerable `(=, =) | =`-regular relation `S p x y` is the graph of a partial recursive map `D`. -/
private lemma exists_const_funComplexity_singleton_eq_condK_partrec
    {S : BitString → BitString → BitString → Prop} (hS : IsCondDescriptionMode .eq .eq .eq S) :
    ∃ D : Map, Partrec D ∧ ∀ p y x, x ∈ D (p, y) ↔ S p x y := by
  classical
  obtain ⟨chk, hchk, -, hiff⟩ := IsRE.exists_stageApprox hS.1
  let f : BitString × BitString → ℕ → Option BitString := fun q n =>
    (Encodable.decode (α := BitString) n.unpair.1).bind (fun x =>
      if chk (q.1, x, q.2) n.unpair.2 = true then some x else none)
  have hf : Computable₂ f := by
    have h_lookup : Computable
        (fun p : (BitString × BitString) × ℕ => Encodable.decode (α := BitString) p.2.unpair.1) :=
      Computable.comp Computable.decode
        (Computable.comp Computable.fst (Computable.comp Computable.unpair Computable.snd))
    have h_chk : Computable
        (fun r : ((BitString × BitString) × ℕ) × BitString =>
          chk (r.1.1.1, r.2, r.1.1.2) r.1.2.unpair.2) := by
      have h1 : Computable (fun r : ((BitString × BitString) × ℕ) × BitString => r.1.1.1) :=
        Computable.fst.comp (Computable.fst.comp Computable.fst)
      have h2 : Computable (fun r : ((BitString × BitString) × ℕ) × BitString => r.1.1.2) :=
        Computable.snd.comp (Computable.fst.comp Computable.fst)
      have h3 : Computable
          (fun r : ((BitString × BitString) × ℕ) × BitString => r.1.2.unpair.2) :=
        Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst))
      have h4 : Computable
          (fun r : ((BitString × BitString) × ℕ) × BitString => (r.1.1.1, r.2, r.1.1.2)) :=
        Computable.pair h1 (Computable.pair Computable.snd h2)
      have h5 := Computable.comp
        (f := fun q : (BitString × BitString × BitString) × ℕ => chk q.1 q.2) hchk
        (Computable.pair h4 h3)
      exact h5
    have h_step : Computable₂ (fun (p : (BitString × BitString) × ℕ) (x : BitString) =>
        (if chk (p.1.1, x, p.1.2) p.2.unpair.2 = true then some x else none :
          Option BitString)) := by
      refine (Computable.cond h_chk (Computable.option_some.comp Computable.snd)
        (Computable.const (none : Option BitString))).of_eq ?_
      intro r
      cases h : chk (r.1.1.1, r.2, r.1.1.2) r.1.2.unpair.2 <;> simp [h]
    have h6 := Computable.option_bind h_lookup h_step
    exact h6
  have hfsome : ∀ q n x, f q n = some x ↔
      (Encodable.decode (α := BitString) n.unpair.1 = some x ∧
        chk (q.1, x, q.2) n.unpair.2 = true) := by
    intro q n x
    simp only [f]
    cases hd : Encodable.decode (α := BitString) n.unpair.1 with
    | none => simp
    | some z =>
      by_cases hc : chk (q.1, z, q.2) n.unpair.2 = true
      · simp only [Option.bind_some, hc, ite_true, Option.some.injEq]
        constructor
        · rintro rfl; exact ⟨rfl, hc⟩
        · exact fun h => h.1.symm ▸ rfl
      · simp only [Option.bind_some]
        rw [ite_eq_right hc]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨h1, h2⟩
          obtain rfl := Option.some.inj h1
          exact absurd h2 hc
  have hS_of : ∀ q n x, f q n = some x → S q.1 x q.2 := by
    intro q n x h
    rw [hfsome] at h
    exact (hiff (q.1, x, q.2)).2 ⟨_, h.2⟩
  refine ⟨fun q => Nat.rfindOpt (f q), Partrec.rfindOpt hf, ?_⟩
  intro p y x
  change x ∈ Nat.rfindOpt (f (p, y)) ↔ S p x y
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec h
    exact hS_of _ _ _ (Option.mem_def.mp hn)
  · intro h
    obtain ⟨s, hs⟩ := (hiff (p, x, y)).1 h
    have hn : f (p, y) (Nat.pair (Encodable.encode x) s) = some x := by
      rw [hfsome]
      simpa using hs
    have hdom := Nat.rfindOpt_dom.2 ⟨_, x, Option.mem_def.mpr hn⟩
    obtain ⟨k, hk⟩ := Nat.rfindOpt_spec (Part.get_mem hdom)
    have hSk := hS_of _ _ _ (Option.mem_def.mp hk)
    have : (Nat.rfindOpt (f (p, y))).get hdom = x := hS.2 hSk h rfl rfl
    rw [← this]
    exact Part.get_mem hdom

/-- **SUV Problem 203 (Section 6.3, printed p. 201), part 2.** The complexity of the function
`y ↦ x` with domain `{y}` is `C(x | y) + O(1)`.

Proof idea: a function decompressor restricted to singletons is a conditional decompressor, and
a conditional decompressor `D` gives the function decompressor `T(a) = D(a, ·)`. -/
theorem exists_const_funComplexity_singleton_eq_condK
    {T : BitString → BitString → BitString → Prop} (hT : IsOptimalFunDecompressor T) {U : Map}
    (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x y,
      funComplexity T {(y, x)} ≤ condK U x y + c ∧ condK U x y ≤ funComplexity T {(y, x)} + c := by
  obtain ⟨D, hDp, hD⟩ :=
    exists_const_funComplexity_singleton_eq_condK_partrec hT.1
  obtain ⟨c₁, hc₁⟩ := hU.2 D hDp
  let T' : BitString → BitString → BitString → Prop := fun a x y => x ∈ U (a, y)
  have hT' : IsCondDescriptionMode .eq .eq .eq T' := by
    refine ⟨?_, ?_⟩
    · exact (Partrec.graphIsRe U hU.1).comp_computable
        (g := fun q : BitString × BitString × BitString => ((q.1, q.2.2), q.2.1))
        (Computable.pair (Computable.pair Computable.fst (Computable.snd.comp Computable.snd))
          (Computable.fst.comp Computable.snd))
    · intro p₁ x₁ y₁ p₂ x₂ y₂ h₁ h₂ hp hy
      have hp' : p₁ = p₂ := hp
      have hy' : y₁ = y₂ := hy
      subst hp' hy'
      exact Part.mem_unique h₁ h₂
  obtain ⟨c₂, hc₂⟩ := hT.2 T' hT'
  refine ⟨c₁ + c₂, fun x y => ⟨?_, ?_⟩⟩
  · have h1 : funComplexity T' {(y, x)} ≤ condK U x y := by
      refine sInf_le_sInf ?_
      rintro l ⟨p, hp, rfl⟩
      exact ⟨p, by simpa [T'] using hp, rfl⟩
    calc funComplexity T {(y, x)} ≤ funComplexity T' {(y, x)} + c₂ := hc₂ _
      _ ≤ condK U x y + c₂ := by gcongr
      _ ≤ condK U x y + ((c₁ + c₂ : ℕ) : ℕ∞) := by
        gcongr
        exact_mod_cast Nat.le_add_left _ _
  · have h2 : condK D x y ≤ funComplexity T {(y, x)} := by
      refine sInf_le_sInf ?_
      rintro l ⟨a, ha, rfl⟩
      exact ⟨a, (hD a y x).2 (by simpa using ha), rfl⟩
    calc condK U x y ≤ condK D x y + c₁ := hc₁ x y
      _ ≤ funComplexity T {(y, x)} + c₁ := by gcongr
      _ ≤ funComplexity T {(y, x)} + ((c₁ + c₂ : ℕ) : ℕ∞) := by
        gcongr
        exact_mod_cast Nat.le_add_right _ _

/-- A numbering `ν` (`n ↦ ν n`, a partial function `ℕ →. ℕ`) is *computable* if
`⟨n, x⟩ ↦ ν n x` is partial computable. -/
def IsComputableNumbering (ν : ℕ → ℕ →. ℕ) : Prop :=
  Partrec₂ ν

/-- SUV Section 6.3: a computable numbering `ν` is *optimal* (Schnorr) if every computable
numbering `μ` reduces to it by a total computable `h` with `h(n) = O(n)`: `μ n = ν (h n)`.
We write `h(n) = O(n)` as `h n ≤ c * (n + 1)`, which reads `n = 0` sensibly. Equivalently, the
string for `h(n)` is longer than the string for `n` by at most a constant. -/
def IsOptimalNumbering (ν : ℕ → ℕ →. ℕ) : Prop :=
  IsComputableNumbering ν ∧
    ∀ μ, IsComputableNumbering μ →
      ∃ h : ℕ → ℕ, Computable h ∧ (∃ c : ℕ, ∀ n, h n ≤ c * (n + 1)) ∧ ∀ n, μ n = ν (h n)

/-- The exponent `u` in `m = 2 ^ u * (2 * v + 1)`. -/
private def exists_isOptimalNumbering_decU (m : ℕ) : ℕ :=
  m.findGreatest (fun j => m % 2 ^ j = 0)

/-- The odd part `v` in `m = 2 ^ u * (2 * v + 1)`. -/
private def exists_isOptimalNumbering_decV (m : ℕ) : ℕ :=
  m / 2 ^ (exists_isOptimalNumbering_decU m) / 2

private lemma exists_isOptimalNumbering_decU_enc (u v : ℕ) :
    exists_isOptimalNumbering_decU (2 ^ u * (2 * v + 1)) = u := by
  unfold exists_isOptimalNumbering_decU
  rw [Nat.findGreatest_eq_iff]
  refine ⟨?_, fun _ => ?_, fun j hj _ => ?_⟩
  · calc u ≤ 2 ^ u := (Nat.lt_two_pow_self).le
      _ ≤ 2 ^ u * (2 * v + 1) := Nat.le_mul_of_pos_right _ (by omega)
  · exact Nat.mod_eq_zero_of_dvd (Dvd.intro _ rfl)
  · intro h
    replace h := Nat.dvd_of_mod_eq_zero h
    have h1 : 2 ^ (u + 1) ∣ 2 ^ u * (2 * v + 1) :=
      (pow_dvd_pow 2 hj).trans h
    rw [pow_succ] at h1
    have h2 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
    omega

private lemma exists_isOptimalNumbering_decV_enc (u v : ℕ) :
    exists_isOptimalNumbering_decV (2 ^ u * (2 * v + 1)) = v := by
  unfold exists_isOptimalNumbering_decV
  rw [exists_isOptimalNumbering_decU_enc, Nat.mul_div_cancel_left _ (by positivity)]
  omega

private lemma exists_isOptimalNumbering_decU_primrec :
    Primrec exists_isOptimalNumbering_decU := by
  have h2 : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  refine Primrec.nat_findGreatest Primrec.id ?_
  refine Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst
    (h2.comp (Primrec.const 2) Primrec.snd)) (Primrec.const 0)

private lemma exists_isOptimalNumbering_decV_primrec :
    Primrec exists_isOptimalNumbering_decV := by
  have h2 : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact Primrec.nat_div.comp (Primrec.nat_div.comp Primrec.id
    (h2.comp (Primrec.const 2) exists_isOptimalNumbering_decU_primrec)) (Primrec.const 2)

/-- **SUV Theorem 130 (Section 6.3, printed p. 202).** Optimal numberings exist.

Proof idea: take a programming language for functions of two arguments, and let `û v` (with
`û` a self-delimiting code of `u`) be a number of the function obtained from program `u` by
fixing the first argument to `v`. The reduction `v ↦ û v` multiplies numbers by `2 ^ O(l(u))`. -/
theorem exists_isOptimalNumbering : ∃ ν, IsOptimalNumbering ν := by
  refine ⟨fun m x => Nat.Partrec.Code.eval
    (Denumerable.ofNat Nat.Partrec.Code (exists_isOptimalNumbering_decU m))
    (Nat.pair (exists_isOptimalNumbering_decV m) x), ?_, ?_⟩
  · have hm : Computable (fun p : ℕ × ℕ => exists_isOptimalNumbering_decU p.1) :=
      exists_isOptimalNumbering_decU_primrec.to_comp.comp Computable.fst
    have hv : Computable (fun p : ℕ × ℕ =>
        Nat.pair (exists_isOptimalNumbering_decV p.1) p.2) :=
      Primrec₂.natPair.to_comp.comp
        (exists_isOptimalNumbering_decV_primrec.to_comp.comp Computable.fst) Computable.snd
    exact Nat.Partrec.Code.eval_part.comp
      ((Computable.ofNat Nat.Partrec.Code).comp hm) hv
  · intro μ hμ
    have hμ' : Nat.Partrec (fun n => μ n.unpair.1 n.unpair.2) := by
      refine Partrec.nat_iff.1 ?_
      exact Partrec.comp (f := fun p : ℕ × ℕ => μ p.1 p.2) hμ Computable.unpair
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hμ'
    refine ⟨fun n => 2 ^ Encodable.encode c * (2 * n + 1), ?_,
      ⟨2 ^ (Encodable.encode c + 1), fun n => ?_⟩, fun n => ?_⟩
    · have h2 : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.1 Nat.Primrec.pow
      exact (Primrec.nat_mul.comp
        (h2.comp (Primrec.const 2) (Primrec.const (Encodable.encode c)))
        (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))).to_comp
    · have : 2 ^ Encodable.encode c * (2 * n + 1) ≤ 2 ^ (Encodable.encode c + 1) * (n + 1) := by
        rw [pow_succ]; nlinarith [Nat.zero_le (2 ^ Encodable.encode c),
          Nat.zero_le (2 ^ Encodable.encode c * n)]
      exact this
    · funext x
      simp only [exists_isOptimalNumbering_decU_enc, exists_isOptimalNumbering_decV_enc,
        Denumerable.ofNat_encode]
      have := congrFun hc (Nat.pair n x)
      simpa using this.symm

/-- Schnorr complexity of the task "map `x` to `y`" in a numbering `ν`: the least length of (the
binary string of) a number `n` with `ν n x = y`. -/
noncomputable def numberingComplexity (ν : ℕ → ℕ →. ℕ) (x y : ℕ) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : y ∈ ν n x), ((Nat.bits n).length : ℕ∞)

private lemma exists_const_numberingComplexity_eq_condK_dropLast :
    Computable (fun n : ℕ => (Nat.bits n).dropLast) := by
  have H : (fun n : ℕ => (Nat.bits n).dropLast) =
      (fun n : ℕ => (Nat.bits n).reverse.tail.reverse) := by
    funext n
    simp [List.dropLast_eq_take]
  rw [H]
  apply Primrec.to_comp
  exact Primrec.list_reverse.comp (Primrec.list_tail.comp
    (Primrec.list_reverse.comp primrec_natBits))

private lemma exists_const_numberingComplexity_eq_condK_decodeBits_ne_zero (u : BitString) :
    decodeBits (u ++ [true]) ≠ 0 := by
  induction u with
  | nil => decide
  | cons b bs ih =>
    rw [List.cons_append]
    cases b
    · intro h
      change 2 * decodeBits (bs ++ [true]) = 0 at h
      exact ih (by omega)
    · intro h
      change 2 * decodeBits (bs ++ [true]) + 1 = 0 at h
      omega

private lemma exists_const_numberingComplexity_eq_condK_natBits_decodeBits (u : BitString) :
    Nat.bits (decodeBits (u ++ [true])) = u ++ [true] := by
  induction u with
  | nil => rfl
  | cons b bs ih =>
    have hne := exists_const_numberingComplexity_eq_condK_decodeBits_ne_zero bs
    rw [List.cons_append]
    have e : decodeBits (b :: (bs ++ [true])) = Nat.bit b (decodeBits (bs ++ [true])) := by
      cases b
      · rfl
      · change 2 * decodeBits (bs ++ [true]) + 1 = Nat.bit true (decodeBits (bs ++ [true]))
        rfl
    rw [e, Nat.bits_append_bit _ _ (fun h => absurd h hne), ih]

private lemma exists_const_numberingComplexity_eq_condK_size (c n : ℕ) :
    (Nat.bits (c * (n + 1))).length ≤ (Nat.bits c).length + (Nat.bits n).length + 1 := by
  simp only [Nat.size_eq_bits_len]
  have h2 := size_mul_le c (n + 1)
  have h3 : Nat.size (n + 1) ≤ Nat.size n + 1 := by
    rw [Nat.size_le]
    have := Nat.lt_size_self n
    calc n + 1 < 2 ^ (Nat.size n) + 1 := by omega
      _ ≤ 2 ^ (Nat.size n + 1) := by
        have : 1 ≤ 2 ^ Nat.size n := Nat.one_le_two_pow
        rw [pow_succ]; omega
  omega

/-- **SUV Section 6.3 (printed p. 202), unnumbered remark.** In an optimal numbering, the least
complexity of a function that maps `x` to `y` is `C(y | x) + O(1)`. Numbers are coded by
`Nat.bits`, as everywhere in the library.

Proof idea: an optimal conditional decompressor gives a computable numbering, which reduces to
`ν` with `O(1)` length overhead. Conversely, `ν` itself is a conditional decompressor. -/
theorem exists_const_numberingComplexity_eq_condK {ν : ℕ → ℕ →. ℕ} (hν : IsOptimalNumbering ν)
    {U : Map} (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x y,
      numberingComplexity ν x y ≤ condK U (Nat.bits y) (Nat.bits x) + c ∧
        condK U (Nat.bits y) (Nat.bits x) ≤ numberingComplexity ν x y + c := by
  classical
  let μ : ℕ → ℕ →. ℕ := fun n x =>
    (U ((Nat.bits n).dropLast, Nat.bits x)).map decodeBits
  have hμ : IsComputableNumbering μ := by
    have h1 : Computable (fun q : ℕ × ℕ => ((Nat.bits q.1).dropLast, Nat.bits q.2)) :=
      Computable.pair
        (exists_const_numberingComplexity_eq_condK_dropLast.comp Computable.fst)
        (natBits_computable.comp Computable.snd)
    exact (hU.1.comp h1).map (decodeBits_computable.comp Computable.snd).to₂
  obtain ⟨h, hh, ⟨c₀, hc₀⟩, hhμ⟩ := hν.2 μ hμ
  let D : Map := fun q => (ν (decodeBits q.1) (decodeBits q.2)).map Nat.bits
  have hD : Partrec D := by
    have h1 : Computable (fun q : BitString × BitString => (decodeBits q.1, decodeBits q.2)) :=
      Computable.pair (decodeBits_computable.comp Computable.fst)
        (decodeBits_computable.comp Computable.snd)
    exact (Partrec.comp (f := fun p : ℕ × ℕ => ν p.1 p.2) hν.1 h1).map
      (natBits_computable.comp Computable.snd).to₂
  obtain ⟨c₁, hc₁⟩ := hU.2 D hD
  refine ⟨(Nat.bits c₀).length + 2 + c₁, fun x y => ⟨?_, ?_⟩⟩
  · by_cases hS : (candidateLengths U (Nat.bits y) (Nat.bits x)).Nonempty
    · have hmem := csInf_mem hS
      obtain ⟨p, hp, hpl⟩ := hmem
      set n := decodeBits (p ++ [true]) with hn_def
      have hnl : (Nat.bits n).length = p.length + 1 := by
        rw [hn_def, exists_const_numberingComplexity_eq_condK_natBits_decodeBits]; simp
      have hn : y ∈ μ n x := by
        refine (Part.mem_map_iff _).2 ⟨Nat.bits y, ?_, decodeBits_natBits y⟩
        have e : (Nat.bits n).dropLast = p := by
          rw [hn_def, exists_const_numberingComplexity_eq_condK_natBits_decodeBits]
          exact List.dropLast_concat
        rw [e]; exact hp
      rw [hhμ] at hn
      have hle : numberingComplexity ν x y ≤ (((Nat.bits (h n)).length : ℕ) : ℕ∞) := by
        unfold numberingComplexity
        exact iInf₂_le (f := fun (m : ℕ) (_ : y ∈ ν m x) => (((Nat.bits m).length : ℕ) : ℕ∞))
          (h n) hn
      have hlen : (Nat.bits (h n)).length ≤ p.length + ((Nat.bits c₀).length + 2) := by
        have h1 : (Nat.bits (h n)).length ≤ (Nat.bits (c₀ * (n + 1))).length := by
          rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
          exact Nat.size_le_size (hc₀ n)
        have h2 := exists_const_numberingComplexity_eq_condK_size c₀ n
        omega
      have hsInf : condK U (Nat.bits y) (Nat.bits x) = (p.length : ℕ∞) := by
        unfold condK; rw [← hpl]
      rw [hsInf]
      refine hle.trans ?_
      calc (((Nat.bits (h n)).length : ℕ) : ℕ∞)
          ≤ ((p.length + ((Nat.bits c₀).length + 2) : ℕ) : ℕ∞) := by exact_mod_cast hlen
        _ ≤ ((p.length + ((Nat.bits c₀).length + 2 + c₁) : ℕ) : ℕ∞) := by
          exact_mod_cast Nat.add_le_add_left (Nat.le_add_right _ _) _
        _ = (p.length : ℕ∞) + (((Nat.bits c₀).length + 2 + c₁ : ℕ) : ℕ∞) := by push_cast; ring
    · have : condK U (Nat.bits y) (Nat.bits x) = ⊤ := by
        unfold condK
        rw [Set.not_nonempty_iff_eq_empty.1 hS]; exact sInf_empty
      rw [this]; simp
  · have h2 : condK D (Nat.bits y) (Nat.bits x) ≤ numberingComplexity ν x y := by
      refine le_iInf fun n => le_iInf fun hn => ?_
      refine sInf_le ⟨Nat.bits n, ?_, rfl⟩
      refine (Part.mem_map_iff _).2 ⟨y, ?_, rfl⟩
      simpa using hn
    calc condK U (Nat.bits y) (Nat.bits x)
        ≤ condK D (Nat.bits y) (Nat.bits x) + c₁ := hc₁ _ _
      _ ≤ numberingComplexity ν x y + c₁ := by gcongr
      _ ≤ numberingComplexity ν x y + (((Nat.bits c₀).length + 2 + c₁ : ℕ) : ℕ∞) := by
        gcongr
        exact_mod_cast Nat.le_add_left _ _

end GeneralScheme

end Kolmogorov
