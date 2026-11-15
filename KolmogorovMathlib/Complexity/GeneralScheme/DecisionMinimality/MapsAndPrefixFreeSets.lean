import KolmogorovMathlib.Complexity.GeneralScheme.DecisionBasic
import KolmogorovMathlib.Prefix.StableDecompressors
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity

/-!
# Computable Maps and Prefix-Free Sets for Decision Complexity

This module proves items (g)-(k) of Theorem 127 of Shen-Uspensky-Vereshchagin (Section 6.1) for
the decision complexity `KR`. Computable continuous maps between strings, infinite sequences and
numbers change `KR` (or plain complexity `C`) by at most an additive constant. A prefix-free set
of strings of decision complexity below `n` has fewer than `2 ^ n` elements, and `KR` is upper
semicomputable.

## Main declarations

* `exists_const_KROf_comp_le`: `KR(f(x)) ≤ KR(x) + O(1)` for a computable map `f : Σ → Σ`.
* `exists_const_plainK_comp_le_KROf`: `C(f(x)) ≤ KR(x) + O(1)` for a computable map
  `f : Σ → ℕ⊥`.
* `exists_const_KROf_comp_le_plainK`: `KR(f(x)) ≤ C(x) + O(1)` for a computable map
  `f : ℕ⊥ → Σ`.
* `encard_lt_two_pow_of_isPrefixFree_KROf_lt`: a prefix-free set of strings of decision
  complexity `< n` has fewer than `2 ^ n` elements.
* `isUpperSemicomputable_KROf`: `KR` is upper semicomputable.
-/

namespace Kolmogorov

namespace GeneralScheme

/-- **SUV Theorem 127 (g) (Section 6.1, printed p. 194).** If `f : Σ → Σ` is a computable
continuous map, then `KR(f(x)) ≤ KR(x) + O(1)`, with the constant depending on `f` only.
`f(x)` may be an infinite sequence, so the claim is stated for every finite prefix `y` of
`f(x)`, i.e. `streamLowerGraph f x y`. Since `KR` is monotone, this is the same as bounding
`KR(f(x))`.

Proof idea: compose an optimal decision decompressor with `f` and compare the composition with
the optimal one. Compare `exists_const_KMOf_le_comp` (Theorem 85). -/
theorem exists_const_KROf_comp_le {R : DecisionDecompressor} (hR : R.IsOptimal)
    {f : BitStream → BitStream} (hf : IsComputableStreamMap f) :
    ∃ c : ℕ, ∀ x y : BitString, streamLowerGraph f x y → KROf R y ≤ KROf R x + c := by
  have hlg := continuousStreamMap_lowerGraph_isStreamLowerGraph hf.1.1
  let M : DecisionDecompressor :=
    { rel := fun p y => ∃ x, R.rel p x ∧ streamLowerGraph f x y
      re := by
        have h1 : IsRE (fun q : (BitString × BitString) × BitString => R.rel q.1.1 q.2) :=
          IsRE.comp_computable R.re
            (g := fun q : (BitString × BitString) × BitString => (q.1.1, q.2))
            (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
        have h2 : IsRE (fun q : (BitString × BitString) × BitString =>
            streamLowerGraph f q.2 q.1.2) :=
          IsRE.comp_computable hf.2
            (g := fun q : (BitString × BitString) × BitString => (q.2, q.1.2))
            (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))
        exact IsRE.exists_encodable
          (R := fun (a : BitString × BitString) (x : BitString) =>
            R.rel a.1 x ∧ streamLowerGraph f x a.2) (h1.and h2)
      nil_mem := fun p => ⟨[], R.nil_mem p, hlg.1 []⟩
      prefix_closed := fun p y y' ⟨x, hx, hxy⟩ hy' => ⟨x, hx, hlg.2.1 x y y' hxy hy'⟩
      regular := by
        intro p₁ y₁ p₂ y₂ ⟨x₁, hx₁, hy₁⟩ ⟨x₂, hx₂, hy₂⟩ hp
        have hp' : p₁ = p₂ := hp
        subst hp'
        exact hlg.output_compatible_of_input_compatible (R.regular hx₁ hx₂ rfl) hy₁ hy₂ }
  obtain ⟨c, hc⟩ := hR M
  refine ⟨c, fun x y hxy => ?_⟩
  have hKM : KROf M y ≤ KROf R x := by
    apply sInf_le_sInf
    rintro l ⟨p, hp, rfl⟩
    exact ⟨p, ⟨x, hp, hxy⟩, rfl⟩
  exact (hc y).trans (add_le_add_left hKM c)

/-- A functional RE relation is the graph of a partial computable function. -/
private lemma exists_const_plainK_comp_le_KROf_functional {α β : Type*}
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

/-- **SUV Theorem 127 (h) (Section 6.1, printed p. 194).** If `f : Σ → ℕ⊥` is a computable
continuous map, then `C(f(x)) ≤ KR(x) + O(1)`. On finite inputs such a map is a partial
computable prefix-stable function (Theorem 53, `IsPrefixStableFun`).

Proof idea: the composition of an optimal decision decompressor with `f` is a plain
decompressor. On input `p`, apply `f` to the prefixes of `R(p)` until it is defined. Prefix
stability makes the value equal to `f(x)` whenever `x` is a prefix of `R(p)`. -/
theorem exists_const_plainK_comp_le_KROf {R : DecisionDecompressor} (_hR : R.IsOptimal)
    {U : Map} (hU : isOptimalConditional U) {f : BitString →. BitString} (hf : Partrec f)
    (hfs : IsPrefixStableFun f) :
    ∃ c : ℕ, ∀ x y, y ∈ f x → plainK U y ≤ KROf R x + c := by
  have hGraph : IsRE (fun q : BitString × BitString => q.2 ∈ f q.1) :=
    Partrec.graphIsRe f hf
  have hRE : IsRE (fun q : BitString × BitString =>
      ∃ x, R.rel q.1 x ∧ q.2 ∈ f x) := by
    have h1 : IsRE (fun q : (BitString × BitString) × BitString => R.rel q.1.1 q.2) :=
      IsRE.comp_computable R.re
        (g := fun q : (BitString × BitString) × BitString => (q.1.1, q.2))
        (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
    have h2 : IsRE (fun q : (BitString × BitString) × BitString => q.1.2 ∈ f q.2) :=
      IsRE.comp_computable hGraph
        (g := fun q : (BitString × BitString) × BitString => (q.2, q.1.2))
        (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))
    exact IsRE.exists_encodable
      (R := fun (a : BitString × BitString) (x : BitString) => R.rel a.1 x ∧ a.2 ∈ f x)
      (h1.and h2)
  obtain ⟨D, hD, hDS⟩ := exists_const_plainK_comp_le_KROf_functional
    (R := fun (p : BitString) (y : BitString) => ∃ x, R.rel p x ∧ y ∈ f x) hRE (by
      rintro p y y' ⟨x, hx, hy⟩ ⟨x', hx', hy'⟩
      rcases R.regular hx hx' rfl with h | h
      · exact Part.mem_unique (hfs x x' y hy h) hy'
      · exact Part.mem_unique hy (hfs x' x y' hy' h))
  let V : Map := fun q => D q.1
  have hV : isDecompressor V := hD.comp Computable.fst
  obtain ⟨c, hc⟩ := hU.2 V hV
  refine ⟨c, fun x y hy => ?_⟩
  have hle : plainK V y ≤ KROf R x := by
    refine le_sInf ?_
    rintro n ⟨p, hp, rfl⟩
    exact sInf_le ⟨p, (hDS p y).mpr ⟨x, hp, hy⟩, rfl⟩
  exact (hc y []).trans (add_le_add_left hle _)

/-- **SUV Theorem 127 (i) (Section 6.1, printed p. 195).** If `f : ℕ⊥ → Σ` is a computable
continuous map, then `KR(f(x)) ≤ C(x) + O(1)`. Restricted to strings, such a map is a decision
decompressor `F` (its value at `⊥` is a prefix of every value, so it adds nothing; see
`range_KROf_eq_range_contDecisionMap_complexity`). The claim is stated for every prefix `z` of
`f(x)`.

Proof idea: the composition of an optimal plain decompressor with `F` is a decision
decompressor. -/
theorem exists_const_KROf_comp_le_plainK {R : DecisionDecompressor} (hR : R.IsOptimal)
    {U : Map} (hU : isOptimalConditional U) (F : DecisionDecompressor) :
    ∃ c : ℕ, ∀ x z, F.rel x z → KROf R z ≤ plainK U x + c := by
  classical
  let M : DecisionDecompressor :=
    { rel := fun p z => z = [] ∨ ∃ x, x ∈ U (p, []) ∧ F.rel x z
      re := by
        have hG : IsRE (fun q : (BitString × BitString) × BitString => q.2 ∈ U (q.1.1, [])) :=
          (Partrec.graphIsRe U hU.1).comp_computable
            (g := fun q : (BitString × BitString) × BitString => ((q.1.1, ([] : BitString)), q.2))
            (Computable.pair
              (Computable.pair (Computable.fst.comp Computable.fst) (Computable.const []))
              Computable.snd)
        have hF' : IsRE (fun q : (BitString × BitString) × BitString => F.rel q.2 q.1.2) :=
          F.re.comp_computable
            (g := fun q : (BitString × BitString) × BitString => (q.2, q.1.2))
            (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))
        have hE := IsRE.exists_encodable
          (R := fun (a : BitString × BitString) (x : BitString) => x ∈ U (a.1, []) ∧ F.rel x a.2)
          (hG.and hF')
        have hN : IsRE (fun q : BitString × BitString => q.2 = []) :=
          isRE_of_computable_bool _ (fun q => decide (q.2 = [])) (fun q => by simp)
            (Primrec.to_comp (PrimrecPred.decide
              (Primrec.eq.comp (Primrec.snd) (Primrec.const []))))
        exact hN.or hE
      nil_mem := fun p => Or.inl rfl
      prefix_closed := by
        rintro p x x' (rfl | ⟨y, hy, hF1⟩) hx'
        · exact Or.inl (List.prefix_nil.mp hx')
        · exact Or.inr ⟨y, hy, F.prefix_closed hF1 hx'⟩
      regular := by
        rintro p₁ x₁ p₂ x₂ (rfl | ⟨y₁, hy₁, h₁⟩) (rfl | ⟨y₂, hy₂, h₂⟩) hp
        · exact Or.inl (List.prefix_refl _)
        · exact Or.inl (List.nil_prefix)
        · exact Or.inr (List.nil_prefix)
        · have hpp : p₁ = p₂ := hp
          subst hpp
          have : y₁ = y₂ := Part.mem_unique hy₁ hy₂
          subst this
          exact F.regular h₁ h₂ rfl }
  obtain ⟨c, hc⟩ := hR M
  refine ⟨c, fun x z hxz => ?_⟩
  have h : KROf M z ≤ plainK U x := by
    refine le_sInf ?_
    rintro n ⟨p, hp, rfl⟩
    exact modeComplexity_le_length (R := M.rel) (Or.inr ⟨x, hp, hxz⟩)
  exact (hc z).trans (add_le_add_left h _)

/-- **SUV Theorem 127 (j) (Section 6.1, printed p. 195).** A prefix-free set of strings of
decision complexity less than `n` has fewer than `2 ^ n` elements. This holds for every
decision decompressor. `encard` also covers infinite sets.

Proof idea: incompatible strings cannot share a description (regularity), so the elements
have pairwise different descriptions of length `< n`, and there are fewer than `2 ^ n` such
strings. -/
theorem encard_lt_two_pow_of_isPrefixFree_KROf_lt (M : DecisionDecompressor)
    {S : Set BitString} (hS : IsPrefixFree S) (n : ℕ) (h : ∀ x ∈ S, KROf M x < n) :
    S.encard < 2 ^ n := by
  classical
  have hex : ∀ x : S, ∃ p : BitString, M.rel p x.1 ∧ p.length < n := by
    intro x
    have hx := h x.1 x.2
    simp only [KROf, modeComplexity, sInf_lt_iff, Set.mem_ofPred_eq] at hx
    obtain ⟨l, ⟨p, hp, rfl⟩, hl⟩ := hx
    exact ⟨p, hp, by exact_mod_cast hl⟩
  choose f hf1 hf2 using hex
  have hinj : Set.InjOn (fun x : S => f x) Set.univ := by
    intro x _ y _ hxy
    have hc := M.regular (hf1 x) (hf1 y) (by simpa [StrRel.Holds] using hxy)
    have : x.1 = y.1 := by
      rcases hc with hc | hc
      · exact hS x.2 y.2 hc
      · exact (hS y.2 x.2 hc).symm
    exact Subtype.ext this
  have h1 : (Set.univ : Set S).encard ≤ ({p : BitString | p.length < n} : Set BitString).encard :=
      by
    calc (Set.univ : Set S).encard = ((fun x : S => f x) '' Set.univ).encard :=
          (hinj.encard_image).symm
      _ ≤ _ := Set.encard_le_encard (by
          rintro _ ⟨x, _, rfl⟩
          exact hf2 x)
  have h2 : (Set.univ : Set S).encard = S.encard := by
    rw [Set.encard_univ]; rfl
  have h3 : ∀ m : ℕ, ({p : BitString | p.length < m} : Set BitString).encard + 1 ≤ 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      set A : Set BitString := {p : BitString | p.length < m}
      have hsub : ({p : BitString | p.length < m + 1} : Set BitString) ⊆
          {[]} ∪ (((fun x : BitString => false :: x) '' A) ∪ ((fun x : BitString => true :: x) ''
              A)) := by
        intro x hx
        cases x with
        | nil => simp
        | cons a x =>
          have htail : x.length < m := by simpa using hx
          cases a
          · exact Set.mem_union_right _ (Set.mem_union_left _ ⟨x, htail, rfl⟩)
          · exact Set.mem_union_right _ (Set.mem_union_right _ ⟨x, htail, rfl⟩)
      have hle : ({p : BitString | p.length < m + 1} : Set BitString).encard ≤ 1 + (A.encard +
          A.encard) := by
        refine (Set.encard_le_encard hsub).trans ?_
        refine (Set.encard_union_le _ _).trans ?_
        refine add_le_add (by simp) ?_
        refine (Set.encard_union_le _ _).trans ?_
        exact add_le_add (Set.encard_image_le _ _) (Set.encard_image_le _ _)
      calc _ ≤ 1 + (A.encard + A.encard) + 1 := add_le_add_left hle 1
        _ = (A.encard + 1) + (A.encard + 1) := by ring
        _ ≤ 2 ^ m + 2 ^ m := add_le_add ih ih
        _ = 2 ^ (m + 1) := by ring
  have h4 := h3 n
  have hfin : ({p : BitString | p.length < n} : Set BitString).encard ≠ ⊤ := by
    intro htop
    rw [htop] at h4
    simp at h4
  calc S.encard = (Set.univ : Set S).encard := h2.symm
    _ ≤ _ := h1
    _ < _ + 1 := ENat.lt_add_one_iff hfin |>.mpr le_rfl
    _ ≤ 2 ^ n := h4

/-- **SUV Theorem 127 (k) (Section 6.1, printed p. 195).** `KR` is upper semicomputable. This
holds for every decision decompressor.

Proof: `KR_M(x) < n` iff some `p` of length `< n` has `M.rel p x`, a bounded search over an
enumerable relation (`IsRE.existsInList`). -/
theorem isUpperSemicomputable_KROf (M : DecisionDecompressor) :
    IsUpperSemicomputable (KROf M) := by
  obtain ⟨f, hf, hfd⟩ := M.re
  let bound : BitString × ℕ → List BitString := fun q =>
    (List.range q.2).flatMap exactLengthPrograms
  have hbound : Computable bound :=
    (Primrec.list_flatMap (Primrec.list_range.comp Primrec.snd)
      (primrec_exactLengthPrograms.comp Primrec.snd).to₂).to_comp
  have hR : IsRE (fun q : (BitString × ℕ) × BitString => M.rel q.2 q.1.1) :=
    ⟨fun q => f (q.2, q.1.1),
      hf.comp (Computable.pair Computable.snd (Computable.fst.comp Computable.fst)),
      fun q => hfd _⟩
  have key : ∀ q : BitString × ℕ, KROf M q.1 < q.2 ↔ ∃ p ∈ bound q, M.rel p q.1 := by
    intro q
    simp only [KROf, modeComplexity, sInf_lt_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨l, ⟨p, hp, rfl⟩, hl⟩
      refine ⟨p, ?_, hp⟩
      simp only [bound, List.mem_flatMap, List.mem_range]
      exact ⟨p.length, by exact_mod_cast hl, mem_exactLengthPrograms_self p⟩
    · rintro ⟨p, hpb, hp⟩
      simp only [bound, List.mem_flatMap, List.mem_range] at hpb
      obtain ⟨m, hm, hpm⟩ := hpb
      refine ⟨p.length, ⟨p, hp, rfl⟩, ?_⟩
      rw [exactLengthPrograms_length_eq m p hpm]
      exact_mod_cast hm
  obtain ⟨g, hg, hgd⟩ := IsRE.existsInList (R := fun a b => M.rel b a.1) hR bound hbound
  exact ⟨g, hg, fun q => (hgd q).trans (key q).symm⟩

end GeneralScheme
end Kolmogorov
