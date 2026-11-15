import KolmogorovMathlib.Complexity.GeneralScheme.DecisionBasic
import KolmogorovMathlib.Prefix.StableDecompressors
import KolmogorovMathlib.Complexity.PairComplexity.LogarithmicTerms.ConditionalBounds
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinOnline

/-!
# Regular Relations

Regular relations between descriptions and objects, and the existence of optimal description
modes of each of the four kinds. A relation `S` is regular when related descriptions and
objects are compatible in the sense prescribed by a pair of comparison modes (equality or
compatibility, as prefixes of one another).

Main declarations:

* `exists_prefixStableFun_of_isRegular_compat_eq`: a `≍`-`=`-regular relation is the graph of a
  prefix-stable partial function (Problem 197 (a)).
* `isStreamLowerGraph_streamGapFill_of_isRegular`: a `≍`-`≍`-regular relation determines a
  continuous stream map (Problem 197 (b)).
* `exists_decisionDecompressor_of_isDescriptionMode_eq_compat`: an enumerable `=`-`≍`-regular
  relation is given by a decision decompressor (Problem 197 (c)).
* `exists_isOptimalDescriptionMode`: each of the four kinds of description mode has an optimal
  element (Theorem 128).
* `exists_const_modeComplexity_eq_eq_plainK`: in the `=`-`=` case the optimal complexity agrees
  with plain complexity up to a constant (Theorem 128).

This formalizes Section 6.2 of Shen, Uspensky and Vereshchagin, "Kolmogorov complexity and
algorithmic randomness".
-/

namespace Kolmogorov

namespace GeneralScheme

/-- **SUV Problem 197 (a) (Section 6.2, printed p. 197).** A ≍-=-regular relation determines a
continuous map `Σ → ℕ⊥`. On finite inputs this is the partial function `f` with `f(u) = y` iff
some prefix of `u` is related to `y`. It is automatically prefix-stable.

Proof idea: two prefixes of `u` are compatible, so by regularity they are related to the same
object, and `f` is well defined. -/
theorem exists_prefixStableFun_of_isRegular_compat_eq {S : BitString → BitString → Prop}
    (hS : IsRegular .compat .eq S) :
    ∃ f : BitString →. BitString, IsPrefixStableFun f ∧
      ∀ u y, y ∈ f u ↔ ∃ x, x <+: u ∧ S x y := by
  classical
  let f : BitString →. BitString := fun u =>
    ⟨∃ y x, x <+: u ∧ S x y, fun h => Classical.choose h⟩
  have key : ∀ u y, y ∈ f u ↔ ∃ x, x <+: u ∧ S x y := by
    intro u y
    change y ∈ Part.mk _ _ ↔ _
    rw [Part.mem_mk_iff]
    constructor
    · rintro ⟨h, rfl⟩
      exact Classical.choose_spec h
    · rintro ⟨x, hx, hxy⟩
      have h : ∃ y x, x <+: u ∧ S x y := ⟨y, x, hx, hxy⟩
      refine ⟨h, ?_⟩
      obtain ⟨x', hx', hx'y⟩ := Classical.choose_spec h
      exact hS hx'y hxy (List.prefix_or_prefix_of_prefix hx' hx)
  refine ⟨f, fun u v z hz huv => ?_, key⟩
  obtain ⟨x, hx, hxz⟩ := (key u z).1 hz
  exact (key v z).2 ⟨x, hx.trans huv, hxz⟩

/-- **SUV Problem 197 (b) (Section 6.2, printed p. 197).** A ≍-≍-regular relation determines a
continuous map `Σ → Σ`: its gap-filling closure is the lower graph of a continuous stream map
(Theorem 81). This is the library's `streamGapFill_isStreamLowerGraph` (Problem 137), via
`isRegular_compat_compat_iff`. -/
theorem isStreamLowerGraph_streamGapFill_of_isRegular {S : BitString → BitString → Prop}
    (hS : IsRegular .compat .compat S) : IsStreamLowerGraph (streamGapFill S) :=
  streamGapFill_isStreamLowerGraph ((isRegular_compat_compat_iff S).1 hS)

/-- **SUV Problem 197 (c) (Section 6.2, printed p. 197).** An enumerable =-≍-regular relation
determines a computable continuous map `ℕ⊥ → Σ`, i.e. a decision decompressor. Its graph is the
closure of `S` under prefixes of the object. Enumerability is assumed, which is the case used in
Theorem 128. Without it, the same closure is a non-computable continuous map.

Proof idea: by regularity the objects related to one description are pairwise compatible, so
the prefix closure is a chain for every `p`, and it is enumerable together with `S`. -/
theorem exists_decisionDecompressor_of_isDescriptionMode_eq_compat
    {S : BitString → BitString → Prop} (hS : IsDescriptionMode .eq .compat S) :
    ∃ M : DecisionDecompressor, ∀ p v, M.rel p v ↔ (v = [] ∨ ∃ y, v <+: y ∧ S p y) := by
  classical
  obtain ⟨hRE, hreg⟩ := hS
  have hpre : Computable (fun q : (BitString × BitString) × BitString =>
      decide (q.1.2 <+: q.2)) := by
    have htake : Primrec (fun q : (BitString × BitString) × BitString =>
        q.2.take q.1.2.length) :=
      Primrec.list_take.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd
    have hrel : PrimrecPred (fun q : (BitString × BitString) × BitString =>
        q.2.take q.1.2.length = q.1.2) :=
      PrimrecRel.comp Primrec.eq htake (Primrec.snd.comp Primrec.fst)
    refine (Primrec.ite hrel (Primrec.const true) (Primrec.const false)).to_comp.of_eq
      fun q => ?_
    by_cases h : q.2.take q.1.2.length = q.1.2
    · have : q.1.2 <+: q.2 := List.prefix_iff_eq_take.mpr h.symm
      simp [h, this]
    · have : ¬ q.1.2 <+: q.2 := fun h' => h (List.prefix_iff_eq_take.mp h').symm
      simp [h, this]
  have hSq : IsRE (fun q : (BitString × BitString) × BitString => S q.1.1 q.2) :=
    hRE.comp_computable (g := fun q : (BitString × BitString) × BitString => (q.1.1, q.2))
      (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  have h1 : IsRE (fun q : (BitString × BitString) × BitString =>
      q.1.2 <+: q.2 ∧ S q.1.1 q.2) :=
    (hSq.and_computable hpre).of_iff fun q => by simp
  have h2 : IsRE (fun q : BitString × BitString => ∃ y, q.2 <+: y ∧ S q.1 y) :=
    IsRE.exists_encodable (R := fun (q : BitString × BitString) (y : BitString) =>
      q.2 <+: y ∧ S q.1 y) h1
  have h3 : IsRE (fun q : BitString × BitString => q.2 = []) :=
    isRE_of_computable_bool _ (fun q => decide (q.2 = []))
      (fun q => by simp)
      (Primrec.to_comp ((Primrec.eq.comp Primrec.snd (Primrec.const [])).decide))
  have hre : IsRE (fun q : BitString × BitString =>
      q.2 = [] ∨ ∃ y, q.2 <+: y ∧ S q.1 y) := h3.or h2
  refine ⟨⟨fun p v => v = [] ∨ ∃ y, v <+: y ∧ S p y, hre, fun p => Or.inl rfl, ?_, ?_⟩,
    fun p v => Iff.rfl⟩
  · rintro p x x' (rfl | ⟨y, hxy, hy⟩) hx'
    · exact Or.inl (List.prefix_nil.mp hx')
    · exact Or.inr ⟨y, hx'.trans hxy, hy⟩
  · rintro p₁ x₁ p₂ x₂ h₁ h₂ (rfl : p₁ = p₂)
    rcases h₁ with rfl | ⟨y₁, hx₁, hy₁⟩
    · exact Or.inl (List.nil_prefix)
    rcases h₂ with rfl | ⟨y₂, hx₂, hy₂⟩
    · exact Or.inr (List.nil_prefix)
    rcases hreg hy₁ hy₂ rfl with h | h
    · exact List.prefix_or_prefix_of_prefix (hx₁.trans h) hx₂
    · exact List.prefix_or_prefix_of_prefix hx₁ (hx₂.trans h)

/-- A functional RE relation on bit strings is the graph of a partial recursive function. -/
private lemma exists_isOptimalDescriptionMode_functional {R : BitString → BitString → Prop}
    (hR : IsRE (fun q : BitString × BitString => R q.1 q.2))
    (hfun : ∀ a b b', R a b → R a b' → b = b') :
    ∃ f : BitString →. BitString, Partrec f ∧ ∀ a b, b ∈ f a ↔ R a b := by
  obtain ⟨g, hg, hdom⟩ := hR
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg
  let step : BitString → ℕ → Option BitString := fun a n =>
    (Encodable.decode (α := BitString) n.unpair.1).bind fun b =>
      if (Nat.Partrec.Code.evaln (n.unpair.2 + 1) c (Encodable.encode (a, b))).isSome
      then some b else none
  have hstep : Computable₂ step := by
    have hdec : Computable (fun p : BitString × ℕ =>
        Encodable.decode (α := BitString) p.2.unpair.1) :=
      Computable.decode.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
    have hk : Computable (fun q : (BitString × ℕ) × BitString => q.1.2.unpair.2 + 1) :=
      Primrec.to_comp (Primrec.succ.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))))
    have hin : Computable (fun q : (BitString × ℕ) × BitString => Encodable.encode (q.1.1, q.2)) :=
      Computable.comp Computable.encode
        (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
    have hev : Computable (fun q : (BitString × ℕ) × BitString =>
        (Nat.Partrec.Code.evaln (q.1.2.unpair.2 + 1) c (Encodable.encode (q.1.1, q.2))).isSome) :=
      Primrec.option_isSome.to_comp.comp
        ((evalnCoreComputable c).comp (Computable.pair hk hin))
    have hbody : Computable₂ (fun (p : BitString × ℕ) (b : BitString) =>
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
  refine ⟨fun a => Nat.rfindOpt (step a), Partrec.rfindOpt hstep,
    fun a b => ⟨hsound a b, fun hab => ?_⟩⟩
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

private lemma exists_isOptimalDescriptionMode_decide_prefix :
    Computable (fun q : BitString × BitString => decide (q.2 <+: q.1)) := by
  have H : Computable (fun q : BitString × BitString => q.1.take q.2.length) :=
    (Primrec.list_take.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst).to_comp
  have H2 : Computable (fun q : BitString × BitString =>
      decide (q.1.take q.2.length = q.2)) :=
    (Primrec.to_comp (PrimrecPred.decide Primrec.eq)).comp (Computable.pair H Computable.snd)
  refine H2.of_eq fun q => ?_
  exact decide_eq_decide.mpr (by rw [List.prefix_iff_eq_take]; exact eq_comm)

private lemma exists_isOptimalDescriptionMode_isRE_prefixClosure {S : BitString → BitString → Prop}
    (hS : IsRE (fun q : BitString × BitString => S q.1 q.2)) :
    IsRE (fun q : BitString × BitString => ∃ x, x <+: q.1 ∧ S x q.2) := by
  have h1 : IsRE (fun a : (BitString × BitString) × BitString => S a.2 a.1.2) :=
    hS.comp_computable (g := fun a : (BitString × BitString) × BitString => (a.2, a.1.2))
      (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))
  have hdp : Computable (fun a : (BitString × BitString) × BitString =>
      decide (a.2 <+: a.1.1)) :=
    have hg : Computable (fun a : (BitString × BitString) × BitString => (a.1.1, a.2)) :=
      Computable.pair (Computable.fst.comp Computable.fst) Computable.snd
    Computable.comp (f := fun q : BitString × BitString => decide (q.2 <+: q.1))
      (g := fun a : (BitString × BitString) × BitString => (a.1.1, a.2))
      exists_isOptimalDescriptionMode_decide_prefix hg
  have h2 : IsRE (fun a : (BitString × BitString) × BitString =>
      decide (a.2 <+: a.1.1) = true ∧ S a.2 a.1.2) := h1.and_computable hdp
  have h3 : IsRE (fun a : (BitString × BitString) × BitString =>
      a.2 <+: a.1.1 ∧ S a.2 a.1.2) :=
    h2.of_iff fun a => by rw [decide_eq_true_iff]
  exact IsRE.exists_encodable (R := fun (q : BitString × BitString) (x : BitString) =>
    x <+: q.1 ∧ S x q.2) h3

private lemma exists_isOptimalDescriptionMode_isRE_map (V : Map) (hV : isDecompressor V) :
    IsRE (fun q : BitString × BitString => q.2 ∈ V (q.1, [])) := by
  obtain ⟨f, hf, hd⟩ := Partrec.graphIsRe V hV
  refine ⟨fun q => f ((q.1, []), q.2), ?_, fun q => hd _⟩
  exact hf.comp (Computable.pair (Computable.pair Computable.fst (Computable.const []))
    Computable.snd)

private lemma exists_isOptimalDescriptionMode_modeComplexity_map (V : Map) (x : BitString) :
    modeComplexity (fun p x => x ∈ V (p, [])) x = condK V x [] := by
  unfold modeComplexity condK
  congr 1
  ext l
  simp only [Set.mem_ofPred_eq, candidateLengths, produces, programLength]
  constructor <;> rintro ⟨p, hp, rfl⟩ <;> exact ⟨p, hp, rfl⟩

private lemma exists_isOptimalDescriptionMode_eq_eq :
    ∃ R, IsOptimalDescriptionMode .eq .eq R := by
  obtain ⟨U, hUdec, hUopt⟩ := exists_isOptimalConditional
  refine ⟨fun p x => x ∈ U (p, []), ⟨exists_isOptimalDescriptionMode_isRE_map U hUdec, ?_⟩, ?_⟩
  · intro p₁ x₁ p₂ x₂ h₁ h₂ hp
    change p₁ = p₂ at hp
    subst hp
    exact Part.mem_unique h₁ h₂
  · rintro S ⟨hSre, hreg⟩
    obtain ⟨D, hD, hDR⟩ := exists_isOptimalDescriptionMode_functional hSre
      (fun a b b' h h' => hreg h h' rfl)
    obtain ⟨c, hc⟩ := hUopt (fun q => D q.1) (hD.comp Computable.fst)
    refine ⟨c, fun x => ?_⟩
    have hDK : condK (fun q => D q.1) x [] = modeComplexity S x := by
      unfold modeComplexity condK
      congr 1
      ext l
      simp only [Set.mem_ofPred_eq, candidateLengths, produces, programLength]
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, (hDR p x).mp hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, (hDR p x).mpr hp, rfl⟩
    rw [exists_isOptimalDescriptionMode_modeComplexity_map, ← hDK]
    exact hc x []

private lemma exists_isOptimalDescriptionMode_compat_eq :
    ∃ R, IsOptimalDescriptionMode .compat .eq R := by
  obtain ⟨U, ⟨hUdec, hUst⟩, hUopt⟩ := exists_optimal_prefixStable_decompressor
  refine ⟨fun p x => x ∈ U (p, []), ⟨exists_isOptimalDescriptionMode_isRE_map U hUdec, ?_⟩, ?_⟩
  · intro p₁ x₁ p₂ x₂ h₁ h₂ hp
    change x₁ = x₂
    rcases hp with hp | hp
    · exact Part.mem_unique (hUst [] p₁ p₂ x₁ h₁ hp) h₂
    · exact Part.mem_unique h₁ (hUst [] p₂ p₁ x₂ h₂ hp)
  · rintro S ⟨hSre, hreg⟩
    have hfun : ∀ u y y', (∃ x, x <+: u ∧ S x y) → (∃ x, x <+: u ∧ S x y') → y = y' := by
      rintro u y y' ⟨x, hx, hxy⟩ ⟨x', hx', hx'y'⟩
      exact hreg hxy hx'y' (List.prefix_or_prefix_of_prefix hx hx')
    obtain ⟨f, hf, hfR⟩ := exists_isOptimalDescriptionMode_functional
      (R := fun u y => ∃ x, x <+: u ∧ S x y)
      (exists_isOptimalDescriptionMode_isRE_prefixClosure hSre) hfun
    have hMdec : isDecompressor (fun q : BitString × BitString => f q.1) :=
      hf.comp Computable.fst
    have hMst : IsPrefixStableMachine (fun q : BitString × BitString => f q.1) := by
      intro c u v z hz huv
      obtain ⟨x, hx, hxz⟩ := (hfR u z).mp hz
      exact (hfR v z).mpr ⟨x, hx.trans huv, hxz⟩
    obtain ⟨c, hc⟩ := hUopt _ ⟨hMdec, hMst⟩
    refine ⟨c, fun x => ?_⟩
    rw [exists_isOptimalDescriptionMode_modeComplexity_map]
    refine (hc x []).trans (add_le_add ?_ le_rfl)
    refine le_sInf ?_
    rintro l ⟨p, hp, rfl⟩
    exact sInf_le ⟨p, (hfR p x).mpr ⟨p, List.prefix_refl p, hp⟩, rfl⟩

/-- **SUV Theorem 128 (Section 6.2, printed p. 198), existence.** For each of the four
combinations `α, β ∈ {=, ≍}` there is an optimal α-β description mode.

Proof idea: enumerable α-β-regular relations correspond to computable continuous maps of the
corresponding spaces (Problem 197), and these have optimal elements (Theorems 48, 84,
Problem 192). Alternatively, directly: trim the enumerable relations to regular ones and
combine them with self-delimiting indices. -/
theorem exists_isOptimalDescriptionMode (α β : StrRel) :
    ∃ R, IsOptimalDescriptionMode α β R := by
  cases α <;> cases β
  · exact exists_isOptimalDescriptionMode_eq_eq
  · obtain ⟨M, hM⟩ := exists_optimal_decisionDecompressor
    refine ⟨M.rel, ⟨M.re, M.regular⟩, fun S hS => ?_⟩
    obtain ⟨M', hM'⟩ := exists_decisionDecompressor_of_isDescriptionMode_eq_compat hS
    obtain ⟨c, hc⟩ := hM M'
    refine ⟨c, fun x => (hc x).trans (add_le_add ?_ le_rfl)⟩
    refine le_sInf ?_
    rintro l ⟨p, hp, rfl⟩
    exact modeComplexity_le_length (R := M'.rel)
      ((hM' p x).2 (Or.inr ⟨x, List.prefix_refl x, hp⟩))
  · exact exists_isOptimalDescriptionMode_compat_eq
  · obtain ⟨R, hRreg, hRre, hopt⟩ := exists_optimalConsistentRelation
    exact ⟨R, ⟨hRre, (isRegular_compat_compat_iff R).2 hRreg⟩,
      fun S hS => hopt S ((isRegular_compat_compat_iff S).1 hS.2) hS.1⟩

/-- A functional RE relation on bit strings is the graph of a partial recursive function. -/
private lemma exists_const_modeComplexity_eq_eq_plainK_functional {R : BitString → BitString → Prop}
    (hR : IsRE (fun q : BitString × BitString => R q.1 q.2))
    (hfun : ∀ a b b', R a b → R a b' → b = b') :
    ∃ f : BitString →. BitString, Partrec f ∧ ∀ a b, b ∈ f a ↔ R a b := by
  obtain ⟨g, hg, hdom⟩ := hR
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg
  let step : BitString → ℕ → Option BitString := fun a n =>
    (Encodable.decode (α := BitString) n.unpair.1).bind fun b =>
      if (Nat.Partrec.Code.evaln (n.unpair.2 + 1) c (Encodable.encode (a, b))).isSome
      then some b else none
  have hstep : Computable₂ step := by
    have hdec : Computable (fun p : BitString × ℕ =>
        Encodable.decode (α := BitString) p.2.unpair.1) :=
      Computable.decode.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
    have hk : Computable (fun q : (BitString × ℕ) × BitString => q.1.2.unpair.2 + 1) :=
      Primrec.to_comp (Primrec.succ.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))))
    have hin : Computable (fun q : (BitString × ℕ) × BitString => Encodable.encode (q.1.1, q.2)) :=
      Computable.comp Computable.encode
        (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
    have hev : Computable (fun q : (BitString × ℕ) × BitString =>
        (Nat.Partrec.Code.evaln (q.1.2.unpair.2 + 1) c (Encodable.encode (q.1.1, q.2))).isSome) :=
      Primrec.option_isSome.to_comp.comp
        ((evalnCoreComputable c).comp (Computable.pair hk hin))
    have hbody : Computable₂ (fun (p : BitString × ℕ) (b : BitString) =>
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
  refine ⟨fun a => Nat.rfindOpt (step a), Partrec.rfindOpt hstep,
    fun a b => ⟨hsound a b, fun hab => ?_⟩⟩
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

/-- **SUV Theorem 128 (Section 6.2, printed p. 198), case `=`-`=`.** The optimal =-=-complexity
is plain complexity: =-=-regular relations are graphs of partial functions. -/
theorem exists_const_modeComplexity_eq_eq_plainK {R : BitString → BitString → Prop}
    (hR : IsOptimalDescriptionMode .eq .eq R) {U : Map} (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x, modeComplexity R x ≤ plainK U x + c ∧ plainK U x ≤ modeComplexity R x + c := by
  obtain ⟨⟨hRre, hreg⟩, hopt⟩ := hR
  obtain ⟨hUdec, hUopt⟩ := hU
  obtain ⟨D, hD, hDR⟩ := exists_const_modeComplexity_eq_eq_plainK_functional hRre
    (fun a b b' h h' => hreg h h' rfl)
  obtain ⟨c₁, hc₁⟩ := hUopt (fun q => D q.1) (hD.comp Computable.fst)
  let T : BitString → BitString → Prop := fun p x => x ∈ U (p, [])
  have hTRE : IsRE (fun q : BitString × BitString => T q.1 q.2) := by
    obtain ⟨f, hf, hd⟩ := Partrec.graphIsRe U hUdec
    refine ⟨fun q => f ((q.1, []), q.2), ?_, fun q => hd _⟩
    exact hf.comp (Computable.pair (Computable.pair Computable.fst (Computable.const []))
      Computable.snd)
  have hTreg : IsRegular .eq .eq T := by
    intro p₁ x₁ p₂ x₂ h₁ h₂ hp
    change p₁ = p₂ at hp
    subst hp
    exact Part.mem_unique h₁ h₂
  obtain ⟨c₂, hc₂⟩ := hopt T ⟨hTRE, hTreg⟩
  have hT : ∀ x, modeComplexity T x = plainK U x := by
    intro x
    unfold modeComplexity plainK condK
    congr 1
    ext l
    simp only [Set.mem_ofPred_eq, candidateLengths, produces, programLength, T]
    constructor <;> rintro ⟨p, hp, rfl⟩ <;> exact ⟨p, hp, rfl⟩
  have hDK : ∀ x, condK (fun q => D q.1) x [] = modeComplexity R x := by
    intro x
    unfold modeComplexity condK
    congr 1
    ext l
    simp only [Set.mem_ofPred_eq, candidateLengths, produces, programLength]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, (hDR p x).mp hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, (hDR p x).mpr hp, rfl⟩
  refine ⟨max c₁ c₂, fun x => ⟨?_, ?_⟩⟩
  · calc modeComplexity R x ≤ modeComplexity T x + c₂ := hc₂ x
      _ = plainK U x + c₂ := by rw [hT]
      _ ≤ plainK U x + (max c₁ c₂ : ℕ) := by
        gcongr; exact_mod_cast le_max_right _ _
  · calc plainK U x ≤ condK (fun q => D q.1) x [] + c₁ := hc₁ x []
      _ = modeComplexity R x + c₁ := by rw [hDK]
      _ ≤ modeComplexity R x + (max c₁ c₂ : ℕ) := by
        gcongr; exact_mod_cast le_max_left _ _

end GeneralScheme
end Kolmogorov
