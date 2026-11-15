import KolmogorovMathlib.InformationLogic.Problems

/-!
# Bridge lemmas: algorithms between problems bound their complexities

Every complexity bound of SUV Chapter 13 is proved by exhibiting an algorithm that transforms a
solution of one problem into a solution of another, possibly with `O(log n)` bits of advice
(the number `n` and one bit).  This module turns such algorithms into complexity inequalities,
and provides the standard admissible calculus.
-/

namespace Kolmogorov
namespace InformationLogic

open ProblemCalculus

/-- Auxiliary lemma, not a numbered SUV item (used throughout Chapter 13).  A partial computable
map does not increase plain complexity by more than a constant: the partial analogue of the
library lemma `plainK_map_le` (compose the decompressor with the map and use optimality). -/
theorem plainK_le_of_mem_partrec (D : Map) (hD : isOptimalConditional D)
    (f : BitString →. BitString) (hf : Partrec f) :
    ∃ c : ℕ, ∀ x y, y ∈ f x → plainK D y ≤ plainK D x + (c : ℕ∞) := by
  let E : Map := fun pair => (D (pair.1, [])).bind f
  have hE : isDecompressor E :=
    Partrec.bind (Partrec.comp hD.1 (Computable.pair Computable.fst (Computable.const [])))
      (hf.comp Computable.snd).to₂
  obtain ⟨c, hc⟩ := hD.2 E hE
  refine ⟨c, fun x y hy => le_trans (hc y []) ?_⟩
  gcongr
  apply sInf_le_sInf
  rintro n ⟨p, hp, rfl⟩
  exact ⟨p, Part.mem_bind_iff.2 ⟨x, hp, hy⟩, rfl⟩

/-- Auxiliary lemma, not a numbered SUV item (used throughout Chapter 13).  An algorithm that
maps every solution of `X` to a solution of `Y` gives `C(Y) ≤ C(X) + O(1)`, with a constant
depending on the algorithm only (not on `X`, `Y`).  This is the form in which SUV Chapter 13
uses "an algorithm transforms solutions"; apply the map to a simplest solution of `X`. -/
theorem problemK_le_of_partrec (D : Map) (hD : isOptimalConditional D)
    (f : BitString →. BitString) (hf : Partrec f) :
    ∃ c : ℕ, ∀ X Y : Set BitString, (∀ x ∈ X, ∃ y ∈ Y, y ∈ f x) →
      problemK D Y ≤ problemK D X + (c : ℕ∞) := by
  obtain ⟨c, hc⟩ := plainK_le_of_mem_partrec D hD f hf
  refine ⟨c, fun X Y hXY => ?_⟩
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simp
  obtain ⟨x, hx, hxeq⟩ := exists_mem_plainK_eq_problemK D hX
  obtain ⟨y, hy, hyf⟩ := hXY x hx
  calc problemK D Y ≤ plainK D y := problemK_le_of_mem D hy
    _ ≤ plainK D x + c := hc x y hyf
    _ = problemK D X + c := by rw [hxeq]

/-- Auxiliary lemma, not a numbered SUV item (Section 13.2, printed p. 404).  A problem that has
a fixed solution `s` has complexity at most `C(s)`; with an optimal decompressor this is a
finite constant (`C(s) ≤ |s| + O(1)`). -/
theorem exists_problemK_le_of_mem (D : Map) (hD : isOptimalConditional D) (s : BitString) :
    ∃ c : ℕ, ∀ X : Set BitString, s ∈ X → problemK D X ≤ (c : ℕ∞) := by
  obtain ⟨c, hc⟩ := plainK_le_length D hD
  exact ⟨s.length + c, fun X hs => (problemK_le_of_mem D hs).trans (by simpa using hc s)⟩

/-- Auxiliary lemma, not a numbered SUV item (Sections 13.1, 13.3, 13.4).  An algorithm that gets
a solution of `X`, the number `n` and one advice bit, and produces a solution of `Y` (for some
value of the bit, which may depend on the solution), gives
`C(Y) ≤ C(X) + O(log n)`, the constant depending on the algorithm only.  This is the form of
the `O(log n)` bounds of SUV §§13.1, 13.3, 13.4 ("given `n`, a solution and one additional bit").

Proof idea: `C(f(x, n, b)) ≤ C(x, n, b) + O(1) ≤ C(x) + O(log n)`, coding `n` and `b`
self-delimitingly in front of a shortest description of `x`
(cf. `plainK_pair_le_add_two_log`). -/
theorem problemK_le_of_partrec_advice (D : Map) (hD : isOptimalConditional D)
    (f : BitString × (ℕ × Bool) →. BitString) (hf : Partrec f) :
    ∃ c : ℕ, ∀ (X Y : Set BitString) (n : ℕ),
      (∀ x ∈ X, ∃ b : Bool, ∃ y ∈ Y, y ∈ f (x, n, b)) →
        problemK D Y ≤ problemK D X + (logSlack c n : ℕ∞) := by
  let E : Map := fun pr =>
    (D ((decodeSecond pr.1).tail, [])).bind fun x =>
      f (x, decodeBits (decodeFirst pr.1), (decodeSecond pr.1).headI)
  have hE : isDecompressor E := by
    have h1 : Computable fun pr : BitString × BitString => (decodeSecond pr.1).tail :=
      Primrec.list_tail.to_comp.comp (decodeSecond_computable.comp Computable.fst)
    have h2 : Computable fun pr : BitString × BitString => decodeBits (decodeFirst pr.1) :=
      decodeBits_computable.comp (decodeFirst_computable.comp Computable.fst)
    have h3 : Computable fun pr : BitString × BitString => (decodeSecond pr.1).headI :=
      Primrec.list_headI.to_comp.comp (decodeSecond_computable.comp Computable.fst)
    refine Partrec.bind (hD.1.comp (h1.pair (Computable.const []))) ?_
    exact hf.comp (Computable.snd.pair ((h2.comp Computable.fst).pair
      (h3.comp Computable.fst)))
  obtain ⟨cE, hcE⟩ := hD.2 E hE
  refine ⟨cE + 3, fun X Y n hXY => ?_⟩
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simp
  obtain ⟨x, hx, hxeq⟩ := exists_mem_plainK_eq_problemK D hX
  obtain ⟨b, y, hy, hyf⟩ := hXY x hx
  obtain ⟨p, hp, hplen⟩ := exists_program_le_cVal D hD x
  obtain ⟨c0, hc0⟩ := plainK_le_length D hD
  have hne : plainK D x ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top (x.length + c0))
    calc plainK D x ≤ (x.length : ℕ∞) + (c0 : ℕ∞) := hc0 x
    _ = ((x.length + c0 : ℕ) : ℕ∞) := by push_cast; rfl
  have hpK : (p.length : ℕ∞) ≤ plainK D x := by
    have h1 : (p.length : ℕ∞) ≤ (cVal D x : ℕ∞) := by exact_mod_cast hplen
    rwa [cVal, ENat.natCast_toNat hne] at h1
  set r : BitString := pairCode (Nat.bits n) (b :: p) with hr
  have hprod : produces E r [] y := by
    change y ∈ (D ((decodeSecond r).tail, [])).bind fun x =>
      f (x, decodeBits (decodeFirst r), (decodeSecond r).headI)
    simp only [hr, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits,
      List.tail_cons, List.headI_cons]
    exact Part.mem_bind_iff.2 ⟨x, hp, hyf⟩
  have hrlen : (r.length : ℕ∞) ≤ (p.length : ℕ∞) + (logSlack 2 n : ℕ∞) := by
    rw [hr, length_pairCode, List.length_cons]
    unfold logSlack
    exact_mod_cast (by omega)
  calc problemK D Y ≤ plainK D y := problemK_le_of_mem D hy
    _ ≤ plainK E y + (cE : ℕ∞) := hcE y []
    _ ≤ (r.length : ℕ∞) + (cE : ℕ∞) := by
        gcongr
        exact sInf_le ⟨r, hprod, rfl⟩
    _ ≤ plainK D x + (logSlack 2 n : ℕ∞) + (cE : ℕ∞) := by
        gcongr
        exact hrlen.trans (add_le_add_left hpK _)
    _ ≤ problemK D X + (logSlack (cE + 3) n : ℕ∞) := by
        rw [← hxeq]
        have : logSlack 2 n + cE ≤ logSlack (cE + 3) n := by
          unfold logSlack; nlinarith
        have h' : (logSlack 2 n : ℕ∞) + (cE : ℕ∞) ≤ (logSlack (cE + 3) n : ℕ∞) := by
          exact_mod_cast this
        calc plainK D x + (logSlack 2 n : ℕ∞) + (cE : ℕ∞)
            = plainK D x + ((logSlack 2 n : ℕ∞) + (cE : ℕ∞)) := by rw [add_assoc]
          _ ≤ _ := by gcongr

/-- Auxiliary lemma, not a numbered SUV item (Section 13.1, printed p. 401).  Projection to the
first component: `C(X) ≤ C(X ∧ Y) + O(1)` (apply `P.unpair` and take the first component;
`problemK_le_of_partrec`). -/
theorem problemK_left_le_conj (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ X Y : Set BitString, problemK D X ≤ problemK D (P.conj X Y) + (c : ℕ∞) := by
  obtain ⟨-, hunpair, hinv, -, -, -⟩ := hP
  have hf : Partrec (fun z : BitString => ((P.unpair z).map Prod.fst : Part BitString)) :=
    Computable.ofOption (Computable.option_map hunpair (Computable.fst.comp Computable.snd).to₂)
  obtain ⟨c, hc⟩ := problemK_le_of_partrec D hD _ hf
  refine ⟨c, fun X Y => hc _ _ ?_⟩
  rintro z ⟨x, hx, y, -, rfl⟩
  exact ⟨x, hx, by simp [hinv]⟩

/-- Auxiliary lemma, not a numbered SUV item (Section 13.1, printed p. 401).  Projection to the
second component: `C(Y) ≤ C(X ∧ Y) + O(1)` (apply `P.unpair`, take the second component). -/
theorem problemK_right_le_conj (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ X Y : Set BitString, problemK D Y ≤ problemK D (P.conj X Y) + (c : ℕ∞) := by
  obtain ⟨-, hunpair, hinv, -, -, -⟩ := hP
  have hf : Partrec (fun z : BitString => ((P.unpair z).map Prod.snd : Part BitString)) :=
    Computable.ofOption (Computable.option_map hunpair (Computable.snd.comp Computable.snd).to₂)
  obtain ⟨c, hc⟩ := problemK_le_of_partrec D hD _ hf
  refine ⟨c, fun X Y => hc _ _ ?_⟩
  rintro z ⟨x, -, y, hy, rfl⟩
  exact ⟨y, hy, by simp [hinv]⟩

/-- Auxiliary lemma, not a numbered SUV item (Section 13.1, printed p. 402: Gödel languages
exist).  The library's universal decompressor, read as a programming language
(`[p](x) = universalDecompressor (p, x)`), has the Gödel property: a language `V` with
code `e` is translated by `s ↦ unaryPrefix (encode e) ++ s` (see `universal_simulation`). -/
theorem isGodelLang_universalDecompressor : IsGodelLang universalDecompressor := by
  refine ⟨isDecompressor_universalDecompressor, fun V hV => ?_⟩
  let g : ℕ →. ℕ := fun n =>
    ((Encodable.decode n : Option (BitString × BitString)) : Part (BitString × BitString)).bind
      (fun p => (V p).map Encodable.encode)
  have hg : Partrec g := Partrec.bind (Computable.ofOption Computable.decode)
    (Partrec.map (hV.comp Computable.snd) (Computable.encode.comp Computable.snd).to₂).to₂
  obtain ⟨e, he⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hg)
  refine ⟨fun s => unaryPrefix (Encodable.encode e) ++ s,
    (Primrec.list_append.comp (Primrec.const _) Primrec.id).to_comp, fun s x => ?_⟩
  rw [universal_simulation, he]
  simp only [g, Encodable.encodek, Part.coe_some, Part.bind_some, Part.map_map,
    Function.comp_def, Option.getD_some]
  exact Part.map_id' (fun _ => rfl) _

/-- Auxiliary lemma, not a numbered SUV item (Section 13.1, printed p. 402).  Gödel languages
exist (`isGodelLang_universalDecompressor`). -/
theorem exists_isGodelLang : ∃ L : Map, IsGodelLang L :=
  ⟨_, isGodelLang_universalDecompressor⟩

/-- Auxiliary lemma, not a numbered SUV item (Section 13.2, printed p. 404).  The standard
calculus over a Gödel language is admissible: `pairCode` is computable and
injective, `pairUnpair` is its computable inverse (`decodeFirst_pairCode`,
`decodeSecond_pairCode`, `pairCode_primrec`, `CodedFiniteDistribution.decodeFirst_primrec`),
and the tags `[false]`, `[true]` differ. -/
theorem std_admissible {L : Map} (hL : IsGodelLang L) : (std L).Admissible := by
  have hpc : Primrec₂ pairCode := CodedFiniteDistribution.pairCode_primrec
  have hf : Primrec decodeFirst := CodedFiniteDistribution.decodeFirst_primrec
  have hs : Primrec decodeSecond := CodedFiniteDistribution.decodeSecond_primrec
  refine ⟨hpc.to_comp, ?_, fun x y => ?_, fun z x y h => ?_, by simp [std], hL⟩
  · have hc : PrimrecPred (fun z : BitString => pairCode (decodeFirst z) (decodeSecond z) = z) :=
      Primrec.eq.comp (hpc.comp hf hs) Primrec.id
    exact (Primrec.ite hc (Primrec.option_some.comp (hf.pair hs)) (Primrec.const none)).to_comp
  · simp [std, pairUnpair, decodeFirst_pairCode, decodeSecond_pairCode]
  · simp only [std, pairUnpair] at h ⊢
    split_ifs at h with hz
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hz

/-- Auxiliary lemma, not a numbered SUV item (Section 13.2, printed p. 404).  Admissible calculi
exist, so the statements of the chapter are not vacuous (`std_admissible`). -/
theorem exists_admissible : ∃ P : ProblemCalculus, P.Admissible :=
  ⟨_, std_admissible isGodelLang_universalDecompressor⟩

end InformationLogic
end Kolmogorov
