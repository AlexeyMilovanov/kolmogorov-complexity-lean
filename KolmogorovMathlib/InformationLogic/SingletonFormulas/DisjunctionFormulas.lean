import KolmogorovMathlib.InformationLogic.Bridges
import KolmogorovMathlib.InformationLogic.IntuitionisticBounds
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerBallModels

/-!
# Disjunction Formulas

Complexities of formulas of the problem calculus built from singleton problems with
disjunction, conjunction and implication, up to `O(log n)` for strings of length at most `n`.
The main declarations are `problemK_disj_le_imp_imp_singleton` (the complexity of `{x} ∨ {y}` is
at most that of `({x} → {y}) → {y}`), and `problemK_imp_imp_le_disj_conj_imp` and
`problemK_disj_conj_imp_le_imp_imp` (the complexities of `({x} → {y}) → {z}` and of
`{z} ∨ ({x} ∧ ({y} → {z}))` agree).  The proofs use effective searches over programs of
two-point functions.  This formalizes the part of the book by Shen, Uspensky and Vereshchagin
on the logic of problems and Kolmogorov complexity.
-/

namespace Kolmogorov
namespace InformationLogic
open ProblemCalculus

/-- Step 1 of the proof of `problemK_disj_le_imp_imp_singleton`: the programs `l_τ` of
the two-point functions `τ = [u ↦ v, w ↦ z, else ↦ []]`.  There is a total computable
`ℓ u v w z` (the program of `τ`, found effectively from the table of `τ` by the Gödel property of
`P.lang`) such that (a) `ℓ u v w z` computes `u ↦ v`, i.e. `v ∈ [ℓ u v w z](u)`, when `u ≠ w`, and
(b) `ℓ u v w z = ℓ w z u v` when `u ≠ w` (the program depends on the function `τ` only, so the
key is the table sorted by a fixed order, e.g. by `Encodable.encode` of the first entry). -/
private theorem problemK_disj_le_imp_imp_singleton_programs
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ ℓ : BitString → BitString → BitString → BitString → BitString,
      Computable (fun q : (BitString × BitString) × (BitString × BitString) =>
        ℓ q.1.1 q.1.2 q.2.1 q.2.2) ∧
      (∀ u v w z, u ≠ w → ℓ u v w z = ℓ w z u v) ∧
      (∀ u v w z, u ≠ w → v ∈ P.lang (ℓ u v w z, u)) := by
  obtain ⟨-, -, -, -, -, -, hG⟩ := hP
  have hpc : Primrec₂ pairCode := CodedFiniteDistribution.pairCode_primrec
  have hf : Primrec decodeFirst := CodedFiniteDistribution.decodeFirst_primrec
  have hs : Primrec decodeSecond := CodedFiniteDistribution.decodeSecond_primrec
  let key : (BitString × BitString) × (BitString × BitString) → BitString := fun q =>
    if Encodable.encode q.1.1 ≤ Encodable.encode q.2.1 then
      pairCode (pairCode q.1.1 q.1.2) (pairCode q.2.1 q.2.2)
    else pairCode (pairCode q.2.1 q.2.2) (pairCode q.1.1 q.1.2)
  have hkey : Primrec key := by
    have h1 : Primrec (fun q : (BitString × BitString) × (BitString × BitString) => q.1.1) :=
      Primrec.fst.comp Primrec.fst
    have h2 : Primrec (fun q : (BitString × BitString) × (BitString × BitString) => q.1.2) :=
      Primrec.snd.comp Primrec.fst
    have h3 : Primrec (fun q : (BitString × BitString) × (BitString × BitString) => q.2.1) :=
      Primrec.fst.comp Primrec.snd
    have h4 : Primrec (fun q : (BitString × BitString) × (BitString × BitString) => q.2.2) :=
      Primrec.snd.comp Primrec.snd
    have hle : PrimrecPred (fun q : (BitString × BitString) × (BitString × BitString) =>
        Encodable.encode q.1.1 ≤ Encodable.encode q.2.1) :=
      Primrec.nat_le.comp (Primrec.encode.comp h1) (Primrec.encode.comp h3)
    exact Primrec.ite hle (hpc.comp (hpc.comp h1 h2) (hpc.comp h3 h4))
      (hpc.comp (hpc.comp h3 h4) (hpc.comp h1 h2))
  let V : Map := fun q => Part.some (if q.2 = decodeFirst (decodeFirst q.1) then
    decodeSecond (decodeFirst q.1) else decodeSecond (decodeSecond q.1))
  have hV : Partrec V := by
    have hp : Primrec (fun q : BitString × BitString =>
        if q.2 = decodeFirst (decodeFirst q.1) then decodeSecond (decodeFirst q.1)
          else decodeSecond (decodeSecond q.1)) := by
      have hq1 : Primrec (fun q : BitString × BitString => decodeFirst q.1) :=
        hf.comp Primrec.fst
      have hq2 : Primrec (fun q : BitString × BitString => decodeSecond q.1) :=
        hs.comp Primrec.fst
      exact Primrec.ite (Primrec.eq.comp Primrec.snd (hf.comp hq1))
        (hs.comp hq1) (hs.comp hq2)
    exact hp.to_comp.partrec
  obtain ⟨t, ht, hts⟩ := hG V hV
  refine ⟨fun u v w z => t (key ((u, v), (w, z))), ?_, ?_, ?_⟩
  · exact ht.comp hkey.to_comp
  · intro u v w z huw
    have hne : Encodable.encode u ≠ Encodable.encode w := fun h => huw (Encodable.encode_injective
        h)
    simp only [key]
    split_ifs <;> first | rfl | omega
  · intro u v w z huw
    have hne : Encodable.encode u ≠ Encodable.encode w := fun h => huw (Encodable.encode_injective
        h)
    rw [hts]
    change v ∈ Part.some _
    rw [Part.mem_some_iff]
    by_cases hle : Encodable.encode u ≤ Encodable.encode w
    · have hk : key ((u, v), (w, z)) = pairCode (pairCode u v) (pairCode w z) := ite_eq_left hle
      rw [hk, decodeFirst_pairCode, decodeFirst_pairCode, ite_eq_left rfl, decodeSecond_pairCode]
    · have hk : key ((u, v), (w, z)) = pairCode (pairCode w z) (pairCode u v) := ite_eq_right hle
      rw [hk, decodeFirst_pairCode, decodeFirst_pairCode, ite_eq_right huw, decodeSecond_pairCode,
        decodeSecond_pairCode]

/-- Compatibility of a pair `(u, v)` with a program `p` at level `n` (SUV printed p. 405, in the
form with two-point functions): for all `w, z` of length at most `n` with `w ≠ u`, the function
`τ = [u ↦ v, w ↦ z, else ↦ []]` is solved by `ℓ`, and `[p](ℓ u v w z) = v`. -/
private def problemK_disj_le_imp_imp_singleton_Compat (P : ProblemCalculus)
    (ℓ : BitString → BitString → BitString → BitString → BitString)
    (n : ℕ) (p u v : BitString) : Prop :=
  u.length ≤ n ∧ v.length ≤ n ∧
    ∀ w z : BitString, w.length ≤ n → z.length ≤ n → w ≠ u → v ∈ P.lang (p, ℓ u v w z)

/-- Step-bounded evaluation of a partial computable function: `Nat.Partrec.Code.evaln` pulled
back along the encodings. -/
private theorem problemK_disj_le_imp_imp_singleton_search_stepEval
    {α β : Type} [Primcodable α] [Primcodable β] {f : α →. β} (hf : Partrec f) :
    ∃ E : α → ℕ → Option β, Computable₂ E ∧
      (∀ (a : α) (s t : ℕ) (b : β), s ≤ t → E a s = some b → E a t = some b) ∧
      (∀ (a : α) (b : β), b ∈ f a ↔ ∃ s, E a s = some b) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  have hevalr : ∀ a : α,
      Nat.Partrec.Code.eval c (Encodable.encode a) = Part.map Encodable.encode (f a) := by
    intro a
    simp only [hc]
    rw [Encodable.encodek]
    simp
  refine ⟨fun a s => (Nat.Partrec.Code.evaln s c (Encodable.encode a)).bind
    (fun m => Encodable.decode m), ?_, ?_, ?_⟩
  · have hsnd : Primrec (fun x : α × ℕ => x.2) := Primrec.snd
    have hfst : Primrec (fun x : α × ℕ => x.1) := Primrec.fst
    have h_prim := Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair hsnd (Primrec.const c)) (Primrec.encode.comp hfst))
    exact Computable.option_bind (Primrec.to_comp h_prim)
      (Computable.decode.comp Computable.snd)
  · intro a s t b hst h
    simp only at h ⊢
    rcases hev : Nat.Partrec.Code.evaln s c (Encodable.encode a) with _ | m
    · rw [hev] at h; simp at h
    · have hmono : Nat.Partrec.Code.evaln t c (Encodable.encode a) = some m :=
        Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hst (Option.mem_def.mpr hev))
      rw [hev] at h
      rw [hmono]
      exact h
  · intro a b
    simp only
    constructor
    · intro hb
      have hmem : Encodable.encode b ∈ Nat.Partrec.Code.eval c (Encodable.encode a) := by
        rw [hevalr a]
        exact Part.mem_map _ hb
      obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
      refine ⟨s, ?_⟩
      rw [Option.mem_def.mp hs]
      simp only [Option.bind]
      exact Encodable.encodek b
    · rintro ⟨s, hs⟩
      rcases hev : Nat.Partrec.Code.evaln s c (Encodable.encode a) with _ | m
      · rw [hev] at hs; simp at hs
      · rw [hev] at hs
        have hdec : (Encodable.decode m : Option β) = some b := hs
        have hmem : m ∈ Nat.Partrec.Code.eval c (Encodable.encode a) :=
          Nat.Partrec.Code.evaln_complete.mpr ⟨s, Option.mem_def.mpr hev⟩
        rw [hevalr a] at hmem
        obtain ⟨x, hx, hxm⟩ := (Part.mem_map_iff _).mp hmem
        have hxb : x = b := by
          have hd2 : (Encodable.decode (Encodable.encode x) : Option β) = some b := by
            rw [hxm]; exact hdec
          rw [Encodable.encodek] at hd2
          exact Option.some_injective _ hd2
        rwa [← hxb]

/-- All bit strings of length at most `n`. -/
private def problemK_disj_le_imp_imp_singleton_search_strs : ℕ → List BitString
  | 0 => [[]]
  | n + 1 => [] :: (problemK_disj_le_imp_imp_singleton_search_strs n).flatMap
      (fun b => [false :: b, true :: b])

private theorem problemK_disj_le_imp_imp_singleton_search_mem_strs (n : ℕ)
    (s : BitString) :
    s ∈ problemK_disj_le_imp_imp_singleton_search_strs n ↔ s.length ≤ n := by
  induction n generalizing s with
  | zero =>
    simp only [problemK_disj_le_imp_imp_singleton_search_strs, List.mem_singleton,
      Nat.le_zero, List.length_eq_zero_iff]
  | succ n ih =>
    cases s with
    | nil => simp [problemK_disj_le_imp_imp_singleton_search_strs]
    | cons b t =>
      simp only [problemK_disj_le_imp_imp_singleton_search_strs, List.mem_cons,
        List.mem_flatMap, List.length_cons, Nat.add_le_add_iff_right]
      constructor
      · rintro (h | ⟨a, ha, h⟩)
        · exact absurd h (List.cons_ne_nil _ _)
        · have : t = a := by
            cases b <;> simp at h <;> simp [h]
          subst this
          exact (ih t).1 ha
      · intro h
        refine Or.inr ⟨t, (ih t).2 h, ?_⟩
        cases b <;> simp

private theorem problemK_disj_le_imp_imp_singleton_search_primrec_strs :
    Primrec problemK_disj_le_imp_imp_singleton_search_strs := by
  have h : Primrec (fun n : ℕ => Nat.rec (motive := fun _ => List BitString) [[]]
      (fun _ (q : List BitString) => [] :: q.flatMap (fun b => [false :: b, true :: b])) n) := by
    refine Primrec.nat_rec₁ [[]]
      (f := fun _ (q : List BitString) => [] :: q.flatMap (fun b => [false :: b, true :: b])) ?_
    refine Primrec.list_cons.comp (Primrec.const _) ?_
    refine Primrec.list_flatMap Primrec.snd ?_
    refine Primrec.list_cons.comp ?_ (Primrec.list_cons.comp ?_ (Primrec.const _))
    · exact Primrec.list_cons.comp (Primrec.const _) Primrec.snd
    · exact Primrec.list_cons.comp (Primrec.const _) Primrec.snd
  refine h.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih => simp only [problemK_disj_le_imp_imp_singleton_search_strs, ← ih]

/-- All pairs of bit strings of length at most `n`. -/
private def problemK_disj_le_imp_imp_singleton_search_pairs (n : ℕ) :
    List (BitString × BitString) :=
  (problemK_disj_le_imp_imp_singleton_search_strs n).flatMap fun a =>
    (problemK_disj_le_imp_imp_singleton_search_strs n).map fun b => (a, b)

private theorem problemK_disj_le_imp_imp_singleton_search_mem_pairs (n : ℕ)
    (q : BitString × BitString) :
    q ∈ problemK_disj_le_imp_imp_singleton_search_pairs n ↔
      q.1.length ≤ n ∧ q.2.length ≤ n := by
  obtain ⟨a, b⟩ := q
  simp only [problemK_disj_le_imp_imp_singleton_search_pairs, List.mem_flatMap,
    List.mem_map, Prod.mk.injEq, problemK_disj_le_imp_imp_singleton_search_mem_strs]
  constructor
  · rintro ⟨a', ha', b', hb', rfl, rfl⟩
    exact ⟨ha', hb'⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, rfl, rfl⟩

private theorem problemK_disj_le_imp_imp_singleton_search_primrec_pairs :
    Primrec problemK_disj_le_imp_imp_singleton_search_pairs := by
  have hs := problemK_disj_le_imp_imp_singleton_search_primrec_strs
  unfold problemK_disj_le_imp_imp_singleton_search_pairs
  refine Primrec.list_flatMap hs ?_
  refine Primrec.list_map (hs.comp Primrec.fst) ?_
  exact Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd

/-- The decidable test `ok_k` at time bound `k` for the candidate pair `uv`. -/
private def problemK_disj_le_imp_imp_singleton_search_okf
    (ℓ : BitString → BitString → BitString → BitString → BitString)
    (E : BitString × BitString → ℕ → Option BitString)
    (x : (BitString × ℕ) × ℕ) (uv : BitString × BitString) : Bool :=
  (problemK_disj_le_imp_imp_singleton_search_pairs x.1.2).foldr
    (fun wz s => (decide (wz.1 = uv.1) ||
      decide (E (x.1.1, ℓ uv.1 uv.2 wz.1 wz.2) x.2 = some uv.2)) && s) true

/-- The first candidate pair passing the test at time bound `k`. -/
private def problemK_disj_le_imp_imp_singleton_search_G
    (ℓ : BitString → BitString → BitString → BitString → BitString)
    (E : BitString × BitString → ℕ → Option BitString)
    (x : (BitString × ℕ) × ℕ) : Option (BitString × BitString) :=
  (problemK_disj_le_imp_imp_singleton_search_pairs x.1.2).foldr
    (fun uv acc => cond (problemK_disj_le_imp_imp_singleton_search_okf ℓ E x uv)
      (some uv) acc) none

private theorem problemK_disj_le_imp_imp_singleton_search_foldr_and {γ : Type}
    (l : List γ) (q : γ → Bool) :
    l.foldr (fun x s => q x && s) true = true ↔ ∀ x ∈ l, q x = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private theorem problemK_disj_le_imp_imp_singleton_search_foldr_cond {γ : Type}
    (l : List γ) (q : γ → Bool) :
    (∀ r, l.foldr (fun x acc => cond (q x) (some x) acc) none = some r →
      r ∈ l ∧ q r = true) ∧
    ((∃ x ∈ l, q x = true) → ∃ r, l.foldr (fun x acc => cond (q x) (some x) acc) none = some r) :=
        by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun r hr => ?_, fun ⟨x, hx, hqx⟩ => ?_⟩
    · cases hq : q a
      · simp only [List.foldr_cons, hq, Bool.cond_false] at hr
        obtain ⟨h1, h2⟩ := ih1 r hr
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩
      · simp only [List.foldr_cons, hq, Bool.cond_true, Option.some.injEq] at hr
        subst hr
        exact ⟨List.mem_cons_self, hq⟩
    · cases hq : q a
      · simp only [List.foldr_cons, hq, Bool.cond_false]
        apply ih2
        rcases List.mem_cons.1 hx with rfl | hx
        · rw [hq] at hqx; exact absurd hqx (by simp)
        · exact ⟨x, hx, hqx⟩
      · exact ⟨a, by simp [hq]⟩

private theorem problemK_disj_le_imp_imp_singleton_search_exists_bound {γ : Type}
    (l : List γ) (Q : γ → ℕ → Prop) (hmono : ∀ x s t, s ≤ t → Q x s → Q x t)
    (h : ∀ x ∈ l, ∃ s, Q x s) : ∃ K, ∀ x ∈ l, Q x K := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a l ih =>
    obtain ⟨K1, hK1⟩ := h a List.mem_cons_self
    obtain ⟨K2, hK2⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨max K1 K2, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hmono _ _ _ (le_max_left _ _) hK1
    · exact hmono _ _ _ (le_max_right _ _) (hK2 x hx)

private theorem problemK_disj_le_imp_imp_singleton_search_computable_G
    (ℓ : BitString → BitString → BitString → BitString → BitString)
    (hℓ : Computable (fun q : (BitString × BitString) × (BitString × BitString) =>
        ℓ q.1.1 q.1.2 q.2.1 q.2.2))
    (E : BitString × BitString → ℕ → Option BitString) (hE : Computable₂ E) :
    Computable (problemK_disj_le_imp_imp_singleton_search_G ℓ E) := by
  have hpairs := problemK_disj_le_imp_imp_singleton_search_primrec_pairs.to_comp
  have hokf : Computable₂ (problemK_disj_le_imp_imp_singleton_search_okf ℓ E) := by
    have hwz : Computable (fun q : (((BitString × ℕ) × ℕ) × (BitString × BitString)) ×
        ((BitString × BitString) × Bool) => q.2.1) := Computable.fst.comp Computable.snd
    have hs : Computable (fun q : (((BitString × ℕ) × ℕ) × (BitString × BitString)) ×
        ((BitString × BitString) × Bool) => q.2.2) := Computable.snd.comp Computable.snd
    have hu : Computable (fun q : (((BitString × ℕ) × ℕ) × (BitString × BitString)) ×
        ((BitString × BitString) × Bool) => q.1.2.1) :=
      Computable.fst.comp (Computable.snd.comp Computable.fst)
    have hv : Computable (fun q : (((BitString × ℕ) × ℕ) × (BitString × BitString)) ×
        ((BitString × BitString) × Bool) => q.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    have hk : Computable (fun q : (((BitString × ℕ) × ℕ) × (BitString × BitString)) ×
        ((BitString × BitString) × Bool) => q.1.1.2) :=
      Computable.snd.comp (Computable.fst.comp Computable.fst)
    have hp : Computable (fun q : (((BitString × ℕ) × ℕ) × (BitString × BitString)) ×
        ((BitString × BitString) × Bool) => q.1.1.1.1) :=
      Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
    have hw := Computable.fst.comp hwz
    have hz := Computable.snd.comp hwz
    have hℓq := hℓ.comp ((hu.pair hv).pair (hw.pair hz))
    have hEq := hE.comp (hp.pair hℓq) hk
    have h1 := (Primrec.eq (α := BitString)).decide.to_comp.comp hw hu
    have h2 := (Primrec.eq (α := Option BitString)).decide.to_comp.comp hEq
      (Computable.option_some.comp hv)
    have h3 := Primrec.or.to_comp.comp h1 h2
    have hh := Primrec.and.to_comp.comp h3 hs
    exact Computable.list_foldr
      (l := fun y : ((BitString × ℕ) × ℕ) × (BitString × BitString) =>
        problemK_disj_le_imp_imp_singleton_search_pairs y.1.1.2)
      (g := fun _ => true)
      (h := fun y z => (decide (z.1.1 = y.2.1) ||
        decide (E (y.1.1.1, ℓ y.2.1 y.2.2 z.1.1 z.1.2) y.1.2 = some y.2.2)) && z.2)
      (hpairs.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))
      (Computable.const true) hh
  have hGh : Computable₂ (fun (x : (BitString × ℕ) × ℕ) (z : (BitString × BitString) ×
      Option (BitString × BitString)) =>
      cond (problemK_disj_le_imp_imp_singleton_search_okf ℓ E x z.1) (some z.1) z.2) := by
    refine Computable.cond ?_ (Computable.option_some.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
    exact hokf.comp Computable.fst (Computable.fst.comp Computable.snd)
  exact Computable.list_foldr
    (l := fun x : (BitString × ℕ) × ℕ =>
      problemK_disj_le_imp_imp_singleton_search_pairs x.1.2)
    (g := fun _ => none)
    (h := fun x z => cond (problemK_disj_le_imp_imp_singleton_search_okf ℓ E x z.1)
      (some z.1) z.2)
    (hpairs.comp (Computable.snd.comp Computable.fst)) (Computable.const none) hGh

/-- Step 2 of the proof of `problemK_disj_le_imp_imp_singleton`: compatible pairs
can be found effectively.  For a computable `ℓ`, there is a partial computable `F (p, n)` such
that every value of `F (p, n)` is a pair compatible with `p` at level `n`, and `F (p, n)` is
defined as soon as some compatible pair exists.  (Proof: compatibility of `(u, v)` is
semi-decidable, as a finite conjunction over `w, z` of length at most `n` of the halting of
`[p](ℓ u v w z)` with the right value; search in parallel over the finitely many `(u, v)` and over
the running time, e.g. with `Nat.Partrec.Code.evaln`, `Nat.rfind`.) -/
private theorem problemK_disj_le_imp_imp_singleton_search
    (P : ProblemCalculus) (hP : P.Admissible)
    (ℓ : BitString → BitString → BitString → BitString → BitString)
    (hℓ : Computable (fun q : (BitString × BitString) × (BitString × BitString) =>
        ℓ q.1.1 q.1.2 q.2.1 q.2.2)) :
    ∃ F : BitString × ℕ →. BitString × BitString, Partrec F ∧
      (∀ p n, ∀ r ∈ F (p, n),
        problemK_disj_le_imp_imp_singleton_Compat P ℓ n p r.1 r.2) ∧
      (∀ p n u v, problemK_disj_le_imp_imp_singleton_Compat P ℓ n p u v → (F (p, n)).Dom) := by
  obtain ⟨-, -, -, -, -, hgodel⟩ := hP
  obtain ⟨E, hEc, hEmono, hE⟩ :=
    problemK_disj_le_imp_imp_singleton_search_stepEval hgodel.1
  have hG := problemK_disj_le_imp_imp_singleton_search_computable_G ℓ hℓ E hEc
  refine ⟨fun a => Nat.rfindOpt (fun k =>
    problemK_disj_le_imp_imp_singleton_search_G ℓ E (a, k)), ?_, ?_, ?_⟩
  · exact Partrec.rfindOpt (f := fun a k =>
      problemK_disj_le_imp_imp_singleton_search_G ℓ E (a, k)) hG
  · intro p n r hr
    obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hr
    have hk' : problemK_disj_le_imp_imp_singleton_search_G ℓ E ((p, n), k) = some r :=
      hk
    obtain ⟨hmem, hok⟩ :=
      (problemK_disj_le_imp_imp_singleton_search_foldr_cond _ _).1 r hk'
    obtain ⟨hr1, hr2⟩ :=
      (problemK_disj_le_imp_imp_singleton_search_mem_pairs n r).1 hmem
    refine ⟨hr1, hr2, fun w z hw hz hwu => ?_⟩
    have hall := (problemK_disj_le_imp_imp_singleton_search_foldr_and _ _).1 hok (w, z)
      ((problemK_disj_le_imp_imp_singleton_search_mem_pairs n (w, z)).2 ⟨hw, hz⟩)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hall
    rcases hall with h | h
    · exact absurd h hwu
    · exact (hE _ _).2 ⟨k, h⟩
  · intro p n u v ⟨hu, hv, hc⟩
    have hbound := problemK_disj_le_imp_imp_singleton_search_exists_bound
      (problemK_disj_le_imp_imp_singleton_search_pairs n)
      (fun wz s => wz.1 ≠ u → E (p, ℓ u v wz.1 wz.2) s = some v)
      (fun wz s t hst h hne => hEmono _ _ _ _ hst (h hne)) (by
        intro wz hwz
        obtain ⟨hw, hz⟩ := (problemK_disj_le_imp_imp_singleton_search_mem_pairs n wz).1 hwz
        by_cases hne : wz.1 = u
        · exact ⟨0, fun h => absurd hne h⟩
        · obtain ⟨s, hs⟩ := (hE _ _).1 (hc wz.1 wz.2 hw hz hne)
          exact ⟨s, fun _ => hs⟩)
    obtain ⟨K, hK⟩ := hbound
    have hok : problemK_disj_le_imp_imp_singleton_search_okf ℓ E ((p, n), K) (u, v) =
        true := by
      unfold problemK_disj_le_imp_imp_singleton_search_okf
      refine (problemK_disj_le_imp_imp_singleton_search_foldr_and _ _).2 ?_
      intro wz hwz
      by_cases hne : wz.1 = u
      · simp [hne]
      · simp [hK wz hwz hne]
    have huv : (u, v) ∈ problemK_disj_le_imp_imp_singleton_search_pairs n :=
      (problemK_disj_le_imp_imp_singleton_search_mem_pairs n (u, v)).2 ⟨hu, hv⟩
    obtain ⟨r, hr⟩ := (problemK_disj_le_imp_imp_singleton_search_foldr_cond
      (problemK_disj_le_imp_imp_singleton_search_pairs n) _).2 ⟨(u, v), huv, hok⟩
    change (Nat.rfindOpt _).Dom
    rw [Nat.rfindOpt_dom]
    exact ⟨K, r, hr⟩

/-- SUV Theorem 240 (Section 13.3, printed p. 406), second inequality.
`C(x ∨ y) ≤ C((x → y) → y) + O(log n)` for strings of length at most `n`.  Book's algorithm (2):
call `(u, v) ∈ S × S` compatible with a solution `p` if `[p](l_τ) = v` for all `τ` with
`τ(u) = v`; `(x, y)` is compatible, and two compatible pairs agree in the first or in the second
coordinate.  For the first compatible pair `(u, v)`, `u = x` or `v = y`; one advice bit says
which, and the output is `[0, u]` or `[1, v]` (`problemK_le_of_partrec_advice`). -/
theorem problemK_disj_le_imp_imp_singleton (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y : BitString), x.length ≤ n → y.length ≤ n →
      problemK D (P.disj {x} {y}) ≤
        problemK D (P.imp (P.imp {x} {y}) {y}) + (logSlack k n : ℕ∞) := by
  obtain ⟨ℓ, hℓc, hℓsym, hℓmem⟩ := problemK_disj_le_imp_imp_singleton_programs P hP
  obtain ⟨F, hF, hFsound, hFdom⟩ := problemK_disj_le_imp_imp_singleton_search P hP ℓ hℓc
  obtain ⟨hpair, -, -, -, -, -⟩ := hP
  let f : BitString × (ℕ × Bool) →. BitString := fun q =>
    (F (q.1, q.2.1)).map (fun r => cond q.2.2 (P.pair P.tag1 r.2) (P.pair P.tag0 r.1))
  have hf : Partrec f := by
    have hg : Computable (fun a : (BitString × (ℕ × Bool)) × (BitString × BitString) =>
        cond a.1.2.2 (P.pair P.tag1 a.2.2) (P.pair P.tag0 a.2.1)) := by
      refine Computable.cond (Computable.snd.comp (Computable.snd.comp Computable.fst)) ?_ ?_
      · exact hpair.comp (Computable.const _) (Computable.snd.comp Computable.snd)
      · exact hpair.comp (Computable.const _) (Computable.fst.comp Computable.snd)
    exact Partrec.map (hF.comp (Computable.fst.pair
      (Computable.fst.comp Computable.snd))) hg.to₂
  obtain ⟨c, hc⟩ := problemK_le_of_partrec_advice D hD f hf
  refine ⟨c, fun n x y hx hy => hc _ _ n ?_⟩
  intro p hp
  have hcompat : problemK_disj_le_imp_imp_singleton_Compat P ℓ n p x y := by
    refine ⟨hx, hy, fun w z _ _ hwx => ?_⟩
    obtain ⟨y', hy', hmem⟩ := hp (ℓ x y w z) (fun x' hx' => ⟨y, Set.mem_singleton y, by
      rw [Set.mem_singleton_iff] at hx'
      subst hx'
      exact hℓmem x' y w z (Ne.symm hwx)⟩)
    rw [Set.mem_singleton_iff] at hy'
    subst hy'
    exact hmem
  obtain ⟨r, hr⟩ := Part.dom_iff_mem.1 (hFdom p n x y hcompat)
  obtain ⟨hru, hrv, hrc⟩ := hFsound p n r hr
  have hxy : r.1 = x ∨ r.2 = y := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have e1 := hrc x y hx hy (Ne.symm h1)
    obtain ⟨-, -, hxc⟩ := hcompat
    have e2 := hxc r.1 r.2 hru hrv h1
    rw [hℓsym x y r.1 r.2 (Ne.symm h1)] at e2
    exact h2 (Part.mem_unique e1 e2)
  rcases hxy with h | h
  · refine ⟨false, P.pair P.tag0 x, Or.inl ⟨x, Set.mem_singleton x, rfl⟩, ?_⟩
    exact Part.mem_map_iff _ |>.2 ⟨r, hr, by simp [h]⟩
  · refine ⟨true, P.pair P.tag1 y, Or.inr ⟨y, Set.mem_singleton y, rfl⟩, ?_⟩
    exact Part.mem_map_iff _ |>.2 ⟨r, hr, by simp [h]⟩

/-- SUV Theorem 241 (Section 13.3, printed p. 407), first inequality.  The complexity of
`(x → y) → z` is at most that of `z ∨ (x ∧ (y → z))` up to `O(log n)` for strings of length at
most `n` (the proof gives `O(1)`).  Book: `z` becomes the constant program; `[x, q]` with `q`
converting `y` to `z` becomes "apply the given solution of `x → y` to `x`, then `q`".  (By
Problem 335 the latter complexity is `min (C(z), C(x) + C(z | x, y))`.) -/
theorem problemK_imp_imp_le_disj_conj_imp (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y z : BitString), x.length ≤ n → y.length ≤ n → z.length ≤ n →
      problemK D (P.imp (P.imp {x} {y}) {z}) ≤
        problemK D (P.disj {z} (P.conj {x} (P.imp {y} {z}))) + (logSlack k n : ℕ∞) := by
  obtain ⟨-, hunpair, hinv, -, -, hL, hG⟩ := hP
  have hfst : Computable (fun z : BitString => ((P.unpair z).map Prod.fst).getD []) :=
    Computable.option_getD
      (Computable.option_map hunpair (Computable.fst.comp Computable.snd).to₂)
      (Computable.const [])
  have hsnd : Computable (fun z : BitString => ((P.unpair z).map Prod.snd).getD []) :=
    Computable.option_getD
      (Computable.option_map hunpair (Computable.snd.comp Computable.snd).to₂)
      (Computable.const [])
  -- `t0 [0, z]` prints `z`; `t1 [1, [x, q]]` applies its input to `x`, then `q`
  obtain ⟨t0, ht0, hts0⟩ :=
    hG (fun r => Part.some (((P.unpair r.1).map Prod.snd).getD []))
      (hsnd.comp Computable.fst).partrec
  obtain ⟨t1, ht1, hts1⟩ :=
    hG (fun r => (P.lang (r.2, ((P.unpair (((P.unpair r.1).map Prod.snd).getD [])).map
        Prod.fst).getD [])).bind (fun b => P.lang ((((P.unpair (((P.unpair r.1).map
        Prod.snd).getD [])).map Prod.snd).getD []), b)))
      (Partrec.bind (hL.comp (Computable.snd.pair (hfst.comp (hsnd.comp Computable.fst))))
        (hL.comp ((hsnd.comp (hsnd.comp (Computable.fst.comp Computable.fst))).pair
          Computable.snd)).to₂)
  obtain ⟨c0, hc0⟩ := plainK_map_le D hD t0 ht0
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD t1 ht1
  refine ⟨max c0 c1, fun n x y z _ _ _ => ?_⟩
  have hne : (P.disj {z} (P.conj {x} (P.imp {y} {z}))).Nonempty :=
    ⟨P.pair P.tag0 z, Or.inl ⟨z, Set.mem_singleton z, rfl⟩⟩
  obtain ⟨s, hs, hseq⟩ := exists_mem_plainK_eq_problemK D hne
  rw [← hseq]
  rcases hs with ⟨z', hz', rfl⟩ | ⟨c, ⟨a, ha, q, hq, rfl⟩, rfl⟩
  · rw [Set.mem_singleton_iff] at hz'
    subst hz'
    have hmem : t0 (P.pair P.tag0 z') ∈ P.imp (P.imp {x} {y}) {z'} := by
      intro w _
      refine ⟨z', Set.mem_singleton z', ?_⟩
      rw [hts0]
      simp [hinv]
    calc _ ≤ plainK D (t0 (P.pair P.tag0 z')) := problemK_le_of_mem D hmem
      _ ≤ plainK D (P.pair P.tag0 z') + c0 := hc0 _
      _ ≤ plainK D (P.pair P.tag0 z') + (logSlack (max c0 c1) n : ℕ∞) := by
          gcongr
          exact (le_max_left c0 c1).trans (Nat.le_add_left _ _)
  · rw [Set.mem_singleton_iff] at ha
    subst ha
    have hmem : t1 (P.pair P.tag1 (P.pair a q)) ∈ P.imp (P.imp {a} {y}) {z} := by
      intro w hw
      obtain ⟨y', hy', hwy⟩ := hw a (Set.mem_singleton a)
      rw [Set.mem_singleton_iff] at hy'
      subst hy'
      obtain ⟨z', hz', hqz⟩ := hq y' (Set.mem_singleton y')
      refine ⟨z', hz', ?_⟩
      rw [hts1]
      simp only [hinv, Option.map_some, Option.getD_some]
      exact Part.mem_bind_iff.2 ⟨y', hwy, hqz⟩
    calc _ ≤ plainK D (t1 (P.pair P.tag1 (P.pair a q))) := problemK_le_of_mem D hmem
      _ ≤ plainK D (P.pair P.tag1 (P.pair a q)) + c1 := hc1 _
      _ ≤ plainK D (P.pair P.tag1 (P.pair a q)) + (logSlack (max c0 c1) n : ℕ∞) := by
          gcongr
          exact (le_max_right c0 c1).trans (Nat.le_add_left _ _)

/-- Compatibility of the triple `(u, v, w)` with a program `p` at level `n` (SUV printed p. 407),
relative to a choice `ltau n τ` of a program computing `τ` on the strings of length at most `n`:
`[p](l_τ) = w` for every `τ` mapping the strings of length `≤ n` to such strings with
`τ(u) = v`. -/
private def problemK_disj_conj_imp_le_imp_imp_Compat (P : ProblemCalculus)
    (ltau : ℕ → (BitString → BitString) → BitString) (p : BitString) (n : ℕ)
    (u v w : BitString) : Prop :=
  ∀ τ : BitString → BitString, (∀ s, s.length ≤ n → (τ s).length ≤ n) → τ u = v →
    w ∈ P.lang (p, ltau n τ)

/-- Computability of a finite conjunction `(f a).all (p a)` over a computable list. -/
private lemma problemK_disj_conj_imp_le_imp_imp_search_aux_list_all {α β : Type}
    [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Computable f) (hp : Computable₂ p) :
    Computable (fun a => (f a).all (p a)) := by
  have hstep : Computable₂ (fun (a : α) (q : ℕ × Bool) =>
      q.2 && (((f a)[q.1]?).map (p a)).getD true) := by
    have hget : Computable (fun r : α × (ℕ × Bool) => (f r.1)[r.2.1]?) :=
      Computable.list_getElem?.comp (hf.comp Computable.fst)
        (Computable.fst.comp Computable.snd)
    have hmap : Computable (fun r : α × (ℕ × Bool) => ((f r.1)[r.2.1]?).map (p r.1)) :=
      Computable.option_map hget (hp.comp (Computable.fst.comp Computable.fst) Computable.snd)
    have hgd : Computable (fun r : α × (ℕ × Bool) => (((f r.1)[r.2.1]?).map (p r.1)).getD true) :=
      Computable.option_getD hmap (Computable.const true)
    exact (Primrec.and.to_comp).comp (Computable.snd.comp Computable.snd) hgd
  have hrec := Computable.nat_rec (f := fun a => (f a).length) (g := fun _ => true)
    (h := fun a q => q.2 && (((f a)[q.1]?).map (p a)).getD true)
    (Computable.list_length.comp hf) (Computable.const true) hstep
  refine hrec.of_eq (fun a => ?_)
  have key : ∀ k, Nat.rec (motive := fun _ => Bool) true
      (fun y IH => IH && (((f a)[y]?).map (p a)).getD true) k = ((f a).take k).all (p a) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [ih, List.take_add_one, List.all_append]
      cases h : (f a)[k]? <;> simp
  have := key (f a).length
  simpa using this

/-- The table of `τ` on the strings of length `≤ n`, as a list of pairs. -/
private def problemK_disj_conj_imp_le_imp_imp_search_aux_mk (n : ℕ)
    (τ : BitString → BitString) : List (BitString × BitString) :=
  (boundedPrograms n).map (fun s => (s, τ s))

/-- Lookup in a table (the first matching key). -/
private def problemK_disj_conj_imp_le_imp_imp_search_aux_lk
    (T : List (BitString × BitString)) (s : BitString) : Option BitString :=
  T.foldr (fun e acc => bif decide (e.1 = s) then some e.2 else acc) none

private lemma problemK_disj_conj_imp_le_imp_imp_search_aux_lk_map
    (τ : BitString → BitString) (ss : List BitString) (s : BitString)
    (hs : s ∈ ss) :
    problemK_disj_conj_imp_le_imp_imp_search_aux_lk (ss.map (fun s => (s, τ s))) s =
      some (τ s) := by
  induction ss with
  | nil => simp at hs
  | cons a rest ih =>
    by_cases h : a = s
    · subst h; simp [problemK_disj_conj_imp_le_imp_imp_search_aux_lk]
    · have hs' : s ∈ rest := by
        rcases List.mem_cons.1 hs with h' | h'
        · exact absurd h'.symm h
        · exact h'
      have h' : decide (a = s) = false := by simpa using h
      simp only [problemK_disj_conj_imp_le_imp_imp_search_aux_lk, List.map_cons,
        List.foldr_cons, h', Bool.cond_false]
      exact ih hs'

/-- The language `V (c, s)`: decode `c` as a table and look `s` up in it. -/
private def problemK_disj_conj_imp_le_imp_imp_search_aux_V : Map := fun q =>
  Part.ofOption ((Encodable.decode (α := List (BitString × BitString)) (bitsToNat q.1)).bind
    (fun T => problemK_disj_conj_imp_le_imp_imp_search_aux_lk T q.2))

private lemma problemK_disj_conj_imp_le_imp_imp_search_aux_lk_primrec :
    Primrec₂ problemK_disj_conj_imp_le_imp_imp_search_aux_lk := by
  have hh : Primrec₂ (fun (x : List (BitString × BitString) × BitString)
      (y : (BitString × BitString) × Option BitString) =>
      bif decide (y.1.1 = x.2) then some y.1.2 else y.2) := by
    change Primrec (fun r : (List (BitString × BitString) × BitString) ×
        ((BitString × BitString) × Option BitString) =>
        bif decide (r.2.1.1 = r.1.2) then some r.2.1.2 else r.2.2)
    have hc : Primrec (fun r : (List (BitString × BitString) × BitString) ×
        ((BitString × BitString) × Option BitString) => decide (r.2.1.1 = r.1.2)) :=
      Primrec.eq.decide.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)
    have hs : Primrec (fun r : (List (BitString × BitString) × BitString) ×
        ((BitString × BitString) × Option BitString) => some r.2.1.2) :=
      Primrec.option_some.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    have ho : Primrec (fun r : (List (BitString × BitString) × BitString) ×
        ((BitString × BitString) × Option BitString) => r.2.2) :=
      Primrec.snd.comp Primrec.snd
    exact Primrec.cond hc hs ho
  exact Primrec.list_foldr (f := fun x : List (BitString × BitString) × BitString => x.1)
    (g := fun _ => (none : Option BitString)) Primrec.fst (Primrec.const none) hh

private lemma problemK_disj_conj_imp_le_imp_imp_search_aux_V_partrec :
    Partrec problemK_disj_conj_imp_le_imp_imp_search_aux_V := by
  have h : Computable (fun q : BitString × BitString =>
      (Encodable.decode (α := List (BitString × BitString)) (bitsToNat q.1)).bind
        (fun T => problemK_disj_conj_imp_le_imp_imp_search_aux_lk T q.2)) := by
    refine Computable.option_bind ?_ ?_
    · exact Computable.decode.comp (bitsToNat_computable.comp Computable.fst)
    · exact (problemK_disj_conj_imp_le_imp_imp_search_aux_lk_primrec.to_comp).comp
        Computable.snd (Computable.snd.comp Computable.fst)
  exact Computable.ofOption h

/-- All tables `ss → vals`: lists of pairs `(s, val)` with `val ∈ vals s`, one for each `s ∈ ss`. -/
private def problemK_disj_conj_imp_le_imp_imp_search_aux_tabs
    (vals : BitString → List BitString) (ss : List BitString) :
    List (List (BitString × BitString)) :=
  ss.foldr (fun s acc => (vals s).flatMap (fun val => acc.map (fun T => (s, val) :: T))) [[]]

/-- The tables of the maps from the strings of length `≤ n` to themselves with `u ↦ v`. -/
private def problemK_disj_conj_imp_le_imp_imp_search_aux_tables (n : ℕ) (u v : BitString) :
    List (List (BitString × BitString)) :=
  problemK_disj_conj_imp_le_imp_imp_search_aux_tabs
    (fun s => if s = u then [v] else boundedPrograms n) (boundedPrograms n)

private lemma problemK_disj_conj_imp_le_imp_imp_search_aux_tabs_mem_of
    (vals : BitString → List BitString) (τ : BitString → BitString)
    (ss : List BitString) (h : ∀ s ∈ ss, τ s ∈ vals s) :
    ss.map (fun s => (s, τ s)) ∈
      problemK_disj_conj_imp_le_imp_imp_search_aux_tabs vals ss := by
  induction ss with
  | nil => simp [problemK_disj_conj_imp_le_imp_imp_search_aux_tabs]
  | cons a rest ih =>
    simp only [problemK_disj_conj_imp_le_imp_imp_search_aux_tabs, List.foldr_cons,
      List.map_cons, List.mem_flatMap, List.mem_map]
    refine ⟨τ a, h a (List.mem_cons_self), ?_⟩
    exact ⟨_, ih (fun s hs => h s (List.mem_cons_of_mem _ hs)), rfl⟩

private lemma problemK_disj_conj_imp_le_imp_imp_search_aux_tabs_exists
    (vals : BitString → List BitString) (ss : List BitString)
    (hnd : ss.Nodup) (T : List (BitString × BitString))
    (hT : T ∈ problemK_disj_conj_imp_le_imp_imp_search_aux_tabs vals ss) :
    ∃ τ : BitString → BitString, ss.map (fun s => (s, τ s)) = T ∧ ∀ s ∈ ss, τ s ∈ vals s := by
  induction ss generalizing T with
  | nil =>
    simp only [problemK_disj_conj_imp_le_imp_imp_search_aux_tabs, List.foldr_nil,
      List.mem_singleton] at hT
    exact ⟨fun _ => [], by simp [hT], by simp⟩
  | cons a rest ih =>
    simp only [problemK_disj_conj_imp_le_imp_imp_search_aux_tabs, List.foldr_cons,
      List.mem_flatMap, List.mem_map] at hT
    obtain ⟨val, hval, T', hT', rfl⟩ := hT
    obtain ⟨hna, hnr⟩ := List.nodup_cons.1 hnd
    obtain ⟨τ', hτ'1, hτ'2⟩ := ih hnr T' hT'
    refine ⟨Function.update τ' a val, ?_, ?_⟩
    · simp only [List.map_cons, Function.update_self]
      congr 1
      rw [← hτ'1]
      refine List.map_congr_left (fun s hs => ?_)
      have : s ≠ a := fun h => hna (h ▸ hs)
      simp [Function.update_of_ne this]
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · simpa using hval
      · have : s ≠ a := fun h => hna (h ▸ hs)
        simpa [Function.update_of_ne this] using hτ'2 s hs

private lemma problemK_disj_conj_imp_le_imp_imp_search_aux_tables_primrec :
    Primrec (fun x : ℕ × BitString × BitString =>
      problemK_disj_conj_imp_le_imp_imp_search_aux_tables x.1 x.2.1 x.2.2) := by
  have hf : Primrec (fun r : (ℕ × BitString × BitString) × (BitString ×
      List (List (BitString × BitString))) =>
      (if r.2.1 = r.1.2.1 then [r.1.2.2] else boundedPrograms r.1.1)) := by
    have hc : PrimrecPred (fun r : (ℕ × BitString × BitString) × (BitString ×
        List (List (BitString × BitString))) => r.2.1 = r.1.2.1) :=
      Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    have h1 : Primrec (fun r : (ℕ × BitString × BitString) × (BitString ×
        List (List (BitString × BitString))) => [r.1.2.2]) :=
      Primrec.list_cons.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.const ([] : List BitString))
    have h2 : Primrec (fun r : (ℕ × BitString × BitString) × (BitString ×
        List (List (BitString × BitString))) => boundedPrograms r.1.1) :=
      primrec_boundedPrograms.comp (Primrec.fst.comp Primrec.fst)
    exact Primrec.ite hc h1 h2
  have hg : Primrec₂ (fun (r : (ℕ × BitString × BitString) × (BitString ×
      List (List (BitString × BitString)))) (val : BitString) =>
      r.2.2.map (fun T => (r.2.1, val) :: T)) := by
    have hl : Primrec (fun r : (ℕ × BitString × BitString) × (BitString ×
        List (List (BitString × BitString))) => r.2.2) :=
      Primrec.snd.comp Primrec.snd
    have hb : Primrec₂ (fun (r : ((ℕ × BitString × BitString) × (BitString ×
        List (List (BitString × BitString)))) × BitString)
        (T : List (BitString × BitString)) => (r.1.2.1, r.2) :: T) := by
      change Primrec (fun q : (((ℕ × BitString × BitString) × (BitString ×
        List (List (BitString × BitString)))) × BitString) × List (BitString × BitString) =>
        (q.1.1.2.1, q.1.2) :: q.2)
      exact Primrec.list_cons.comp
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp Primrec.fst)) Primrec.snd
    exact Primrec.list_map (hl.comp Primrec.fst) hb
  have hh : Primrec₂ (fun (x : ℕ × BitString × BitString) (y : BitString ×
      List (List (BitString × BitString))) =>
      (if y.1 = x.2.1 then [x.2.2] else boundedPrograms x.1).flatMap
        (fun val => y.2.map (fun T => (y.1, val) :: T))) :=
    Primrec.list_flatMap hf hg
  exact Primrec.list_foldr (f := fun x : ℕ × BitString × BitString => boundedPrograms x.1)
    (g := fun _ => ([[]] : List (List (BitString × BitString))))
    (primrec_boundedPrograms.comp Primrec.fst) (Primrec.const _) hh

private lemma problemK_disj_conj_imp_le_imp_imp_search_aux_exists_common {α : Type}
    (q : α → ℕ → Bool) (hmono : ∀ a s t, s ≤ t → q a s = true → q a t = true) (l : List α)
    (h : ∀ a ∈ l, ∃ s, q a s = true) : ∃ s, ∀ a ∈ l, q a s = true := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a rest ih =>
    obtain ⟨s1, hs1⟩ := h a List.mem_cons_self
    obtain ⟨s2, hs2⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨max s1 s2, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hmono _ _ _ (le_max_left _ _) hs1
    · exact hmono _ _ _ (le_max_right _ _) (hs2 b hb)

/-- Computability of the stage test of the search of
`problemK_disj_conj_imp_le_imp_imp_search`, uniformly in the components. -/
private lemma problemK_disj_conj_imp_le_imp_imp_search_aux_chk_computable {α : Type}
    [Primcodable α] (t : BitString → BitString) (ht : Computable t)
    (chk0 : (BitString × BitString) × BitString → ℕ → Bool) (hchk0 : Computable₂ chk0)
    {fp : α → BitString} {fn : α → ℕ} {fu fv fw : α → BitString} {fs : α → ℕ}
    (hp : Computable fp) (hn : Computable fn) (hu : Computable fu) (hv : Computable fv)
    (hw : Computable fw) (hs : Computable fs) :
    Computable (fun a : α =>
      decide ((fu a).length ≤ fn a) && decide ((fv a).length ≤ fn a) &&
        (problemK_disj_conj_imp_le_imp_imp_search_aux_tables (fn a) (fu a) (fv a)).all
          (fun T => chk0 ((fp a, t (Nat.bits (Encodable.encode T))), fw a) (fs a))) := by
  have hle : ∀ {f : α → BitString}, Computable f →
      Computable (fun a => decide ((f a).length ≤ fn a)) := by
    intro f hf
    exact (Primrec.nat_le.decide.to_comp).comp (Computable.list_length.comp hf) hn
  have htab : Computable (fun a : α =>
      problemK_disj_conj_imp_le_imp_imp_search_aux_tables (fn a) (fu a) (fv a)) :=
    (problemK_disj_conj_imp_le_imp_imp_search_aux_tables_primrec.to_comp).comp
      (hn.pair (hu.pair hv))
  have hT : Computable (fun r : α × List (BitString × BitString) =>
      t (Nat.bits (Encodable.encode r.2))) :=
    ht.comp ((primrec_natBits.to_comp).comp (Computable.encode.comp Computable.snd))
  have hall := problemK_disj_conj_imp_le_imp_imp_search_aux_list_all htab
    (p := fun a T => chk0 ((fp a, t (Nat.bits (Encodable.encode T))), fw a) (fs a))
    (hchk0.comp (((hp.comp Computable.fst).pair hT).pair (hw.comp Computable.fst))
      (hs.comp Computable.fst))
  exact (Primrec.and.to_comp).comp ((Primrec.and.to_comp).comp (hle hu) (hle hv)) hall

/-- Step 1 of the proof of `problemK_disj_conj_imp_le_imp_imp`: compatible triples
are enumerable from `p` and `n`.  There are a choice `ltau n τ` of a program computing `τ` on
the strings of length `≤ n` (from the Gödel property of `P.lang`: `ltau n τ` is the image, under
the computable translation of the Gödel property, of a code of the finite table of `τ` on the
strings of length `≤ n`) and a partial computable search `F (p, n)`, which dovetails over all
triples `(u, v, w)` of strings of length `≤ n` and checks, for each of the finitely many tables
`τ'` of maps from these strings to themselves with `τ'(u) = v`, that `[p](l_τ') = w`, such that:
every output of `F` is a compatible triple with `u`, `v` of length `≤ n`, and `F (p, n)` halts
whenever some triple of strings of length `≤ n` is compatible. -/
private theorem problemK_disj_conj_imp_le_imp_imp_search (P : ProblemCalculus)
    (hP : P.Admissible) :
    ∃ (ltau : ℕ → (BitString → BitString) → BitString)
      (F : BitString × ℕ →. BitString × BitString × BitString), Partrec F ∧
      (∀ n τ s, s.length ≤ n → τ s ∈ P.lang (ltau n τ, s)) ∧
      (∀ p n u v w, (u, v, w) ∈ F (p, n) → u.length ≤ n ∧ v.length ≤ n ∧
        problemK_disj_conj_imp_le_imp_imp_Compat P ltau p n u v w) ∧
      (∀ p n x y z, x.length ≤ n → y.length ≤ n → z.length ≤ n →
        problemK_disj_conj_imp_le_imp_imp_Compat P ltau p n x y z → (F (p, n)).Dom) := by
  obtain ⟨-, -, -, -, -, hL, hG⟩ := hP
  obtain ⟨t, ht, hts⟩ := hG _
    problemK_disj_conj_imp_le_imp_imp_search_aux_V_partrec
  obtain ⟨chk0, hchk0, hmono0, hiff0⟩ :=
    IsRE.exists_stageApprox (Partrec.graphIsRe P.lang hL)
  let ltau : ℕ → (BitString → BitString) → BitString := fun n τ =>
    t (Nat.bits (Encodable.encode
      (problemK_disj_conj_imp_le_imp_imp_search_aux_mk n τ)))
  have hltau : ∀ n τ s, s.length ≤ n → τ s ∈ P.lang (ltau n τ, s) := by
    intro n τ s hs
    have h1 : P.lang (ltau n τ, s) =
        problemK_disj_conj_imp_le_imp_imp_search_aux_V
          (Nat.bits (Encodable.encode
            (problemK_disj_conj_imp_le_imp_imp_search_aux_mk n τ)), s) := hts _ _
    have h2 := problemK_disj_conj_imp_le_imp_imp_search_aux_lk_map τ (boundedPrograms n) s
      ((mem_boundedPrograms_iff s n).2 hs)
    rw [h1]
    simp only [problemK_disj_conj_imp_le_imp_imp_search_aux_V, bitsToNat_bits,
      Encodable.encodek, Option.bind_some]
    rw [show problemK_disj_conj_imp_le_imp_imp_search_aux_lk
        (problemK_disj_conj_imp_le_imp_imp_search_aux_mk n τ) s = some (τ s) from h2]
    exact Part.mem_some _
  let chk : (BitString × ℕ) × (BitString × BitString × BitString) → ℕ → Bool := fun a s =>
    decide (a.2.1.length ≤ a.1.2) && decide (a.2.2.1.length ≤ a.1.2) &&
      (problemK_disj_conj_imp_le_imp_imp_search_aux_tables a.1.2 a.2.1 a.2.2.1).all
        (fun T => chk0 ((a.1.1, t (Nat.bits (Encodable.encode T))), a.2.2.2) s)
  have hchk : Computable₂ chk :=
    problemK_disj_conj_imp_le_imp_imp_search_aux_chk_computable t ht chk0 hchk0
      (fp := fun q : ((BitString × ℕ) × (BitString × BitString × BitString)) × ℕ => q.1.1.1)
      (fn := fun q => q.1.1.2) (fu := fun q => q.1.2.1) (fv := fun q => q.1.2.2.1)
      (fw := fun q => q.1.2.2.2) (fs := fun q => q.2)
      (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.snd.comp (Computable.fst.comp Computable.fst))
      (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
      Computable.snd
  let g : BitString × ℕ → ℕ → Option (BitString × BitString × BitString) := fun a m =>
    (Encodable.decode (α := BitString × BitString × BitString) m.unpair.1).bind
      (fun b => bif chk (a, b) m.unpair.2 then some b else none)
  have hg : Computable₂ g := by
    have h1 : Computable (fun z : (BitString × ℕ) × ℕ =>
        Encodable.decode (α := BitString × BitString × BitString) z.2.unpair.1) :=
      Computable.decode.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
    have h2 : Computable₂ (fun (z : (BitString × ℕ) × ℕ) (b : BitString × BitString × BitString) =>
        bif chk (z.1, b) z.2.unpair.2 then some b else none) := by
      refine Computable.cond (hchk.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)
        (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst))))
        (Computable.option_some.comp Computable.snd) (Computable.const none)
    exact (Computable.option_bind h1 h2).to₂
  have hiff : ∀ p n u v w, (∃ s, chk ((p, n), (u, v, w)) s = true) ↔
      (u.length ≤ n ∧ v.length ≤ n ∧
        ∀ T ∈ problemK_disj_conj_imp_le_imp_imp_search_aux_tables n u v,
          w ∈ P.lang (p, t (Nat.bits (Encodable.encode T)))) := by
    intro p n u v w
    constructor
    · rintro ⟨s, hs⟩
      simp only [chk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs
      obtain ⟨⟨hu, hv⟩, hall⟩ := hs
      exact ⟨hu, hv, fun T hT => (hiff0 ((p, t (Nat.bits (Encodable.encode T))), w)).2
        ⟨s, hall T hT⟩⟩
    · rintro ⟨hu, hv, hall⟩
      obtain ⟨s, hs⟩ := problemK_disj_conj_imp_le_imp_imp_search_aux_exists_common
        (fun T s => chk0 ((p, t (Nat.bits (Encodable.encode T))), w) s)
        (fun T s s' hss' => hmono0 _ _ _ hss')
        (problemK_disj_conj_imp_le_imp_imp_search_aux_tables n u v)
        (fun T hT => (hiff0 ((p, t (Nat.bits (Encodable.encode T))), w)).1 (hall T hT))
      refine ⟨s, ?_⟩
      simp only [chk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      exact ⟨⟨hu, hv⟩, hs⟩
  refine ⟨ltau, fun a => Nat.rfindOpt (g a), Partrec.rfindOpt hg, hltau, ?_, ?_⟩
  · intro p n u v w hr
    obtain ⟨m, hm⟩ := Nat.rfindOpt_spec hr
    simp only [g, Option.mem_def, Option.bind_eq_some_iff] at hm
    obtain ⟨b', hb', hc⟩ := hm
    cases hck : chk ((p, n), b') m.unpair.2
    · simp [hck] at hc
    · simp only [hck, Bool.cond_true, Option.some.injEq] at hc
      subst hc
      obtain ⟨hu, hv, hall⟩ := (hiff p n u v w).1 ⟨_, hck⟩
      refine ⟨hu, hv, ?_⟩
      intro τ hτ huv
      refine hall _ ?_
      refine problemK_disj_conj_imp_le_imp_imp_search_aux_tabs_mem_of
        (fun s => if s = u then [v] else boundedPrograms n) τ (boundedPrograms n) ?_
      intro s hs
      by_cases hsu : s = u
      · subst hsu; simp [huv]
      · simp only [hsu, ite_false]
        exact (mem_boundedPrograms_iff _ _).2 (hτ s ((mem_boundedPrograms_iff _ _).1 hs))
  · intro p n x y z hx hy hz hcomp
    have hex : ∃ s, chk ((p, n), (x, y, z)) s = true := by
      refine (hiff p n x y z).2 ⟨hx, hy, ?_⟩
      intro T hT
      obtain ⟨τ, hτT, hτv⟩ :=
        problemK_disj_conj_imp_le_imp_imp_search_aux_tabs_exists
          (fun s => if s = x then [y] else boundedPrograms n) (boundedPrograms n)
          (boundedPrograms_nodup n) T hT
      have hxτ : τ x = y := by
        have := hτv x ((mem_boundedPrograms_iff _ _).2 hx)
        simpa using this
      have hτ : ∀ s, s.length ≤ n → (τ s).length ≤ n := by
        intro s hs
        have := hτv s ((mem_boundedPrograms_iff _ _).2 hs)
        by_cases hsx : s = x
        · subst hsx
          simp only [ite_true, List.mem_singleton] at this
          rw [this]; exact hy
        · simp only [hsx, ite_false] at this
          exact (mem_boundedPrograms_iff _ _).1 this
      have := hcomp τ hτ hxτ
      rw [← hτT]
      exact this
    obtain ⟨s, hs⟩ := hex
    refine Nat.rfindOpt_dom.2 ⟨Nat.pair (Encodable.encode (x, y, z)) s, (x, y, z), ?_⟩
    simp [g, hs]

/-- Step 2 of the proof of `problemK_disj_conj_imp_le_imp_imp`: if `p` solves
`(x → y) → z`, then `(x, y, z)` is compatible with `p` (for `l_τ` with `τ(x) = y` solves
`x → y`). -/
private theorem problemK_disj_conj_imp_le_imp_imp_compat (P : ProblemCalculus)
    (ltau : ℕ → (BitString → BitString) → BitString)
    (hltau : ∀ n τ s, s.length ≤ n → τ s ∈ P.lang (ltau n τ, s))
    (p : BitString) (n : ℕ) (x y z : BitString) (x_len : x.length ≤ n)
    (hp : p ∈ P.imp (P.imp {x} {y}) {z}) :
    problemK_disj_conj_imp_le_imp_imp_Compat P ltau p n x y z := by
  intro τ hτ hτx
  have hq : ltau n τ ∈ P.imp {x} {y} := by
    intro x' hx'
    rw [Set.mem_singleton_iff] at hx'
    subst hx'
    exact ⟨τ x', by simp [hτx], hltau n τ x' x_len⟩
  obtain ⟨z', hz', hz'm⟩ := hp _ hq
  rw [Set.mem_singleton_iff] at hz'
  subst hz'
  exact hz'm

/-- Step 3 of the proof of `problemK_disj_conj_imp_le_imp_imp`: two compatible
triples agree in the third coordinate or in the first one (otherwise the map `τ` with
`τ(x) = y`, `τ(u) = v` gives `w = z`). -/
private theorem problemK_disj_conj_imp_le_imp_imp_agree (P : ProblemCalculus)
    (ltau : ℕ → (BitString → BitString) → BitString) (p : BitString) (n : ℕ)
    (x y z u v w : BitString) (hy : y.length ≤ n) (hv : v.length ≤ n)
    (h1 : problemK_disj_conj_imp_le_imp_imp_Compat P ltau p n x y z)
    (h2 : problemK_disj_conj_imp_le_imp_imp_Compat P ltau p n u v w) :
    w = z ∨ u = x := by
  by_cases hux : u = x
  · exact Or.inr hux
  refine Or.inl ?_
  classical
  let τ : BitString → BitString := fun s => if s = x then y else if s = u then v else s
  have hτ : ∀ s, s.length ≤ n → (τ s).length ≤ n := by
    intro s hs
    simp only [τ]
    split_ifs <;> assumption
  have hτx : τ x = y := by simp [τ]
  have hτu : τ u = v := by simp [τ, hux]
  exact Part.mem_unique (h2 τ hτ hτu) (h1 τ hτ hτx)

/-- SUV Theorem 241 (Section 13.3, printed p. 407), second inequality.
`C(z ∨ (x ∧ (y → z))) ≤ C((x → y) → z) + O(log n)` for strings of length at most `n`.  Book:
triples `(u, v, w) ∈ S³` compatible with `p` (`[p](l_τ) = w` whenever `τ(u) = v`); `(x, y, z)`
is compatible.  For the first compatible triple, either `w = z` (advice bit 0: output `[0, w]`),
or `u = x` (otherwise a `τ` with `τ(x) = y`, `τ(u) = v` gives `w = z`) and the program
`y' ↦ [p](const y')` solves `y → z`, since the constant program `const y` solves `x → y` (advice
bit 1: output `[1, [u, that program]]`, computed from `p` by the Gödel property). -/
theorem problemK_disj_conj_imp_le_imp_imp (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y z : BitString), x.length ≤ n → y.length ≤ n → z.length ≤ n →
      problemK D (P.disj {z} (P.conj {x} (P.imp {y} {z}))) ≤
        problemK D (P.imp (P.imp {x} {y}) {z}) + (logSlack k n : ℕ∞) := by
  obtain ⟨ltau, F, hF, hltau, hFsound, hFdom⟩ :=
    problemK_disj_conj_imp_le_imp_imp_search P hP
  obtain ⟨hpair, hunpair, hinv, -, -, hL, hG⟩ := hP
  -- `c s` is the constant program `s`; `t2 p` is the program `y' ↦ [p](const y')`
  obtain ⟨c, hc, hcs⟩ := hG (fun q => Part.some q.1) Computable.fst.partrec
  obtain ⟨t2, ht2, hts2⟩ := hG (fun q => P.lang (q.1, c q.2))
    (hL.comp (Computable.fst.pair (hc.comp Computable.snd)))
  let f : BitString × (ℕ × Bool) →. BitString := fun a =>
    (F (a.1, a.2.1)).bind (fun r => Part.some (cond a.2.2
      (P.pair P.tag1 (P.pair r.1 (t2 a.1))) (P.pair P.tag0 r.2.2)))
  have hf : Partrec f := by
    have ha : Computable (fun q : (BitString × (ℕ × Bool)) × (BitString × BitString × BitString) =>
        q.1) := Computable.fst
    have hr : Computable (fun q : (BitString × (ℕ × Bool)) × (BitString × BitString × BitString) =>
        q.2) := Computable.snd
    have h0 : Computable (fun q : (BitString × (ℕ × Bool)) × (BitString × BitString × BitString) =>
        P.pair P.tag0 q.2.2.2) :=
      hpair.comp (Computable.const _) (Computable.snd.comp (Computable.snd.comp hr))
    have h1 : Computable (fun q : (BitString × (ℕ × Bool)) × (BitString × BitString × BitString) =>
        P.pair P.tag1 (P.pair q.2.1 (t2 q.1.1))) :=
      hpair.comp (Computable.const _) (hpair.comp (Computable.fst.comp hr)
        (ht2.comp (Computable.fst.comp ha)))
    have hb : Computable (fun q : (BitString × (ℕ × Bool)) × (BitString × BitString × BitString) =>
        q.1.2.2) := Computable.snd.comp (Computable.snd.comp ha)
    exact Partrec.bind (hF.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))
      (Computable.partrec (Computable.cond hb h1 h0)).to₂
  obtain ⟨k, hk⟩ := problemK_le_of_partrec_advice D hD f hf
  refine ⟨k, fun n x y z hx hy hz => hk _ _ n ?_⟩
  intro p hp
  have hcomp := problemK_disj_conj_imp_le_imp_imp_compat P ltau hltau p n x y z hx hp
  obtain ⟨⟨u, v, w⟩, hr⟩ := Part.dom_iff_mem.1 (hFdom p n x y z hx hy hz hcomp)
  obtain ⟨hu, hv, hcomp'⟩ := hFsound p n u v w hr
  rcases problemK_disj_conj_imp_le_imp_imp_agree P ltau p n x y z u v w hy hv hcomp
    hcomp' with rfl | rfl
  · refine ⟨false, P.pair P.tag0 w, Or.inl ⟨w, Set.mem_singleton w, rfl⟩, ?_⟩
    exact Part.mem_bind_iff.2 ⟨(u, v, w), hr, by simp⟩
  · refine ⟨true, P.pair P.tag1 (P.pair u (t2 p)),
      Or.inr ⟨P.pair u (t2 p), ⟨u, Set.mem_singleton u, t2 p, ?_, rfl⟩, rfl⟩, ?_⟩
    · intro y' hy'
      rw [Set.mem_singleton_iff] at hy'
      subst hy'
      have hq : c y' ∈ P.imp {u} {y'} := by
        intro x' hx'
        rw [Set.mem_singleton_iff] at hx'
        subst hx'
        exact ⟨y', Set.mem_singleton y', by rw [hcs]; exact Part.mem_some _⟩
      obtain ⟨z', hz', hz'm⟩ := hp _ hq
      exact ⟨z', hz', by rw [hts2]; exact hz'm⟩
    · exact Part.mem_bind_iff.2 ⟨(u, v, w), hr, by simp⟩

end InformationLogic
end Kolmogorov
