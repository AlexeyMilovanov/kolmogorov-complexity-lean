import KolmogorovMathlib.InformationLogic.Formulas
import KolmogorovMathlib.InformationLogic.OperationsComplexity
import KolmogorovMathlib.InformationLogic.OperationsProblems
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools

/-!
# Implication Upper Bound

This module treats the complexity of the problem `((x → y) → y) → (x ∨ y)` in the calculus of
problems, formalizing Theorem 242 of Section 13.4 of Shen, Uspensky and Vereshchagin,
"Kolmogorov complexity and algorithmic randomness".

## Main declarations

* `exists_partrec_diagonal`: a partial computable diagonal function `ℕ →. Fin k`, which for
  `k = 2` yields computably inseparable enumerable sets.
* `problemK_imp_imp_imp_disj_le_min_condK`: the upper bound, the complexity of the problem is at
  most `min (C(x|y), C(y|x))` up to a logarithmic term.
* `exists_uniform_solution_imp_imp_imp_disj_pdisj`: a single program solving
  `(((x → y) → y) → (x ∨ y)) → ((x → y) ∨~ (y → x))` for all strings `x`, `y`.
* `min_condK_le_problemK_imp_imp_imp_disj`: the matching lower bound, so that for independent
  random `x`, `y` of length `n` the complexity is close to `n`.
-/

namespace Kolmogorov
namespace InformationLogic

open ProblemCalculus PFormula

/-- SUV Section 13.4, computable diagonal function (printed p. 410).  There is a partial
computable *diagonal* function `d : ℕ →. Fin k`: every partial computable `u : ℕ →. Fin k`
agrees with `d` at some `i` (`d i = u i` as partial values: both undefined, or both defined and
equal).  Construction (book): `d(i)` is the value of the `i`-th partial computable function at
`i` (`Nat.Partrec.Code.eval`, `Nat.Partrec.Code.exists_code`).  For `k = 2` the preimages
`A = d⁻¹(0)`, `B = d⁻¹(1)` are computably inseparable enumerable sets (used in Theorem 242): a
total computable `u` with `u = 1` on `A` and `u = 0` on `B` would differ from `d` everywhere. -/
theorem exists_partrec_diagonal (k : ℕ) :
    ∃ d : ℕ →. Fin k, Partrec d ∧ ∀ u : ℕ →. Fin k, Partrec u → ∃ i, d i = u i := by
  refine ⟨fun i => ((Denumerable.ofNat Nat.Partrec.Code i).eval i).bind
      (fun r => ((Encodable.decode r : Option (Fin k)) : Part (Fin k))), ?_, ?_⟩
  · exact Partrec.bind
      (Nat.Partrec.Code.eval_part.comp (Primrec.ofNat Nat.Partrec.Code).to_comp Computable.id)
      (Computable.ofOption (Computable.decode.comp Computable.snd)).to₂
  · intro u hu
    have hg : Partrec (fun i => (u i).map (Encodable.encode : Fin k → ℕ)) :=
      Partrec.map hu (Computable.encode.comp Computable.snd).to₂
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hg)
    refine ⟨Encodable.encode c, ?_⟩
    simp only [Denumerable.ofNat_encode, hc]
    ext a
    simp

/-- Auxiliary lemma for `problemK_imp_imp_imp_disj_le_min_condK`: a bounded universal quantifier
over a computable list preserves enumerability (take the maximum of the stages of the finitely many
witnesses, `IsRE.exists_stageApprox`). -/
private lemma problemK_imp_imp_imp_disj_le_min_condK_forallInList {α β : Type} [Primcodable α]
    [Primcodable β] [Inhabited β] {R : α → β → Prop} (hR : IsRE (fun z : α × β => R z.1 z.2))
    (bound : α → List β) (hbound : Computable bound) :
    IsRE (fun a => ∀ b ∈ bound a, R a b) := by
  obtain ⟨chk, hchk, hmono, hiff⟩ := IsRE.exists_stageApprox hR
  have h1 : IsRE (fun z : α × ℕ => ∀ b ∈ bound z.1, chk (z.1, b) z.2 = true) := by
    refine isRE_of_computable_bool _
      (fun z => !((bound z.1).any (fun b => !chk (z.1, b) z.2))) ?_ ?_
    · intro z; simp
    · have hp : Computable₂ (fun (z : α × ℕ) (b : β) => !chk (z.1, b) z.2) :=
        (Primrec.not.to_comp.comp (hchk.comp ((Computable.fst.comp Computable.fst).pair
          Computable.snd) (Computable.snd.comp Computable.fst))).to₂
      exact Primrec.not.to_comp.comp
        (computable_list_any (hbound.comp Computable.fst) hp)
  refine (IsRE.exists_encodable (R := fun a s => ∀ b ∈ bound a, chk (a, b) s = true) h1).of_iff ?_
  intro a
  constructor
  · rintro ⟨s, hs⟩ b hb
    exact (hiff (a, b)).2 ⟨s, hs b hb⟩
  · intro h
    suffices H : ∀ l : List β, (∀ b ∈ l, R a b) → ∃ s, ∀ b ∈ l, chk (a, b) s = true from H _ h
    intro l
    induction l with
    | nil => intro _; exact ⟨0, by simp⟩
    | cons b l ih =>
      intro hl
      obtain ⟨s1, hs1⟩ := (hiff (a, b)).1 (hl b List.mem_cons_self)
      obtain ⟨s2, hs2⟩ := ih (fun b' hb' => hl b' (List.mem_cons_of_mem _ hb'))
      refine ⟨max s1 s2, ?_⟩
      intro b' hb'
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact hmono _ _ _ (le_max_left _ _) hs1
      · exact hmono _ _ _ (le_max_right _ _) (hs2 b' hb')

/-- Auxiliary lemma for `problemK_imp_imp_imp_disj_le_min_condK`: an enumerable relation has a
partial computable selector (dovetail over candidates and stages with `Nat.rfindOpt`); it is
defined wherever a witness exists and every output is a witness. -/
lemma problemK_imp_imp_imp_disj_le_min_condK_select {α β : Type} [Primcodable α]
    [Primcodable β] {R : α → β → Prop} (hR : IsRE (fun z : α × β => R z.1 z.2)) :
    ∃ F : α →. β, Partrec F ∧ (∀ a b, b ∈ F a → R a b) ∧ (∀ a b, R a b → (F a).Dom) := by
  obtain ⟨chk, hchk, hmono, hiff⟩ := IsRE.exists_stageApprox hR
  let g : α → ℕ → Option β := fun a m =>
    (Encodable.decode (α := β) m.unpair.1).bind
      (fun b => bif chk (a, b) m.unpair.2 then some b else none)
  have hg : Computable₂ g := by
    have h1 : Computable (fun z : α × ℕ => Encodable.decode (α := β) z.2.unpair.1) :=
      Computable.decode.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
    have h2 : Computable₂ (fun (z : α × ℕ) (b : β) =>
        bif chk (z.1, b) z.2.unpair.2 then some b else none) := by
      refine Computable.cond (hchk.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)
        (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst))))
        (Computable.option_some.comp Computable.snd) (Computable.const none)
    exact (Computable.option_bind h1 h2).to₂
  refine ⟨fun a => Nat.rfindOpt (g a), Partrec.rfindOpt hg, ?_, ?_⟩
  · intro a b hb
    obtain ⟨m, hm⟩ := Nat.rfindOpt_spec hb
    simp only [g, Option.mem_def, Option.bind_eq_some_iff] at hm
    obtain ⟨b', hb', hc⟩ := hm
    cases hck : chk (a, b') m.unpair.2
    · simp [hck] at hc
    · simp only [hck, Bool.cond_true, Option.some.injEq] at hc
      subst hc
      exact (hiff (a, b')).2 ⟨_, hck⟩
  · intro a b hab
    obtain ⟨s, hs⟩ := (hiff (a, b)).1 hab
    refine Nat.rfindOpt_dom.2 ⟨Nat.pair (Encodable.encode b) s, b, ?_⟩
    simp [g, hs]

/-- Auxiliary lemma for `problemK_imp_imp_imp_disj_le_min_condK`: the test programs.  There are
programs `R a b c`, computable from `(a, b, c)`, with `[R a b c](z) = b` for `z = a` and `c`
otherwise (Gödel translation of the corresponding language). -/
private lemma problemK_imp_imp_imp_disj_le_min_condK_programs (P : ProblemCalculus)
    (hP : P.Admissible) :
    ∃ R : BitString → BitString → BitString → BitString,
      Computable (fun w : BitString × BitString × BitString => R w.1 w.2.1 w.2.2) ∧
      ∀ a b c z, P.lang (R a b c, z) = Part.some (if z = a then b else c) := by
  have hGod := hP.2.2.2.2.2
  have hdf : Computable decodeFirst := CodedFiniteDistribution.decodeFirst_primrec.to_comp
  have hds : Computable decodeSecond := CodedFiniteDistribution.decodeSecond_primrec.to_comp
  have hpc : Computable₂ pairCode := CodedFiniteDistribution.pairCode_primrec.to_comp
  let V : Map := fun r => Part.some (if r.2 = decodeFirst r.1 then
    decodeFirst (decodeSecond r.1) else decodeSecond (decodeSecond r.1))
  have hV : Partrec V := by
    have hc : Computable (fun r : BitString × BitString => decide (r.2 = decodeFirst r.1)) :=
      Primrec.eq.decide.to_comp.comp Computable.snd (hdf.comp Computable.fst)
    refine (Computable.cond hc (hdf.comp (hds.comp Computable.fst))
      (hds.comp (hds.comp Computable.fst))).partrec.of_eq ?_
    intro r
    by_cases h : r.2 = decodeFirst r.1 <;> simp [V, h]
  obtain ⟨t, ht, hts⟩ := hGod.2 V hV
  refine ⟨fun a b c => t (pairCode a (pairCode b c)), ?_, ?_⟩
  · exact ht.comp (hpc.comp Computable.fst
      (hpc.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)))
  · intro a b c z
    rw [hts]
    simp [V, decodeFirst_pairCode, decodeSecond_pairCode]

/-- Auxiliary lemma for `problemK_imp_imp_imp_disj_le_min_condK`: the search of the book.  A pair
`(u, v)` of strings of length at most `n` is *compatible* with `q` if `[q](R a b c) = v` for all
`a, b, c` of length at most `n` such that the test program `R a b c` maps `u` to `v`.  For a
solution `q` of `(x → y) → y` the pair `(x, y)` is compatible, and two compatible pairs `(u, v)`,
`(u', v')` with `u ≠ u'` have `v = v'` (the program `R u v v'` is tested for both), so every
compatible pair has `u = x` or `v = y`.  `W ((p, n), q)` searches for a compatible `(u, v)` and
either a second compatible pair `(u', v') ≠ (u, v)` or the event `[p](v) = u`, and prints `[1, v]`
if `u ≠ u'`, `[0, u]` otherwise; if `[p](y) = x` the search succeeds (with `(x, y)` for both
pairs) and every outcome is `[0, x]` or `[1, y]`. -/
private lemma problemK_imp_imp_imp_disj_le_min_condK_search (P : ProblemCalculus)
    (hP : P.Admissible) :
    ∃ W : (BitString × ℕ) × BitString →. BitString, Partrec W ∧
      ∀ (p : BitString) (n : ℕ) (q x y : BitString), x.length ≤ n → y.length ≤ n →
        q ∈ P.imp (P.imp {x} {y}) {y} → x ∈ P.lang (p, y) →
        ∃ w ∈ W ((p, n), q), w = P.pair P.tag0 x ∨ w = P.pair P.tag1 y := by
  obtain ⟨R, hR, hRspec⟩ := problemK_imp_imp_imp_disj_le_min_condK_programs P hP
  have hL : Partrec P.lang := hP.2.2.2.2.2.1
  have hpair : Computable₂ P.pair := hP.1
  -- the triples `(a, b, c)` of strings of length at most `n`
  let tr : ℕ → List (BitString × BitString × BitString) := fun n =>
    (boundedPrograms n).flatMap (fun a => (boundedPrograms n).flatMap
      (fun b => (boundedPrograms n).map (fun c => (a, b, c))))
  have htr : Computable tr := by
    have hb := primrec_boundedPrograms
    have h3 : Primrec₂ (fun (z : ℕ × BitString) (b : BitString) =>
        (boundedPrograms z.1).map (fun c => (z.2, b, c))) := by
      refine Primrec.list_map (hb.comp (Primrec.fst.comp Primrec.fst)) ?_
      exact (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
    have h2 : Primrec₂ (fun (n : ℕ) (a : BitString) => (boundedPrograms n).flatMap
        (fun b => (boundedPrograms n).map (fun c => (a, b, c)))) := by
      refine Primrec.list_flatMap (hb.comp Primrec.fst) ?_
      exact (h3.comp Primrec.fst Primrec.snd).to₂
    exact (Primrec.list_flatMap hb h2).to_comp
  have hmemtr : ∀ n (w : BitString × BitString × BitString),
      w ∈ tr n ↔ w.1.length ≤ n ∧ w.2.1.length ≤ n ∧ w.2.2.length ≤ n := by
    intro n w
    obtain ⟨a, b, c⟩ := w
    simp [tr, mem_boundedPrograms_iff]
  -- compatibility of `(u, v)` with `q`: every tested program mapping `u` to `v` is sent to `v`
  let compat : ℕ → BitString → BitString → BitString → Prop := fun n q u v =>
    u.length ≤ n ∧ v.length ≤ n ∧ ∀ w ∈ tr n, (if u = w.1 then w.2.1 else w.2.2) = v →
      v ∈ P.lang (q, R w.1 w.2.1 w.2.2)
  have hite : Computable (fun z : ((ℕ × BitString) × (BitString × BitString)) ×
      (BitString × BitString × BitString) => if z.1.2.1 = z.2.1 then z.2.2.1 else z.2.2.2) := by
    have hc : Computable (fun z : ((ℕ × BitString) × (BitString × BitString)) ×
        (BitString × BitString × BitString) => decide (z.1.2.1 = z.2.1)) :=
      Primrec.eq.decide.to_comp.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (Computable.fst.comp Computable.snd)
    refine (Computable.cond hc (Computable.fst.comp (Computable.snd.comp Computable.snd))
      (Computable.snd.comp (Computable.snd.comp Computable.snd))).of_eq ?_
    intro z
    by_cases h : z.1.2.1 = z.2.1 <;> simp [h]
  have hatom : IsRE (fun z : ((ℕ × BitString) × (BitString × BitString)) ×
      (BitString × BitString × BitString) =>
      (if z.1.2.1 = z.2.1 then z.2.2.1 else z.2.2.2) = z.1.2.2 →
        z.1.2.2 ∈ P.lang (z.1.1.2, R z.2.1 z.2.2.1 z.2.2.2)) := by
    have hg := (Partrec.graphIsRe P.lang hL).comp_computable
      (g := fun z : ((ℕ × BitString) × (BitString × BitString)) ×
        (BitString × BitString × BitString) =>
        ((z.1.1.2, R z.2.1 z.2.2.1 z.2.2.2), z.1.2.2))
      (((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
        (hR.comp Computable.snd)).pair (Computable.snd.comp (Computable.snd.comp Computable.fst)))
    have hd := isRE_of_computable_bool (fun z : ((ℕ × BitString) × (BitString × BitString)) ×
        (BitString × BitString × BitString) =>
        (if z.1.2.1 = z.2.1 then z.2.2.1 else z.2.2.2) ≠ z.1.2.2)
      (fun z => !decide ((if z.1.2.1 = z.2.1 then z.2.2.1 else z.2.2.2) = z.1.2.2))
      (fun z => by simp)
      (Primrec.not.to_comp.comp (Primrec.eq.decide.to_comp.comp hite
        (Computable.snd.comp (Computable.snd.comp Computable.fst))))
    refine (hd.or hg).of_iff (fun z => ?_)
    constructor
    · rintro (h | h) h'
      · exact absurd h' h
      · exact h
    · intro h
      by_cases h' : (if z.1.2.1 = z.2.1 then z.2.2.1 else z.2.2.2) = z.1.2.2
      · exact Or.inr (h h')
      · exact Or.inl h'
  have hcompat : IsRE (fun z : (ℕ × BitString) × (BitString × BitString) =>
      compat z.1.1 z.1.2 z.2.1 z.2.2) := by
    have hall := problemK_imp_imp_imp_disj_le_min_condK_forallInList
      (R := fun (z : (ℕ × BitString) × (BitString × BitString))
        (w : BitString × BitString × BitString) =>
        (if z.2.1 = w.1 then w.2.1 else w.2.2) = z.2.2 → z.2.2 ∈ P.lang (z.1.2, R w.1 w.2.1 w.2.2))
      hatom (fun z : (ℕ × BitString) × (BitString × BitString) => tr z.1.1)
      (htr.comp (Computable.fst.comp Computable.fst))
    have hlen : Computable (fun z : (ℕ × BitString) × (BitString × BitString) =>
        decide (z.2.1.length ≤ z.1.1) && decide (z.2.2.length ≤ z.1.1)) :=
      Primrec.and.to_comp.comp
        (Primrec.nat_le.decide.to_comp.comp
          (Computable.list_length.comp (Computable.fst.comp Computable.snd))
          (Computable.fst.comp Computable.fst))
        (Primrec.nat_le.decide.to_comp.comp
          (Computable.list_length.comp (Computable.snd.comp Computable.snd))
          (Computable.fst.comp Computable.fst))
    refine (hall.and_computable hlen).of_iff (fun z => ?_)
    simp only [compat, Bool.and_eq_true, decide_eq_true_eq]
    tauto
  -- the events of the search
  let ev : (BitString × ℕ) × BitString → (BitString × BitString) × (BitString × BitString) →
      Prop := fun a b => compat a.1.2 a.2 b.1.1 b.1.2 ∧
        ((compat a.1.2 a.2 b.2.1 b.2.2 ∧ b.1 ≠ b.2) ∨
          (b.1.1 = b.2.1 ∧ b.1.1 ∈ P.lang (a.1.1, b.1.2)))
  have hev : IsRE (fun z : ((BitString × ℕ) × BitString) ×
      ((BitString × BitString) × (BitString × BitString)) => ev z.1 z.2) := by
    have hc1 := hcompat.comp_computable
      (g := fun z : ((BitString × ℕ) × BitString) ×
        ((BitString × BitString) × (BitString × BitString)) =>
        ((z.1.1.2, z.1.2), (z.2.1.1, z.2.1.2)))
      (((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.snd.comp Computable.fst)).pair
        ((Computable.fst.comp (Computable.fst.comp Computable.snd)).pair
          (Computable.snd.comp (Computable.fst.comp Computable.snd))))
    have hc2 := hcompat.comp_computable
      (g := fun z : ((BitString × ℕ) × BitString) ×
        ((BitString × BitString) × (BitString × BitString)) =>
        ((z.1.1.2, z.1.2), (z.2.2.1, z.2.2.2)))
      (((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.snd.comp Computable.fst)).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
          (Computable.snd.comp (Computable.snd.comp Computable.snd))))
    have hne : Computable (fun z : ((BitString × ℕ) × BitString) ×
        ((BitString × BitString) × (BitString × BitString)) => !decide (z.2.1 = z.2.2)) :=
      Primrec.not.to_comp.comp (Primrec.eq.decide.to_comp.comp
        (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd))
    have heq : Computable (fun z : ((BitString × ℕ) × BitString) ×
        ((BitString × BitString) × (BitString × BitString)) => decide (z.2.1.1 = z.2.2.1)) :=
      Primrec.eq.decide.to_comp.comp (Computable.fst.comp (Computable.fst.comp Computable.snd))
        (Computable.fst.comp (Computable.snd.comp Computable.snd))
    have hg := (Partrec.graphIsRe P.lang hL).comp_computable
      (g := fun z : ((BitString × ℕ) × BitString) ×
        ((BitString × BitString) × (BitString × BitString)) =>
        ((z.1.1.1, z.2.1.2), z.2.1.1))
      (((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.snd.comp (Computable.fst.comp Computable.snd))).pair
        (Computable.fst.comp (Computable.fst.comp Computable.snd)))
    refine (hc1.and ((hc2.and_computable hne).or (hg.and_computable heq))).of_iff (fun z => ?_)
    simp only [ev, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    tauto
  obtain ⟨F, hF, hFsound, hFcomp⟩ := problemK_imp_imp_imp_disj_le_min_condK_select hev
  let out : (BitString × BitString) × (BitString × BitString) → BitString := fun b =>
    if b.1.1 = b.2.1 then P.pair P.tag0 b.1.1 else P.pair P.tag1 b.1.2
  have hout : Computable out := by
    have hc : Computable (fun b : (BitString × BitString) × (BitString × BitString) =>
        decide (b.1.1 = b.2.1)) :=
      Primrec.eq.decide.to_comp.comp (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd)
    refine (Computable.cond hc (hpair.comp (Computable.const P.tag0)
      (Computable.fst.comp Computable.fst))
      (hpair.comp (Computable.const P.tag1) (Computable.snd.comp Computable.fst))).of_eq ?_
    intro b
    by_cases h : b.1.1 = b.2.1 <;> simp [out, h]
  refine ⟨fun a => (F a).map out, hF.map (hout.comp Computable.snd).to₂, ?_⟩
  intro p n q x y hx hy hq hpy
  -- `(x, y)` is compatible with `q`
  have hcxy : compat n q x y := by
    refine ⟨hx, hy, fun w _ hw => ?_⟩
    have hmem : R w.1 w.2.1 w.2.2 ∈ P.imp {x} {y} := by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact ⟨y, rfl, by rw [hRspec, hw]; exact Part.mem_some _⟩
    obtain ⟨b, hb, hbq⟩ := hq _ hmem
    rw [Set.mem_singleton_iff] at hb
    rw [hb] at hbq
    exact hbq
  -- two compatible pairs with different first components have equal second components
  have hpr : ∀ u v u' v', compat n q u v → compat n q u' v' → u ≠ u' → v = v' := by
    intro u v u' v' h h' hne
    have e1 := h.2.2 (u, v, v') ((hmemtr n _).2 ⟨h.1, h.2.1, h'.2.1⟩) (by simp)
    have e2 := h'.2.2 (u, v, v') ((hmemtr n _).2 ⟨h.1, h.2.1, h'.2.1⟩)
      (by simp [Ne.symm hne])
    exact Part.mem_unique e1 e2
  have hxy : ∀ u v, compat n q u v → u = x ∨ v = y := by
    intro u v h
    by_cases hu : u = x
    · exact Or.inl hu
    · exact Or.inr (hpr u v x y h hcxy hu)
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.1
    (hFcomp ((p, n), q) ((x, y), (x, y)) ⟨hcxy, Or.inr ⟨rfl, hpy⟩⟩)
  refine ⟨out b, Part.mem_map _ hb, ?_⟩
  obtain ⟨⟨u, v⟩, ⟨u', v'⟩⟩ := b
  have hev' := hFsound _ _ hb
  change compat n q u v ∧ ((compat n q u' v' ∧ (u, v) ≠ (u', v')) ∨
    (u = u' ∧ u ∈ P.lang (p, v))) at hev'
  obtain ⟨h1, h2⟩ := hev'
  by_cases huu : u = u'
  · left
    have hux : u = x := by
      by_contra hux
      have hvy : v = y := (hxy u v h1).resolve_left hux
      rcases h2 with ⟨h3, hne⟩ | ⟨-, h4⟩
      · have hv'y : v' = y := (hxy u' v' h3).resolve_left (fun h => hux (huu.trans h))
        exact hne (by rw [huu, hvy, hv'y])
      · rw [hvy] at h4
        exact hux (Part.mem_unique h4 hpy)
    change (if u = u' then P.pair P.tag0 u else P.pair P.tag1 v) = P.pair P.tag0 x
    rw [ite_eq_left huu, hux]
  · right
    have h3 : compat n q u' v' := by
      rcases h2 with ⟨h3, -⟩ | ⟨h4, -⟩
      · exact h3
      · exact absurd h4 huu
    have hvy : v = y := by
      by_contra hvy
      have hux : u = x := (hxy u v h1).resolve_right hvy
      have hvv : v = v' := hpr u v u' v' h1 h3 huu
      have hu'x : u' = x := (hxy u' v' h3).resolve_right (fun h => hvy (hvv.trans h))
      exact huu (hux.trans hu'x.symm)
    change (if u = u' then P.pair P.tag0 u else P.pair P.tag1 v) = P.pair P.tag1 y
    rw [ite_eq_right huu, hvy]

/-- SUV Theorem 242 (Section 13.4, printed p. 408), upper bound.  The complexity of
`((x → y) → y) → (x ∨ y)` is at most `min (C(x|y), C(y|x)) + O(log n)` for strings of length at
most `n`.  Book: `C(y|x) + O(1)`: if `p` maps `x` to `y` and `q` solves `(x → y) → y` then
`[q](p) = y`, so `q ↦ [1, [q](p)]` is a solution computed from `p`.  `C(x|y) + O(log n)`: given
`p` mapping `y` to `x`, `q` and `n`, find the first pair `(u, v)` compatible with `q` (as in
Theorem 240); then in parallel look for a second compatible pair `(u', v')` and check
`[p](v) = u`; one of the two events happens, and `v ≠ v'` or `[p](v) = u` gives `u = x`,
`u ≠ u'` gives `v = y` (all compatible pairs share the first component `x` or the second
component `y`).  Reductions: `problemK_le_of_partrec`, `problemK_le_of_partrec_advice` from
`{x} → {y}`, resp. `{y} → {x}`, and `problemK_imp_singleton_le_condK`. -/
theorem problemK_imp_imp_imp_disj_le_min_condK (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y : BitString), x.length ≤ n → y.length ≤ n →
      problemK D (P.imp (P.imp (P.imp {x} {y}) {y}) (P.disj {x} {y})) ≤
        min (condK D x y) (condK D y x) + (logSlack k n : ℕ∞) := by
  have hGod := hP.2.2.2.2.2
  have hL : Partrec P.lang := hGod.1
  have hpair : Computable₂ P.pair := hP.1
  -- the `C(y|x) + O(1)` bound: `q ↦ [1, [q](p)]`
  let V1 : Map := fun pq => (P.lang (pq.2, pq.1)).bind (fun w => Part.some (P.pair P.tag1 w))
  have hV1 : Partrec V1 :=
    Partrec.bind (hL.comp (Computable.snd.pair Computable.fst))
      (hpair.comp (Computable.const P.tag1) Computable.snd).partrec.to₂
  obtain ⟨t1, ht1, hts1⟩ := hGod.2 V1 hV1
  obtain ⟨ca, hca⟩ := problemK_le_of_partrec D hD (fun p => Part.some (t1 p)) ht1.partrec
  obtain ⟨cb, hcb⟩ := problemK_imp_singleton_le_condK D hD P hP
  -- the `C(x|y) + O(log n)` bound: the search of the book, with `n` as advice
  obtain ⟨W, hW, hWsol⟩ := problemK_imp_imp_imp_disj_le_min_condK_search P hP
  have hdf : Computable decodeFirst := CodedFiniteDistribution.decodeFirst_primrec.to_comp
  have hds : Computable decodeSecond := CodedFiniteDistribution.decodeSecond_primrec.to_comp
  have hpc : Computable₂ pairCode := CodedFiniteDistribution.pairCode_primrec.to_comp
  let V2 : Map := fun sq => W ((decodeFirst sq.1, (decodeSecond sq.1).length), sq.2)
  have hV2 : Partrec V2 :=
    hW.comp (((hdf.comp Computable.fst).pair
      (Computable.list_length.comp (hds.comp Computable.fst))).pair Computable.snd)
  obtain ⟨t2, ht2, hts2⟩ := hGod.2 V2 hV2
  have hf : Partrec (fun z : BitString × ℕ × Bool =>
      (Part.some (t2 (pairCode z.1 (List.replicate z.2.1 false))) : Part BitString)) :=
    (ht2.comp (hpc.comp Computable.fst
      (Primrec.list_replicate.to_comp.comp (Computable.fst.comp Computable.snd)
        (Computable.const false)))).partrec
  obtain ⟨cc, hcc⟩ := problemK_le_of_partrec_advice D hD _ hf
  obtain ⟨cs, hcs⟩ := problemK_imp_singleton_le_condK D hD P hP
  refine ⟨ca + cb + cc + cs, fun n x y hx hy => ?_⟩
  have h1 : problemK D (P.imp (P.imp (P.imp {x} {y}) {y}) (P.disj {x} {y})) ≤
      condK D y x + (logSlack (ca + cb + cc + cs) n : ℕ∞) := by
    have hmem : ∀ p ∈ P.imp {x} {y}, ∃ a ∈
        P.imp (P.imp (P.imp {x} {y}) {y}) (P.disj {x} {y}),
        a ∈ (fun p => (Part.some (t1 p) : Part BitString)) p := by
      intro p hp
      refine ⟨t1 p, fun q hq => ?_, Part.mem_some _⟩
      obtain ⟨b, hb, hbq⟩ := hq p hp
      rw [Set.mem_singleton_iff] at hb
      subst hb
      refine ⟨P.pair P.tag1 b, Or.inr ⟨b, rfl, rfl⟩, ?_⟩
      rw [hts1]
      exact Part.mem_bind_iff.2 ⟨b, hbq, Part.mem_some _⟩
    have e1 : ca + cb ≤ logSlack (ca + cb) n := Nat.le_add_left _ _
    have e2 := logSlack_mono_left (c := ca + cb) (c' := ca + cb + cc + cs) (by omega) n
    calc _ ≤ problemK D (P.imp {x} {y}) + (ca : ℕ∞) := hca _ _ hmem
      _ ≤ (condK D y x + (cb : ℕ∞)) + (ca : ℕ∞) := by gcongr; exact hcb x y
      _ = condK D y x + ((ca + cb : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ _ := by
        gcongr
        exact_mod_cast e1.trans e2
  have h2 : problemK D (P.imp (P.imp (P.imp {x} {y}) {y}) (P.disj {x} {y})) ≤
      condK D x y + (logSlack (ca + cb + cc + cs) n : ℕ∞) := by
    have hmem : ∀ p ∈ P.imp {y} {x}, ∃ _b : Bool, ∃ a ∈
        P.imp (P.imp (P.imp {x} {y}) {y}) (P.disj {x} {y}),
        a ∈ (Part.some (t2 (pairCode p (List.replicate n false))) : Part BitString) := by
      intro p hp
      refine ⟨false, t2 (pairCode p (List.replicate n false)), fun q hq => ?_, Part.mem_some _⟩
      obtain ⟨b, hb, hbp⟩ := hp y rfl
      rw [Set.mem_singleton_iff] at hb
      rw [hb] at hbp
      obtain ⟨w, hw, hw'⟩ := hWsol p n q x y hx hy hq hbp
      refine ⟨w, ?_, ?_⟩
      · rcases hw' with rfl | rfl
        · exact Or.inl ⟨x, rfl, rfl⟩
        · exact Or.inr ⟨y, rfl, rfl⟩
      · rw [hts2]
        simpa [V2, decodeFirst_pairCode, decodeSecond_pairCode] using hw
    have e1 : cs ≤ logSlack cs n := Nat.le_add_left _ _
    have e2 := logSlack_mono_left (c := cs + cc) (c' := ca + cb + cc + cs) (by omega) n
    have e3 := logSlack_add_constants cs cc n
    calc _ ≤ problemK D (P.imp {y} {x}) + (logSlack cc n : ℕ∞) := hcc _ _ n hmem
      _ ≤ (condK D x y + (cs : ℕ∞)) + (logSlack cc n : ℕ∞) := by gcongr; exact hcs y x
      _ = condK D x y + ((cs + logSlack cc n : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ _ := by
        gcongr
        exact_mod_cast (by omega : cs + logSlack cc n ≤ logSlack (ca + cb + cc + cs) n)
  rw [← min_add_add_right]
  exact le_min h2 h1

/-- Step 1 of the proof of `exists_uniform_solution_imp_imp_imp_disj_pdisj`: the programs
`q_i(u, v)` of the book.  For a partial computable `d : ℕ →. Fin 2` there is a total computable
`Q i u v` such that `Q i u v` solves `(x → y) → y` (i.e. maps every `s` with `y ∈ [s](x)` to `y`)
whenever `d i = 0` and `v = y` (`i ∈ A`), or `d i = 1` and `u = x` (`i ∈ B`), or `u = x`, `v = y`.
Book: on input `s`, `[Q i u v](s)` runs in parallel `d i` and `[s](u)`: if `d i = 0` output `v`;
if `d i = 1` output `[s](u)`; if `[s](u) = v` output `v`.  (Use `Partrec.merge` twice: the three
partial functions agree where they overlap; then the Gödel translation of `P.lang`,
`IsGodelLang`, applied to the language `V (code(i, u, v), s)`.) -/
private theorem exists_uniform_solution_imp_imp_imp_disj_pdisj_programs
    (P : ProblemCalculus) (hP : P.Admissible) (d : ℕ →. Fin 2) (hd : Partrec d) :
    ∃ Q : ℕ → BitString → BitString → BitString,
      Computable (fun z : ℕ × BitString × BitString => Q z.1 z.2.1 z.2.2) ∧
      ∀ (x y : BitString) (i : ℕ) (u v : BitString),
        ((d i = Part.some 0 ∧ v = y) ∨ (d i = Part.some 1 ∧ u = x) ∨ (u = x ∧ v = y)) →
        Q i u v ∈ P.imp (P.imp {x} {y}) {y} := by
  have hGod := hP.2.2.2.2.2
  have hL : Partrec P.lang := hGod.1
  have hdf : Computable decodeFirst := CodedFiniteDistribution.decodeFirst_primrec.to_comp
  have hds : Computable decodeSecond := CodedFiniteDistribution.decodeSecond_primrec.to_comp
  have hpc : Computable₂ pairCode := CodedFiniteDistribution.pairCode_primrec.to_comp
  -- the data `z = ((i, u, v), s)`
  have hi : Computable (fun z : (ℕ × BitString × BitString) × BitString => z.1.1) :=
    Computable.fst.comp Computable.fst
  have hu : Computable (fun z : (ℕ × BitString × BitString) × BitString => z.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hv : Computable (fun z : (ℕ × BitString × BitString) × BitString => z.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun z : (ℕ × BitString × BitString) × BitString => z.2) :=
    Computable.snd
  have hdz : Partrec (fun z : (ℕ × BitString × BitString) × BitString => d z.1.1) :=
    hd.comp hi
  have hLu : Partrec (fun z : (ℕ × BitString × BitString) × BitString => P.lang (z.2, z.1.2.1)) :=
    hL.comp (hs.pair hu)
  let f1 : (ℕ × BitString × BitString) × BitString →. BitString := fun z =>
    (d z.1.1).bind
      (fun b => (↑(if b = 0 then some z.1.2.2 else none : Option BitString) : Part BitString))
  let f2 : (ℕ × BitString × BitString) × BitString →. BitString := fun z =>
    ((d z.1.1).bind
      (fun b => (↑(if b = 1 then some () else none : Option Unit) : Part Unit))).bind
      (fun _ => P.lang (z.2, z.1.2.1))
  let f3 : (ℕ × BitString × BitString) × BitString →. BitString := fun z =>
    (P.lang (z.2, z.1.2.1)).bind
      (fun r => (↑(if r = z.1.2.2 then some z.1.2.2 else none : Option BitString) :
        Part BitString))
  have hf1 : Partrec f1 := by
    refine hdz.bind ?_
    refine Computable.ofOption ?_
    have hc : Computable (fun q : ((ℕ × BitString × BitString) × BitString) × Fin 2 =>
        decide (q.2 = 0)) :=
      Primrec.eq.decide.to_comp.comp Computable.snd (Computable.const _)
    refine (Computable.cond hc (Computable.option_some.comp (hv.comp Computable.fst))
      (Computable.const none)).of_eq ?_
    intro q
    by_cases h : q.2 = 0 <;> simp [h]
  have hf2 : Partrec f2 := by
    refine Partrec.bind (hdz.bind ?_) (hLu.comp Computable.fst).to₂
    refine Computable.ofOption ?_
    have hc : Computable (fun q : ((ℕ × BitString × BitString) × BitString) × Fin 2 =>
        decide (q.2 = 1)) :=
      Primrec.eq.decide.to_comp.comp Computable.snd (Computable.const _)
    refine (Computable.cond hc (Computable.option_some.comp (Computable.const ()))
      (Computable.const none)).of_eq ?_
    intro q
    by_cases h : q.2 = 1 <;> simp [h]
  have hf3 : Partrec f3 := by
    refine hLu.bind ?_
    refine Computable.ofOption ?_
    have hc : Computable (fun q : ((ℕ × BitString × BitString) × BitString) × BitString =>
        decide (q.2 = q.1.1.2.2)) :=
      Primrec.eq.decide.to_comp.comp Computable.snd (hv.comp Computable.fst)
    refine (Computable.cond hc (Computable.option_some.comp (hv.comp Computable.fst))
      (Computable.const none)).of_eq ?_
    intro q
    by_cases h : q.2 = q.1.1.2.2 <;> simp [h]
  obtain ⟨k1, hk1, hk1s⟩ := Partrec.merge' hf1 hf2
  obtain ⟨k, hk, hks⟩ := Partrec.merge' hk1 hf3
  let V : Map := fun r => k (((decodeFirst r.1).length, decodeFirst (decodeSecond r.1),
    decodeSecond (decodeSecond r.1)), r.2)
  have hV : Partrec V := by
    refine hk.comp ?_
    exact (((Computable.list_length.comp (hdf.comp Computable.fst)).pair
      ((hdf.comp (hds.comp Computable.fst)).pair (hds.comp (hds.comp Computable.fst)))).pair
        Computable.snd)
  obtain ⟨t, ht, hts⟩ := hGod.2 V hV
  refine ⟨fun i u v => t (pairCode (List.replicate i false) (pairCode u v)), ?_, ?_⟩
  · refine ht.comp (hpc.comp (Primrec.list_replicate.to_comp.comp Computable.fst
      (Computable.const false)) (hpc.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)))
  · intro x y i u v hcase s hs
    have hVk : ∀ s', P.lang (t (pairCode (List.replicate i false) (pairCode u v)), s') =
        k ((i, u, v), s') := by
      intro s'
      rw [hts]
      simp [V, decodeFirst_pairCode, decodeSecond_pairCode]
    obtain ⟨b, hb, hbL⟩ := hs x rfl
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine ⟨b, rfl, ?_⟩
    rw [hVk]
    have o1 : ∀ w, w ∈ f1 ((i, u, v), s) → d i = Part.some 0 ∧ w = v := by
      intro w hw
      simp only [f1, Part.mem_bind_iff, Part.mem_coe] at hw
      obtain ⟨c, hc, hw⟩ := hw
      by_cases h : c = 0
      · simp only [h, ite_true, Option.mem_def, Option.some.injEq] at hw
        exact ⟨Part.eq_some_iff.2 (h ▸ hc), hw.symm⟩
      · simp [h] at hw
    have o2 : ∀ w, w ∈ f2 ((i, u, v), s) → d i = Part.some 1 ∧ w ∈ P.lang (s, u) := by
      intro w hw
      simp only [f2, Part.mem_bind_iff, Part.mem_coe] at hw
      obtain ⟨_, ⟨c, hc, hw1⟩, hw2⟩ := hw
      by_cases h : c = 1
      · exact ⟨Part.eq_some_iff.2 (h ▸ hc), hw2⟩
      · simp [h] at hw1
    have o3 : ∀ w, w ∈ f3 ((i, u, v), s) → w = v ∧ v ∈ P.lang (s, u) := by
      intro w hw
      simp only [f3, Part.mem_bind_iff, Part.mem_coe] at hw
      obtain ⟨r, hr, hw⟩ := hw
      by_cases h : r = v
      · simp only [h, ite_true, Option.mem_def, Option.some.injEq] at hw
        exact ⟨hw.symm, h ▸ hr⟩
      · simp [h] at hw
    have hbu : u = x → ∀ w ∈ P.lang (s, u), w = b := fun hux w hw => by
      subst hux; exact Part.mem_unique hw hbL
    have hall1 : ∀ w, w ∈ f1 ((i, u, v), s) → w = b := by
      intro w hw
      obtain ⟨h0, rfl⟩ := o1 w hw
      rcases hcase with ⟨_, h⟩ | ⟨h1, _⟩ | ⟨_, h⟩
      · exact h
      · rw [h1] at h0; exact absurd (Part.some_injective h0) (by decide)
      · exact h
    have hall2 : ∀ w, w ∈ f2 ((i, u, v), s) → w = b := by
      intro w hw
      obtain ⟨h1, hw⟩ := o2 w hw
      rcases hcase with ⟨h0, _⟩ | ⟨_, hu⟩ | ⟨hu, _⟩
      · rw [h0] at h1; exact absurd (Part.some_injective h1) (by decide)
      · exact hbu hu w hw
      · exact hbu hu w hw
    have hall3 : ∀ w, w ∈ f3 ((i, u, v), s) → w = b := by
      intro w hw
      obtain ⟨rfl, hv⟩ := o3 w hw
      rcases hcase with ⟨_, h⟩ | ⟨_, hu⟩ | ⟨_, h⟩
      · exact h
      · exact hbu hu _ hv
      · exact h
    have hex : (∃ w, w ∈ f1 ((i, u, v), s)) ∨ (∃ w, w ∈ f2 ((i, u, v), s)) ∨
        (∃ w, w ∈ f3 ((i, u, v), s)) := by
      rcases hcase with ⟨h0, hvb⟩ | ⟨h1, hu⟩ | ⟨hu, hvb⟩
      · left
        exact ⟨v, Part.mem_bind_iff.2 ⟨0, by rw [h0]; exact Part.mem_some _, by simp⟩⟩
      · right; left
        subst hu
        exact ⟨b, Part.mem_bind_iff.2 ⟨(), Part.mem_bind_iff.2
          ⟨1, by rw [h1]; exact Part.mem_some _, by simp⟩, hbL⟩⟩
      · right; right
        subst hu; subst hvb
        exact ⟨v, Part.mem_bind_iff.2 ⟨v, hbL, by simp⟩⟩
    have hkdom : (k ((i, u, v), s)).Dom := by
      refine ((hks _).2).2 ?_
      rcases hex with ⟨w, hw⟩ | ⟨w, hw⟩ | ⟨w, hw⟩
      · exact Or.inl (((hk1s _).2).2 (Or.inl (Part.dom_iff_mem.2 ⟨w, hw⟩)))
      · exact Or.inl (((hk1s _).2).2 (Or.inr (Part.dom_iff_mem.2 ⟨w, hw⟩)))
      · exact Or.inr (Part.dom_iff_mem.2 ⟨w, hw⟩)
    have hkb : ∀ w ∈ k ((i, u, v), s), w = b := by
      intro w hw
      rcases (hks _).1 w hw with h | h
      · rcases (hk1s _).1 w h with h | h
        · exact hall1 w h
        · exact hall2 w h
      · exact hall3 w h
    have hget := Part.get_mem hkdom
    rw [hkb _ hget] at hget
    exact hget

/-- Step 2 of the proof of `exists_uniform_solution_imp_imp_imp_disj_pdisj`: generic
dovetailing (unbounded parallel search).  For a partial computable `G a b` there is a partial
computable `H a` that searches all `b` in parallel: every output of `H a` is an output of some
`G a b`, and `H a` is defined as soon as some `G a b` is defined.  (Take a code of `G`, and
`Nat.rfind` over pairs `(b, steps)` of `Nat.Partrec.Code.evaln`, cf. `IsRE.exists_encodable` in
`REClosure`.) -/
private theorem exists_uniform_solution_imp_imp_imp_disj_pdisj_search
    {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ] (G : α → β →. γ)
    (hG : Partrec (fun z : α × β => G z.1 z.2)) :
    ∃ H : α →. γ, Partrec H ∧ (∀ a c, c ∈ H a → ∃ b, c ∈ G a b) ∧
      (∀ a b, (G a b).Dom → (H a).Dom) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hG
  let f : α → ℕ → Option γ := fun a n =>
    (Encodable.decode (α := β) n.unpair.1).bind fun b =>
      (Nat.Partrec.Code.evaln n.unpair.2 c (Encodable.encode (a, b))).bind
        (Encodable.decode (α := γ))
  have hf : Computable₂ f := by
    have h1 : Computable (fun p : α × ℕ => Encodable.decode (α := β) p.2.unpair.1) :=
      Computable.comp Computable.decode
        (Computable.comp Computable.fst (Computable.comp Computable.unpair Computable.snd))
    have h2 : Computable₂ (fun (p : α × ℕ) (b : β) =>
        Nat.Partrec.Code.evaln p.2.unpair.2 c (Encodable.encode (p.1, b))) := by
      have h_steps : Computable (fun q : (α × ℕ) × β => q.1.2.unpair.2) :=
        Primrec.to_comp
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))
      have h_input : Computable (fun q : (α × ℕ) × β => Encodable.encode (q.1.1, q.2)) :=
        Computable.comp Computable.encode
          (Primrec.to_comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
      have hev : Primrec (fun q : (ℕ × Nat.Partrec.Code) × ℕ =>
          Nat.Partrec.Code.evaln q.1.1 q.1.2 q.2) := Nat.Partrec.Code.primrec_evaln
      exact (hev.to_comp).comp
        (Computable.pair (Computable.pair h_steps (Computable.const c)) h_input)
    have h3 : Computable₂ (fun (q : (α × ℕ) × β) (m : ℕ) => Encodable.decode (α := γ) m) :=
      (Computable.decode.comp Computable.snd).to₂
    have h4 : Computable₂ (fun (p : α × ℕ) (b : β) =>
        (Nat.Partrec.Code.evaln p.2.unpair.2 c (Encodable.encode (p.1, b))).bind
          (Encodable.decode (α := γ))) :=
      Computable.option_bind h2 h3
    exact Computable.option_bind h1 h4
  refine ⟨fun a => Nat.rfindOpt (f a), Partrec.rfindOpt hf, ?_, ?_⟩
  · intro a c' hc'
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hc'
    simp only [f, Option.mem_def, Option.bind_eq_some_iff] at hn
    obtain ⟨b, hb, m, hm, hdec⟩ := hn
    refine ⟨b, ?_⟩
    have hev : m ∈ (G a b).map (Encodable.encode : γ → ℕ) := by
      have h := Nat.Partrec.Code.evaln_sound hm
      rw [hc] at h
      simpa using h
    obtain ⟨c'', hc'', rfl⟩ := Part.mem_map_iff _ |>.1 hev
    rw [Encodable.encodek] at hdec
    obtain rfl := Option.some.inj hdec
    exact hc''
  · intro a b hdom
    obtain ⟨c'', hc''⟩ := Part.dom_iff_mem.1 hdom
    have hm : Encodable.encode c'' ∈ (G a b).map (Encodable.encode : γ → ℕ) :=
      Part.mem_map _ hc''
    have hev : Encodable.encode c'' ∈ Nat.Partrec.Code.eval c (Encodable.encode (a, b)) := by
      rw [hc]
      simpa using hm
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.1 hev
    rw [Nat.rfindOpt_dom]
    refine ⟨Nat.pair (Encodable.encode b) k, c'', ?_⟩
    rw [Option.mem_def] at hk ⊢
    simp only [f, Nat.unpair_pair, Encodable.encodek, Option.bind_some]
    rw [hk]
    simp

/-- Generic search used in step 3 of the proof of
`exists_uniform_solution_imp_imp_imp_disj_pdisj_searches`. -/
private theorem exists_uniform_solution_imp_imp_imp_disj_pdisj_searches_aux
    (P : ProblemCalculus) (hP : P.Admissible) (d : ℕ →. Fin 2) (hd : Partrec d)
    (j0 : Fin 2) (tag : BitString)
    (q : BitString × BitString → ℕ × BitString → BitString)
    (hq : Computable (fun z : (BitString × BitString) × (ℕ × BitString) => q z.1 z.2)) :
    ∃ R : BitString × BitString →. BitString, Partrec R ∧
      (∀ p a z, z ∈ R (p, a) → ∃ (i : ℕ) (v w : BitString), d i = Part.some j0 ∧
        w ∈ P.lang (p, q (p, a) (i, v)) ∧ P.unpair w = some (tag, z)) ∧
      (∀ p a (i : ℕ) (v w z : BitString), d i = Part.some j0 → w ∈ P.lang (p, q (p, a) (i, v)) →
        P.unpair w = some (tag, z) → (R (p, a)).Dom) := by
  let e : Fin 2 → BitString → Option BitString := fun j w =>
    (P.unpair w).bind (fun tz => if tz.1 = tag ∧ j = j0 then some tz.2 else none)
  have he : Computable (fun z : Fin 2 × BitString => e z.1 z.2) := by
    refine Computable.option_bind (hP.2.1.comp Computable.snd) ?_
    have hc : Computable (fun r : (Fin 2 × BitString) × (BitString × BitString) =>
        decide (r.2.1 = tag ∧ r.1.1 = j0)) := by
      have h1 : Computable (fun r : (Fin 2 × BitString) × (BitString × BitString) =>
          decide (r.2.1 = tag)) :=
        (Primrec.eq.decide.to_comp).comp (Computable.fst.comp Computable.snd)
          (Computable.const _)
      have h2 : Computable (fun r : (Fin 2 × BitString) × (BitString × BitString) =>
          decide (r.1.1 = j0)) :=
        (Primrec.eq.decide.to_comp).comp (Computable.fst.comp Computable.fst)
          (Computable.const _)
      have := (Primrec.and.to_comp).comp h1 h2
      refine Computable.of_eq this fun r => ?_
      simp
    have := Computable.cond hc
      (Computable.option_some.comp (Computable.snd.comp Computable.snd))
      (Computable.const (none : Option BitString))
    refine Computable.of_eq this fun r => ?_
    by_cases h : r.2.1 = tag ∧ r.1.1 = j0 <;> simp [h]
  let G : BitString × BitString → ℕ × BitString →. BitString := fun a b =>
    (d b.1).bind fun j => (P.lang (a.1, q a b)).bind fun w => (e j w : Part BitString)
  have hG : Partrec (fun z : (BitString × BitString) × (ℕ × BitString) => G z.1 z.2) := by
    have hz1 : Computable (fun z : (BitString × BitString) × (ℕ × BitString) => z.1) :=
      Computable.fst
    have hz2 : Computable (fun z : (BitString × BitString) × (ℕ × BitString) => z.2) :=
      Computable.snd
    have hi : Computable (fun z : (BitString × BitString) × (ℕ × BitString) => z.2.1) :=
      Computable.fst.comp hz2
    have hp : Computable (fun z : (BitString × BitString) × (ℕ × BitString) => z.1.1) :=
      Computable.fst.comp hz1
    have hl : Partrec (fun z : (BitString × BitString) × (ℕ × BitString) =>
        P.lang (z.1.1, q z.1 z.2)) :=
      hP.2.2.2.2.2.1.comp (hp.pair hq)
    refine Partrec.bind (hd.comp hi) ?_
    refine Partrec.bind (hl.comp Computable.fst) ?_
    have hj : Computable (fun r : (((BitString × BitString) × (ℕ × BitString)) × Fin 2) ×
        BitString => r.1.2) := Computable.snd.comp Computable.fst
    have hw : Computable (fun r : (((BitString × BitString) × (ℕ × BitString)) × Fin 2) ×
        BitString => r.2) := Computable.snd
    have hE := he.comp (hj.pair hw)
    have hE' := Computable.ofOption hE
    refine Partrec.of_eq hE' fun r => ?_
    rfl
  obtain ⟨H, hH, hsound, hcomp⟩ :=
    exists_uniform_solution_imp_imp_imp_disj_pdisj_search
      (α := BitString × BitString) (β := ℕ × BitString) (γ := BitString) G hG
  refine ⟨H, hH, ?_, ?_⟩
  · intro p a z hz
    obtain ⟨⟨i, v⟩, hb⟩ := hsound _ _ hz
    simp only [G, Part.mem_bind_iff] at hb
    obtain ⟨j, hj, w, hw, hz'⟩ := hb
    have hz'' : e j w = some z := by simpa using hz'
    simp only [e, Option.bind_eq_some_iff] at hz''
    obtain ⟨⟨t, z'⟩, hu, hif⟩ := hz''
    by_cases hc : t = tag ∧ j = j0
    · rw [ite_eq_left hc] at hif
      obtain rfl : z' = z := Option.some.inj hif
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨i, v, w, Part.eq_some_iff.2 hj, hw, hu⟩
    · rw [ite_eq_right hc] at hif; exact absurd hif (by simp)
  · intro p a i v w z hdi hw hu
    refine hcomp (p, a) (i, v) ?_
    simp only [G]
    rw [Part.dom_iff_mem]
    refine ⟨z, ?_⟩
    refine Part.mem_bind_iff.2 ⟨j0, by rw [hdi]; exact Part.mem_some _, ?_⟩
    refine Part.mem_bind_iff.2 ⟨w, hw, ?_⟩
    simp [e, hu]

/-- Step 3 of the proof of `exists_uniform_solution_imp_imp_imp_disj_pdisj`: the searches
`r₁`, `r₂`, from step 2.  For partial computable `d` and total computable `Q`, there are partial
computable `R₁, R₂ : BitString × BitString →. BitString`.  `R₁ (p, x')` searches all `i`, `v`
with `d i = 1` for an output `w` of `[p](Q i x' v)` with `P.unpair w = some (tag1, z)` and prints
`z`; `R₂ (p, y')` searches all `i`, `u` with `d i = 0` for an output of `[p](Q i u y')` of the form
`[tag0, z]`.  Every output comes from some witness (soundness); a witness gives a defined value
(completeness). -/
private theorem exists_uniform_solution_imp_imp_imp_disj_pdisj_searches
    (P : ProblemCalculus) (hP : P.Admissible) (d : ℕ →. Fin 2) (hd : Partrec d)
    (Q : ℕ → BitString → BitString → BitString)
    (hQ : Computable (fun z : ℕ × BitString × BitString => Q z.1 z.2.1 z.2.2)) :
    ∃ R₁ R₂ : BitString × BitString →. BitString, Partrec R₁ ∧ Partrec R₂ ∧
      (∀ p x' z, z ∈ R₁ (p, x') → ∃ (i : ℕ) (v w : BitString), d i = Part.some 1 ∧
        w ∈ P.lang (p, Q i x' v) ∧ P.unpair w = some (P.tag1, z)) ∧
      (∀ p x' (i : ℕ) (v w z : BitString), d i = Part.some 1 → w ∈ P.lang (p, Q i x' v) →
        P.unpair w = some (P.tag1, z) → (R₁ (p, x')).Dom) ∧
      (∀ p y' z, z ∈ R₂ (p, y') → ∃ (i : ℕ) (u w : BitString), d i = Part.some 0 ∧
        w ∈ P.lang (p, Q i u y') ∧ P.unpair w = some (P.tag0, z)) ∧
      (∀ p y' (i : ℕ) (u w z : BitString), d i = Part.some 0 → w ∈ P.lang (p, Q i u y') →
        P.unpair w = some (P.tag0, z) → (R₂ (p, y')).Dom) := by
  obtain ⟨R₁, hR₁, hS₁, hC₁⟩ := exists_uniform_solution_imp_imp_imp_disj_pdisj_searches_aux
    P hP d hd 1 P.tag1 (fun a b => Q b.1 a.2 b.2)
    (hQ.comp ((Computable.fst.comp Computable.snd).pair
      ((Computable.snd.comp Computable.fst).pair (Computable.snd.comp Computable.snd))))
  obtain ⟨R₂, hR₂, hS₂, hC₂⟩ := exists_uniform_solution_imp_imp_imp_disj_pdisj_searches_aux
    P hP d hd 0 P.tag0 (fun a b => Q b.1 b.2 a.2)
    (hQ.comp ((Computable.fst.comp Computable.snd).pair
      ((Computable.snd.comp Computable.snd).pair (Computable.snd.comp Computable.fst))))
  exact ⟨R₁, R₂, hR₁, hR₂, hS₁, hC₁, hS₂, hC₂⟩

/-- SUV Theorem 242, key step of the lower bound (Section 13.4, printed p. 409).  One program
solves `(((x → y) → y) → (x ∨ y)) → ((x → y) ∨~ (y → x))` for all strings `x`, `y` at once.
Book: with inseparable enumerable `A`, `B` (`exists_partrec_diagonal` with `k = 2`) and the
programs `q_i(u, v)` ("`i ∈ A`: output `v`; `i ∈ B`: output `[s](u)`; `[s](u) = v`: output
`v`"), `q_i(u, y)` (for `i ∈ A`), `q_i(x, v)` (for `i ∈ B`) and `q_i(x, y)` (for all `i`) solve
`(x → y) → y`.  The program `r₁` runs `p` on `q_i(x', v)` (`x'` its input) for `i ∈ B` and all
`v` until an output `[1, z]` appears and prints `z`; `r₂` runs `p` on `q_i(u, y')` for `i ∈ A`
and all `u` until `[0, z]` appears.  If `r₁` fails on `x` and `r₂` on `y`, the tag of
`[p](q_i(x, y))` is a total computable separator of `A` and `B`.  The solution maps `p` to
`[r₁, r₂]`; it does not depend on `x`, `y`. -/
theorem exists_uniform_solution_imp_imp_imp_disj_pdisj (P : ProblemCalculus)
    (hP : P.Admissible) :
    ∃ s : BitString, ∀ x y : BitString,
      s ∈ P.imp (P.imp (P.imp (P.imp {x} {y}) {y}) (P.disj {x} {y}))
        (P.pdisj (P.imp {x} {y}) (P.imp {y} {x})) := by
  obtain ⟨d, hd, hdiag⟩ := exists_partrec_diagonal 2
  obtain ⟨Q, hQ, hQsol⟩ :=
    exists_uniform_solution_imp_imp_imp_disj_pdisj_programs P hP d hd
  obtain ⟨R₁, R₂, hR₁, hR₂, hS₁, hC₁, hS₂, hC₂⟩ :=
    exists_uniform_solution_imp_imp_imp_disj_pdisj_searches P hP d hd Q hQ
  have hGod := hP.2.2.2.2.2
  have hL : Partrec P.lang := hGod.1
  obtain ⟨t₁, ht₁, h₁⟩ := hGod.2 R₁ hR₁
  obtain ⟨t₂, ht₂, h₂⟩ := hGod.2 R₂ hR₂
  have hV : Partrec (fun z : BitString × BitString =>
      (Part.some (P.pair (t₁ z.2) (t₂ z.2)) : Part BitString)) :=
    Computable.partrec (hP.1.comp (ht₁.comp Computable.snd) (ht₂.comp Computable.snd))
  obtain ⟨t₀, ht₀, h₀⟩ := hGod.2 _ hV
  have hne : P.tag0 ≠ P.tag1 := hP.2.2.2.2.1
  have hunp : ∀ a b, P.unpair (P.pair a b) = some (a, b) := hP.2.2.1
  refine ⟨t₀ [], fun x y p hp => ?_⟩
  refine ⟨P.pair (t₁ p) (t₂ p), ?_, ?_⟩
  swap
  · have := h₀ [] p
    rw [this]
    exact Part.mem_some _
  refine ⟨t₁ p, t₂ p, rfl, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  -- the outputs of `p` on solutions of `(x → y) → y`
  have hq : ∀ q ∈ P.imp (P.imp {x} {y}) {y}, ∃ w ∈ P.lang (p, q),
      w = P.pair P.tag0 x ∨ w = P.pair P.tag1 y := by
    intro q hq
    obtain ⟨w, hw, hwL⟩ := hp q hq
    refine ⟨w, hwL, ?_⟩
    rcases hw with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · rw [Set.mem_singleton_iff] at ha; subst ha; exact Or.inl rfl
    · rw [Set.mem_singleton_iff] at hb; subst hb; exact Or.inr rfl
  have hno1 : ¬ (R₁ (p, x)).Dom := by
    intro hdom
    obtain ⟨z, hz⟩ := Part.dom_iff_mem.1 hdom
    obtain ⟨i, v, w, hdi, hwL, hwu⟩ := hS₁ p x z hz
    obtain ⟨w', hw'L, hw'⟩ := hq _ (hQsol x y i x v (Or.inr (Or.inl ⟨hdi, rfl⟩)))
    have hww : w' = w := Part.mem_unique hw'L hwL
    subst hww
    rcases hw' with rfl | rfl
    · rw [hunp] at hwu
      exact hne (Prod.mk.inj (Option.some.inj hwu)).1
    · rw [hunp] at hwu
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hwu)
      apply hn1
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact ⟨y, rfl, by rw [h₁]; exact hz⟩
  have hno2 : ¬ (R₂ (p, y)).Dom := by
    intro hdom
    obtain ⟨z, hz⟩ := Part.dom_iff_mem.1 hdom
    obtain ⟨i, u, w, hdi, hwL, hwu⟩ := hS₂ p y z hz
    obtain ⟨w', hw'L, hw'⟩ := hq _ (hQsol x y i u y (Or.inl ⟨hdi, rfl⟩))
    have hww : w' = w := Part.mem_unique hw'L hwL
    subst hww
    rcases hw' with rfl | rfl
    · rw [hunp] at hwu
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hwu)
      apply hn2
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact ⟨x, rfl, by rw [h₂]; exact hz⟩
    · rw [hunp] at hwu
      exact hne (Prod.mk.inj (Option.some.inj hwu)).1.symm
  -- the separator: the tag of `[p](Q i x y)`
  let g : BitString → Fin 2 := fun w => if (P.unpair w).map Prod.fst = some P.tag1 then 1 else 0
  have hg : Computable g := by
    have hc : Computable (fun w : BitString =>
        decide ((P.unpair w).map Prod.fst = some P.tag1)) :=
      (Primrec.eq.decide.to_comp).comp
        (Computable.option_map hP.2.1 (Computable.fst.comp Computable.snd).to₂)
        (Computable.const _)
    have := Computable.cond hc (Computable.const (1 : Fin 2)) (Computable.const (0 : Fin 2))
    refine Computable.of_eq this fun w => ?_
    simp only [g]
    by_cases h : (P.unpair w).map Prod.fst = some P.tag1 <;> simp [h]
  let u : ℕ →. Fin 2 := fun i => (P.lang (p, Q i x y)).bind (fun w => Part.some (g w))
  have hu : Partrec u := by
    refine Partrec.bind (hL.comp (((Computable.const p).pair
      (hQ.comp (Computable.id.pair (Computable.const (x, y))))))) ?_
    exact (hg.comp Computable.snd).partrec.to₂
  obtain ⟨i, hi⟩ := hdiag u hu
  obtain ⟨w, hwL, hw⟩ := hq _ (hQsol x y i x y (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  have hui : u i = Part.some (g w) := by
    apply Part.eq_some_iff.2
    exact Part.mem_bind_iff.2 ⟨w, hwL, Part.mem_some _⟩
  rw [hui] at hi
  rcases hw with rfl | rfl
  · have hg0 : g (P.pair P.tag0 x) = 0 := by
      simp only [g, hunp, Option.map_some]
      rw [ite_eq_right (fun h => hne (Option.some.inj h))]
    rw [hg0] at hi
    exact hno2 (hC₂ p y i x _ x hi hwL (hunp _ _))
  · have hg1 : g (P.pair P.tag1 y) = 1 := by
      simp [g, hunp]
    rw [hg1] at hi
    exact hno1 (hC₁ p x i y _ y hi hwL (hunp _ _))

/-- SUV Theorem 242 (Section 13.4, printed p. 408), lower bound.
`min (C(x|y), C(y|x)) ≤ C(((x → y) → y) → (x ∨ y)) + O(log n)` for strings of length at most
`n` (the proof gives `O(1)`).  From
`exists_uniform_solution_imp_imp_imp_disj_pdisj`, `problemK_le_of_partrec`, Problem 333
(`problemK_disj_le_pdisj`), `min_le_problemK_disj` and `condK_le_problemK_imp_singleton`.
In particular, for independent random `x`, `y` of length `n` the complexity is close to `n`. -/
theorem min_condK_le_problemK_imp_imp_imp_disj (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y : BitString), x.length ≤ n → y.length ≤ n →
      min (condK D x y) (condK D y x) ≤
        problemK D (P.imp (P.imp (P.imp {x} {y}) {y}) (P.disj {x} {y})) +
          (logSlack k n : ℕ∞) := by
  obtain ⟨s, hs⟩ := exists_uniform_solution_imp_imp_imp_disj_pdisj P hP
  have hLs : Partrec (fun w : BitString => P.lang (s, w)) :=
    hP.2.2.2.2.2.1.comp ((Computable.const s).pair Computable.id)
  obtain ⟨c1, hc1⟩ := problemK_le_of_partrec D hD _ hLs
  obtain ⟨c2, hc2⟩ := problemK_disj_le_pdisj D hD P hP
  obtain ⟨c3, hc3⟩ := min_le_problemK_disj D hD P hP
  obtain ⟨c4, hc4⟩ := condK_le_problemK_imp_singleton D hD P hP
  refine ⟨c1 + c2 + c3 + c4, fun n x y _ _ => ?_⟩
  set A := P.imp (P.imp (P.imp {x} {y}) {y}) (P.disj {x} {y})
  have h1 : problemK D (P.pdisj (P.imp {x} {y}) (P.imp {y} {x})) ≤ problemK D A + c1 :=
    hc1 _ _ (fun p hp => hs x y p hp)
  have hmin : min (condK D x y) (condK D y x) ≤
      min (problemK D (P.imp {x} {y})) (problemK D (P.imp {y} {x})) + c4 := by
    rcases le_total (problemK D (P.imp {x} {y})) (problemK D (P.imp {y} {x})) with h | h
    · rw [min_eq_left h]; exact (min_le_right _ _).trans (hc4 x y)
    · rw [min_eq_right h]; exact (min_le_left _ _).trans (hc4 y x)
  have key : min (condK D x y) (condK D y x) ≤ problemK D A + ((c1 + c2 + c3 + c4 : ℕ) : ℕ∞) :=
    calc min (condK D x y) (condK D y x)
        ≤ min (problemK D (P.imp {x} {y})) (problemK D (P.imp {y} {x})) + c4 := hmin
      _ ≤ (problemK D (P.disj (P.imp {x} {y}) (P.imp {y} {x})) + c3) + c4 := by
          gcongr; exact hc3 _ _
      _ ≤ ((problemK D (P.pdisj (P.imp {x} {y}) (P.imp {y} {x})) + c2) + c3) + c4 := by
          gcongr; exact hc2 _ _
      _ ≤ (((problemK D A + c1) + c2) + c3) + c4 := by gcongr
      _ = problemK D A + ((c1 + c2 + c3 + c4 : ℕ) : ℕ∞) := by push_cast; ring
  refine key.trans ?_
  gcongr
  exact Nat.le_add_left _ _

end InformationLogic
end Kolmogorov
