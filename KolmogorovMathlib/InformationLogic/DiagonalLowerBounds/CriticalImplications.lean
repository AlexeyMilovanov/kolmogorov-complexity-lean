import KolmogorovMathlib.InformationLogic.DiagonalLowerBounds.ImplicationUpperBound

/-!
# Critical Implications

Lower bound on the complexity of a problem built from "critical data": for strings
`u_0, …, u_{k-1}`, the complexity of the implication problem `C.formula` evaluated on the
singletons `{u_i}` is at least `min_m C(u_m | all other u_t)` up to an additive constant.

The main declarations are `condK_others_le_problemK_criticalData` (the general case, SUV
Theorem 244 of Section 13.4) and `condK_others_le_problemK_criticalData_single` (the case of
a single pair, SUV Theorem 243).  The proof is a diagonal argument: a partial computable
diagonal function, programs solving the component problems for a tentative solution, and a
parallel search for a solution that picks out the coordinate `m` realizing the minimum.  The
private lemmas build these programs and prove their correctness.
-/

namespace Kolmogorov
namespace InformationLogic
open ProblemCalculus PFormula

/-- Auxiliary glue lemma for `condK_others_le_problemK_criticalData`: a partial computable
`G (p, o)` maps a program `p` to `x` with `condK D x o ≤ C(p) + O(1)`. -/
private theorem condK_others_le_problemK_criticalData_condK_le (D : Map)
    (hD : isOptimalConditional D) (G : BitString × BitString →. BitString) (hG : Partrec G) :
    ∃ c : ℕ, ∀ p o x, x ∈ G (p, o) → condK D x o ≤ plainK D p + (c : ℕ∞) := by
  let E : Map := fun pr => (D (pr.1, [])).bind (fun p => G (p, pr.2))
  have hE : isDecompressor E :=
    Partrec.bind (hD.1.comp (Computable.fst.pair (Computable.const [])))
      (hG.comp (Computable.snd.pair (Computable.snd.comp Computable.fst))).to₂
  obtain ⟨c, hc⟩ := hD.2 E hE
  refine ⟨c, fun p o x hx => ?_⟩
  refine (hc x o).trans ?_
  gcongr
  change sInf (candidateLengths E x o) ≤ sInf (candidateLengths D p [])
  apply sInf_le_sInf
  rintro n ⟨r, hr, rfl⟩
  exact ⟨r, Part.mem_bind_iff.2 ⟨p, hr, hx⟩, rfl⟩

/-- Step 1 of the proof of `condK_others_le_problemK_criticalData_programs`: the
Gödel translation.  Every partial computable `V : α × BitString →. BitString` (`α` primcodable)
is realised in the language of an admissible calculus by a total computable translation
`q : α → BitString` of the parameter, `[q a](s) = V (a, s)`.  (Encode `a` in unary,
`List.replicate (Encodable.encode a) false`, and apply the Gödel property of `P.lang` to
`V' (c, s) = V (decode |c|, s)`.) -/
private theorem condK_others_le_problemK_criticalData_godel
    (P : ProblemCalculus) (hP : P.Admissible) {α : Type} [Primcodable α]
    (V : α × BitString →. BitString) (hV : Partrec V) :
    ∃ q : α → BitString, Computable q ∧
      ∀ (a : α) (s : BitString), P.lang (q a, s) = V (a, s) := by
  let V' : Map := fun r =>
    ((Encodable.decode (α := α) r.1.length : Option α) : Part α).bind (fun a => V (a, r.2))
  have hV' : Partrec V' := by
    refine Partrec.bind (Computable.ofOption
      (Computable.decode.comp (Computable.list_length.comp Computable.fst))) ?_
    exact hV.comp ((Computable.snd).pair (Computable.snd.comp Computable.fst)) |>.to₂
  obtain ⟨t, ht, hts⟩ := hP.2.2.2.2.2.2 V' hV'
  refine ⟨fun a => t (List.replicate (Encodable.encode a) false), ?_, ?_⟩
  · refine ht.comp ?_
    exact (Primrec.list_replicate.to_comp.comp (Computable.encode)
      (Computable.const false))
  · intro a s
    rw [hts]
    simp [V']

/-- The right-nested pair `[a₁, [a₂, … a_n]]` of a list of strings (`[a]` for one string);
auxiliary definition for `condK_others_le_problemK_criticalData_race`. -/
private def condK_others_le_problemK_criticalData_programs_nest (P : ProblemCalculus)
    (l : List BitString) : BitString :=
  (l.foldr (fun a r => some (r.elim a (P.pair a))) none).getD []

/-- The list of the elements of the right-nested disjunction of the singletons of a list of
strings, in the order of the disjuncts. -/
private def condK_others_le_problemK_criticalData_programs_ylist (P : ProblemCalculus)
    (l : List BitString) : List BitString :=
  l.foldr (fun a r => if r = [] then [a] else P.pair P.tag0 a :: r.map (P.pair P.tag1)) []

/-- The indices of a finset of variables, in increasing order. -/
private def condK_others_le_problemK_criticalData_programs_finIds {k : ℕ}
    (I : Finset (Fin k)) : List (Fin k) :=
  (List.finRange k).filter (fun i => decide (i ∈ I))

private theorem condK_others_le_problemK_criticalData_programs_nest_single
    (P : ProblemCalculus) (a : BitString) :
    condK_others_le_problemK_criticalData_programs_nest P [a] = a := by
  simp [condK_others_le_problemK_criticalData_programs_nest]

private theorem condK_others_le_problemK_criticalData_programs_nest_cons_cons
    (P : ProblemCalculus) (a b : BitString) (l : List BitString) :
    condK_others_le_problemK_criticalData_programs_nest P (a :: b :: l) =
      P.pair a (condK_others_le_problemK_criticalData_programs_nest P (b :: l)) := by
  simp [condK_others_le_problemK_criticalData_programs_nest, List.foldr]

private theorem condK_others_le_problemK_criticalData_programs_ylist_cons
    (P : ProblemCalculus) (a : BitString) (l : List BitString) :
    condK_others_le_problemK_criticalData_programs_ylist P (a :: l) =
      if condK_others_le_problemK_criticalData_programs_ylist P l = [] then [a]
      else P.pair P.tag0 a ::
        (condK_others_le_problemK_criticalData_programs_ylist P l).map (P.pair P.tag1) :=
  rfl

private theorem condK_others_le_problemK_criticalData_programs_ylist_ne_nil
    (P : ProblemCalculus) (l : List BitString) (hl : l ≠ []) :
    condK_others_le_problemK_criticalData_programs_ylist P l ≠ [] := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a l =>
    rw [condK_others_le_problemK_criticalData_programs_ylist_cons]
    split_ifs <;> simp

private theorem condK_others_le_problemK_criticalData_programs_conj_mem
    (P : ProblemCalculus) {k : ℕ} (dd : PFormula (Fin k)) (u : Fin k → BitString) :
    ∀ L : List (Fin k), L ≠ [] →
      condK_others_le_problemK_criticalData_programs_nest P (L.map u) ∈
        (conjList dd (L.map PFormula.var)).eval P (fun j => {u j}) := by
  intro L
  induction L with
  | nil => intro h; exact absurd rfl h
  | cons a L ih =>
    intro _
    cases L with
    | nil =>
      simp [condK_others_le_problemK_criticalData_programs_nest_single, conjList,
        PFormula.eval]
    | cons b L =>
      simp only [List.map_cons, conjList, PFormula.eval, ProblemCalculus.conj,
        condK_others_le_problemK_criticalData_programs_nest_cons_cons]
      refine Set.mem_image2.2 ⟨_, rfl, _, ?_, rfl⟩
      simpa using ih (by simp)

private theorem condK_others_le_problemK_criticalData_programs_disj_eq
    (P : ProblemCalculus) {k : ℕ} (dd : PFormula (Fin k)) (u : Fin k → BitString) :
    ∀ L : List (Fin k), L ≠ [] →
      (disjList dd (L.map PFormula.var)).eval P (fun j => {u j}) =
        {y | y ∈ condK_others_le_problemK_criticalData_programs_ylist P (L.map u)} := by
  intro L
  induction L with
  | nil => intro h; exact absurd rfl h
  | cons a L ih =>
    intro _
    cases L with
    | nil =>
      ext y
      simp [disjList, PFormula.eval, condK_others_le_problemK_criticalData_programs_ylist]
    | cons b L =>
      have hne := condK_others_le_problemK_criticalData_programs_ylist_ne_nil P
        ((b :: L).map u) (by simp)
      have ih' := ih (by simp)
      simp only [List.map_cons, disjList, PFormula.eval] at ih' hne ⊢
      rw [ih', condK_others_le_problemK_criticalData_programs_ylist_cons P (u a)
        (u b :: L.map u), ite_eq_right hne]
      ext y
      simp [ProblemCalculus.disj]

private theorem condK_others_le_problemK_criticalData_programs_nest_computable
    (P : ProblemCalculus) (hP : P.Admissible) {γ : Type} [Primcodable γ]
    {f : γ → List BitString} (hf : Computable f) :
    Computable (fun a => condK_others_le_problemK_criticalData_programs_nest P (f a)) := by
  have hh : Computable₂ (fun (_ : γ) (p : BitString × Option BitString) =>
      (some (p.2.elim p.1 (P.pair p.1)) : Option BitString)) := by
    have h0 : Computable (fun x : γ × (BitString × Option BitString) =>
        x.2.2.elim x.2.1 (P.pair x.2.1)) := by
      refine (Computable.option_casesOn (o := fun x : γ × (BitString × Option BitString) => x.2.2)
        (f := fun x => x.2.1) (g := fun x r => P.pair x.2.1 r)
        (Computable.snd.comp Computable.snd) (Computable.fst.comp Computable.snd)
        (hP.1.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
          Computable.snd).to₂).of_eq ?_
      intro x
      cases x.2.2 <;> rfl
    exact (Computable.option_some.comp h0).to₂
  exact Computable.option_getD (Computable.list_foldr hf (Computable.const none) hh)
    (Computable.const [])

private theorem condK_others_le_problemK_criticalData_programs_ylist_computable
    (P : ProblemCalculus) (hP : P.Admissible) {γ : Type} [Primcodable γ]
    {f : γ → List BitString} (hf : Computable f) :
    Computable (fun a => condK_others_le_problemK_criticalData_programs_ylist P (f a)) := by
  have hh : Computable₂ (fun (_ : γ) (p : BitString × List BitString) =>
      (if p.2 = [] then [p.1] else P.pair P.tag0 p.1 :: p.2.map (P.pair P.tag1) :
        List BitString)) := by
    have hc : Computable (fun x : γ × (BitString × List BitString) => decide (x.2.2 = [])) :=
      Primrec.eq.decide.to_comp.comp (Computable.snd.comp Computable.snd) (Computable.const [])
    have h1 : Computable (fun x : γ × (BitString × List BitString) => [x.2.1]) :=
      Computable.list_cons.comp (Computable.fst.comp Computable.snd) (Computable.const [])
    have h2 : Computable (fun x : γ × (BitString × List BitString) =>
        P.pair P.tag0 x.2.1 :: x.2.2.map (P.pair P.tag1)) := by
      refine Computable.list_cons.comp (hP.1.comp (Computable.const P.tag0)
        (Computable.fst.comp Computable.snd)) ?_
      refine Computable.list_map (Computable.snd.comp Computable.snd) ?_
      exact (hP.1.comp (Computable.const P.tag1) Computable.snd).to₂
    refine (Computable.cond hc h1 h2).to₂.of_eq ?_
    intro a
    by_cases h : a.2.2 = [] <;> simp [h]
  exact (Computable.list_foldr hf (Computable.const []) hh).of_eq (fun a => rfl)

private theorem condK_others_le_problemK_criticalData_programs_decide_mem
    {γ β : Type} [Primcodable γ] [Primcodable β] [Inhabited β] [DecidableEq β]
    {f : γ → List β} {g : γ → β} (hf : Computable f) (hg : Computable g) :
    Computable (fun a => decide (g a ∈ f a)) := by
  have hp : Computable₂ (fun (a : γ) (b : β) => decide (g a = b)) :=
    (primrec_decideEq.to_comp.comp (hg.comp Computable.fst) Computable.snd).to₂
  refine (computable_list_any hf hp).of_eq (fun a => ?_)
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  simp

/-- The acceptance relation of the race `V ((l, i, v), s)` of the book (`Il l`, `Jl l` the
lists of the indices of `I_l`, `J_l`): (a) `y ∈ Y_l(v)` and `y = [s](x_l(v))`; (b) `d i = m ∈ I_l`
and `y` is the first element of `Y_l(v)`; (c) `d i = m ∉ I_l` and `y = [s](x_l(v))`. -/
private def condK_others_le_problemK_criticalData_programs_rel (P : ProblemCalculus)
    {k : ℕ} (d : ℕ →. Fin k) (Il Jl : ℕ → List (Fin k))
    (w : ℕ × ℕ × (Fin k → BitString)) (s y : BitString) : Prop :=
  (y ∈ condK_others_le_problemK_criticalData_programs_ylist P ((Jl w.1).map w.2.2) ∧
    y ∈ P.lang (s, condK_others_le_problemK_criticalData_programs_nest P
      ((Il w.1).map w.2.2))) ∨
  (∃ m : Fin k, m ∈ d w.2.1 ∧ m ∈ Il w.1 ∧
    y = (condK_others_le_problemK_criticalData_programs_ylist P
      ((Jl w.1).map w.2.2)).headD []) ∨
  (∃ m : Fin k, m ∈ d w.2.1 ∧ m ∉ Il w.1 ∧
    y ∈ P.lang (s, condK_others_le_problemK_criticalData_programs_nest P
      ((Il w.1).map w.2.2)))

private theorem condK_others_le_problemK_criticalData_programs_select
    (P : ProblemCalculus) (hP : P.Admissible) {k : ℕ} (hk : 0 < k)
    (d : ℕ →. Fin k) (hd : Partrec d) (Il Jl : ℕ → List (Fin k))
    (hIl : Computable Il) (hJl : Computable Jl) :
    ∃ V : (ℕ × ℕ × (Fin k → BitString)) × BitString →. BitString, Partrec V ∧
      ∀ (w : ℕ × ℕ × (Fin k → BitString)) (s y : BitString),
        (y ∈ V (w, s) →
          condK_others_le_problemK_criticalData_programs_rel P d Il Jl w s y) ∧
        (condK_others_le_problemK_criticalData_programs_rel P d Il Jl w s y →
          (V (w, s)).Dom) := by
  have : Inhabited (Fin k) := ⟨⟨0, hk⟩⟩
  have hL : Partrec P.lang := hP.2.2.2.2.2.1
  have hv : Computable₂ (fun (w : ℕ × ℕ × (Fin k → BitString)) (t : Fin k) => w.2.2 t) :=
    Computable.fin_app.comp (Computable.snd.comp Computable.snd |>.comp Computable.fst)
      Computable.snd
  have hXs : Computable (fun w : ℕ × ℕ × (Fin k → BitString) => (Il w.1).map w.2.2) :=
    Computable.list_map (hIl.comp Computable.fst) hv
  have hYs : Computable (fun w : ℕ × ℕ × (Fin k → BitString) => (Jl w.1).map w.2.2) :=
    Computable.list_map (hJl.comp Computable.fst) hv
  have hX := condK_others_le_problemK_criticalData_programs_nest_computable P hP hXs
  have hY := condK_others_le_problemK_criticalData_programs_ylist_computable P hP hYs
  -- the graph of `[s](x_l(v))`
  have hg1 : IsRE (fun z : ((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString =>
      z.2 ∈ P.lang (z.1.2, condK_others_le_problemK_criticalData_programs_nest P
        ((Il z.1.1.1).map z.1.1.2.2))) :=
    (Partrec.graphIsRe P.lang hL).comp_computable
      (g := fun z : ((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString =>
        ((z.1.2, condK_others_le_problemK_criticalData_programs_nest P
          ((Il z.1.1.1).map z.1.1.2.2)), z.2))
      (((Computable.snd.comp Computable.fst).pair
        (hX.comp (Computable.fst.comp Computable.fst))).pair Computable.snd)
  -- the graph of `d i`
  have hg2 : IsRE (fun p : (((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString) × Fin k =>
      p.2 ∈ d p.1.1.1.2.1) :=
    (Partrec.graphIsRe d hd).comp_computable
      (g := fun p : (((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString) × Fin k =>
        (p.1.1.1.2.1, p.2))
      ((Computable.fst.comp (Computable.snd.comp (Computable.fst.comp
        (Computable.fst.comp Computable.fst)))).pair Computable.snd)
  have hmemI : Computable (fun p : (((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString) ×
      Fin k => decide (p.2 ∈ Il p.1.1.1.1)) :=
    condK_others_le_problemK_criticalData_programs_decide_mem
      (f := fun p : (((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString) × Fin k =>
        Il p.1.1.1.1) (g := fun p => p.2)
      (hIl.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))))
      Computable.snd
  have hA : IsRE (fun z : ((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString =>
      z.2 ∈ condK_others_le_problemK_criticalData_programs_ylist P
        ((Jl z.1.1.1).map z.1.1.2.2) ∧
      z.2 ∈ P.lang (z.1.2, condK_others_le_problemK_criticalData_programs_nest P
        ((Il z.1.1.1).map z.1.1.2.2))) := by
    have p1 : Computable (fun z : ((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString =>
        decide (z.2 ∈ condK_others_le_problemK_criticalData_programs_ylist P
          ((Jl z.1.1.1).map z.1.1.2.2))) :=
      condK_others_le_problemK_criticalData_programs_decide_mem
        (f := fun z : ((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString =>
          condK_others_le_problemK_criticalData_programs_ylist P
            ((Jl z.1.1.1).map z.1.1.2.2)) (g := fun z => z.2)
        (hY.comp (Computable.fst.comp Computable.fst)) Computable.snd |>.of_eq
          (fun _ => by congr)
    refine (hg1.and_computable p1).of_iff (fun z => ?_)
    simp
  have hB : IsRE (fun z : ((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString =>
      ∃ m : Fin k, m ∈ d z.1.1.2.1 ∧ m ∈ Il z.1.1.1 ∧
        z.2 = (condK_others_le_problemK_criticalData_programs_ylist P
          ((Jl z.1.1.1).map z.1.1.2.2)).headD []) := by
    refine IsRE.exists_encodable (R := fun (z : ((ℕ × ℕ × (Fin k → BitString)) × BitString) ×
        BitString) (m : Fin k) => m ∈ d z.1.1.2.1 ∧ m ∈ Il z.1.1.1 ∧
        z.2 = (condK_others_le_problemK_criticalData_programs_ylist P
          ((Jl z.1.1.1).map z.1.1.2.2)).headD []) ?_
    have hhd : Computable (fun p : (((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString) ×
        Fin k => (condK_others_le_problemK_criticalData_programs_ylist P
          ((Jl p.1.1.1.1).map p.1.1.1.2.2)).headD []) :=
      (Computable.option_getD (Primrec.list_head?.to_comp.comp
        (hY.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))))
        (Computable.const [])).of_eq (fun p => by simp [List.headD_eq_head?_getD])
    have hp : Computable (fun p : (((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString) ×
        Fin k => decide (p.2 ∈ Il p.1.1.1.1) &&
          decide (p.1.2 = (condK_others_le_problemK_criticalData_programs_ylist P
            ((Jl p.1.1.1.1).map p.1.1.1.2.2)).headD [])) :=
      Primrec.and.to_comp.comp hmemI
        (primrec_decideEq.to_comp.comp (Computable.snd.comp Computable.fst) hhd)
    refine (hg2.and_computable hp).of_iff (fun p => ?_)
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    tauto
  have hC : IsRE (fun z : ((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString =>
      ∃ m : Fin k, m ∈ d z.1.1.2.1 ∧ m ∉ Il z.1.1.1 ∧
        z.2 ∈ P.lang (z.1.2, condK_others_le_problemK_criticalData_programs_nest P
          ((Il z.1.1.1).map z.1.1.2.2))) := by
    refine IsRE.exists_encodable (R := fun (z : ((ℕ × ℕ × (Fin k → BitString)) × BitString) ×
        BitString) (m : Fin k) => m ∈ d z.1.1.2.1 ∧ m ∉ Il z.1.1.1 ∧
        z.2 ∈ P.lang (z.1.2, condK_others_le_problemK_criticalData_programs_nest P
          ((Il z.1.1.1).map z.1.1.2.2))) ?_
    have hg1' : IsRE (fun p : (((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString) ×
        Fin k => p.1.2 ∈ P.lang (p.1.1.2, condK_others_le_problemK_criticalData_programs_nest
          P ((Il p.1.1.1.1).map p.1.1.1.2.2))) :=
      hg1.comp_computable
        (g := fun p : (((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString) × Fin k => p.1)
        Computable.fst
    have hp : Computable (fun p : (((ℕ × ℕ × (Fin k → BitString)) × BitString) × BitString) ×
        Fin k => !decide (p.2 ∈ Il p.1.1.1.1)) :=
      Primrec.not.to_comp.comp hmemI
    refine ((hg1'.and hg2).and_computable hp).of_iff (fun p => ?_)
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    tauto
  have hRel := (hA.or (hB.or hC))
  obtain ⟨F, hF, hFsound, hFcomp⟩ :=
    problemK_imp_imp_imp_disj_le_min_condK_select
      (R := fun (a : (ℕ × ℕ × (Fin k → BitString)) × BitString) (y : BitString) =>
        condK_others_le_problemK_criticalData_programs_rel P d Il Jl a.1 a.2 y) hRel
  exact ⟨F, hF, fun w s y => ⟨hFsound (w, s) y, hFcomp (w, s) y⟩⟩

/-- Step 2 of the proof of `condK_others_le_problemK_criticalData_programs`: the
race of the book, as one partial computable function.  For the critical data `C` (pairs
`(I_l, J_l)`, `l < N`, in the list `C.pairs`) and `d : ℕ →. Fin k` partial computable there is a
partial computable `V ((l, i, v), s)` (the program `s` is the input) such that: whenever `v = u`,
or `d i = m` is defined and `v` differs from `u` at most at `m`, and `l < N`, and `s` is a
solution of `X_l(u) → Y_l(u)` (`X_l` the conjunction of the singletons `{u t}`, `t ∈ I_l`, `Y_l`
the disjunction of `{u t}`, `t ∈ J_l`, both nested to the right as in `C.premise`, `C.target`),
`V ((l, i, v), s)` is defined with a value in `Y_l(u)`.
Book: `V ((l,i,v), s)` waits, in parallel, (a) for `[s](x_l(v))` to be an element of `Y_l(v)`
(`x_l(v)` the nested pair of the `v t`, `t ∈ I_l`, the tentative solution of `X_l`), which is
then returned; (b) for `d i` to converge to some `m ∈ I_l`, then the first element of `Y_l(v)`
(the disjunct of the least `t ∈ J_l`) is returned; (c) for `d i` to converge to some `m ∉ I_l`
and `[s](x_l(v))` to converge, then that value is returned.  (Implemented through the RE
relation "(a) or (b) or (c) holds for `y`" and the partial computable selector of an RE relation,
`problemK_imp_imp_imp_disj_le_min_condK_select`.)  Correctness: if `v = u`, (a) fires with the
value of `[s](x_l(u))`, and (b), (c) give elements of `Y_l(u)`.  If `d i = m` and `v` differs from
`u` at most at `m`: for `m ∈ I_l` we have `m ∉ J_l` (disjointness), hence `Y_l(v) = Y_l(u)` and
(a), (b) are correct (and (b) fires); for `m ∉ I_l` we have `x_l(v) = x_l(u)`, so
`[s](x_l(v)) ∈ Y_l(u)` and (a), (c) are correct (and (c) fires). -/
private theorem condK_others_le_problemK_criticalData_race
    (P : ProblemCalculus) (hP : P.Admissible) {k : ℕ} (C : CriticalData k)
    (d : ℕ →. Fin k) (hd : Partrec d) :
    ∃ V : (ℕ × ℕ × (Fin k → BitString)) × BitString →. BitString, Partrec V ∧
      ∀ (u : Fin k → BitString) (i : ℕ) (v : Fin k → BitString) (l : ℕ)
        (hl : l < C.pairs.length),
        (v = u ∨ ∃ m : Fin k, d i = Part.some m ∧ ∀ t, t ≠ m → v t = u t) →
        ∀ s ∈ P.imp ((C.premise C.pairs[l].1).eval P (fun j => {u j}))
            ((C.target C.pairs[l].2).eval P (fun j => {u j})),
          ∃ y ∈ (C.target C.pairs[l].2).eval P (fun j => {u j}), y ∈ V ((l, i, v), s) := by
  have hIlc : Computable (fun l : ℕ => (C.pairs.map
      (fun p => condK_others_le_problemK_criticalData_programs_finIds p.1)).getD l []) :=
    ((Primrec.list_getD []).comp (Primrec.const _) Primrec.id).to_comp
  have hJlc : Computable (fun l : ℕ => (C.pairs.map
      (fun p => condK_others_le_problemK_criticalData_programs_finIds p.2)).getD l []) :=
    ((Primrec.list_getD []).comp (Primrec.const _) Primrec.id).to_comp
  obtain ⟨V, hV, hVspec⟩ := condK_others_le_problemK_criticalData_programs_select P hP C.pos
    d hd _ _ hIlc hJlc
  refine ⟨V, hV, ?_⟩
  intro u i v l hl hv s hs
  have hIl' : (C.pairs.map
      (fun p => condK_others_le_problemK_criticalData_programs_finIds p.1)).getD l [] =
      condK_others_le_problemK_criticalData_programs_finIds C.pairs[l].1 := by
    simp [List.getD_eq_getElem?_getD, hl]
  have hJl' : (C.pairs.map
      (fun p => condK_others_le_problemK_criticalData_programs_finIds p.2)).getD l [] =
      condK_others_le_problemK_criticalData_programs_finIds C.pairs[l].2 := by
    simp [List.getD_eq_getElem?_getD, hl]
  have hmem : C.pairs[l] ∈ C.pairs := List.getElem_mem hl
  have hI1 := C.left_nonempty _ hmem
  have hJ1 := C.right_nonempty _ hmem
  have hdisj := C.disjoint _ hmem
  generalize C.pairs[l] = p at *
  -- the data
  have hmemF : ∀ (I : Finset (Fin k)) (t : Fin k),
      t ∈ condK_others_le_problemK_criticalData_programs_finIds I ↔ t ∈ I := by
    intro I t
    simp [condK_others_le_problemK_criticalData_programs_finIds]
  have hneF : ∀ I : Finset (Fin k), I.Nonempty →
      condK_others_le_problemK_criticalData_programs_finIds I ≠ [] := by
    intro I ⟨t, ht⟩ h
    have := (hmemF I t).2 ht
    rw [h] at this
    simp at this
  have hXmem : condK_others_le_problemK_criticalData_programs_nest P
      ((condK_others_le_problemK_criticalData_programs_finIds p.1).map u) ∈
        (C.premise p.1).eval P (fun j => {u j}) :=
    condK_others_le_problemK_criticalData_programs_conj_mem P C.dflt u _ (hneF _ hI1)
  have hYeq : (C.target p.2).eval P (fun j => {u j}) = {y | y ∈
      condK_others_le_problemK_criticalData_programs_ylist P
        ((condK_others_le_problemK_criticalData_programs_finIds p.2).map u)} :=
    condK_others_le_problemK_criticalData_programs_disj_eq P C.dflt u _ (hneF _ hJ1)
  obtain ⟨y0, hy0Y, hy0L⟩ := hs _ hXmem
  rw [hYeq] at hy0Y
  rw [hYeq]
  simp only [Set.mem_ofPred_eq] at hy0Y ⊢
  -- the relation
  have hrel := fun y => (hVspec (l, i, v) s y)
  simp only [condK_others_le_problemK_criticalData_programs_rel, hIl', hJl', hmemF] at hrel
  have hmemhead : ∀ w : List (Fin k), (condK_others_le_problemK_criticalData_programs_ylist
      P (w.map v)).headD [] ∈ condK_others_le_problemK_criticalData_programs_ylist
      P (w.map v) ∨ w = [] := by
    intro w
    by_cases hw : w = []
    · exact Or.inr hw
    · left
      have hne := condK_others_le_problemK_criticalData_programs_ylist_ne_nil P (w.map v)
        (by simpa using hw)
      obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil hne
      rw [ht]; simp
  have hhead := (hmemhead (condK_others_le_problemK_criticalData_programs_finIds
      p.2)).resolve_right
    (hneF _ hJ1)
  have hdom : (V ((l, i, v), s)).Dom := by
    rcases hv with rfl | ⟨m, hm, hvm⟩
    · exact ((hrel y0).2 (Or.inl ⟨hy0Y, hy0L⟩))
    · have hmd : m ∈ d i := by rw [hm]; exact Part.mem_some m
      by_cases hmI : m ∈ p.1
      · exact (hrel _).2 (Or.inr (Or.inl ⟨m, hmd, hmI, rfl⟩))
      · have hXeq : (condK_others_le_problemK_criticalData_programs_finIds p.1).map v =
            (condK_others_le_problemK_criticalData_programs_finIds p.1).map u :=
          List.map_congr_left (fun t ht => hvm t (fun h => hmI (h ▸ (hmemF _ _).1 ht)))
        exact (hrel y0).2 (Or.inr (Or.inr ⟨m, hmd, hmI, by rw [hXeq]; exact hy0L⟩))
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 hdom
  refine ⟨y, ?_, hy⟩
  have hsound := (hrel y).1 hy
  rcases hv with rfl | ⟨m, hm, hvm⟩
  · rcases hsound with ⟨h1, _⟩ | ⟨m', _, _, h⟩ | ⟨m', _, _, h⟩
    · exact h1
    · rw [h]; exact hhead
    · rw [Part.mem_unique h hy0L]; exact hy0Y
  · have hmd : m ∈ d i := by rw [hm]; exact Part.mem_some m
    by_cases hmI : m ∈ p.1
    · have hJeq : (condK_others_le_problemK_criticalData_programs_finIds p.2).map v =
          (condK_others_le_problemK_criticalData_programs_finIds p.2).map u :=
        List.map_congr_left (fun t ht => hvm t (fun h =>
          (Finset.disjoint_left.1 hdisj hmI) (h ▸ (hmemF _ _).1 ht)))
      rw [hJeq] at hsound hhead
      rcases hsound with ⟨h1, _⟩ | ⟨m', _, _, h⟩ | ⟨m', hm', hm'I, h⟩
      · exact h1
      · rw [h]; exact hhead
      · exact absurd (Part.mem_unique hm' hmd ▸ hmI) hm'I
    · have hXeq : (condK_others_le_problemK_criticalData_programs_finIds p.1).map v =
          (condK_others_le_problemK_criticalData_programs_finIds p.1).map u :=
        List.map_congr_left (fun t ht => hvm t (fun h => hmI (h ▸ (hmemF _ _).1 ht)))
      rw [hXeq] at hsound
      rcases hsound with ⟨_, h2⟩ | ⟨m', hm', hm'I, _⟩ | ⟨m', _, _, h⟩
      · rw [Part.mem_unique h2 hy0L]; exact hy0Y
      · exact absurd (Part.mem_unique hm' hmd ▸ hm'I) hmI
      · rw [Part.mem_unique h hy0L]; exact hy0Y

/-- The nested pair `[q off, [q (off+1), …]]` of `n` programs (for `n = 1` just `q off`),
auxiliary definition for `condK_others_le_problemK_criticalData_pack`. -/
private def condK_others_le_problemK_criticalData_programs_packQ (P : ProblemCalculus)
    {k : ℕ} (q : ℕ → ℕ → (Fin k → BitString) → BitString) :
    ℕ → ℕ → ℕ → (Fin k → BitString) → BitString
  | _, 0, _, _ => []
  | off, 1, i, v => q off i v
  | off, n + 2, i, v => P.pair (q off i v)
      (condK_others_le_problemK_criticalData_programs_packQ P q (off + 1) (n + 1) i v)

private theorem condK_others_le_problemK_criticalData_programs_packQ_computable
    (P : ProblemCalculus) (hP : P.Admissible) {k : ℕ}
    (q : ℕ → ℕ → (Fin k → BitString) → BitString)
    (hq : Computable (fun x : ℕ × ℕ × (Fin k → BitString) => q x.1 x.2.1 x.2.2)) :
    ∀ (n off : ℕ), Computable (fun x : ℕ × (Fin k → BitString) =>
      condK_others_le_problemK_criticalData_programs_packQ P q off n x.1 x.2) := by
  intro n
  induction n with
  | zero => intro off; exact Computable.const []
  | succ n ih =>
    intro off
    have hq' : Computable (fun x : ℕ × (Fin k → BitString) => q off x.1 x.2) :=
      hq.comp ((Computable.const off).pair Computable.id)
    cases n with
    | zero => exact hq'
    | succ n =>
      exact hP.1.comp hq' (ih (off + 1))

private theorem condK_others_le_problemK_criticalData_programs_packQ_mem
    (P : ProblemCalculus) {k : ℕ} (C : CriticalData k)
    (q : ℕ → ℕ → (Fin k → BitString) → BitString) (u : Fin k → BitString) (i : ℕ)
    (v : Fin k → BitString) :
    ∀ (ps : List (Finset (Fin k) × Finset (Fin k))) (off : ℕ), ps ≠ [] →
      (∀ (j : ℕ) (hj : j < ps.length), q (off + j) i v ∈
        (PFormula.imp (PFormula.imp (C.premise ps[j].1) (C.target ps[j].2))
          (C.target ps[j].2)).eval P (fun j => {u j})) →
      condK_others_le_problemK_criticalData_programs_packQ P q off ps.length i v ∈
        (conjList C.dflt (ps.map fun p =>
          imp (imp (C.premise p.1) (C.target p.2)) (C.target p.2))).eval P (fun j => {u j}) := by
  intro ps
  induction ps with
  | nil => intro off h; exact absurd rfl h
  | cons p ps ih =>
    intro off _ h
    cases ps with
    | nil =>
      have := h 0 (by simp)
      simpa [condK_others_le_problemK_criticalData_programs_packQ, conjList] using this
    | cons p' ps =>
      simp only [List.length_cons, List.map_cons, conjList,
        condK_others_le_problemK_criticalData_programs_packQ, PFormula.eval,
        ProblemCalculus.conj]
      refine Set.mem_image2.2 ⟨_, ?_, _, ?_, rfl⟩
      · exact h 0 (by simp)
      · have := ih (off + 1) (by simp) (fun j hj => by
          have := h (j + 1) (by rw [List.length_cons]; exact Nat.succ_lt_succ hj)
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)
        simpa using this

/-- Step 3 of the proof of `condK_others_le_problemK_criticalData_programs`:
packing the programs `q_l`, `l < N`, into one solution of the premise.  For a computable family
`q l i v` of programs there is a total computable `Q i v` (the nested pair
`[q 0 i v, …, q (N-1) i v]`, right-nested as `conjList`; for `N = 1` just `q 0 i v`) such that
if every `q l i v`, `l < N`, is a solution of `(X_l → Y_l) → Y_l` evaluated at the singletons
`{u t}`, then `Q i v` is a solution of `((X₁ → Y₁) → Y₁) ∧ … ∧ ((X_N → Y_N) → Y_N)` at the
singletons `{u t}`.  (Induction on the list `C.pairs`, `ProblemCalculus.conj = image2 pair`;
`Q` is computable by `list_foldr`.) -/
private theorem condK_others_le_problemK_criticalData_pack
    (P : ProblemCalculus) (hP : P.Admissible) {k : ℕ} (C : CriticalData k)
    (q : ℕ → ℕ → (Fin k → BitString) → BitString)
    (hq : Computable (fun x : ℕ × ℕ × (Fin k → BitString) => q x.1 x.2.1 x.2.2)) :
    ∃ Q : ℕ → (Fin k → BitString) → BitString,
      Computable (fun x : ℕ × (Fin k → BitString) => Q x.1 x.2) ∧
      ∀ (u : Fin k → BitString) (i : ℕ) (v : Fin k → BitString),
        (∀ (l : ℕ) (hl : l < C.pairs.length), q l i v ∈
          (PFormula.imp (PFormula.imp (C.premise C.pairs[l].1) (C.target C.pairs[l].2))
            (C.target C.pairs[l].2)).eval P (fun j => {u j})) →
        Q i v ∈ (conjList C.dflt (C.pairs.map fun p =>
          imp (imp (C.premise p.1) (C.target p.2)) (C.target p.2))).eval P (fun j => {u j}) := by
  refine ⟨fun i v => condK_others_le_problemK_criticalData_programs_packQ P q 0
    C.pairs.length i v,
    condK_others_le_problemK_criticalData_programs_packQ_computable P hP q hq
      C.pairs.length 0, ?_⟩
  intro u i v h
  exact condK_others_le_problemK_criticalData_programs_packQ_mem P C q u i v C.pairs 0
    C.pairs_ne_nil (fun j hj => by simpa using h j hj)

/-- Step 1 of the proof of `condK_others_le_problemK_criticalData`: the programs
`q_{1,i}(v), …, q_{N,i}(v)` of the book, packed into one solution of the premise.  For a partial
computable `d : ℕ →. Fin k` there is a total computable `Q i v` (`i : ℕ`, `v : Fin k → BitString`
a tentative tuple) such that, for every `u`, whenever `v = u` or `d i = m` is defined and `v`
differs from `u` at most at the coordinate `m`, the string `Q i v` is a solution of the premise
`((X₁ → Y₁) → Y₁) ∧ … ∧ ((X_N → Y_N) → Y_N)` of the critical implication evaluated at the
singletons `{u t}` (the nested pair `[q₁, …, q_N]` of programs `q_l` solving `(X_l → Y_l) → Y_l`).
Book: `q_{l,i}(v)` on input `s` waits, in parallel, for the output of `[s]` on the tentative
solution `[v_t]_{t ∈ I_l}` of `X_l` to be of the form `[t, v_t]`, `t ∈ J_l`, and for `d(i)` to
converge to some `m ∈ I_l`; in the first case it returns that output, in the second case
`[t₀, v_{t₀}]` for the least `t₀ ∈ J_l`.  The programs are produced from `(l, i, v)` by the Gödel
translation of `P.lang`.  Correctness: if `v = u`, or `d i = m` and `v` differs from `u` at most
at `m`, then for every `s ∈ X_l(u) → Y_l(u)` the output is in `Y_l(u)` (if `m ∉ I_l` then
`x_l(v) = x_l(u)`; if `m ∈ I_l` then `m ∉ J_l`, so `v_{t₀} = u_{t₀}`). -/
private theorem condK_others_le_problemK_criticalData_programs
    (P : ProblemCalculus) (hP : P.Admissible) {k : ℕ} (C : CriticalData k)
    (d : ℕ →. Fin k) (hd : Partrec d) :
    ∃ Q : ℕ → (Fin k → BitString) → BitString,
      Computable (fun x : ℕ × (Fin k → BitString) => Q x.1 x.2) ∧
      ∀ (u : Fin k → BitString) (i : ℕ) (v : Fin k → BitString),
        (v = u ∨ ∃ m : Fin k, d i = Part.some m ∧ ∀ t, t ≠ m → v t = u t) →
        Q i v ∈ (conjList C.dflt (C.pairs.map fun p =>
          imp (imp (C.premise p.1) (C.target p.2)) (C.target p.2))).eval P (fun j => {u j}) := by
  obtain ⟨V, hV, hVspec⟩ := condK_others_le_problemK_criticalData_race
    P hP C d hd
  obtain ⟨q, hq, hqspec⟩ := condK_others_le_problemK_criticalData_godel
    P hP V hV
  obtain ⟨Q, hQ, hQspec⟩ := condK_others_le_problemK_criticalData_pack
    P hP C (fun l i v => q (l, i, v)) hq
  refine ⟨Q, hQ, fun u i v hv => hQspec u i v (fun l hl => ?_)⟩
  intro s hs
  obtain ⟨y, hy, hyV⟩ := hVspec u i v l hl hv s hs
  exact ⟨y, hy, by rw [hqspec]; exact hyV⟩

/-- Auxiliary decoder for `condK_others_le_problemK_criticalData_decode`: peels the tags of a
solution of the right-nested disjunction of the variables of the list `l` (default `d`). -/
private def condK_others_le_problemK_criticalData_decode_decL (P : ProblemCalculus)
    {k : ℕ} (d : Fin k) : List (Fin k) → BitString → Option (Fin k × BitString)
  | [], z => some (d, z)
  | [a], z => some (a, z)
  | a :: b :: l, z => (P.unpair z).bind fun p =>
      bif decide (p.1 = P.tag0) then some (a, p.2)
      else bif decide (p.1 = P.tag1)
        then condK_others_le_problemK_criticalData_decode_decL P d (b :: l) p.2
        else none

private lemma condK_others_le_problemK_criticalData_decode_decL_computable
    (P : ProblemCalculus) (hP : P.Admissible) {k : ℕ} (d : Fin k) :
    ∀ l : List (Fin k), Computable
      (condK_others_le_problemK_criticalData_decode_decL P d l)
  | [] => (Computable.option_some.comp ((Computable.const d).pair Computable.id)).of_eq
      fun _ => rfl
  | [a] => (Computable.option_some.comp ((Computable.const a).pair Computable.id)).of_eq
      fun _ => rfl
  | a :: b :: l => by
    have ih := condK_others_le_problemK_criticalData_decode_decL_computable P hP d (b :: l)
    refine Computable.of_eq (f := fun z => (P.unpair z).bind fun p =>
      bif decide (p.1 = P.tag0) then some (a, p.2)
      else bif decide (p.1 = P.tag1)
        then condK_others_le_problemK_criticalData_decode_decL P d (b :: l) p.2
        else none) ?_ fun z => by simp only
            [condK_others_le_problemK_criticalData_decode_decL]
    refine Computable.option_bind hP.2.1 ?_
    have h0 : Computable fun q : BitString × (BitString × BitString) =>
        decide (q.2.1 = P.tag0) :=
      (Primrec.eq.decide.to_comp).comp (Computable.fst.comp Computable.snd) (Computable.const _)
        |>.of_eq fun _ => rfl
    have h1 : Computable fun q : BitString × (BitString × BitString) =>
        decide (q.2.1 = P.tag1) :=
      (Primrec.eq.decide.to_comp).comp (Computable.fst.comp Computable.snd) (Computable.const _)
        |>.of_eq fun _ => rfl
    refine Computable.cond h0
      (Computable.option_some.comp ((Computable.const a).pair (Computable.snd.comp Computable.snd)))
      (Computable.cond h1 (ih.comp (Computable.snd.comp Computable.snd)) (Computable.const none))

private lemma condK_others_le_problemK_criticalData_decode_decL_correct
    (P : ProblemCalculus) (hP : P.Admissible) {k : ℕ} (d : Fin k) (u : Fin k → BitString) :
    ∀ (l : List (Fin k)) (z : BitString),
      z ∈ (disjList (var d) (l.map var)).eval P (fun j => {u j}) →
      ∃ m : Fin k, condK_others_le_problemK_criticalData_decode_decL P d l z = some (m, u m)
  | [], z, hz => ⟨d, by
      simp only [List.map_nil, disjList, PFormula.eval, Set.mem_singleton_iff] at hz
      simp [condK_others_le_problemK_criticalData_decode_decL, hz]⟩
  | [a], z, hz => ⟨a, by
      simp only [List.map_cons, List.map_nil, disjList, PFormula.eval,
        Set.mem_singleton_iff] at hz
      simp [condK_others_le_problemK_criticalData_decode_decL, hz]⟩
  | a :: b :: l, z, hz => by
    simp only [List.map_cons, disjList, PFormula.eval, ProblemCalculus.disj] at hz
    rcases hz with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
    · refine ⟨a, ?_⟩
      simp only [Set.mem_singleton_iff] at hx
      simp [condK_others_le_problemK_criticalData_decode_decL, hP.2.2.1, hx]
    · obtain ⟨m, hm⟩ := condK_others_le_problemK_criticalData_decode_decL_correct P hP d u
        (b :: l) y (by simpa using hy)
      refine ⟨m, ?_⟩
      have hne : ¬ P.tag1 = P.tag0 := fun h => hP.2.2.2.2.1 h.symm
      simp [condK_others_le_problemK_criticalData_decode_decL, hP.2.2.1, hne, hm]

/-- Step 2 of the proof of `condK_others_le_problemK_criticalData`: decoding a solution
of `Z = u₁ ∨ … ∨ u_k` (right-nested disjunction of the singletons `{u t}`, `k > 0`).  There is a
total computable `dec` (independent of `u`) such that every `z ∈ Z(u)` is decoded as
`some (m, u m)`.  Book: a solution is `[0, u₁]`, or `[1, [0, u₂]]`, …, the last one being
`[1, [1, … u_k]]` (for `k = 1` just `u₁`); `dec` peels off the tags with `P.unpair`, `P.tag0`,
`P.tag1` (`tag0 ≠ tag1`, injectivity of `pair` via `unpair (pair x y) = some (x, y)`), by
recursion on the list `finsetVars univ`. -/
private theorem condK_others_le_problemK_criticalData_decode
    (P : ProblemCalculus) (hP : P.Admissible) {k : ℕ} (C : CriticalData k) :
    ∃ dec : BitString → Option (Fin k × BitString), Computable dec ∧
      ∀ (u : Fin k → BitString) (z : BitString),
        z ∈ C.conclusion.eval P (fun j => {u j}) → ∃ m : Fin k, dec z = some (m, u m) := by
  have hfin : finsetVars (Finset.univ : Finset (Fin k)) = (List.finRange k).map var := by
    simp [finsetVars]
  refine ⟨condK_others_le_problemK_criticalData_decode_decL P ⟨0, C.pos⟩
      (List.finRange k),
    condK_others_le_problemK_criticalData_decode_decL_computable P hP _ _, ?_⟩
  intro u z hz
  refine condK_others_le_problemK_criticalData_decode_decL_correct P hP ⟨0, C.pos⟩ u
    (List.finRange k) z ?_
  simpa [CriticalData.conclusion, CriticalData.dflt, hfin] using hz

private theorem condK_others_le_problemK_criticalData_search_code
    {α σ : Type*} [Primcodable α] [Primcodable σ] {f : α →. σ}
    (hf : Partrec f) :
    ∃ c : Nat.Partrec.Code, (∀ a x, x ∈ f a ↔
      ∃ s, Encodable.encode x ∈ Nat.Partrec.Code.evaln s c (Encodable.encode a)) ∧
      ∀ a s e z, e ∈ Nat.Partrec.Code.evaln s c (Encodable.encode a) →
        (Encodable.decode e : Option σ) = some z → z ∈ f a := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hf
  refine ⟨c, fun a x => ?_, fun a s e z he hz => ?_⟩
  · rw [← Nat.Partrec.Code.evaln_complete, hc]
    simp
  · have h := Nat.Partrec.Code.evaln_sound he
    rw [hc] at h
    simp only [Encodable.encodek] at h
    have h' : ∃ x ∈ f a, Encodable.encode x = e := by simpa using h
    obtain ⟨x, hx, rfl⟩ := h'
    rw [Encodable.encodek] at hz
    cases hz
    exact hx

private def condK_others_le_problemK_criticalData_search_reinsert {k : ℕ} (m : Fin k)
    (x : BitString × BitString) : Fin k → BitString :=
  fun t => if t = m then x.2 else
    (decodeListCode x.1).getD (((List.finRange k).filter (fun t => decide (t ≠ m))).idxOf t) []

private lemma condK_others_le_problemK_criticalData_search_reinsert_eq {k : ℕ}
    (u : Fin k → BitString) (m : Fin k) (w : BitString) :
    condK_others_le_problemK_criticalData_search_reinsert m (othersCode u m, w) =
      Function.update u m w := by
  funext t
  unfold condK_others_le_problemK_criticalData_search_reinsert
  by_cases h : t = m
  · subst h; simp
  · rw [ite_eq_right h, Function.update_of_ne h]
    unfold othersCode
    rw [decodeListCode_listCode, List.getD_eq_getElem?_getD]
    have hmem : t ∈ (List.finRange k).filter (fun t => decide (t ≠ m)) := by simp [h]
    have hlt := List.idxOf_lt_length_iff.2 hmem
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt]
    simp

private lemma condK_others_le_problemK_criticalData_search_finCurry
    {α β : Type*} [Primcodable α] [Primcodable β] {n : ℕ}
    {f : α → Fin n → β} (hf : ∀ i, Computable fun a => f a i) : Computable f := by
  refine (Primrec.vector_get'.to_comp.comp
    (Computable.vector_ofFn fun i => hf i)).of_eq fun a => ?_
  funext i
  simp

private lemma condK_others_le_problemK_criticalData_search_reinsert_computable {k : ℕ}
    (m : Fin k) :
    Computable (condK_others_le_problemK_criticalData_search_reinsert m) := by
  refine condK_others_le_problemK_criticalData_search_finCurry fun t => ?_
  unfold condK_others_le_problemK_criticalData_search_reinsert
  by_cases h : t = m
  · simpa [h] using Computable.snd
  · simp only [h, ite_false]
    exact (Primrec.list_getD []).to_comp.comp
      (decodeListCode_computable.comp Computable.fst) (Computable.const _)

private def condK_others_le_problemK_criticalData_search_out {k : ℕ}
    (dec : BitString → Option (Fin k × BitString)) (m : Fin k)
    (z : BitString) : Option BitString :=
  (dec z).bind fun r => if r.1 = m then some r.2 else none

private lemma condK_others_le_problemK_criticalData_search_out_computable {k : ℕ}
    (dec : BitString → Option (Fin k × BitString))
    (hdec : Computable dec) (m : Fin k) :
    Computable (condK_others_le_problemK_criticalData_search_out dec m) := by
  unfold condK_others_le_problemK_criticalData_search_out
  refine Computable.option_bind hdec ?_
  refine (Computable.cond (Primrec.eq.decide.to_comp.comp
    (Computable.fst.comp Computable.snd) (Computable.const m))
    (Computable.option_some.comp (Computable.snd.comp Computable.snd))
    (Computable.const none)).of_eq fun y => ?_
  by_cases h : y.2.1 = m <;> simp [h]

open Nat.Partrec in
private def condK_others_le_problemK_criticalData_search_run {k : ℕ} (cL : Code)
    (Q : ℕ → (Fin k → BitString) → BitString)
    (dec : BitString → Option (Fin k × BitString)) (m : Fin k)
    (a : BitString × BitString) (q : ℕ × ℕ × BitString) : Option BitString :=
  ((Code.evaln q.1 cL (Encodable.encode (a.1, Q q.2.1
      (condK_others_le_problemK_criticalData_search_reinsert m (a.2, q.2.2))))).bind
    (fun e => (Encodable.decode e : Option BitString))).bind
    (condK_others_le_problemK_criticalData_search_out dec m)

open Nat.Partrec in
private lemma condK_others_le_problemK_criticalData_search_run_computable {k : ℕ}
    (cL : Code) (Q : ℕ → (Fin k → BitString) → BitString)
    (hQ : Computable (fun x : ℕ × (Fin k → BitString) => Q x.1 x.2))
    (dec : BitString → Option (Fin k × BitString)) (hdec : Computable dec) (m : Fin k) :
    Computable (fun y : (BitString × BitString) × (ℕ × ℕ × BitString) =>
      condK_others_le_problemK_criticalData_search_run cL Q dec m y.1 y.2) := by
  unfold condK_others_le_problemK_criticalData_search_run
  have hs : Computable fun y : (BitString × BitString) × (ℕ × ℕ × BitString) => y.2.1 :=
    Computable.fst.comp Computable.snd
  have hi : Computable fun y : (BitString × BitString) × (ℕ × ℕ × BitString) => y.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hw : Computable fun y : (BitString × BitString) × (ℕ × ℕ × BitString) => y.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have ha : Computable fun y : (BitString × BitString) × (ℕ × ℕ × BitString) => y.1 :=
    Computable.fst
  have hQ' : Computable fun y : (BitString × BitString) × (ℕ × ℕ × BitString) =>
      Q y.2.2.1 (condK_others_le_problemK_criticalData_search_reinsert m
        (y.1.2, y.2.2.2)) :=
    hQ.comp (hi.pair
      ((condK_others_le_problemK_criticalData_search_reinsert_computable m).comp
        ((Computable.snd.comp ha).pair hw)))
  have hx : Computable fun y : (BitString × BitString) × (ℕ × ℕ × BitString) =>
      Encodable.encode (y.1.1, Q y.2.2.1
        (condK_others_le_problemK_criticalData_search_reinsert m (y.1.2, y.2.2.2))) :=
    Computable.encode.comp ((Computable.fst.comp ha).pair hQ')
  have hz : Computable fun y : (BitString × BitString) × (ℕ × ℕ × BitString) =>
      Code.evaln y.2.1 cL (Encodable.encode (y.1.1,
        Q y.2.2.1 (condK_others_le_problemK_criticalData_search_reinsert m
          (y.1.2, y.2.2.2)))) :=
    Nat.Partrec.Code.primrec_evaln.to_comp.comp ((hs.pair (Computable.const cL)).pair hx)
  refine Computable.option_bind (Computable.option_bind hz
    (Primrec.decode.to_comp.comp Computable.snd)) ?_
  exact ((condK_others_le_problemK_criticalData_search_out_computable dec hdec m).comp
    Computable.snd)

open Nat.Partrec in
private def condK_others_le_problemK_criticalData_search_stage {k : ℕ} (cd cL : Code)
    (Q : ℕ → (Fin k → BitString) → BitString)
    (dec : BitString → Option (Fin k × BitString)) (m : Fin k)
    (a : BitString × BitString) (q : ℕ × ℕ × BitString) : Option BitString :=
  (Code.evaln q.1 cd q.2.1).bind fun e =>
    cond (decide (e = Encodable.encode m))
      (condK_others_le_problemK_criticalData_search_run cL Q dec m a q) none

open Nat.Partrec in
private lemma condK_others_le_problemK_criticalData_search_stage_computable {k : ℕ}
    (cd cL : Code) (Q : ℕ → (Fin k → BitString) → BitString)
    (hQ : Computable (fun x : ℕ × (Fin k → BitString) => Q x.1 x.2))
    (dec : BitString → Option (Fin k × BitString)) (hdec : Computable dec) (m : Fin k) :
    Computable (fun y : (BitString × BitString) × (ℕ × ℕ × BitString) =>
      condK_others_le_problemK_criticalData_search_stage cd cL Q dec m y.1 y.2) := by
  unfold condK_others_le_problemK_criticalData_search_stage
  have hs : Computable fun y : (BitString × BitString) × (ℕ × ℕ × BitString) => y.2.1 :=
    Computable.fst.comp Computable.snd
  have hi : Computable fun y : (BitString × BitString) × (ℕ × ℕ × BitString) => y.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hd : Computable fun y : (BitString × BitString) × (ℕ × ℕ × BitString) =>
      Code.evaln y.2.1 cd y.2.2.1 :=
    Nat.Partrec.Code.primrec_evaln.to_comp.comp ((hs.pair (Computable.const cd)).pair hi)
  have hrun : Computable fun y : ((BitString × BitString) × (ℕ × ℕ × BitString)) × ℕ =>
      condK_others_le_problemK_criticalData_search_run cL Q dec m y.1.1 y.1.2 :=
    (condK_others_le_problemK_criticalData_search_run_computable cL Q hQ dec hdec m).comp
      Computable.fst
  have hc : Computable fun y : ((BitString × BitString) × (ℕ × ℕ × BitString)) × ℕ =>
      decide (y.2 = Encodable.encode m) :=
    Primrec.eq.decide.to_comp.comp Computable.snd (Computable.const _)
  exact Computable.option_bind hd (Computable.cond hc hrun (Computable.const none))

open Nat.Partrec in
private def condK_others_le_problemK_criticalData_search_step {k : ℕ} (cd cL : Code)
    (Q : ℕ → (Fin k → BitString) → BitString)
    (dec : BitString → Option (Fin k × BitString)) (m : Fin k)
    (a : BitString × BitString) (n : ℕ) : Option BitString :=
  (Encodable.decode (α := ℕ × ℕ × BitString) n).bind
    (condK_others_le_problemK_criticalData_search_stage cd cL Q dec m a)

open Nat.Partrec in
private lemma condK_others_le_problemK_criticalData_search_step_computable {k : ℕ}
    (cd cL : Code) (Q : ℕ → (Fin k → BitString) → BitString)
    (hQ : Computable (fun x : ℕ × (Fin k → BitString) => Q x.1 x.2))
    (dec : BitString → Option (Fin k × BitString)) (hdec : Computable dec) (m : Fin k) :
    Computable₂ (condK_others_le_problemK_criticalData_search_step cd cL Q dec m) := by
  unfold Computable₂ condK_others_le_problemK_criticalData_search_step
  refine Computable.option_bind (Primrec.decode.to_comp.comp Computable.snd) ?_
  have h := (condK_others_le_problemK_criticalData_search_stage_computable
    cd cL Q hQ dec hdec m).comp
    ((Computable.fst.comp Computable.fst).pair
      (Computable.snd : Computable fun y : ((BitString × BitString) × ℕ) × (ℕ × ℕ × BitString) =>
        y.2))
  exact h

open Nat.Partrec in
private lemma condK_others_le_problemK_criticalData_search_step_sound {k : ℕ}
    (cd cL : Code) (Q : ℕ → (Fin k → BitString) → BitString)
    (dec : BitString → Option (Fin k × BitString)) (m : Fin k)
    (a : BitString × BitString) (n : ℕ) (w' : BitString)
    (h : condK_others_le_problemK_criticalData_search_step cd cL Q dec m a n =
      some w') :
    ∃ (s i : ℕ) (w z : BitString) (e' : ℕ), Code.evaln s cd i = some (Encodable.encode m) ∧
      Code.evaln s cL (Encodable.encode (a.1, Q i
        (condK_others_le_problemK_criticalData_search_reinsert m (a.2, w)))) = some e' ∧
        (Encodable.decode e' : Option BitString) = some z ∧ dec z = some (m, w') := by
  unfold condK_others_le_problemK_criticalData_search_step
    condK_others_le_problemK_criticalData_search_stage
    condK_others_le_problemK_criticalData_search_run
    condK_others_le_problemK_criticalData_search_out at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, -, e, he, h2⟩ := h
  obtain ⟨s, i, w⟩ := q
  by_cases hem : e = Encodable.encode m
  · subst hem
    simp only [decide_true, Bool.cond_true, Option.bind_eq_some_iff] at h2
    obtain ⟨z, ⟨e', he', hz⟩, r, hr, h3⟩ := h2
    obtain ⟨r1, r2⟩ := r
    by_cases hr1 : r1 = m
    · subst hr1
      simp only [ite_true, Option.some.injEq] at h3
      subst h3
      exact ⟨s, i, w, z, e', he, he', hz, hr⟩
    · simp [hr1] at h3
  · simp [hem] at h2

open Nat.Partrec in
private lemma condK_others_le_problemK_criticalData_search_step_complete {k : ℕ}
    (cd cL : Code) (Q : ℕ → (Fin k → BitString) → BitString)
    (dec : BitString → Option (Fin k × BitString)) (m : Fin k)
    (a : BitString × BitString) (s i : ℕ) (w z w' : BitString)
    (hd : Code.evaln s cd i = some (Encodable.encode m))
    (hL : Code.evaln s cL (Encodable.encode (a.1, Q i
      (condK_others_le_problemK_criticalData_search_reinsert m (a.2, w)))) =
      some (Encodable.encode z))
    (hz : dec z = some (m, w')) :
    condK_others_le_problemK_criticalData_search_step cd cL Q dec m a
      (Encodable.encode (s, i, w)) = some w' := by
  unfold condK_others_le_problemK_criticalData_search_step
    condK_others_le_problemK_criticalData_search_stage
    condK_others_le_problemK_criticalData_search_run
    condK_others_le_problemK_criticalData_search_out
  simp only [Encodable.encodek, Option.bind_some, hd, hL, hz, decide_true, Bool.cond_true, ite_true]

open Nat.Partrec in
/-- Step 3 of the proof of `condK_others_le_problemK_criticalData`: the `m`-th
algorithm of the book, a pure dovetailed search.  Given partial computable `d`, a partial
computable language `L`, a computable `Q` and a computable decoder `dec`, there are partial
computable `F m (p, o)` such that, with `o = othersCode u m` (the code of all `u t`, `t ≠ m`; the
substitution of a candidate `w` for the missing coordinate `m` is a computable function of
`(m, o, w)`, giving `Function.update u m w`):
(sound) every output `w'` of `F m (p, othersCode u m)` comes from some `i`, `w`, `z` with
`d i = m`, `z ∈ [p](Q i (update u m w))` and `dec z = (m, w')`;
(complete) if such `i`, `w`, `z`, `w'` exist then `F m (p, othersCode u m)` is defined.
Book: for all `w`, `i` with `d(i) = m`, run `p` on `Q i (update u m w)` and wait for an output
decoded as `[m, w']` (search over triples `(i, w, steps)` with `Nat.rfind`/`evaln`); the
`m`-th coordinate is reinserted into the decoded `listCode` of `o`. -/
private theorem condK_others_le_problemK_criticalData_search {k : ℕ}
    (d : ℕ →. Fin k) (hd : Partrec d) (L : Map) (hL : Partrec L)
    (Q : ℕ → (Fin k → BitString) → BitString)
    (hQ : Computable (fun x : ℕ × (Fin k → BitString) => Q x.1 x.2))
    (dec : BitString → Option (Fin k × BitString)) (hdec : Computable dec) :
    ∃ F : Fin k → BitString × BitString →. BitString, (∀ m, Partrec (F m)) ∧
      (∀ (u : Fin k → BitString) (m : Fin k) (p w' : BitString),
        w' ∈ F m (p, othersCode u m) →
          ∃ (i : ℕ) (w z : BitString), d i = Part.some m ∧
            z ∈ L (p, Q i (Function.update u m w)) ∧ dec z = some (m, w')) ∧
      (∀ (u : Fin k → BitString) (m : Fin k) (p : BitString) (i : ℕ) (w z w' : BitString),
        d i = Part.some m → z ∈ L (p, Q i (Function.update u m w)) → dec z = some (m, w') →
          (F m (p, othersCode u m)).Dom) := by
  obtain ⟨cd, hcd, hcd'⟩ := condK_others_le_problemK_criticalData_search_code hd
  obtain ⟨cL, hcL, hcL'⟩ := condK_others_le_problemK_criticalData_search_code hL
  refine ⟨fun m a => Nat.rfindOpt
      (condK_others_le_problemK_criticalData_search_step cd cL Q dec m a),
    fun m => Partrec.rfindOpt
      (condK_others_le_problemK_criticalData_search_step_computable
        cd cL Q hQ dec hdec m), ?_, ?_⟩
  · intro u m p w' hw'
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hw'
    obtain ⟨s, i, w, z, e', hs1, hs2, hs3, hs4⟩ :=
      condK_others_le_problemK_criticalData_search_step_sound cd cL Q dec m _ n w' hn
    refine ⟨i, w, z, ?_, ?_, hs4⟩
    · apply Part.eq_some_iff.2
      exact (hcd i m).2 ⟨s, by simpa using hs1⟩
    · rw [← condK_others_le_problemK_criticalData_search_reinsert_eq u m w]
      exact hcL' _ s e' z hs2 hs3
  · intro u m p i w z w' hdi hz hzd
    rw [← condK_others_le_problemK_criticalData_search_reinsert_eq u m w] at hz
    obtain ⟨s1, hs1⟩ := (hcd i m).1 (by rw [hdi]; exact Part.mem_some m)
    obtain ⟨s2, hs2⟩ := (hcL (p, Q i
      (condK_others_le_problemK_criticalData_search_reinsert m
        (othersCode u m, w))) z).1 hz
    have e1 : Code.evaln (max s1 s2) cd i = some (Encodable.encode m) :=
      Code.evaln_mono (le_max_left _ _) (by simpa using hs1)
    have e2 := Code.evaln_mono (le_max_right s1 s2) hs2
    have := condK_others_le_problemK_criticalData_search_step_complete
      cd cL Q dec m (p, othersCode u m) (max s1 s2) i w z w' e1 e2 hzd
    exact Nat.rfindOpt_dom.2 ⟨_, w', this⟩

/-- SUV Theorem 244 (Section 13.4, printed p. 412).  For a critical implication
`((X₁ → Y₁) → Y₁) ∧ … ∧ ((X_N → Y_N) → Y_N) → Z` on singletons `u₁, …, u_k` (`X_l` the
conjunction of the `u_t`, `t ∈ I_l`, `Y_l` the disjunction of the `u_t`, `t ∈ J_l`, `Z` the
disjunction of all `u_t`), the complexity is at least the minimal conditional complexity of
some `u_m` given all the other `u_t` (`othersCode u m`), with `O(1)` precision (the constant
depends on the formula only, not on the strings).
Book's proof: a diagonal function `d : ℕ →. Fin k` (`exists_partrec_diagonal`); programs
`q_{l,i}(v)` solving `(X_l → Y_l) → Y_l` whenever `v = u`, or `v` differs from `u` only at
coordinate `d(i)` (on input `s`: in parallel compute `d(i)` and apply `s` to the tentative
solution of `X_l` built from `v`, waiting for an output `[t, v_t]`, `t ∈ J_l`; if `d(i) = m ∉ I_l`
return the output of `s`, if `m ∈ I_l` return `[t, v_t]` for the least `t ∈ J_l`); the `m`-th
algorithm applies the given solution to `[q_{1,i}(v), …, q_{N,i}(v)]` for all `v` differing from
`u` at most at `m` and all `i` with `d(i) = m`, and waits for an output `[m, *]`.  If no `m`
succeeds, `i ↦ (index of [p]([q_{1,i}(u), …, q_{N,i}(u)]))` is a total computable function
differing from `d` everywhere, contradicting the diagonal property. -/
theorem condK_others_le_problemK_criticalData (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) {k : ℕ} (C : CriticalData k) :
    ∃ c : ℕ, ∀ u : Fin k → BitString, ∃ m : Fin k,
      condK D (u m) (othersCode u m) ≤
        problemK D (C.formula.eval P (fun i => {u i})) + (c : ℕ∞) := by
  obtain ⟨d, hd, hdiag⟩ := exists_partrec_diagonal k
  obtain ⟨Q, hQ, hQsol⟩ := condK_others_le_problemK_criticalData_programs P hP C d hd
  obtain ⟨dec, hdec, hdecsol⟩ := condK_others_le_problemK_criticalData_decode P hP C
  have hL : Partrec P.lang := hP.2.2.2.2.2.1
  obtain ⟨F, hF, hFsound, hFcomp⟩ :=
    condK_others_le_problemK_criticalData_search d hd P.lang hL Q hQ dec hdec
  have hc : ∀ m, ∃ c : ℕ, ∀ p o x, x ∈ F m (p, o) → condK D x o ≤ plainK D p + (c : ℕ∞) :=
    fun m => condK_others_le_problemK_criticalData_condK_le D hD (F m) (hF m)
  choose c hc using hc
  refine ⟨Finset.univ.sup c, fun u => ?_⟩
  rcases (C.formula.eval P (fun i => {u i})).eq_empty_or_nonempty with hS | hS
  · refine ⟨⟨0, C.pos⟩, ?_⟩
    rw [hS, problemK_empty, top_add]; exact le_top
  obtain ⟨p, hp, hpeq⟩ := exists_mem_plainK_eq_problemK D hS
  have hp' : ∀ x ∈ (conjList C.dflt (C.pairs.map fun p =>
      imp (imp (C.premise p.1) (C.target p.2)) (C.target p.2))).eval P (fun j => {u j}),
      ∃ y ∈ C.conclusion.eval P (fun j => {u j}), y ∈ P.lang (p, x) := hp
  let g : ℕ →. Fin k := fun i =>
    (P.lang (p, Q i u)).bind (fun z => (((dec z).map Prod.fst : Option (Fin k)) : Part (Fin k)))
  have hg : Partrec g := by
    refine Partrec.bind (hL.comp ((Computable.const p).pair
      (hQ.comp (Computable.id.pair (Computable.const u))))) ?_
    exact (Computable.ofOption
      (Computable.option_map (hdec.comp Computable.snd)
        (Computable.fst.comp Computable.snd).to₂)).to₂
  obtain ⟨i, hi⟩ := hdiag g hg
  obtain ⟨z, hz, hzL⟩ := hp' _ (hQsol u i u (Or.inl rfl))
  obtain ⟨m, hm⟩ := hdecsol u z hz
  have hdi : d i = Part.some m := by
    rw [hi]
    apply Part.eq_some_iff.2
    exact Part.mem_bind_iff.2 ⟨z, hzL, by simp [hm]⟩
  have hdom := hFcomp u m p i (u m) z (u m) hdi (by simpa using hzL) hm
  obtain ⟨w', hw'⟩ := Part.dom_iff_mem.1 hdom
  obtain ⟨i', w, z', hdi', hz'L, hz'dec⟩ := hFsound u m p w' hw'
  obtain ⟨z'', hz'', hz''L⟩ := hp' _ (hQsol u i' (Function.update u m w) (Or.inr ⟨m, hdi', fun t ht
      =>
    Function.update_of_ne ht _ _⟩))
  have hzz : z'' = z' := Part.mem_unique hz''L hz'L
  subst hzz
  obtain ⟨m'', hm''⟩ := hdecsol u z'' hz''
  rw [hz'dec] at hm''
  obtain ⟨rfl, hwu⟩ := Prod.mk.inj (Option.some.inj hm'')
  refine ⟨m, ?_⟩
  have := hc m p (othersCode u m) w' hw'
  rw [hwu] at this
  refine this.trans ?_
  rw [hpeq]
  gcongr
  exact Finset.le_sup (f := c) (Finset.mem_univ m)

/-- SUV Theorem 243 (Section 13.4, printed p. 410).  The case `N = 1` of Theorem 244: the
problem `((X → Y) → Y) → Z` with `X` the conjunction of `u_i`, `i ∈ I`, `Y` the disjunction of
`u_j`, `j ∈ J` (`I`, `J` nonempty and disjoint) and `Z` the disjunction of all `u_t` has
complexity at least `min_m C(u_m | all other u_t)` up to `O(1)`.  The book proves it first
(diagonal function `d : ℕ →. Fin k`, programs `q_i(v₁, …, v_k)`, see Theorem 244) and then
generalizes it; here it is derived from Theorem 244 (the hypothesis `N = 1` is not needed). -/
theorem condK_others_le_problemK_criticalData_single (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) {k : ℕ} (C : CriticalData k)
    (_hC : C.pairs.length = 1) :
    ∃ c : ℕ, ∀ u : Fin k → BitString, ∃ m : Fin k,
      condK D (u m) (othersCode u m) ≤
        problemK D (C.formula.eval P (fun i => {u i})) + (c : ℕ∞) :=
  condK_others_le_problemK_criticalData D hD P hP C

end InformationLogic
end Kolmogorov
