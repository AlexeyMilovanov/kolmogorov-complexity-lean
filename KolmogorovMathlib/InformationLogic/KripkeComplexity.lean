import KolmogorovMathlib.InformationLogic.Bridges
import KolmogorovMathlib.InformationLogic.Kripke
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools

/-!
# A result similar to Theorem 238 via Kripke models (SUV §13.5)

An. A. Muchnik's direct proof, from a finite Kripke countermodel, that an unprovable formula has
complexity at least `n` on problems of complexity `O(n)` (Theorem 246).  The problems are
infinite: random strings of lengths assigned to the worlds, plus pairs of random strings from
incomparable worlds.
-/

namespace Kolmogorov
namespace InformationLogic

open ProblemCalculus PFormula

/-- SUV Section 13.5, unnumbered claim in the proof of Theorem 246 (printed p. 415): the
conjunction is stable under algorithmic reductions — if `X` reduces to `X'` and `Y` to `Y'`,
then `X ∧ Y` reduces to `X' ∧ Y'` ("a straightforward consequence of the definition").
Proof: unpair, reduce componentwise, pair again. -/
theorem problemReduces_conj (P : ProblemCalculus) (hP : P.Admissible)
    {X X' Y Y' : Set BitString} (hX : ProblemReduces X X') (hY : ProblemReduces Y Y') :
    ProblemReduces (P.conj X Y) (P.conj X' Y') := by
  obtain ⟨hpair, hunpair, hinv, -, -, -⟩ := hP
  obtain ⟨f, hf, hfX⟩ := hX
  obtain ⟨g, hg, hgY⟩ := hY
  refine ⟨fun z => ((P.unpair z : Option (BitString × BitString)) :
      Part (BitString × BitString)).bind
        (fun xy => (f xy.1).bind (fun x' => (g xy.2).map (fun y' => P.pair x' y'))), ?_, ?_⟩
  · exact Partrec.bind (Computable.ofOption hunpair)
      (Partrec.bind (hf.comp (Computable.fst.comp Computable.snd))
        (Partrec.map (hg.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
          (hpair.comp (Computable.snd.comp Computable.fst) Computable.snd).to₂).to₂).to₂
  · rintro z ⟨x, hx, y, hy, rfl⟩
    obtain ⟨x', hx', hfx⟩ := hfX x hx
    obtain ⟨y', hy', hgy⟩ := hgY y hy
    refine ⟨P.pair x' y', ⟨x', hx', y', hy', rfl⟩, ?_⟩
    beta_reduce
    rw [hinv]
    exact Part.mem_bind_iff.2 ⟨(x, y), Part.mem_some _,
      Part.mem_bind_iff.2 ⟨x', hfx, Part.mem_map_iff _ |>.2 ⟨y', hgy, rfl⟩⟩⟩

/-- SUV Section 13.5, unnumbered claim in the proof of Theorem 246 (printed p. 415): the
disjunction is stable under algorithmic reductions — if `X` reduces to `X'` and `Y` to `Y'`,
then `X ∨ Y` reduces to `X' ∨ Y'`.  Proof: unpair, compare the tag with `P.tag0` (decidable;
the tags differ), reduce the tagged component with the matching reduction, keep the tag. -/
theorem problemReduces_disj (P : ProblemCalculus) (hP : P.Admissible)
    {X X' Y Y' : Set BitString} (hX : ProblemReduces X X') (hY : ProblemReduces Y Y') :
    ProblemReduces (P.disj X Y) (P.disj X' Y') := by
  obtain ⟨f, hf, hfX⟩ := hX
  obtain ⟨g, hg, hgY⟩ := hY
  have hab : Computable fun s : BitString => (P.unpair s).getD ([], []) :=
    Computable.option_getD hP.2.1 (Computable.const _)
  have hc : Computable fun s : BitString => decide (((P.unpair s).getD ([], [])).1 = P.tag0) :=
    (Primrec.eq.decide.to_comp).comp (Computable.fst.comp hab) (Computable.const _) |>.of_eq
      fun _ => rfl
  refine ⟨fun s => cond (decide (((P.unpair s).getD ([], [])).1 = P.tag0))
    ((f ((P.unpair s).getD ([], [])).2).map fun w => P.pair P.tag0 w)
    ((g ((P.unpair s).getD ([], [])).2).map fun w => P.pair P.tag1 w), ?_, ?_⟩
  · refine Partrec.cond hc ?_ ?_
    · exact Partrec.map (hf.comp (Computable.snd.comp hab))
        (hP.1.comp (Computable.const _) Computable.snd)
    · exact Partrec.map (hg.comp (Computable.snd.comp hab))
        (hP.1.comp (Computable.const _) Computable.snd)
  · intro s hs
    rcases hs with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
    · obtain ⟨w, hw, hw'⟩ := hfX x hx
      refine ⟨P.pair P.tag0 w, Or.inl ⟨w, hw, rfl⟩, ?_⟩
      simp only [hP.2.2.1 _ x, Option.getD_some, decide_true, Bool.cond_true]
      exact Part.mem_map_iff _ |>.2 ⟨w, hw', rfl⟩
    · obtain ⟨w, hw, hw'⟩ := hgY y hy
      refine ⟨P.pair P.tag1 w, Or.inr ⟨w, hw, rfl⟩, ?_⟩
      have hne : ¬ P.tag1 = P.tag0 := fun h => hP.2.2.2.2.1 h.symm
      simp only [hP.2.2.1 _ y, Option.getD_some, hne, decide_false, Bool.cond_false]
      exact Part.mem_map_iff _ |>.2 ⟨w, hw', rfl⟩

/-- SUV Section 13.5, unnumbered claim in the proof of Theorem 246 (printed p. 415): the
implication is stable under algorithmic reductions, contravariantly in the premise: if `X'`
reduces to `X` and `Y` to `Y'`, then `X → Y` reduces to `X' → Y'` (compose the program with the
two reductions, by the Gödel property of `P.lang`). -/
theorem problemReduces_imp (P : ProblemCalculus) (hP : P.Admissible)
    {X X' Y Y' : Set BitString} (hX : ProblemReduces X' X) (hY : ProblemReduces Y Y') :
    ProblemReduces (P.imp X Y) (P.imp X' Y') := by
  obtain ⟨-, -, -, -, -, hL, hG⟩ := hP
  obtain ⟨f, hf, hfX⟩ := hX
  obtain ⟨g, hg, hgY⟩ := hY
  let V : Map := fun q => (f q.2).bind (fun x => (P.lang (q.1, x)).bind g)
  have hV : Partrec V :=
    Partrec.bind (hf.comp Computable.snd)
      (Partrec.bind (hL.comp ((Computable.fst.comp Computable.fst).pair Computable.snd))
        (hg.comp Computable.snd).to₂).to₂
  obtain ⟨t, ht, hts⟩ := hG V hV
  refine ⟨fun p => Part.some (t p), ht.partrec, fun p hp => ⟨t p, ?_, Part.mem_some _⟩⟩
  intro x' hx'
  obtain ⟨x, hx, hfx⟩ := hfX x' hx'
  obtain ⟨y, hy, hLy⟩ := hp x hx
  obtain ⟨y', hy', hgy⟩ := hgY y hy
  refine ⟨y', hy', ?_⟩
  rw [hts]
  exact Part.mem_bind_iff.2 ⟨x, hfx, Part.mem_bind_iff.2 ⟨y, hLy, hgy⟩⟩

/-! ### Decomposition of `exists_problems_problemK_eval_ge_of_countermodel`

Conventions.  `rand D x`: `x` is *random*, i.e. `|x| ≤ 2 C(x)` (the book's threshold
`length/10` is too weak for the complexity estimates, `length/2` works).  A *length assignment*
`ω : ℕ → Option W` maps a length to its world (`none`: not an allowed length); the family
`ω n` (one assignment for each `n ≥ 1`) must be computable *uniformly in `n`*, since the
reductions between problems depend on `n` and the lower bound `C(Φ(X)) ≥ n` loses
`O(log n)` for that (`problemK_le_of_partrec_advice`).  `xset D P (ω n) T` is the book's `X_Ψ`
for `T = {worlds where Ψ is true}`: `0x` for random `x` from a world of `T`, plus `1y`
for `y ∈ C` (tags and pairs of the calculus `P`). -/

/-- Random strings: complexity at least half of the length. -/
private def exists_problems_problemK_eval_ge_of_countermodel_rand (D : Map) (x : BitString) :
    Prop :=
  (x.length : ℕ∞) ≤ 2 * plainK D x

/-- Random strings of lengths belonging to worlds of `T`. -/
private def exists_problems_problemK_eval_ge_of_countermodel_rset {W : Type} (D : Map)
    (ω : ℕ → Option W) (T : W → Prop) : Set BitString :=
  {x | exists_problems_problemK_eval_ge_of_countermodel_rand D x ∧
    ∃ w, ω x.length = some w ∧ T w}

/-- The book's set `C`: pairs `[y, x]` of random strings from incomparable worlds. -/
private def exists_problems_problemK_eval_ge_of_countermodel_cset {W : Type} [PartialOrder W]
    (D : Map) (P : ProblemCalculus) (ω : ℕ → Option W) : Set BitString :=
  {z | ∃ y x u v, exists_problems_problemK_eval_ge_of_countermodel_rand D y ∧
    exists_problems_problemK_eval_ge_of_countermodel_rand D x ∧
    ω y.length = some u ∧ ω x.length = some v ∧ ¬ u ≤ v ∧ ¬ v ≤ u ∧ z = P.pair y x}

/-- The book's `X_Ψ` for the set `T` of worlds where `Ψ` is true. -/
private def exists_problems_problemK_eval_ge_of_countermodel_xset {W : Type} [PartialOrder W]
    (D : Map) (P : ProblemCalculus) (ω : ℕ → Option W) (T : W → Prop) : Set BitString :=
  P.disj (exists_problems_problemK_eval_ge_of_countermodel_rset D ω T)
    (exists_problems_problemK_eval_ge_of_countermodel_cset D P ω)

/-- The worlds where `Ψ → Θ` is true, from the sets `T`, `T'` of worlds where `Ψ`, `Θ` are. -/
private def exists_problems_problemK_eval_ge_of_countermodel_impset {W : Type} [PartialOrder W]
    (T T' : W → Prop) : W → Prop :=
  fun w => ∀ w', w ≤ w' → T w' → T' w'

/-- Properties of one length assignment `ω` (for the parameter `n ≥ 1`): the root has length `0`
and only it; the top world `t` has the length `20 n`; the allowed lengths are pairwise at least
ten times apart; the nonzero ones are `≥ 20 n`; every non-root world has infinitely many
lengths. -/
private def exists_problems_problemK_eval_ge_of_countermodel_good {W : Type} (r t : W) (n : ℕ)
    (ω : ℕ → Option W) : Prop :=
  ω 0 = some r ∧ ω (20 * n) = some t ∧ (∀ l w, ω l = some w → (w = r ↔ l = 0)) ∧
    (∀ l l', (ω l).isSome → (ω l').isSome → l < l' → 10 * l ≤ l') ∧
    (∀ l, (ω l).isSome → l ≠ 0 → 20 * n ≤ l) ∧
    (∀ w, w ≠ r → {l | ω l = some w}.Infinite)

/-- A family of length assignments, uniformly decidable in `n`, good for every `n ≥ 1`. -/
private def exists_problems_problemK_eval_ge_of_countermodel_family {W : Type} (r t : W)
    (ω : ℕ → ℕ → Option W) : Prop :=
  (∀ w, ComputablePred (fun p : ℕ × ℕ => ω p.1 p.2 = some w)) ∧
    ∀ n, 1 ≤ n → exists_problems_problemK_eval_ge_of_countermodel_good r t n (ω n)

/-- Uniform reducibility of families of problems: one partial computable function of
`(n, solution)`. -/
private def exists_problems_problemK_eval_ge_of_countermodel_ured (A B : ℕ → Set BitString) :
    Prop :=
  ∃ f : ℕ × BitString →. BitString, Partrec f ∧
    ∀ n, 1 ≤ n → ∀ x ∈ A n, ∃ y ∈ B n, y ∈ f (n, x)

/-- Uniform reducibility is reflexive (the identity). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_ured_refl
    (A : ℕ → Set BitString) : exists_problems_problemK_eval_ge_of_countermodel_ured A A :=
  ⟨fun p => Part.some p.2, Computable.snd.partrec, fun _ _ x hx => ⟨x, hx, Part.mem_some _⟩⟩

/-- Uniform reducibility is transitive (compose the two reductions). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_ured_trans
    {A B C : ℕ → Set BitString} (hAB : exists_problems_problemK_eval_ge_of_countermodel_ured A B)
    (hBC : exists_problems_problemK_eval_ge_of_countermodel_ured B C) :
    exists_problems_problemK_eval_ge_of_countermodel_ured A C := by
  obtain ⟨f, hf, hfAB⟩ := hAB
  obtain ⟨g, hg, hgBC⟩ := hBC
  refine ⟨fun p => (f p).bind (fun y => g (p.1, y)),
    Partrec.bind hf (hg.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂,
    fun n hn x hx => ?_⟩
  obtain ⟨y, hy, hfy⟩ := hfAB n hn x hx
  obtain ⟨z, hz, hgz⟩ := hgBC n hn y hy
  exact ⟨z, hz, Part.mem_bind_iff.2 ⟨y, hfy, hgz⟩⟩

/-- Step 1 of the proof of `exists_problems_problemK_eval_ge_of_countermodel`: adding a
top world.  A finite rooted model refuting `Φ` at the root extends (add a new greatest element
`⊤` where all variables are true: `WithTop W`) to a finite rooted model with a top world `t ≠ r`
where all variables are true, still refuting `Φ` at the root (forcing at old worlds is
unchanged: at `⊤` every formula is forced). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_top {k : ℕ}
    (Φ : PFormula (Fin k)) {W : Type} [Finite W] [PartialOrder W] (r : W)
    (V : W → Fin k → Prop) (hr : ∀ w, r ≤ w) (hV : IsMonotoneValuation V)
    (hΦ : ¬ Forces V r Φ) :
    ∃ (W' : Type) (_ : Finite W') (_ : PartialOrder W') (r' t' : W') (V' : W' → Fin k → Prop),
      (∀ w, r' ≤ w) ∧ (∀ w, w ≤ t') ∧ r' ≠ t' ∧ (∀ i, V' t' i) ∧ IsMonotoneValuation V' ∧
        ¬ Forces V' r' Φ := by
  have htop : ∀ A : PFormula (Fin k),
      Forces (fun (w : WithTop W) i => ∀ w0 : W, w = (w0 : WithTop W) → V w0 i) ⊤ A := by
    intro A
    induction A with
    | var i => exact fun w0 h => absurd h WithTop.top_ne_coe
    | conj A B ihA ihB => exact ⟨ihA, ihB⟩
    | disj A B ihA _ => exact Or.inl ihA
    | imp A B _ ihB =>
      intro w' hw' _
      rw [top_le_iff.1 hw']
      exact ihB
  have hcoe : ∀ (A : PFormula (Fin k)) (w : W),
      Forces (fun (w : WithTop W) i => ∀ w0 : W, w = (w0 : WithTop W) → V w0 i)
        (w : WithTop W) A ↔ Forces V w A := by
    intro A
    induction A with
    | var i =>
      intro w
      exact ⟨fun h => h w rfl, fun h w0 hw0 => (WithTop.coe_inj.1 hw0) ▸ h⟩
    | conj A B ihA ihB => intro w; exact and_congr (ihA w) (ihB w)
    | disj A B ihA ihB => intro w; exact or_congr (ihA w) (ihB w)
    | imp A B ihA ihB =>
      intro w
      constructor
      · intro h w' hw' hA
        exact (ihB w').1 (h w' (WithTop.coe_le_coe.2 hw') ((ihA w').2 hA))
      · intro h w' hw' hA
        cases w' using WithTop.recTopCoe with
        | top => exact htop B
        | coe w'' => exact (ihB w'').2 (h w'' (WithTop.coe_le_coe.1 hw') ((ihA w'').1 hA))
  refine ⟨WithTop W, inferInstanceAs (Finite (Option W)), inferInstance, (r : WithTop W), ⊤,
    fun w i => ∀ w0 : W, w = (w0 : WithTop W) → V w0 i, ?_, fun w => le_top,
    WithTop.coe_ne_top, fun i w0 h => absurd h WithTop.top_ne_coe, ?_, ?_⟩
  · intro w
    cases w using WithTop.recTopCoe with
    | top => exact le_top
    | coe w => exact WithTop.coe_le_coe.2 (hr w)
  · intro w w' hww' i hw w0 hw0
    subst hw0
    cases w using WithTop.recTopCoe with
    | top => exact absurd hww' (WithTop.not_top_le_coe w0)
    | coe w1 => exact hV (WithTop.coe_le_coe.1 hww') i (hw w1 rfl)
  · exact fun h => hΦ ((hcoe Φ r).1 h)

/-- Step 2 of the proof of `exists_problems_problemK_eval_ge_of_countermodel`: the
length assignments exist.  For `r ≠ t` in a finite poset: `L = {0} ∪ {20 n 10^j | j ∈ ℕ}`, `0 ↦ r`,
`j = 0 ↦ t`, `j ≥ 1 ↦` the non-root worlds in a cyclic enumeration (each non-root world gets
infinitely many lengths); all sets of lengths are decidable, uniformly in `n`. -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_lengths {W : Type}
    [Finite W] [PartialOrder W] (r t : W) (hrt : r ≠ t) :
    ∃ ω : ℕ → ℕ → Option W,
      exists_problems_problemK_eval_ge_of_countermodel_family r t ω := by
  classical
  obtain ⟨M, ⟨e⟩⟩ := Finite.exists_equiv_fin W
  have hM : 0 < M := Fin.pos (e r)
  have hpow : ∀ j : ℕ, (fun x : ℕ => 10 * x)^[j] 1 = 10 ^ j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, pow_succ, mul_comm]
  have hpowc : Primrec (fun j : ℕ => 10 ^ j) :=
    (Primrec.nat_iterate Primrec.id (Primrec.const 1)
      (Primrec.nat_mul.comp (Primrec.const 10) Primrec.snd).to₂).of_eq hpow
  obtain ⟨jIdx, hjIdx_def⟩ : ∃ f : ℕ × ℕ → ℕ,
      f = fun p => (List.range p.2).findIdx (fun j => decide (20 * p.1 * 10 ^ j = p.2)) :=
    ⟨_, rfl⟩
  have hjIdx : Primrec jIdx := by
    rw [hjIdx_def]
    exact Primrec.list_findIdx (Primrec.list_range.comp Primrec.snd)
      (Primrec.eq.comp (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 20)
        (Primrec.fst.comp Primrec.fst)) (hpowc.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)).decide
  obtain ⟨code, hcode_def⟩ : ∃ f : ℕ → ℕ, f = fun j => if j = 0 then (e t : ℕ) else
      if (j - 1) % M = (e r : ℕ) then (e t : ℕ) else (j - 1) % M := ⟨_, rfl⟩
  have hcode : Primrec code := by
    rw [hcode_def]
    have hm : Primrec (fun j : ℕ => (j - 1) % M) :=
      Primrec.nat_mod.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)) (Primrec.const M)
    exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const _)
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const _)) (Primrec.const _) hm)
  have hcode_ne : ∀ j, code j ≠ (e r : ℕ) := by
    intro j
    rw [hcode_def]
    dsimp only
    split_ifs with h1 h2
    · exact fun h => hrt (e.injective (Fin.ext h)).symm
    · exact fun h => hrt (e.injective (Fin.ext h)).symm
    · exact h2
  obtain ⟨idx, hidx_def⟩ : ∃ f : ℕ × ℕ → ℕ, f = fun p => if p.2 = 0 then (e r : ℕ) else
      if jIdx p < p.2 then code (jIdx p) else M := ⟨_, rfl⟩
  have hidx : Primrec idx := by
    rw [hidx_def]
    exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const _)
      (Primrec.ite (Primrec.nat_lt.comp hjIdx Primrec.snd) (hcode.comp hjIdx) (Primrec.const M))
  have hJ1 : ∀ n j, 1 ≤ n → jIdx (n, 20 * n * 10 ^ j) = j ∧ j < 20 * n * 10 ^ j := by
    intro n j hn
    have hjlt : j < 20 * n * 10 ^ j := by
      have h1 : j < 10 ^ j := Nat.lt_pow_self (by norm_num)
      have h2 : 10 ^ j ≤ 20 * n * 10 ^ j := Nat.le_mul_of_pos_left _ (by omega)
      omega
    refine ⟨?_, hjlt⟩
    rw [hjIdx_def]
    dsimp only
    have hlen : j < (List.range (20 * n * 10 ^ j)).length := by
      rw [List.length_range]; exact hjlt
    refine (List.findIdx_eq hlen).2 ⟨?_, fun j' hj' => ?_⟩
    · simp [List.getElem_range]
    · simp only [List.getElem_range, decide_eq_false_iff_not]
      intro heq
      have h1 : 10 ^ j' < 10 ^ j := Nat.pow_lt_pow_right (by norm_num) hj'
      have h2 : 20 * n * 10 ^ j' < 20 * n * 10 ^ j := Nat.mul_lt_mul_of_pos_left h1 (by omega)
      exact absurd heq (ne_of_lt h2)
  have hJ2 : ∀ n l, jIdx (n, l) < l → 20 * n * 10 ^ jIdx (n, l) = l := by
    intro n l h
    rw [hjIdx_def] at h ⊢
    dsimp only at h ⊢
    have hlen : (List.range l).findIdx (fun j => decide (20 * n * 10 ^ j = l)) <
        (List.range l).length := by rw [List.length_range]; exact h
    have h' := List.findIdx_getElem (w := hlen)
    simp only [List.getElem_range, decide_eq_true_eq] at h'
    exact h'
  let ω : ℕ → ℕ → Option W := fun n l =>
    if h : idx (n, l) < M then some (e.symm ⟨idx (n, l), h⟩) else none
  have hω_iff : ∀ n l w, ω n l = some w ↔ idx (n, l) = (e w : ℕ) := by
    intro n l w
    simp only [ω]
    split_ifs with h
    · rw [Option.some.injEq]
      constructor
      · rintro rfl; simp
      · intro hi
        rw [show (⟨idx (n, l), h⟩ : Fin M) = e w from Fin.ext hi, Equiv.symm_apply_apply]
    · constructor
      · intro h'; exact absurd h' (by simp)
      · intro hi; exact absurd (by rw [hi]; exact (e w).isLt) h
  have hlen_form : ∀ n l, (ω n l).isSome → l ≠ 0 → 20 * n * 10 ^ jIdx (n, l) = l := by
    intro n l hs hl
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hs
    have hi := (hω_iff n l w).1 hw
    rw [hidx_def] at hi
    dsimp only at hi
    rw [ite_eq_right hl] at hi
    split_ifs at hi with hj
    · exact hJ2 n l hj
    · exact absurd hi (by have := (e w).isLt; omega)
  refine ⟨ω, ?_⟩
  unfold exists_problems_problemK_eval_ge_of_countermodel_family
    exists_problems_problemK_eval_ge_of_countermodel_good
  refine ⟨fun w => ?_, fun n hn => ?_⟩
  · refine ComputablePred.computable_iff.2 ⟨fun p => decide (idx p = (e w : ℕ)),
      (Primrec.eq.comp hidx (Primrec.const _)).decide.to_comp, ?_⟩
    funext p
    simp only [decide_eq_true_eq]
    exact propext (hω_iff p.1 p.2 w)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hω_iff, hidx_def]
    simp
  · rw [hω_iff, hidx_def]
    have h := hJ1 n 0 hn
    simp only [pow_zero, mul_one] at h
    dsimp only
    rw [ite_eq_right (by omega), ite_eq_left (by rw [h.1]; exact h.2), h.1, hcode_def]
    simp
  · intro l w hw
    have hi := (hω_iff n l w).1 hw
    rw [hidx_def] at hi
    dsimp only at hi
    by_cases hl : l = 0
    · rw [ite_eq_left hl] at hi
      exact ⟨fun _ => hl, fun _ => (e.injective (Fin.ext hi)).symm⟩
    · rw [ite_eq_right hl] at hi
      have hwr : w ≠ r := by
        intro hwr
        rw [hwr] at hi
        split_ifs at hi with hj
        · exact hcode_ne _ hi
        · have := (e r).isLt; omega
      exact ⟨fun h => absurd h hwr, fun h => absurd h hl⟩
  · intro l l' hs hs' hll'
    by_cases hl : l = 0
    · rw [hl]; simp
    · have hl' : l' ≠ 0 := by omega
      have h1 := hlen_form n l hs hl
      have h2 := hlen_form n l' hs' hl'
      generalize jIdx (n, l) = j at h1
      generalize jIdx (n, l') = j' at h2
      subst h1 h2
      have hjj : j < j' := by
        by_contra hle
        push Not at hle
        have h3 : 10 ^ j' ≤ 10 ^ j := Nat.pow_le_pow_right (by norm_num) hle
        have h4 : 20 * n * 10 ^ j' ≤ 20 * n * 10 ^ j := Nat.mul_le_mul_left _ h3
        exact absurd hll' (not_lt.2 h4)
      have h5 : 10 ^ (j + 1) ≤ 10 ^ j' := Nat.pow_le_pow_right (by norm_num) hjj
      calc 10 * (20 * n * 10 ^ j) = 20 * n * 10 ^ (j + 1) := by ring
        _ ≤ 20 * n * 10 ^ j' := Nat.mul_le_mul_left _ h5
  · intro l hs hl
    have h1 := hlen_form n l hs hl
    have h2 : 1 ≤ 10 ^ jIdx (n, l) := Nat.one_le_pow _ _ (by norm_num)
    rw [← h1]
    nlinarith
  · intro w hw
    have hew : (e w : ℕ) ≠ (e r : ℕ) := fun h => hw (e.injective (Fin.ext h))
    refine Set.infinite_of_injective_forall_mem
      (f := fun k : ℕ => 20 * n * 10 ^ (1 + (e w : ℕ) + k * M)) ?_ ?_
    · intro k1 k2 hk
      have h1 : 10 ^ (1 + (e w : ℕ) + k1 * M) = 10 ^ (1 + (e w : ℕ) + k2 * M) :=
        Nat.eq_of_mul_eq_mul_left (by omega : 0 < 20 * n) hk
      have h3 : 1 + (e w : ℕ) + k1 * M = 1 + (e w : ℕ) + k2 * M :=
        Nat.pow_right_injective (by norm_num : 2 ≤ 10) h1
      have h4 : k1 * M = k2 * M := by omega
      exact Nat.eq_of_mul_eq_mul_right hM h4
    · intro k
      change ω n _ = some w
      rw [hω_iff, hidx_def]
      dsimp only
      obtain ⟨hj1, hj2⟩ := hJ1 n (1 + (e w : ℕ) + k * M) hn
      have hne : 20 * n * 10 ^ (1 + (e w : ℕ) + k * M) ≠ 0 :=
        (Nat.mul_pos (Nat.mul_pos (by norm_num) hn) (pow_pos (by norm_num) _)).ne'
      rw [ite_eq_right hne, ite_eq_left (by rw [hj1]; exact hj2), hj1, hcode_def]
      dsimp only
      have hmod : (1 + (e w : ℕ) + k * M - 1) % M = (e w : ℕ) := by
        rw [show 1 + (e w : ℕ) + k * M - 1 = (e w : ℕ) + k * M by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (e w).isLt]
      rw [ite_eq_right (by omega), hmod, ite_eq_right hew]

/-- Step 3 of the proof of `exists_problems_problemK_eval_ge_of_countermodel`: each
`X_i` has complexity `O(n)`.  A random string `x` of length `20 n` exists (counting: fewer than
`2^{10 n}` programs of length `< 10 n`), belongs to the top world, hence `0x ∈ X_T` whenever the
top world `t ∈ T`; `C(0x) ≤ |x| + O(1) ≤ 20 n + O(1)` (`plainK_le_length`,
`problemK_le_of_partrec` for the pairing with the tag). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_complexity
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible)
    {W : Type} [PartialOrder W] (r t : W) :
    ∃ c : ℕ, ∀ (n : ℕ) (ω : ℕ → Option W) (T : W → Prop), 1 ≤ n →
      exists_problems_problemK_eval_ge_of_countermodel_good r t n ω → T t →
        problemK D (exists_problems_problemK_eval_ge_of_countermodel_xset D P ω T) ≤
          ((c * (n + 1) : ℕ) : ℕ∞) := by
  obtain ⟨hpair, -, -, -, -, -⟩ := hP
  obtain ⟨c1, hc1⟩ := plainK_le_length D hD
  obtain ⟨c2, hc2⟩ := plainK_le_of_mem_partrec D hD (fun x => Part.some (P.pair P.tag0 x))
    (hpair.comp (Computable.const _) Computable.id).partrec
  refine ⟨20 + c1 + c2, fun n ω T _ hgood hT => ?_⟩
  obtain ⟨x, hxlen, hxK⟩ := exists_incompressible_string D [] (20 * n)
  have hrand : exists_problems_problemK_eval_ge_of_countermodel_rand D x := by
    change (x.length : ℕ∞) ≤ 2 * plainK D x
    rw [hxlen, two_mul]
    exact le_add_right hxK
  have hmem : P.pair P.tag0 x ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P ω T :=
    Or.inl ⟨x, ⟨hrand, t, by rw [hxlen]; exact hgood.2.1, hT⟩, rfl⟩
  have hn : 20 * n + c1 + c2 ≤ (20 + c1 + c2) * (n + 1) := by nlinarith
  calc problemK D (exists_problems_problemK_eval_ge_of_countermodel_xset D P ω T)
      ≤ plainK D (P.pair P.tag0 x) := problemK_le_of_mem D hmem
    _ ≤ plainK D x + c2 := hc2 x _ (Part.mem_some _)
    _ ≤ ((x.length : ℕ∞) + c1) + c2 := by gcongr; exact hc1 x
    _ = ((20 * n + c1 + c2 : ℕ) : ℕ∞) := by rw [hxlen]; push_cast; rfl
    _ ≤ (((20 + c1 + c2) * (n + 1) : ℕ) : ℕ∞) := by exact_mod_cast hn

/-- A linear function of `s` is bounded by `2 ^ s` once `s` is large (a copy of
`linear_le_two_pow` from `CommonInformation.ChainNonextractabilityEngine`, not imported here). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_linear_le_two_pow (c e s : ℕ)
    (hs : 4 * (c + e + 1) ≤ s) : c * s + e ≤ 2 ^ s := by
  set x := 2 * (c + e + 1) with hx
  have hxs : 2 * x ≤ s := by omega
  have h1 : x < 2 ^ x := Nat.lt_two_pow_self
  have h2 : s - x < 2 ^ (s - x) := Nat.lt_two_pow_self
  have hsplit : (2 : ℕ) ^ s = 2 ^ x * 2 ^ (s - x) := by
    rw [← pow_add]; congr 1; omega
  have hge : x * (s - x) ≤ 2 ^ s := by
    rw [hsplit]
    exact Nat.mul_le_mul h1.le h2.le
  have hkey : (c + e + 1) * s ≤ x * (s - x) := by
    have hd : s ≤ 2 * (s - x) := by omega
    calc (c + e + 1) * s ≤ (c + e + 1) * (2 * (s - x)) := Nat.mul_le_mul_left _ hd
      _ = x * (s - x) := by rw [hx]; ring
  have hlin : c * s + e ≤ (c + e + 1) * s := by
    have hs1 : 1 ≤ s := by omega
    nlinarith
  omega

/-- Beyond a threshold, `d · size n + e ≤ n` (a copy of `exists_size_linear_threshold` from
`CommonInformation.ChainNonextractabilityEngine`, not imported here). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_size_threshold (d e : ℕ) :
    ∃ T : ℕ, ∀ n : ℕ, T ≤ n → d * Nat.size n + e ≤ n := by
  refine ⟨2 ^ (4 * (d + (d + e) + 1)), fun n hn => ?_⟩
  set S0 := 4 * (d + (d + e) + 1) with hS0
  have hsize : S0 + 1 ≤ Nat.size n := by
    have h := Nat.size_le_size hn
    simpa [Nat.size_pow] using h
  obtain ⟨t, ht'⟩ : ∃ t, Nat.size n = t + 1 := ⟨Nat.size n - 1, by omega⟩
  have hlow : 2 ^ t ≤ n := by
    by_contra hcon
    simp only [not_le] at hcon
    have h := Nat.size_le.mpr hcon
    omega
  have hkey : d * t + (d + e) ≤ 2 ^ t :=
    exists_problems_problemK_eval_ge_of_countermodel_linear_le_two_pow d (d + e) t (by omega)
  have hds : d * Nat.size n + e = d * t + (d + e) := by
    rw [ht']; ring
  omega

/-- Step 4 of the proof of `exists_problems_problemK_eval_ge_of_countermodel`: the
lower bound.  If a family `E n` of problems uniformly reduces to `X_T` for a set `T` of worlds
not containing the root, then `C(E n) ≥ n` for large `n`.  Indeed all elements of `X_T` are
`[0, x]` (`x` random from a nonroot world, so `|x| ≥ 20 n`, `C(x) ≥ 10 n`) or `[1, [y, z]]`
(`y`, `z` random from incomparable worlds, hence nonroot, `C ≥ 10 n`); `C(X_T) ≥ 10 n - O(1)`
by projections (`problemK_le_of_partrec`), and the uniform reduction costs `O(log n)`
(`problemK_le_of_partrec_advice`). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_lower
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible)
    {W : Type} [PartialOrder W] (r t : W) (hr : ∀ w, r ≤ w) (ω : ℕ → ℕ → Option W)
    (hω : exists_problems_problemK_eval_ge_of_countermodel_family r t ω)
    (T : W → Prop) (hT : ¬ T r) (E : ℕ → Set BitString)
    (hE : exists_problems_problemK_eval_ge_of_countermodel_ured E
      (fun n => exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T)) :
    ∃ N : ℕ, ∀ n ≥ N, (n : ℕ∞) ≤ problemK D (E n) := by
  obtain ⟨-, hunpair, hinv, -, -, -⟩ := hP
  obtain ⟨f, hf, hfE⟩ := hE
  obtain ⟨ca, hca⟩ := problemK_le_of_partrec_advice D hD
    (fun q : BitString × (ℕ × Bool) => f (q.2.1, q.1))
    (hf.comp ((Computable.fst.comp Computable.snd).pair Computable.fst))
  obtain ⟨c1, hc1⟩ := plainK_le_of_mem_partrec D hD
    (fun z => (((P.unpair z).map Prod.snd : Option BitString) : Part BitString))
    (Computable.ofOption (Computable.option_map hunpair (Computable.snd.comp Computable.snd).to₂))
  obtain ⟨c2, hc2⟩ := plainK_le_of_mem_partrec D hD
    (fun z => ((((P.unpair z).bind (fun ac => P.unpair ac.2)).map Prod.fst : Option BitString) :
      Part BitString))
    (Computable.ofOption (Computable.option_map (Computable.option_bind hunpair
      (hunpair.comp (Computable.snd.comp Computable.snd)).to₂)
        (Computable.fst.comp Computable.snd).to₂))
  have hbig : ∀ n, 1 ≤ n → ∀ (x : BitString) (w : W),
      exists_problems_problemK_eval_ge_of_countermodel_rand D x → ω n x.length = some w →
        w ≠ r → ((10 * n : ℕ) : ℕ∞) ≤ plainK D x := by
    intro n hn x w hx hw hwr
    have hgood := hω.2 n hn
    have hl0 : x.length ≠ 0 := fun h0 => hwr ((hgood.2.2.1 _ _ hw).2 h0)
    have hl : 20 * n ≤ x.length := hgood.2.2.2.2.1 _ (by rw [hw]; rfl) hl0
    have hx' : (x.length : ℕ∞) ≤ 2 * plainK D x := hx
    by_cases ht : plainK D x = ⊤
    · rw [ht]; exact le_top
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 ht
      rw [← hm] at hx' ⊢
      have : x.length ≤ 2 * m := by exact_mod_cast hx'
      exact_mod_cast (show 10 * n ≤ m by omega)
  have hlow : ∀ n, 1 ≤ n →
      ∀ y ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T,
        ((10 * n : ℕ) : ℕ∞) ≤ plainK D y + ((c1 + c2 : ℕ) : ℕ∞) := by
    intro n hn y hy
    rcases hy with ⟨x, ⟨hx, w, hw, hTw⟩, rfl⟩ |
      ⟨c, ⟨a, b, ua, vb, hra, -, hua, -, hab, -, rfl⟩, rfl⟩
    · have hwr : w ≠ r := fun h => hT (by rw [← h]; exact hTw)
      calc ((10 * n : ℕ) : ℕ∞) ≤ plainK D x := hbig n hn x w hx hw hwr
        _ ≤ plainK D (P.pair P.tag0 x) + c1 := hc1 _ x (by simp [hinv])
        _ ≤ plainK D (P.pair P.tag0 x) + ((c1 + c2 : ℕ) : ℕ∞) := by
          gcongr; exact_mod_cast Nat.le_add_right c1 c2
    · have hwr : ua ≠ r := fun h => hab (by rw [h]; exact hr vb)
      calc ((10 * n : ℕ) : ℕ∞) ≤ plainK D a := hbig n hn a ua hra hua hwr
        _ ≤ plainK D (P.pair P.tag1 (P.pair a b)) + c2 := hc2 _ a (by simp [hinv])
        _ ≤ plainK D (P.pair P.tag1 (P.pair a b)) + ((c1 + c2 : ℕ) : ℕ∞) := by
          gcongr; exact_mod_cast Nat.le_add_left c2 c1
  have hX : ∀ n, 1 ≤ n → ((10 * n : ℕ) : ℕ∞) ≤
      problemK D (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T) +
        ((c1 + c2 : ℕ) : ℕ∞) := by
    intro n hn
    rcases (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T).eq_empty_or_nonempty
      with he | hne
    · rw [he, problemK_empty]; simp
    · obtain ⟨y, hy, hyeq⟩ := exists_mem_plainK_eq_problemK D hne
      rw [← hyeq]
      exact hlow n hn y hy
  obtain ⟨N0, hN0⟩ :=
    exists_problems_problemK_eval_ge_of_countermodel_size_threshold ca (ca + c1 + c2)
  refine ⟨max N0 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hadv := hca (E n) (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T) n
    (fun e he => ⟨false, hfE n hn1 e he⟩)
  have hsl : logSlack ca n + c1 + c2 ≤ n := by
    have h := hN0 n (le_trans (le_max_left _ _) hn)
    rw [logSlack, Nat.size_eq_bits_len]
    linarith
  have h10 := hX n hn1
  by_cases ht : problemK D (E n) = ⊤
  · rw [ht]; exact le_top
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 ht
    rw [← hm] at hadv ⊢
    have h' : ((10 * n : ℕ) : ℕ∞) ≤ ((m + logSlack ca n + (c1 + c2) : ℕ) : ℕ∞) := by
      calc ((10 * n : ℕ) : ℕ∞)
          ≤ problemK D (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T) +
            ((c1 + c2 : ℕ) : ℕ∞) := h10
        _ ≤ ((m : ℕ∞) + (logSlack ca n : ℕ∞)) + ((c1 + c2 : ℕ) : ℕ∞) := by gcongr
        _ = ((m + logSlack ca n + (c1 + c2) : ℕ) : ℕ∞) := by push_cast; ring
    have h'' : 10 * n ≤ m + logSlack ca n + (c1 + c2) := by exact_mod_cast h'
    exact_mod_cast (show n ≤ m by omega)

/-- Step 5a of the proof of `exists_problems_problemK_eval_ge_of_countermodel`:
uniform version of `problemReduces_conj` (same proof, the reduction taking `n` as extra input). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_ured_conj
    (P : ProblemCalculus) (hP : P.Admissible) {A A' B B' : ℕ → Set BitString}
    (hA : exists_problems_problemK_eval_ge_of_countermodel_ured A A')
    (hB : exists_problems_problemK_eval_ge_of_countermodel_ured B B') :
    exists_problems_problemK_eval_ge_of_countermodel_ured (fun n => P.conj (A n) (B n))
      (fun n => P.conj (A' n) (B' n)) := by
  obtain ⟨hpair, hunpair, hinv, -, -, -⟩ := hP
  obtain ⟨f, hf, hfA⟩ := hA
  obtain ⟨g, hg, hgB⟩ := hB
  refine ⟨fun p => ((P.unpair p.2 : Option (BitString × BitString)) :
      Part (BitString × BitString)).bind
        (fun xy => (f (p.1, xy.1)).bind (fun x' => (g (p.1, xy.2)).map (fun y' => P.pair x' y'))),
    ?_, ?_⟩
  · exact Partrec.bind (Computable.ofOption (hunpair.comp Computable.snd))
      (Partrec.bind (hf.comp ((Computable.fst.comp Computable.fst).pair
          (Computable.fst.comp Computable.snd)))
        (Partrec.map (hg.comp ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
            (Computable.snd.comp (Computable.snd.comp Computable.fst))))
          (hpair.comp (Computable.snd.comp Computable.fst) Computable.snd).to₂).to₂).to₂
  · rintro n hn z ⟨x, hx, y, hy, rfl⟩
    obtain ⟨x', hx', hfx⟩ := hfA n hn x hx
    obtain ⟨y', hy', hgy⟩ := hgB n hn y hy
    refine ⟨P.pair x' y', ⟨x', hx', y', hy', rfl⟩, ?_⟩
    beta_reduce
    rw [hinv]
    exact Part.mem_bind_iff.2 ⟨(x, y), Part.mem_some _,
      Part.mem_bind_iff.2 ⟨x', hfx, Part.mem_map_iff _ |>.2 ⟨y', hgy, rfl⟩⟩⟩

/-- Step 5b of the proof of `exists_problems_problemK_eval_ge_of_countermodel`:
uniform version of `problemReduces_disj` (unpair, compare the tag with `P.tag0`, reduce the
tagged component with the matching reduction at the same `n`, keep the tag). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_ured_disj
    (P : ProblemCalculus) (hP : P.Admissible) {A A' B B' : ℕ → Set BitString}
    (hA : exists_problems_problemK_eval_ge_of_countermodel_ured A A')
    (hB : exists_problems_problemK_eval_ge_of_countermodel_ured B B') :
    exists_problems_problemK_eval_ge_of_countermodel_ured (fun n => P.disj (A n) (B n))
      (fun n => P.disj (A' n) (B' n)) := by
  obtain ⟨hpair, hunpair, hinv, -, htag, -⟩ := hP
  obtain ⟨f, hf, hfA⟩ := hA
  obtain ⟨g, hg, hgB⟩ := hB
  have hc : PrimrecPred
      (fun a : (ℕ × BitString) × (BitString × BitString) => a.2.1 = P.tag0) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const _)
  refine ⟨fun p => ((P.unpair p.2 : Option (BitString × BitString)) :
      Part (BitString × BitString)).bind
        (fun z => bif decide (z.1 = P.tag0) then (f (p.1, z.2)).map (P.pair P.tag0)
          else (g (p.1, z.2)).map (P.pair P.tag1)), ?_, ?_⟩
  · exact Partrec.bind (Computable.ofOption (hunpair.comp Computable.snd))
      (Partrec.cond hc.decide.to_comp
        (Partrec.map (hf.comp ((Computable.fst.comp Computable.fst).pair
            (Computable.snd.comp Computable.snd)))
          (hpair.comp (Computable.const _) Computable.snd).to₂)
        (Partrec.map (hg.comp ((Computable.fst.comp Computable.fst).pair
            (Computable.snd.comp Computable.snd)))
          (hpair.comp (Computable.const _) Computable.snd).to₂)).to₂
  · rintro n hn z (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · obtain ⟨x', hx', hfx⟩ := hfA n hn x hx
      refine ⟨P.pair P.tag0 x', Or.inl ⟨x', hx', rfl⟩, ?_⟩
      beta_reduce
      rw [hinv]
      simp only [Part.coe_some, Part.bind_some, decide_true, Bool.cond_true]
      exact Part.mem_map _ hfx
    · obtain ⟨y', hy', hgy⟩ := hgB n hn y hy
      refine ⟨P.pair P.tag1 y', Or.inr ⟨y', hy', rfl⟩, ?_⟩
      beta_reduce
      rw [hinv]
      simp only [Part.coe_some, Part.bind_some, decide_eq_false (Ne.symm htag), Bool.cond_false]
      exact Part.mem_map _ hgy

/-- Step 5c of the proof of `exists_problems_problemK_eval_ge_of_countermodel`:
uniform version of `problemReduces_imp` (contravariant in the premise; the Gödel translation
gets `n` in unary together with the program). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_ured_imp
    (P : ProblemCalculus) (hP : P.Admissible) {A A' B B' : ℕ → Set BitString}
    (hA : exists_problems_problemK_eval_ge_of_countermodel_ured A' A)
    (hB : exists_problems_problemK_eval_ge_of_countermodel_ured B B') :
    exists_problems_problemK_eval_ge_of_countermodel_ured (fun n => P.imp (A n) (B n))
      (fun n => P.imp (A' n) (B' n)) := by
  obtain ⟨hpair, hunpair, hinv, -, -, hL, hG⟩ := hP
  obtain ⟨f, hf, hfA⟩ := hA
  obtain ⟨g, hg, hgB⟩ := hB
  have hlen : ∀ n : ℕ, ((List.cons true)^[n] ([] : BitString)).length = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', List.length_cons, ih]
  have henc : Computable (fun n : ℕ => (List.cons true)^[n] ([] : BitString)) :=
    (Primrec.nat_iterate Primrec.id (Primrec.const ([] : BitString))
      (Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂).to_comp
  let V : Map := fun sx => ((P.unpair sx.1 : Option (BitString × BitString)) :
      Part (BitString × BitString)).bind
    (fun aq => (f (aq.1.length, sx.2)).bind
      (fun x => (P.lang (aq.2, x)).bind (fun y => g (aq.1.length, y))))
  have hV : Partrec V :=
    Partrec.bind (Computable.ofOption (hunpair.comp Computable.fst))
      (Partrec.bind (hf.comp ((Computable.list_length.comp
          (Computable.fst.comp Computable.snd)).pair (Computable.snd.comp Computable.fst)))
        (Partrec.bind (hL.comp ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
            Computable.snd))
          (hg.comp ((Computable.list_length.comp (Computable.fst.comp
            (Computable.snd.comp (Computable.fst.comp Computable.fst)))).pair
              Computable.snd)).to₂).to₂).to₂
  obtain ⟨t, ht, hts⟩ := hG V hV
  refine ⟨fun p => Part.some (t (P.pair ((List.cons true)^[p.1] []) p.2)),
    (ht.comp (hpair.comp (henc.comp Computable.fst) Computable.snd)).partrec, ?_⟩
  intro n hn q hq
  refine ⟨_, ?_, Part.mem_some _⟩
  intro x' hx'
  obtain ⟨x, hx, hfx⟩ := hfA n hn x' hx'
  obtain ⟨y, hy, hLy⟩ := hq x hx
  obtain ⟨y', hy', hgy⟩ := hgB n hn y hy
  refine ⟨y', hy', ?_⟩
  rw [hts]
  refine Part.mem_bind_iff.2 ⟨((List.cons true)^[n] [], q), by simp [hinv], ?_⟩
  rw [hlen]
  exact Part.mem_bind_iff.2 ⟨x, hfx, Part.mem_bind_iff.2 ⟨y, hLy, hgy⟩⟩

/-- A finite disjunction of computable predicates is computable: for a finite type `W`, a
family `Q w` of computable predicates and any `S : W → Prop`, `a ↦ ∃ w, S w ∧ Q w a`. -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_computablePred_exists
    {α W : Type} [Primcodable α] [Finite W] (Q : W → α → Prop)
    (hQ : ∀ w, ComputablePred (Q w)) (S : W → Prop) :
    ComputablePred (fun a => ∃ w, S w ∧ Q w a) := by
  classical
  have := Fintype.ofFinite W
  suffices h : ∀ s : Finset W, ComputablePred (fun a => ∃ w ∈ s, Q w a) by
    refine (h (Finset.univ.filter S)).of_eq ?_
    intro a
    simp
  intro s
  induction s using Finset.induction_on with
  | empty => exact ComputablePred.computable_iff.2 ⟨fun _ => false, Computable.const false,
      by funext a; simp⟩
  | insert w s _ ih =>
    obtain ⟨f, hf, hfeq⟩ := ComputablePred.computable_iff.1 (hQ w)
    obtain ⟨g, hg, hgeq⟩ := ComputablePred.computable_iff.1 ih
    refine ComputablePred.computable_iff.2 ⟨fun a => f a || g a,
      Primrec.or.to_comp.comp hf hg, ?_⟩
    funext a
    have h1 := congrFun hfeq a
    have h2 := congrFun hgeq a
    rw [Bool.or_eq_true, ← h1, ← h2]
    simp only [Finset.mem_insert, exists_eq_or_imp]

/-- Step 6 of the proof of `exists_problems_problemK_eval_ge_of_countermodel`, case (A):
`X_T ∨ X_{T'}` and `X_{T ∪ T'}` are uniformly algorithmically equivalent.  Given an element of
`X_{T∪T'}` (or of the disjunction) read the tags and the length (decidable: `ω` computable). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_disj
    (D : Map) (P : ProblemCalculus) (hP : P.Admissible) {W : Type} [Finite W] [PartialOrder W]
    (r t : W) (ω : ℕ → ℕ → Option W)
    (hω : exists_problems_problemK_eval_ge_of_countermodel_family r t ω) (T T' : W → Prop) :
    exists_problems_problemK_eval_ge_of_countermodel_ured
      (fun n => P.disj (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T)
        (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T'))
      (fun n => exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n)
        (fun w => T w ∨ T' w)) ∧
    exists_problems_problemK_eval_ge_of_countermodel_ured
      (fun n => exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n)
        (fun w => T w ∨ T' w))
      (fun n => P.disj (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T)
        (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T')) := by
  obtain ⟨hpair, hunpair, hinv, -, htag, -⟩ := hP
  have hmono : ∀ (T1 T2 : W → Prop), (∀ w, T1 w → T2 w) → ∀ n,
      exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T1 ⊆
        exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T2 := by
    rintro T1 T2 h n z (⟨x, ⟨hx, w, hw, hTw⟩, rfl⟩ | hz)
    · exact Or.inl ⟨x, ⟨hx, w, hw, h w hTw⟩, rfl⟩
    · exact Or.inr hz
  constructor
  · refine ⟨fun p => ((P.unpair p.2).map Prod.snd : Part BitString),
      Computable.ofOption (Computable.option_map (hunpair.comp Computable.snd)
        (Computable.snd.comp Computable.snd).to₂), ?_⟩
    rintro n - z (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact ⟨a, hmono T _ (fun w h => Or.inl h) n ha, by simp [hinv]⟩
    · exact ⟨b, hmono T' _ (fun w h => Or.inr h) n hb, by simp [hinv]⟩
  · obtain ⟨fT, hfT, hfTeq⟩ := ComputablePred.computable_iff.1
      (exists_problems_problemK_eval_ge_of_countermodel_computablePred_exists
        (fun w (p : ℕ × ℕ) => ω p.1 p.2 = some w) hω.1 T)
    have hfT' : ∀ n l, fT (n, l) = true ↔ ∃ w, T w ∧ ω n l = some w := fun n l => by
      have h := congrFun hfTeq (n, l)
      simp only at h
      rw [h]
    have hc0 : Computable
        (fun q : (ℕ × BitString) × (BitString × BitString) => decide (q.2.1 = P.tag0)) :=
      (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const _)).decide.to_comp
    let bT : ℕ × BitString → Bool := fun p =>
      ((P.unpair p.2).map (fun ax => decide (ax.1 = P.tag0) && !fT (p.1, ax.2.length))).getD false
    have hbT : Computable bT :=
      Computable.option_getD (Computable.option_map (hunpair.comp Computable.snd)
        (Primrec.and.to_comp.comp hc0 (Primrec.not.to_comp.comp (hfT.comp
          ((Computable.fst.comp Computable.fst).pair
            (Computable.list_length.comp (Computable.snd.comp Computable.snd)))))).to₂)
        (Computable.const false)
    refine ⟨fun p => Part.some (bif bT p then P.pair P.tag1 p.2 else P.pair P.tag0 p.2),
      (Computable.cond hbT (hpair.comp (Computable.const _) Computable.snd)
        (hpair.comp (Computable.const _) Computable.snd)).partrec, ?_⟩
    rintro n - e (⟨x, ⟨hx, w, hw, hTw⟩, rfl⟩ | ⟨c, hc, rfl⟩)
    · by_cases hT : T w
      · have hfx : fT (n, x.length) = true := (hfT' n x.length).2 ⟨w, hT, hw⟩
        have hb : bT (n, P.pair P.tag0 x) = false := by simp [bT, hinv, hfx]
        refine ⟨P.pair P.tag0 (P.pair P.tag0 x), Or.inl ⟨_, Or.inl ⟨x, ⟨hx, w, hw, hT⟩, rfl⟩, rfl⟩,
          ?_⟩
        simp only [hb, Bool.cond_false]
        exact Part.mem_some _
      · have hT' : T' w := hTw.resolve_left hT
        have hfx : fT (n, x.length) = false := Bool.eq_false_iff.2 fun h => by
          obtain ⟨w', hw', hw'eq⟩ := (hfT' n x.length).1 h
          rw [hw, Option.some.injEq] at hw'eq
          exact hT (by rw [hw'eq]; exact hw')
        have hb : bT (n, P.pair P.tag0 x) = true := by simp [bT, hinv, hfx]
        refine ⟨P.pair P.tag1 (P.pair P.tag0 x), Or.inr ⟨_, Or.inl ⟨x, ⟨hx, w, hw, hT'⟩, rfl⟩, rfl⟩,
          ?_⟩
        simp only [hb, Bool.cond_true]
        exact Part.mem_some _
    · have hb : bT (n, P.pair P.tag1 c) = false := by simp [bT, hinv, Ne.symm htag]
      refine ⟨P.pair P.tag0 (P.pair P.tag1 c), Or.inl ⟨_, Or.inr ⟨c, hc, rfl⟩, rfl⟩, ?_⟩
      simp only [hb, Bool.cond_false]
      exact Part.mem_some _

/-- `X_T` is monotone in `T`. -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_xset_mono {W : Type}
    [PartialOrder W] (D : Map) (P : ProblemCalculus) (ω : ℕ → Option W) (T1 T2 : W → Prop)
    (h : ∀ w, T1 w → T2 w) :
    exists_problems_problemK_eval_ge_of_countermodel_xset D P ω T1 ⊆
      exists_problems_problemK_eval_ge_of_countermodel_xset D P ω T2 := by
  rintro z (⟨x, ⟨hx, w, hw, hTw⟩, rfl⟩ | hz)
  · exact Or.inl ⟨x, ⟨hx, w, hw, h w hTw⟩, rfl⟩
  · exact Or.inr hz

/-- The combination step shared by cases (B) and (C): a computable `G` such that, for
`a ∈ X_A` and `b ∈ X_B`, `G (n, a, b)` is `a` or `b` if one of them is in `1C`, otherwise
(`a = 0x`, `b = 0y` from worlds `u`, `v`) `b` if `u ≤ v`, `a` if `v ≤ u`, and `1[x, y] ∈ 1C`
if `u`, `v` are incomparable; hence it lies in `X_C` whenever `C` contains the world chosen. -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_comb
    (D : Map) (P : ProblemCalculus) (hP : P.Admissible) {W : Type} [Finite W] [PartialOrder W]
    (r t : W) (ω : ℕ → ℕ → Option W)
    (hω : exists_problems_problemK_eval_ge_of_countermodel_family r t ω) :
    ∃ G : ℕ × (BitString × BitString) → BitString, Computable G ∧
      ∀ (A B C : W → Prop), (∀ u v, u ≤ v → A u → B v → C v) →
        (∀ u v, v ≤ u → A u → B v → C u) → ∀ n,
          ∀ a ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) A,
          ∀ b ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) B,
            G (n, (a, b)) ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) C := by
  obtain ⟨hpair, hunpair, hinv, -, htag, -⟩ := hP
  have hQ : ∀ p : W × W, ComputablePred
      (fun x : ℕ × (ℕ × ℕ) => ω x.1 x.2.1 = some p.1 ∧ ω x.1 x.2.2 = some p.2) := by
    intro p
    obtain ⟨f1, hf1, hf1eq⟩ := ComputablePred.computable_iff.1 (hω.1 p.1)
    obtain ⟨f2, hf2, hf2eq⟩ := ComputablePred.computable_iff.1 (hω.1 p.2)
    refine ComputablePred.computable_iff.2 ⟨fun x => f1 (x.1, x.2.1) && f2 (x.1, x.2.2),
      Primrec.and.to_comp.comp (hf1.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))
        (hf2.comp (Computable.fst.pair (Computable.snd.comp Computable.snd))), ?_⟩
    funext x
    have h1 : (ω x.1 x.2.1 = some p.1) = (f1 (x.1, x.2.1) = true) := congrFun hf1eq (x.1, x.2.1)
    have h2 : (ω x.1 x.2.2 = some p.2) = (f2 (x.1, x.2.2) = true) := congrFun hf2eq (x.1, x.2.2)
    rw [Bool.and_eq_true, ← h1, ← h2]
  obtain ⟨fle, hfle, hfleeq⟩ := ComputablePred.computable_iff.1
    (exists_problems_problemK_eval_ge_of_countermodel_computablePred_exists
      (fun (p : W × W) (x : ℕ × (ℕ × ℕ)) => ω x.1 x.2.1 = some p.1 ∧ ω x.1 x.2.2 = some p.2) hQ
      (fun p => p.1 ≤ p.2))
  have hfle' : ∀ n l1 l2 u v, ω n l1 = some u → ω n l2 = some v →
      (fle (n, (l1, l2)) = true ↔ u ≤ v) := by
    intro n l1 l2 u v h1 h2
    have h : (∃ p : W × W, p.1 ≤ p.2 ∧ ω n l1 = some p.1 ∧ ω n l2 = some p.2) =
        (fle (n, (l1, l2)) = true) := congrFun hfleeq (n, (l1, l2))
    rw [← h]
    constructor
    · rintro ⟨⟨u', v'⟩, hle, h1', h2'⟩
      rw [h1, Option.some.injEq] at h1'
      rw [h2, Option.some.injEq] at h2'
      subst h1' h2'
      exact hle
    · intro hle
      exact ⟨(u, v), hle, h1, h2⟩
  let fstD : BitString → BitString := fun z => ((P.unpair z).map Prod.fst).getD []
  let sndD : BitString → BitString := fun z => ((P.unpair z).map Prod.snd).getD []
  have hfstD : Computable fstD := Computable.option_getD
    (Computable.option_map hunpair (Computable.fst.comp Computable.snd).to₂) (Computable.const [])
  have hsndD : Computable sndD := Computable.option_getD
    (Computable.option_map hunpair (Computable.snd.comp Computable.snd).to₂) (Computable.const [])
  have hdeq : Computable (fun p : BitString × BitString => decide (p.1 = p.2)) :=
    Primrec.eq.decide.to_comp
  let G : ℕ × (BitString × BitString) → BitString := fun p =>
    bif !decide (fstD p.2.1 = P.tag0) then p.2.1
    else bif !decide (fstD p.2.2 = P.tag0) then p.2.2
    else bif fle (p.1, ((sndD p.2.1).length, (sndD p.2.2).length)) then p.2.2
    else bif fle (p.1, ((sndD p.2.2).length, (sndD p.2.1).length)) then p.2.1
    else P.pair P.tag1 (P.pair (sndD p.2.1) (sndD p.2.2))
  have hG : Computable G := by
    have ha : Computable (fun p : ℕ × (BitString × BitString) => p.2.1) :=
      Computable.fst.comp Computable.snd
    have hb : Computable (fun p : ℕ × (BitString × BitString) => p.2.2) :=
      Computable.snd.comp Computable.snd
    have hta : Computable (fun p : ℕ × (BitString × BitString) =>
        !decide (fstD p.2.1 = P.tag0)) :=
      Primrec.not.to_comp.comp (hdeq.comp ((hfstD.comp ha).pair (Computable.const _)))
    have htb : Computable (fun p : ℕ × (BitString × BitString) =>
        !decide (fstD p.2.2 = P.tag0)) :=
      Primrec.not.to_comp.comp (hdeq.comp ((hfstD.comp hb).pair (Computable.const _)))
    have hle1 : Computable (fun p : ℕ × (BitString × BitString) =>
        fle (p.1, ((sndD p.2.1).length, (sndD p.2.2).length))) :=
      hfle.comp (Computable.fst.pair ((Computable.list_length.comp (hsndD.comp ha)).pair
        (Computable.list_length.comp (hsndD.comp hb))))
    have hle2 : Computable (fun p : ℕ × (BitString × BitString) =>
        fle (p.1, ((sndD p.2.2).length, (sndD p.2.1).length))) :=
      hfle.comp (Computable.fst.pair ((Computable.list_length.comp (hsndD.comp hb)).pair
        (Computable.list_length.comp (hsndD.comp ha))))
    have hpr : Computable (fun p : ℕ × (BitString × BitString) =>
        P.pair P.tag1 (P.pair (sndD p.2.1) (sndD p.2.2))) :=
      hpair.comp (Computable.const _) (hpair.comp (hsndD.comp ha) (hsndD.comp hb))
    exact Computable.cond hta ha (Computable.cond htb hb
      (Computable.cond hle1 hb (Computable.cond hle2 ha hpr)))
  refine ⟨G, hG, ?_⟩
  intro A B C hAB hBA n a ha b hb
  rcases ha with ⟨x, ⟨hx, u, hu, hAu⟩, rfl⟩ | ⟨c, hc, rfl⟩
  · rcases hb with ⟨y, ⟨hy, v, hv, hBv⟩, rfl⟩ | ⟨c, hc, rfl⟩
    · by_cases huv : u ≤ v
      · have h1 : fle (n, (x.length, y.length)) = true := (hfle' n _ _ u v hu hv).2 huv
        have hG1 : G (n, (P.pair P.tag0 x, P.pair P.tag0 y)) = P.pair P.tag0 y := by
          simp [G, fstD, sndD, hinv, h1]
        rw [hG1]
        exact Or.inl ⟨y, ⟨hy, v, hv, hAB u v huv hAu hBv⟩, rfl⟩
      · have h1 : fle (n, (x.length, y.length)) = false :=
          Bool.eq_false_iff.2 fun h => huv ((hfle' n _ _ u v hu hv).1 h)
        by_cases hvu : v ≤ u
        · have h2 : fle (n, (y.length, x.length)) = true := (hfle' n _ _ v u hv hu).2 hvu
          have hG1 : G (n, (P.pair P.tag0 x, P.pair P.tag0 y)) = P.pair P.tag0 x := by
            simp [G, fstD, sndD, hinv, h1, h2]
          rw [hG1]
          exact Or.inl ⟨x, ⟨hx, u, hu, hBA u v hvu hAu hBv⟩, rfl⟩
        · have h2 : fle (n, (y.length, x.length)) = false :=
            Bool.eq_false_iff.2 fun h => hvu ((hfle' n _ _ v u hv hu).1 h)
          have hG1 : G (n, (P.pair P.tag0 x, P.pair P.tag0 y)) =
              P.pair P.tag1 (P.pair x y) := by
            simp [G, fstD, sndD, hinv, h1, h2]
          rw [hG1]
          exact Or.inr ⟨P.pair x y, ⟨x, y, u, v, hx, hy, hu, hv, huv, hvu, rfl⟩, rfl⟩
    · have hG1 : G (n, (P.pair P.tag0 x, P.pair P.tag1 c)) = P.pair P.tag1 c := by
        simp [G, fstD, hinv, Ne.symm htag]
      rw [hG1]
      exact Or.inr ⟨c, hc, rfl⟩
  · have hG1 : G (n, (P.pair P.tag1 c, b)) = P.pair P.tag1 c := by
      simp [G, fstD, hinv, Ne.symm htag]
    rw [hG1]
    exact Or.inr ⟨c, hc, rfl⟩

/-- Step 7 of the proof of `exists_problems_problemK_eval_ge_of_countermodel`, case (B):
for upward closed `T`, `T'`, `X_T ∧ X_{T'}` and `X_{T ∩ T'}` are uniformly algorithmically
equivalent (`x ↦ [x, x]`; conversely look at the worlds of the two components: comparable worlds
give an element of the intersection, incomparable ones give an element of `C`). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_conj
    (D : Map) (P : ProblemCalculus) (hP : P.Admissible) {W : Type} [Finite W] [PartialOrder W]
    (r t : W) (ω : ℕ → ℕ → Option W)
    (hω : exists_problems_problemK_eval_ge_of_countermodel_family r t ω) (T T' : W → Prop)
    (hT : ∀ w w', w ≤ w' → T w → T w') (hT' : ∀ w w', w ≤ w' → T' w → T' w') :
    exists_problems_problemK_eval_ge_of_countermodel_ured
      (fun n => P.conj (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T)
        (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T'))
      (fun n => exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n)
        (fun w => T w ∧ T' w)) ∧
    exists_problems_problemK_eval_ge_of_countermodel_ured
      (fun n => exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n)
        (fun w => T w ∧ T' w))
      (fun n => P.conj (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T)
        (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T')) := by
  obtain ⟨G, hG, hGC⟩ := exists_problems_problemK_eval_ge_of_countermodel_comb D P hP r t ω hω
  obtain ⟨hpair, hunpair, hinv, -, -, -⟩ := hP
  constructor
  · refine ⟨fun p => Part.some (G (p.1, (P.unpair p.2).getD ([], []))),
      (hG.comp (Computable.fst.pair (Computable.option_getD (hunpair.comp Computable.snd)
        (Computable.const _)))).partrec, ?_⟩
    rintro n - z ⟨a, ha, b, hb, rfl⟩
    refine ⟨G (n, (a, b)), hGC T T' (fun w => T w ∧ T' w)
      (fun u v huv hu hv => ⟨hT u v huv hu, hv⟩) (fun u v hvu hu hv => ⟨hu, hT' v u hvu hv⟩)
      n a ha b hb, ?_⟩
    simp [hinv]
  · refine ⟨fun p => Part.some (P.pair p.2 p.2),
      (hpair.comp Computable.snd Computable.snd).partrec, ?_⟩
    rintro n - e he
    exact ⟨P.pair e e,
      ⟨e, exists_problems_problemK_eval_ge_of_countermodel_xset_mono D P (ω n) _ _
        (fun w h => h.1) he, e, exists_problems_problemK_eval_ge_of_countermodel_xset_mono D P
        (ω n) _ _ (fun w h => h.2) he, rfl⟩, Part.mem_some _⟩

/-- Step 8 of the proof of `exists_problems_problemK_eval_ge_of_countermodel`, case (C),
the easy half: for upward closed `T`, `T'`, `X_{T → T'}` uniformly reduces to `X_T → X_{T'}`
(the book's cases (1)-(3): given `x ∈ X_{T→T'}` and `y ∈ X_T`, compare the worlds of `x`, `y`
by their lengths and output `x`, `y` or the pair `[x, y]`; if either is in `C` output it; the
program is obtained from `(n, x)` by the Gödel property of `P.lang`). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_imp_easy
    (D : Map) (P : ProblemCalculus) (hP : P.Admissible) {W : Type} [Finite W] [PartialOrder W]
    (r t : W) (ω : ℕ → ℕ → Option W)
    (hω : exists_problems_problemK_eval_ge_of_countermodel_family r t ω) (T T' : W → Prop)
    (hT : ∀ w w', w ≤ w' → T w → T w') (_hT' : ∀ w w', w ≤ w' → T' w → T' w') :
    exists_problems_problemK_eval_ge_of_countermodel_ured
      (fun n => exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n)
        (exists_problems_problemK_eval_ge_of_countermodel_impset T T'))
      (fun n => P.imp (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T)
        (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T')) := by
  obtain ⟨G, hG, hGC⟩ := exists_problems_problemK_eval_ge_of_countermodel_comb D P hP r t ω hω
  obtain ⟨hpair, hunpair, hinv, -, -, hL, hGo⟩ := hP
  have hlen : ∀ n : ℕ, ((List.cons true)^[n] ([] : BitString)).length = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', List.length_cons, ih]
  have henc : Computable (fun n : ℕ => (List.cons true)^[n] ([] : BitString)) :=
    (Primrec.nat_iterate Primrec.id (Primrec.const ([] : BitString))
      (Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂).to_comp
  have hdec : Computable (fun sx : BitString × BitString => (P.unpair sx.1).getD ([], [])) :=
    Computable.option_getD (hunpair.comp Computable.fst) (Computable.const _)
  let V : Map := fun sx => Part.some (G (((P.unpair sx.1).getD ([], [])).1.length,
    (((P.unpair sx.1).getD ([], [])).2, sx.2)))
  have hV : Partrec V := (hG.comp ((Computable.list_length.comp (Computable.fst.comp hdec)).pair
    ((Computable.snd.comp hdec).pair Computable.snd))).partrec
  obtain ⟨tr, htr, htrs⟩ := hGo V hV
  refine ⟨fun p => Part.some (tr (P.pair ((List.cons true)^[p.1] []) p.2)),
    (htr.comp (hpair.comp (henc.comp Computable.fst) Computable.snd)).partrec, ?_⟩
  rintro n - e he
  refine ⟨_, ?_, Part.mem_some _⟩
  intro a ha
  refine ⟨G (n, (e, a)), hGC (exists_problems_problemK_eval_ge_of_countermodel_impset T T') T T'
    (fun u v huv hu hv => hu v huv hv) (fun u v hvu hu hv => hu u le_rfl (hT v u hvu hv))
    n e he a ha, ?_⟩
  rw [htrs]
  simp [V, hinv, hlen]

/-- The strings `x` of length `l` on which the program `q`, run on the input `0x` (that is,
`P.pair P.tag0 x`), outputs (in the language of `P`) a string satisfying `S`; the search of the
book looks for more than `2^{l/2+1}` such `x`. -/
private def exists_problems_problemK_eval_ge_of_countermodel_found (P : ProblemCalculus)
    (q : BitString) (l : ℕ) (S : BitString → Prop) : Prop :=
  2 ^ (l / 2 + 1) <
    {x : BitString | x.length = l ∧ ∃ s, S s ∧ s ∈ P.lang (q, P.pair P.tag0 x)}.ncard

/-- The strings `1[y, z]`, `1[z, y]` with `|z| = l` (case (2) of the book's search). -/
private def exists_problems_problemK_eval_ge_of_countermodel_pairs (P : ProblemCalculus)
    (y : BitString) (l : ℕ) : BitString → Prop :=
  fun s => ∃ z : BitString, z.length = l ∧
    (s = P.pair P.tag1 (P.pair y z) ∨ s = P.pair P.tag1 (P.pair z y))

/-- Counting: more than `2^{l/2+1}` strings of length `l` contain a random one (the strings `x`
with `2 C(x) < l` have programs of length `≤ l/2`, fewer than `2^{l/2+1}` of them). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_exists_rand
    (D : Map) (l : ℕ) (S : Set BitString) (hSl : ∀ x ∈ S, x.length = l)
    (hS : 2 ^ (l / 2 + 1) < S.ncard) :
    ∃ x ∈ S, exists_problems_problemK_eval_ge_of_countermodel_rand D x := by
  classical
  by_contra h
  push Not at h
  have hsub : S ⊆ ↑(compressibleWords D [] (l / 2)) := by
    intro x hx
    have h2 : 2 * plainK D x < (l : ℕ∞) := by rw [← hSl x hx]; exact not_le.1 (h x hx)
    have hlt : plainK D x < ((l / 2 + 1 : ℕ) : ℕ∞) := by
      by_cases ht : plainK D x = ⊤
      · rw [ht] at h2; exact absurd h2 (by simp)
      · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 ht
        rw [← hm] at h2 ⊢
        have : 2 * m < l := by exact_mod_cast h2
        exact_mod_cast (show m < l / 2 + 1 by omega)
    rw [plainK, condK] at hlt
    obtain ⟨b, ⟨p, hp, rfl⟩, hb⟩ := sInf_lt_iff.1 hlt
    have hplen : p.length ≤ l / 2 := by
      have : (p.length : ℕ∞) < ((l / 2 + 1 : ℕ) : ℕ∞) := hb
      exact Nat.lt_succ_iff.1 (by exact_mod_cast this)
    rw [Finset.mem_coe, compressibleWords, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
      exact ⟨p, mem_programsLe _ p hplen, progToOut_eq_some.mpr hp⟩
    · calc condK D x [] ≤ (p.length : ℕ∞) := sInf_le ⟨p, hp, rfl⟩
        _ ≤ ((l / 2 : ℕ) : ℕ∞) := by exact_mod_cast hplen
  have hcard : S.ncard < 2 ^ (l / 2 + 1) := by
    refine lt_of_le_of_lt ?_ (card_compressibleWordsLt D [] (l / 2))
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  omega

/-- The possible outputs of the search on a random input of length `l` (case (C), hard half):
`0t` with `|t| ≤ l/10`, `1[y, z]` with `|y|, |z| ≤ l/10`, or `1[y, z]` / `1[z, y]` with
`|y| ≤ l/10` and `|z| = l`. -/
private def exists_problems_problemK_eval_ge_of_countermodel_shape (P : ProblemCalculus) (l : ℕ)
    (s : BitString) : Prop :=
  (∃ t : BitString, 10 * t.length ≤ l ∧ s = P.pair P.tag0 t) ∨
    (∃ y z : BitString, 10 * y.length ≤ l ∧ 10 * z.length ≤ l ∧
      s = P.pair P.tag1 (P.pair y z)) ∨
    (∃ y : BitString, 10 * y.length ≤ l ∧
      exists_problems_problemK_eval_ge_of_countermodel_pairs P y l s)

/-- Step 9a1 of the proof of `exists_problems_problemK_eval_ge_of_countermodel`: the
complexity estimate of the book's search (case (C), hard half).  There is a constant `c` such
that: if `x` is random, `|x|` is a length of a world `u` where `T'` is false,
`|x| ≥ c + 5 |q|`, and the output `s` of the program `q` on the input `0x` lies in `X_{T'}`, then
`s` has one of the shapes of `shape P |x|`.  Proof: `C(s) ≤ |x| + 2|q| + O(1)` (`s` is computed
from `q` and `x`; a self-delimiting description of `q` followed by `x`); if `s = 0t` with `t`
random from a `T'`-world, then `|t| ≠ |x|` (the world of `|x|` is not in `T'`) and `|t| > |x|`
would give `|t| ≥ 10 |x|` (lengths ten times apart), `C(t) ≥ 5|x|`, contradicting
`C(t) ≤ C(s) + O(1)`; so `10 |t| ≤ |x|`; if `s = 1[y, z]` with `y`, `z` random from
incomparable worlds, then likewise `|y|, |z| ≤ |x|`, `|y| ≠ |z|`, so the shorter one has length
`≤ |x|/10` and the other one is either also that short or has length exactly `|x|`. -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_step9a1_shape
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible)
    {W : Type} [Finite W] [PartialOrder W] (r t : W) (ω : ℕ → ℕ → Option W)
    (hω : exists_problems_problemK_eval_ge_of_countermodel_family r t ω) (T' : W → Prop) :
    ∃ c : ℕ, ∀ (n : ℕ) (q x s : BitString) (u : W), 1 ≤ n →
      ω n x.length = some u → ¬ T' u → c + 5 * q.length ≤ x.length →
      exists_problems_problemK_eval_ge_of_countermodel_rand D x →
      s ∈ P.lang (q, P.pair P.tag0 x) →
      s ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T' →
        exists_problems_problemK_eval_ge_of_countermodel_shape P x.length s := by
  obtain ⟨hpair, hunpair, hinv, -, -, hL, -⟩ := hP
  obtain ⟨c0, hc0⟩ := plainK_le_of_mem_partrec D hD
    (fun z => P.lang (decodeFirst z, P.pair P.tag0 (decodeSecond z)))
    (hL.comp (CodedFiniteDistribution.decodeFirst_primrec.to_comp.pair
      (hpair.comp (Computable.const _) CodedFiniteDistribution.decodeSecond_primrec.to_comp)))
  obtain ⟨cl, hcl⟩ := plainK_le_length D hD
  obtain ⟨c1, hc1⟩ := plainK_le_of_mem_partrec D hD
    (fun z => (((P.unpair z).map Prod.snd : Option BitString) : Part BitString))
    (Computable.ofOption (Computable.option_map hunpair (Computable.snd.comp Computable.snd).to₂))
  obtain ⟨c2, hc2⟩ := plainK_le_of_mem_partrec D hD
    (fun z => ((((P.unpair z).bind (fun ac => P.unpair ac.2)).map Prod.fst : Option BitString) :
      Part BitString))
    (Computable.ofOption (Computable.option_map (Computable.option_bind hunpair
      (hunpair.comp (Computable.snd.comp Computable.snd)).to₂)
        (Computable.fst.comp Computable.snd).to₂))
  obtain ⟨c3, hc3⟩ := plainK_le_of_mem_partrec D hD
    (fun z => ((((P.unpair z).bind (fun ac => P.unpair ac.2)).map Prod.snd : Option BitString) :
      Part BitString))
    (Computable.ofOption (Computable.option_map (Computable.option_bind hunpair
      (hunpair.comp (Computable.snd.comp Computable.snd)).to₂)
        (Computable.snd.comp Computable.snd).to₂))
  refine ⟨c0 + cl + c1 + c2 + c3 + 1, fun n q x s u hn hu hT'u hl hxr hsq hs => ?_⟩
  have hgood := hω.2 n hn
  have hCs : plainK D s ≤ ((x.length + 2 * q.length + 1 + cl + c0 : ℕ) : ℕ∞) := by
    have h1 := hc0 (pairCode q x) s
      (by simpa [decodeFirst_pairCode, decodeSecond_pairCode] using hsq)
    have h2 := hcl (pairCode q x)
    calc plainK D s ≤ plainK D (pairCode q x) + c0 := h1
      _ ≤ (((pairCode q x).length : ℕ∞) + cl) + c0 := add_le_add_left h2 _
      _ = ((x.length + 2 * q.length + 1 + cl + c0 : ℕ) : ℕ∞) := by
        rw [length_pairCode]; push_cast; ring
  have hshort : ∀ (y : BitString) (w : W) (c' : ℕ),
      exists_problems_problemK_eval_ge_of_countermodel_rand D y → ω n y.length = some w →
        plainK D y ≤ plainK D s + c' → c' ≤ c1 + c2 + c3 → y.length ≤ x.length := by
    intro y w c' hy hw hyc hc'
    by_contra hgt
    push Not at hgt
    have h10 : 10 * x.length ≤ y.length :=
      hgood.2.2.2.1 x.length y.length (by rw [hu]; rfl) (by rw [hw]; rfl) hgt
    have hy' : (y.length : ℕ∞) ≤ 2 * plainK D y := hy
    have h3 : (y.length : ℕ∞) ≤
        2 * ((x.length + 2 * q.length + 1 + cl + c0 + c' : ℕ) : ℕ∞) := by
      calc (y.length : ℕ∞) ≤ 2 * plainK D y := hy'
        _ ≤ 2 * (plainK D s + c') := by gcongr
        _ ≤ 2 * (((x.length + 2 * q.length + 1 + cl + c0 : ℕ) : ℕ∞) + c') := by gcongr
        _ = 2 * ((x.length + 2 * q.length + 1 + cl + c0 + c' : ℕ) : ℕ∞) := by push_cast; ring
    have h4 : y.length ≤ 2 * (x.length + 2 * q.length + 1 + cl + c0 + c') := by
      exact_mod_cast h3
    omega
  rcases hs with ⟨t', ⟨ht'r, w, hw, hT'w⟩, rfl⟩ |
    ⟨c, ⟨y, z, uy, vz, hyr, hzr, huy, hvz, hyz, -, rfl⟩, rfl⟩
  · left
    refine ⟨t', ?_, rfl⟩
    have hle := hshort t' w c1 ht'r hw (hc1 _ t' (by simp [hinv])) (by omega)
    have hne : t'.length ≠ x.length := by
      intro heq
      rw [heq, hu, Option.some.injEq] at hw
      exact hT'u (by rw [hw]; exact hT'w)
    exact hgood.2.2.2.1 t'.length x.length (by rw [hw]; rfl) (by rw [hu]; rfl)
      (lt_of_le_of_ne hle hne)
  · right
    have hyl := hshort y uy c2 hyr huy (hc2 _ y (by simp [hinv])) (by omega)
    have hzl := hshort z vz c3 hzr hvz (hc3 _ z (by simp [hinv])) (by omega)
    have hyzne : y.length ≠ z.length := by
      intro heq
      rw [heq, hvz, Option.some.injEq] at huy
      exact hyz (le_of_eq huy.symm)
    by_cases hy : y.length = x.length
    · have hzlt : z.length < x.length := by omega
      have hz10 := hgood.2.2.2.1 z.length x.length (by rw [hvz]; rfl) (by rw [hu]; rfl) hzlt
      right
      exact ⟨z, hz10, y, hy, Or.inr rfl⟩
    · have hy10 := hgood.2.2.2.1 y.length x.length (by rw [huy]; rfl) (by rw [hu]; rfl)
        (lt_of_le_of_ne hyl hy)
      by_cases hz : z.length = x.length
      · right
        exact ⟨y, hy10, z, hz, Or.inl rfl⟩
      · have hz10 := hgood.2.2.2.1 z.length x.length (by rw [hvz]; rfl) (by rw [hu]; rfl)
          (lt_of_le_of_ne hzl hz)
        left
        exact ⟨y, z, hy10, hz10, rfl⟩

/-- Step 9a2 of the proof of `exists_problems_problemK_eval_ge_of_countermodel`: the
pigeonhole of the book's search.  If `l ≥ 40` and on every random input `0x`, `|x| = l`, the
program `q` outputs a string of one of the shapes of `shape P l`, then either some string `s` is
the output on more than `2^{l/2+1}` inputs `0x`, or some `y` is such that on more than
`2^{l/2+1}` inputs the output is `1[y, z]` or `1[z, y]` with `|z| = l`: there are at most
`2^{l/2+1}` nonrandom inputs, and fewer than `(2^{l/10+1})^2` classes (outputs of the first two
shapes, strings `y` of the third shape), while `2^l > 2^{2(l/10+1)} 2^{l/2+1} + 2^{l/2+1}`. -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_step9a2_pigeonhole
    (D : Map) (P : ProblemCalculus) (q : BitString) (l : ℕ) (hl : 40 ≤ l)
    (h : ∀ x : BitString, x.length = l → exists_problems_problemK_eval_ge_of_countermodel_rand D x →
      ∃ s, s ∈ P.lang (q, P.pair P.tag0 x) ∧
        exists_problems_problemK_eval_ge_of_countermodel_shape P l s) :
    (∃ s, exists_problems_problemK_eval_ge_of_countermodel_found P q l (fun s' => s' = s)) ∨
      ∃ y, exists_problems_problemK_eval_ge_of_countermodel_found P q l
        (exists_problems_problemK_eval_ge_of_countermodel_pairs P y l) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hS, hY⟩ := hcon
  set K := 2 ^ (l / 2 + 1) with hK
  set m := l / 10 with hm
  let L := stringsOfLength l
  let B := (programsLe m).toFinset
  let A : BitString → Finset BitString := fun s =>
    L.filter (fun x => s ∈ P.lang (q, P.pair P.tag0 x))
  let Bf : BitString → Finset BitString := fun y =>
    L.filter (fun x => ∃ s', exists_problems_problemK_eval_ge_of_countermodel_pairs P y l s' ∧
      s' ∈ P.lang (q, P.pair P.tag0 x))
  have hA : ∀ s, (A s).card ≤ K := by
    intro s
    have h1 := hS s
    unfold exists_problems_problemK_eval_ge_of_countermodel_found at h1
    have hset : {x : BitString | x.length = l ∧
        ∃ s', s' = s ∧ s' ∈ P.lang (q, P.pair P.tag0 x)} = ↑(A s) := by
      ext x; simp [A, L, mem_stringsOfLength]
    rw [hset, Set.ncard_coe_finset] at h1
    omega
  have hB : ∀ y, (Bf y).card ≤ K := by
    intro y
    have h1 := hY y
    unfold exists_problems_problemK_eval_ge_of_countermodel_found at h1
    have hset : {x : BitString | x.length = l ∧
        ∃ s', exists_problems_problemK_eval_ge_of_countermodel_pairs P y l s' ∧
          s' ∈ P.lang (q, P.pair P.tag0 x)} = ↑(Bf y) := by
      ext x; simp [Bf, L, mem_stringsOfLength]
    rw [hset, Set.ncard_coe_finset] at h1
    omega
  let S1 : Finset BitString := B.image (P.pair P.tag0) ∪
    (B ×ˢ B).image (fun p => P.pair P.tag1 (P.pair p.1 p.2))
  let R := L.filter (fun x => exists_problems_problemK_eval_ge_of_countermodel_rand D x)
  have hR : R ⊆ S1.biUnion A ∪ B.biUnion Bf := by
    intro x hx
    simp only [R, L, Finset.mem_filter, mem_stringsOfLength] at hx
    obtain ⟨s, hs, hshape⟩ := h x hx.1 hx.2
    rcases hshape with ⟨t, ht, rfl⟩ | ⟨y, z, hy, hz, rfl⟩ | ⟨y, hy, hpy⟩
    · apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      refine ⟨P.pair P.tag0 t, Finset.mem_union_left _ (Finset.mem_image.2
        ⟨t, List.mem_toFinset.2 (mem_programsLe m t (by omega)), rfl⟩), ?_⟩
      simp only [A, L, Finset.mem_filter, mem_stringsOfLength]
      exact ⟨hx.1, hs⟩
    · apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      refine ⟨P.pair P.tag1 (P.pair y z), Finset.mem_union_right _ (Finset.mem_image.2
        ⟨(y, z), Finset.mem_product.2 ⟨List.mem_toFinset.2 (mem_programsLe m y (by omega)),
          List.mem_toFinset.2 (mem_programsLe m z (by omega))⟩, rfl⟩), ?_⟩
      simp only [A, L, Finset.mem_filter, mem_stringsOfLength]
      exact ⟨hx.1, hs⟩
    · apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine ⟨y, List.mem_toFinset.2 (mem_programsLe m y (by omega)), ?_⟩
      simp only [Bf, L, Finset.mem_filter, mem_stringsOfLength]
      exact ⟨hx.1, s, hpy, hs⟩
  have hb : B.card + 1 ≤ 2 ^ (m + 1) := by
    have h1 : B.card ≤ (programsLe m).length := List.toFinset_card_le (programsLe m)
    have h2 := length_programsLe_add_one m
    omega
  have hS1 : S1.card ≤ B.card + B.card * B.card := by
    calc S1.card ≤ (B.image (P.pair P.tag0)).card +
          ((B ×ˢ B).image (fun p => P.pair P.tag1 (P.pair p.1 p.2))).card :=
          Finset.card_union_le _ _
      _ ≤ B.card + (B ×ˢ B).card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = B.card + B.card * B.card := by rw [Finset.card_product]
  have hRle : R.card ≤ S1.card * K + B.card * K := by
    calc R.card ≤ (S1.biUnion A ∪ B.biUnion Bf).card := Finset.card_le_card hR
      _ ≤ (S1.biUnion A).card + (B.biUnion Bf).card := Finset.card_union_le _ _
      _ ≤ S1.card * K + B.card * K := Nat.add_le_add
          (Finset.card_biUnion_le_card_mul _ _ _ (fun s _ => hA s))
          (Finset.card_biUnion_le_card_mul _ _ _ (fun y _ => hB y))
  have hnon : (L.filter (fun x => ¬ exists_problems_problemK_eval_ge_of_countermodel_rand D x)).card
      ≤ K := by
    by_contra hlt
    push Not at hlt
    obtain ⟨x, hx, hxr⟩ := exists_problems_problemK_eval_ge_of_countermodel_exists_rand D l
      (↑(L.filter (fun x => ¬ exists_problems_problemK_eval_ge_of_countermodel_rand D x)))
      (fun x hx => by
        have hx' := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).1
        simpa [L, mem_stringsOfLength] using hx')
      (by rwa [Set.ncard_coe_finset])
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2 hxr
  have htot : R.card +
      (L.filter (fun x => ¬ exists_problems_problemK_eval_ge_of_countermodel_rand D x)).card =
        2 ^ l := by
    rw [Finset.card_filter_add_card_filter_not, card_stringsOfLength]
  have hexp : 2 ^ (m + 1) * 2 ^ (m + 1) * K * 2 ≤ 2 ^ l := by
    rw [hK, ← pow_add, ← pow_add, ← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKpos : 1 ≤ K := Nat.one_le_two_pow
  have hsq := Nat.mul_le_mul hb hb
  have h3 : (S1.card + B.card + 1) * K ≤ 2 ^ (m + 1) * 2 ^ (m + 1) * K :=
    Nat.mul_le_mul_right _ (by nlinarith)
  nlinarith

/-- Step 9a of the proof of `exists_problems_problemK_eval_ge_of_countermodel`: the
existence half of the book's search (case (C), hard half).  There is a constant `c` such that for
a program `q` solving `X_T → X_{T'}` and a length `l ≥ c + 5 |q|` of a world `u` with `T` true
and `T'` false, running `q` on the inputs `0x` (`x` of length `l`), either some string `s` is
the output on more than `2^{l/2+1}` of these inputs, or some `y` is such that on more than
`2^{l/2+1}` of these inputs the output is `1[y,z]` or `1[z,y]` with `|z| = l`.  Proof: for a
random `x` of length `l` the input `0x` lies in `X_T` (`T u`), so `s = q(0x)` is defined, lies in
`X_{T'}`, and `C(s) ≤ l + 2|q| + O(1)`; `s` is `0t` with `t` random from a `T'`-world (so
`|t| ≤ l/10`: `|t| ≠ l` as `u ∉ T'`, and `|t| ≥ 10 l` is impossible by complexity) or `1[y,z]`
with random `y, z` from incomparable worlds (different lengths, both `≤ l` by complexity, so one
of them has length `≤ l/10`); count the possible outputs and `y`'s: there are `≤ 2^{l/5+4}`
classes for `≥ 2^l - 2^{l/2+1}` random inputs (pigeonhole). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_search_exists
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible)
    {W : Type} [Finite W] [PartialOrder W] (r t : W) (_hr : ∀ w, r ≤ w) (ω : ℕ → ℕ → Option W)
    (hω : exists_problems_problemK_eval_ge_of_countermodel_family r t ω) (T T' : W → Prop)
    (_hT' : ∀ w w', w ≤ w' → T' w → T' w') :
    ∃ c : ℕ, ∀ (n : ℕ) (q : BitString) (l : ℕ) (u : W), 1 ≤ n →
      q ∈ P.imp (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T)
        (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T') →
      ω n l = some u → T u → ¬ T' u → c + 5 * q.length ≤ l →
        (∃ s, exists_problems_problemK_eval_ge_of_countermodel_found P q l (fun s' => s' = s)) ∨
        ∃ y, exists_problems_problemK_eval_ge_of_countermodel_found P q l
          (exists_problems_problemK_eval_ge_of_countermodel_pairs P y l) := by
  obtain ⟨c1, hc1⟩ :=
    exists_problems_problemK_eval_ge_of_countermodel_step9a1_shape D hD P hP r t ω hω T'
  refine ⟨c1 + 40, fun n q l u hn hq hu hTu hT'u hl => ?_⟩
  apply exists_problems_problemK_eval_ge_of_countermodel_step9a2_pigeonhole D P q l (by omega)
  intro x hxl hxr
  have hx0 : P.pair P.tag0 x ∈
      exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T :=
    Or.inl ⟨x, ⟨hxr, u, by rw [hxl]; exact hu, hTu⟩, rfl⟩
  obtain ⟨s, hs, hsq⟩ := hq _ hx0
  refine ⟨s, hsq, ?_⟩
  have h := hc1 n q x s u hn (by rw [hxl]; exact hu) hT'u (by rw [hxl]; omega) hxr hsq hs
  rwa [hxl] at h

/-- Step 9b of the proof of `exists_problems_problemK_eval_ge_of_countermodel`: the
soundness half of the book's search.  If `q` solves `X_T → X_{T'}`, `l` is a length of a world
`u` with `T u`, and `s` is the output of `q` on more than `2^{l/2+1}` inputs `0x` with `|x| = l`,
then `s ∈ X_{T'}`; if `y` is as in case (2), then `y` is random and comes from a world `v`
incomparable with `u`.  Proof: the number of nonrandom strings of length `l` is `< 2^{l/2+1}`
(fewer than `2^{⌈l/2⌉}` programs of length `< l/2`), so one of these `x` is random; then
`0x ∈ X_T` (as `T u`), so the (unique) output `s` of `q` on `0x` is in `X_{T'}` (resp. is some
`1[y,z]` or `1[z,y]` in `1C` with `|z| = l`, so `z` is from `u` and `y` is random from a world
incomparable with `u`). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_search_sound
    (D : Map) (_hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible)
    {W : Type} [Finite W] [PartialOrder W] (r t : W) (ω : ℕ → ℕ → Option W)
    (_hω : exists_problems_problemK_eval_ge_of_countermodel_family r t ω) (T T' : W → Prop) :
    ∀ (n : ℕ) (q : BitString) (l : ℕ) (u : W), 1 ≤ n →
      q ∈ P.imp (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T)
        (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T') →
      ω n l = some u → T u →
        (∀ s, exists_problems_problemK_eval_ge_of_countermodel_found P q l (fun s' => s' = s) →
          s ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T') ∧
        (∀ y, exists_problems_problemK_eval_ge_of_countermodel_found P q l
            (exists_problems_problemK_eval_ge_of_countermodel_pairs P y l) →
          exists_problems_problemK_eval_ge_of_countermodel_rand D y ∧
            ∃ v, ω n y.length = some v ∧ ¬ u ≤ v ∧ ¬ v ≤ u) := by
  intro n q l u _ hq hu hTu
  obtain ⟨-, -, hinv, -, htag, -⟩ := hP
  have hinj : ∀ a b a' b', P.pair a b = P.pair a' b' → a = a' ∧ b = b' := by
    intro a b a' b' h
    have h' := congrArg P.unpair h
    rw [hinv, hinv] at h'
    simpa only [Option.some.injEq, Prod.mk.injEq] using h'
  have hkey : ∀ S : BitString → Prop,
      exists_problems_problemK_eval_ge_of_countermodel_found P q l S →
        ∃ s, S s ∧ s ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T' := by
    intro S hS
    obtain ⟨x, ⟨hxl, s, hSs, hs⟩, hxr⟩ :=
      exists_problems_problemK_eval_ge_of_countermodel_exists_rand D l _ (fun x hx => hx.1) hS
    have hx0 : P.pair P.tag0 x ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T
        :=
      Or.inl ⟨x, ⟨hxr, u, by rw [hxl]; exact hu, hTu⟩, rfl⟩
    obtain ⟨s', hs', hs'q⟩ := hq _ hx0
    exact ⟨s, hSs, (Part.mem_unique hs hs'q) ▸ hs'⟩
  refine ⟨fun s hs => ?_, fun y hy => ?_⟩
  · obtain ⟨s', rfl, hs'⟩ := hkey _ hs
    exact hs'
  · obtain ⟨s, ⟨z, hzl, hs⟩, hsX⟩ := hkey _ hy
    rcases hsX with ⟨t', -, ht'⟩ | ⟨c, hc, hcs⟩
    · exfalso
      rcases hs with rfl | rfl <;> exact htag (hinj _ _ _ _ ht').1
    · obtain ⟨a, b, ua, vb, hra, hrb, hua, hvb, hab, hba, rfl⟩ := hc
      rcases hs with rfl | rfl
      · obtain ⟨rfl, rfl⟩ := hinj _ _ _ _ (hinj _ _ _ _ hcs).2
        rw [hzl, hu, Option.some.injEq] at hvb
        subst hvb
        exact ⟨hra, ua, hua, hba, hab⟩
      · obtain ⟨rfl, rfl⟩ := hinj _ _ _ _ (hinj _ _ _ _ hcs).2
        rw [hzl, hu, Option.some.injEq] at hua
        subst hua
        exact ⟨hrb, vb, hvb, hab, hba⟩

/-- Step 9c1, decidable test: `s` is a string `1[y, z]` or `1[z, y]` with `|z| = l`. -/
private def exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_pairsB (P :
    ProblemCalculus) (y : BitString) (l : ℕ) (s : BitString) : Bool :=
  ((P.unpair s).map (fun ab => decide (ab.1 = P.tag1) &&
    ((P.unpair ab.2).map (fun cd => (decide (cd.1 = y) && decide (cd.2.length = l)) ||
      (decide (cd.2 = y) && decide (cd.1.length = l)))).getD false)).getD false

/-- Step 9c1: the test of a candidate `(kind, w)` on an output `s`. -/
private def exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test (P :
    ProblemCalculus) (kw : Bool × BitString) (l : ℕ) (s : BitString) : Bool :=
  bif kw.1 then exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_pairsB P kw.2 l s
      else decide (s = kw.2)

/-- Step 9c1: the output of the program `q` on `0x` within `t` steps (the code `c` computes
`P.lang`). -/
private def exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out (P :
    ProblemCalculus) (c : Nat.Partrec.Code) (t : ℕ) (q x : BitString) :
    Option BitString :=
  (Nat.Partrec.Code.evaln t c (Encodable.encode (q, P.pair P.tag0 x))).bind
    (fun n => Encodable.decode (α := BitString) n)

/-- Step 9c1: the stage-`t` count for the candidate `kw`. -/
private def exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt (P :
    ProblemCalculus) (c : Nat.Partrec.Code) (t : ℕ) (kw : Bool × BitString)
    (q : BitString) (l : ℕ) : ℕ :=
  (allStrings l).countP (fun x =>
      ((exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out P c t q x).map
      (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P kw l)).getD false)

/-- Step 9c1: the search predicate on `(q, l)` and the code `n = ⟨τ, candidate⟩`. -/
private def exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_chk (P :
    ProblemCalculus) (c : Nat.Partrec.Code) (a : BitString × ℕ) (n : ℕ) :
    Bool :=
  ((Encodable.decode (α := Bool × BitString) n.unpair.2).map (fun kw =>
    decide (2 ^ (a.2 / 2 + 1) < exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt
        P c n.unpair.1 kw a.1 a.2))).getD false

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_pairsB_computable (P
    : ProblemCalculus) (hP : P.Admissible) :
    Computable (fun u : (BitString × ℕ) × BitString =>
        exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_pairsB P u.1.1 u.1.2 u.2) :=
        by
  obtain ⟨-, hunpair, -, -, -, -⟩ := hP
  have hdeq : Computable₂ (fun a b : BitString => decide (a = b)) :=
    (PrimrecRel.decide Primrec.eq).to_comp
  have hlen : Computable₂ (fun (a : BitString) (l : ℕ) => decide (a.length = l)) :=
    ((PrimrecRel.decide Primrec.eq).comp (Primrec.list_length.comp Primrec.fst)
      Primrec.snd).to_comp
  unfold exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_pairsB
  refine Computable.option_getD (Computable.option_map (hunpair.comp Computable.snd) ?_)
    (Computable.const false)
  have hy : Computable (fun w : (((BitString × ℕ) × BitString) × (BitString × BitString)) ×
      (BitString × BitString) => w.1.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
  have hl : Computable (fun w : (((BitString × ℕ) × BitString) × (BitString × BitString)) ×
      (BitString × BitString) => w.1.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
  have hc1 : Computable (fun w : (((BitString × ℕ) × BitString) × (BitString × BitString)) ×
      (BitString × BitString) => w.2.1) := Computable.fst.comp Computable.snd
  have hc2 : Computable (fun w : (((BitString × ℕ) × BitString) × (BitString × BitString)) ×
      (BitString × BitString) => w.2.2) := Computable.snd.comp Computable.snd
  have hH : Computable₂ (fun (v : ((BitString × ℕ) × BitString) × (BitString × BitString))
      (cd : BitString × BitString) => (decide (cd.1 = v.1.1.1) && decide (cd.2.length = v.1.1.2))
        || (decide (cd.2 = v.1.1.1) && decide (cd.1.length = v.1.1.2))) :=
    Primrec.or.to_comp.comp
      (Primrec.and.to_comp.comp (hdeq.comp hc1 hy) (hlen.comp hc2 hl))
      (Primrec.and.to_comp.comp (hdeq.comp hc2 hy) (hlen.comp hc1 hl))
  refine Primrec.and.to_comp.comp
    (hdeq.comp (Computable.fst.comp Computable.snd) (Computable.const P.tag1))
    (Computable.option_getD (Computable.option_map
      (hunpair.comp (Computable.snd.comp Computable.snd)) hH) (Computable.const false))

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test_computable (P :
    ProblemCalculus) (hP : P.Admissible) :
    Computable (fun u : ((Bool × BitString) × ℕ) × BitString =>
        exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P u.1.1 u.1.2 u.2) :=
        by
  have hdeq : Computable₂ (fun a b : BitString => decide (a = b)) :=
    (PrimrecRel.decide Primrec.eq).to_comp
  have hk : Computable (fun u : ((Bool × BitString) × ℕ) × BitString => u.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hw : Computable (fun u : ((Bool × BitString) × ℕ) × BitString => u.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hl : Computable (fun u : ((Bool × BitString) × ℕ) × BitString => u.1.2) :=
    Computable.snd.comp Computable.fst
  have hs : Computable (fun u : ((Bool × BitString) × ℕ) × BitString => u.2) := Computable.snd
  have hA : Computable (fun u : ((Bool × BitString) × ℕ) × BitString =>
      exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_pairsB P u.1.1.2 u.1.2 u.2) :=
          by
    have := (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_pairsB_computable P
        hP).comp (Computable.pair (Computable.pair hw hl) hs)
    exact this
  have hB : Computable (fun u : ((Bool × BitString) × ℕ) × BitString =>
      decide (u.2 = u.1.1.2)) := hdeq.comp hs hw
  unfold exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test
  exact Computable.cond hk hA hB

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out_computable (P :
    ProblemCalculus) (hP : P.Admissible)
    (c : Nat.Partrec.Code) :
    Computable (fun w : (ℕ × BitString) × BitString =>
        exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out P c w.1.1 w.1.2 w.2) :=
        by
  obtain ⟨hpair, -, -, -, -, -⟩ := hP
  have ht : Computable (fun w : (ℕ × BitString) × BitString => w.1.1) :=
    Computable.fst.comp Computable.fst
  have hq : Computable (fun w : (ℕ × BitString) × BitString => w.1.2) :=
    Computable.snd.comp Computable.fst
  have hx : Computable (fun w : (ℕ × BitString) × BitString => w.2) := Computable.snd
  have hin : Computable (fun w : (ℕ × BitString) × BitString =>
      Encodable.encode (w.1.2, P.pair P.tag0 w.2)) :=
    Computable.encode.comp (Computable.pair hq (hpair.comp (Computable.const P.tag0) hx))
  have hev : Computable (fun w : (ℕ × BitString) × BitString =>
      Nat.Partrec.Code.evaln w.1.1 c (Encodable.encode (w.1.2, P.pair P.tag0 w.2))) :=
    (evalnCoreComputable c).comp (Computable.pair ht hin)
  have hdec : Computable₂ (fun (_ : (ℕ × BitString) × BitString) (n : ℕ) =>
      Encodable.decode (α := BitString) n) :=
    (Computable.decode.comp Computable.snd).to₂
  unfold exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out
  exact Computable.option_bind hev hdec

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt_computable (P :
    ProblemCalculus) (hP : P.Admissible)
    (c : Nat.Partrec.Code) :
    Computable (fun z : (BitString × ℕ) × ℕ × (Bool × BitString) =>
      exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt P c z.2.1 z.2.2 z.1.1
          z.1.2) := by
  have hf : Computable (fun z : (BitString × ℕ) × ℕ × (Bool × BitString) => allStrings z.1.2) :=
    (CodedFiniteDistribution.allStrings_primrec.comp (Primrec.snd.comp Primrec.fst)).to_comp
  have hp : Computable₂ (fun (z : (BitString × ℕ) × ℕ × (Bool × BitString)) (x : BitString) =>
      ((exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out P c z.2.1 z.1.1 x).map
          (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P z.2.2 z.1.2)).getD
          false) := by
    have h1 : Computable (fun v : ((BitString × ℕ) × ℕ × (Bool × BitString)) × BitString =>
        exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out P c v.1.2.1 v.1.1.1 v.2)
            := by
      have ht : Computable (fun v : ((BitString × ℕ) × ℕ × (Bool × BitString)) × BitString =>
          v.1.2.1) := Computable.fst.comp (Computable.snd.comp Computable.fst)
      have hq : Computable (fun v : ((BitString × ℕ) × ℕ × (Bool × BitString)) × BitString =>
          v.1.1.1) := Computable.fst.comp (Computable.fst.comp Computable.fst)
      have hx : Computable (fun v : ((BitString × ℕ) × ℕ × (Bool × BitString)) × BitString =>
          v.2) := Computable.snd
      have := (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out_computable P hP
          c).comp (Computable.pair (Computable.pair ht hq) hx)
      exact this
    have h2 : Computable₂ (fun (v : ((BitString × ℕ) × ℕ × (Bool × BitString)) × BitString)
        (s : BitString) => exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P
            v.1.2.2 v.1.1.2 s) := by
      have hk : Computable (fun w : (((BitString × ℕ) × ℕ × (Bool × BitString)) × BitString) ×
          BitString => w.1.1.2.2) :=
        Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
      have hl : Computable (fun w : (((BitString × ℕ) × ℕ × (Bool × BitString)) × BitString) ×
          BitString => w.1.1.1.2) :=
        Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
      have hs : Computable (fun w : (((BitString × ℕ) × ℕ × (Bool × BitString)) × BitString) ×
          BitString => w.2) := Computable.snd
      have := (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test_computable P
          hP).comp (Computable.pair (Computable.pair hk hl) hs)
      exact this
    exact Computable.option_getD (Computable.option_map h1 h2) (Computable.const false)
  exact (Computable.list_length.comp (computable_list_filter hf hp)).of_eq (fun z => by
    simp [exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt,
        List.countP_eq_length_filter])

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_chk_computable (P :
    ProblemCalculus) (hP : P.Admissible)
    (c : Nat.Partrec.Code) : Computable₂
        (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_chk P c) := by
  have hlt : Computable₂ (fun a b : ℕ => decide (a < b)) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp
  have hpow : Computable (fun v : ((BitString × ℕ) × ℕ) × (Bool × BitString) =>
      2 ^ (v.1.1.2 / 2 + 1)) :=
    (Primrec.list_length.comp (CodedFiniteDistribution.allStrings_primrec.comp
      (Primrec.succ.comp (Primrec.nat_div.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 2))))).to_comp.of_eq
      (fun v => length_allStrings _)
  have hc : Computable (fun v : ((BitString × ℕ) × ℕ) × (Bool × BitString) =>
      exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt P c v.1.2.unpair.1 v.2
          v.1.1.1 v.1.1.2) := by
    have hq : Computable (fun v : ((BitString × ℕ) × ℕ) × (Bool × BitString) => v.1.1) :=
      Computable.fst.comp Computable.fst
    have ht : Computable (fun v : ((BitString × ℕ) × ℕ) × (Bool × BitString) =>
        v.1.2.unpair.1) :=
      Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst))
    have hk : Computable (fun v : ((BitString × ℕ) × ℕ) × (Bool × BitString) => v.2) :=
      Computable.snd
    have := (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt_computable P hP
        c).comp (Computable.pair hq (Computable.pair ht hk))
    exact this
  have hD : Computable₂ (fun (v : (BitString × ℕ) × ℕ) (kw : Bool × BitString) =>
      decide (2 ^ (v.1.2 / 2 + 1) <
          exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt P c v.2.unpair.1 kw
          v.1.1 v.1.2)) := by
    have := hlt.comp hpow hc
    exact this
  have hdec : Computable (fun v : (BitString × ℕ) × ℕ =>
      Encodable.decode (α := Bool × BitString) v.2.unpair.2) :=
    Computable.decode.comp (Computable.snd.comp (Computable.unpair.comp Computable.snd))
  unfold exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_chk
  exact Computable.option_getD (Computable.option_map hdec hD) (Computable.const false)

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_pairsB_iff (P :
    ProblemCalculus) (hP : P.Admissible) (y : BitString) (l : ℕ)
    (s : BitString) :
    exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_pairsB P y l s = true ↔
        exists_problems_problemK_eval_ge_of_countermodel_pairs P y l s := by
  obtain ⟨-, -, hup, hinv, -, -⟩ := hP
  unfold exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_pairsB
      exists_problems_problemK_eval_ge_of_countermodel_pairs
  constructor
  · intro h
    cases h1 : P.unpair s with
    | none => simp [h1] at h
    | some ab =>
      obtain ⟨a, b⟩ := ab
      cases h2 : P.unpair b with
      | none => simp [h1, h2] at h
      | some cd =>
        obtain ⟨c', d⟩ := cd
        simp only [h1, h2, Option.map_some, Option.getD_some, Bool.and_eq_true,
          decide_eq_true_eq, Bool.or_eq_true] at h
        obtain ⟨ha, h⟩ := h
        have hs := hinv s _ _ h1
        have hb := hinv b _ _ h2
        subst ha
        rcases h with ⟨hc, hl⟩ | ⟨hc, hl⟩
        · subst hc
          exact ⟨d, hl, Or.inl (by rw [← hs, ← hb])⟩
        · subst hc
          exact ⟨c', hl, Or.inr (by rw [← hs, ← hb])⟩
  · rintro ⟨z, hz, rfl | rfl⟩ <;> simp [hup, hz]

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test_false (P :
    ProblemCalculus) (w : BitString) (l : ℕ) (s : BitString) :
    exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P (false, w) l s = true ↔ s
        = w := by
  simp [exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test]

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test_true (P :
    ProblemCalculus) (hP : P.Admissible) (w : BitString) (l : ℕ)
    (s : BitString) :
    exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P (true, w) l s = true ↔
      exists_problems_problemK_eval_ge_of_countermodel_pairs P w l s := by
  simp [exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test,
      exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_pairsB_iff P hP]

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out_sound (P :
    ProblemCalculus) (c : Nat.Partrec.Code)
    (hc : c.eval = fun n => (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
      (fun a => Part.map Encodable.encode (P.lang a)))
    {t : ℕ} {q x s : BitString} (h :
        exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out P c t q x = some s) :
    s ∈ P.lang (q, P.pair P.tag0 x) := by
  unfold exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, hs⟩ := h
  have h1 := Nat.Partrec.Code.evaln_sound hn
  rw [hc] at h1
  simp only [Part.mem_bind_iff, Part.mem_ofOption, Encodable.encodek, Option.mem_def,
    Option.some.injEq, Part.mem_map_iff] at h1
  obtain ⟨s'', hs'', a, ha, rfl⟩ := h1
  subst hs''
  rw [Encodable.encodek, Option.some.injEq] at hs
  rw [← hs]; exact ha

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out_complete (P :
    ProblemCalculus) (c : Nat.Partrec.Code)
    (hc : c.eval = fun n => (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
      (fun a => Part.map Encodable.encode (P.lang a)))
    {q x s : BitString} (h : s ∈ P.lang (q, P.pair P.tag0 x)) :
    ∃ t, ∀ t' ≥ t, exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out P c t' q x =
        some s := by
  have h1 : Encodable.encode s ∈ c.eval (Encodable.encode (q, P.pair P.tag0 x)) := by
    rw [hc]
    simp only [Part.mem_bind_iff, Part.mem_ofOption, Encodable.encodek, Option.mem_def,
      Option.some.injEq, Part.mem_map_iff]
    exact ⟨_, rfl, s, h, rfl⟩
  obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp h1
  refine ⟨t, fun t' hle => ?_⟩
  have := Nat.Partrec.Code.evaln_mono hle ht
  unfold exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out
  rw [Option.mem_def] at this
  rw [this]
  simp

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt_eq_card (P :
    ProblemCalculus) (c : Nat.Partrec.Code) (t : ℕ)
    (kw : Bool × BitString) (q : BitString) (l : ℕ) :
    exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt P c t kw q l =
        ((stringsOfLength l).filter
      (fun x => ((exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out P c t q x).map
          (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P kw l)).getD false
          = true)).card := by
  classical
  unfold exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt
  rw [List.countP_eq_length_filter]
  have hnd : ((allStrings l).filter
      (fun x => ((exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out P c t q x).map
          (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P kw l)).getD
          false)).Nodup :=
    (allStrings_nodup l).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext x
  simp [stringsOfLength]

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt_le (P :
    ProblemCalculus) (c : Nat.Partrec.Code)
    (hc : c.eval = fun n => (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
      (fun a => Part.map Encodable.encode (P.lang a)))
    (t : ℕ) (kw : Bool × BitString) (q : BitString) (l : ℕ) :
    exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt P c t kw q l ≤
      {x : BitString | x.length = l ∧ ∃ s,
          exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P kw l s = true ∧
        s ∈ P.lang (q, P.pair P.tag0 x)}.ncard := by
  classical
  rw [exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt_eq_card, ←
      Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_stringsOfLength] at hx
    obtain ⟨hl, hx⟩ := hx
    refine ⟨hl, ?_⟩
    cases ho : exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out P c t q x with
    | none => simp [ho] at hx
    | some s =>
      simp only [ho, Option.map_some, Option.getD_some] at hx
      exact ⟨s, hx, exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out_sound P c hc
          ho⟩
  · refine Set.Finite.subset (Finset.finite_toSet (stringsOfLength l)) ?_
    intro x hx
    exact (Finset.mem_coe.2 ((mem_stringsOfLength l x).2 hx.1))

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt_ge (P :
    ProblemCalculus) (c : Nat.Partrec.Code)
    (hc : c.eval = fun n => (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
      (fun a => Part.map Encodable.encode (P.lang a)))
    (kw : Bool × BitString) (q : BitString) (l : ℕ)
    (h : 2 ^ (l / 2 + 1) < {x : BitString | x.length = l ∧ ∃ s,
        exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P kw l s = true ∧
        s ∈ P.lang (q, P.pair P.tag0 x)}.ncard) :
    ∃ t, 2 ^ (l / 2 + 1) < exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt P c t
        kw q l := by
  classical
  set A : Set BitString := {x : BitString | x.length = l ∧ ∃ s,
      exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P kw l s = true ∧
        s ∈ P.lang (q, P.pair P.tag0 x)} with hA
  set Af : Finset BitString := (stringsOfLength l).filter (fun x => x ∈ A) with hAf
  have hAeq : A = ↑Af := by
    ext x
    simp only [hAf, Finset.coe_filter, mem_stringsOfLength, Set.mem_ofPred_eq]
    constructor
    · intro hx; exact ⟨hx.1, hx⟩
    · intro hx; exact hx.2
  have hev : ∀ x ∈ Af, ∃ t, ∀ t' ≥ t,
      ((exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out P c t' q x).map
          (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P kw l)).getD false
          = true := by
    intro x hx
    have hxA : x ∈ A := by rw [hAeq]; exact hx
    obtain ⟨-, s, hs, hl⟩ := hxA
    obtain ⟨t, ht⟩ := exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out_complete P
        c hc hl
    exact ⟨t, fun t' ht' => by simp [ht t' ht', hs]⟩
  choose! f hf using hev
  refine ⟨Af.sup f, ?_⟩
  rw [exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt_eq_card]
  have hcard : Af.card ≤ ((stringsOfLength l).filter
      (fun x => ((exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_out P c (Af.sup f)
          q x).map (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P kw
          l)).getD false = true)).card := by
    refine Finset.card_le_card (fun x hx => ?_)
    rw [Finset.mem_filter]
    exact ⟨(Finset.mem_filter.1 hx).1, hf x hx _ (Finset.le_sup hx)⟩
  have hn : A.ncard = Af.card := by rw [hAeq, Set.ncard_coe_finset]
  omega

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_found_iff (P :
    ProblemCalculus) (kw : Bool × BitString) (q : BitString)
    (l : ℕ) (S : BitString → Prop) (hS : ∀ s',
        exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P kw l s' = true ↔ S
        s') :
    exists_problems_problemK_eval_ge_of_countermodel_found P q l S ↔
      2 ^ (l / 2 + 1) < {x : BitString | x.length = l ∧ ∃ s,
          exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P kw l s = true ∧
        s ∈ P.lang (q, P.pair P.tag0 x)}.ncard := by
  unfold exists_problems_problemK_eval_ge_of_countermodel_found
  simp only [hS]

private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_kind (P :
    ProblemCalculus) (hP : P.Admissible) (kw : Bool × BitString)
    (q : BitString) (l : ℕ)
    (h : 2 ^ (l / 2 + 1) < {x : BitString | x.length = l ∧ ∃ s,
        exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P kw l s = true ∧
        s ∈ P.lang (q, P.pair P.tag0 x)}.ncard) :
    (∀ s, (bif kw.1 then Sum.inr kw.2 else Sum.inl kw.2 : BitString ⊕ BitString) = Sum.inl s →
      exists_problems_problemK_eval_ge_of_countermodel_found P q l (fun s' => s' = s)) ∧
    (∀ y, (bif kw.1 then Sum.inr kw.2 else Sum.inl kw.2 : BitString ⊕ BitString) = Sum.inr y →
      exists_problems_problemK_eval_ge_of_countermodel_found P q l
        (exists_problems_problemK_eval_ge_of_countermodel_pairs P y l)) := by
  obtain ⟨k, w⟩ := kw
  cases k
  · refine ⟨fun s hs => ?_, fun y hy => by simp at hy⟩
    simp only [Bool.cond_false, Sum.inl.injEq] at hs
    subst hs
    exact (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_found_iff P (false, w) q
        l _ (fun s' => exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test_false P
        w l s')).2 h
  · refine ⟨fun s hs => by simp at hs, fun y hy => ?_⟩
    simp only [Bool.cond_true, Sum.inr.injEq] at hy
    subst hy
    exact (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_found_iff P (true, w) q l
        _ (fun s' => exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test_true P hP
        w l s')).2 h

/-- Step 9c1 of the proof of `exists_problems_problemK_eval_ge_of_countermodel`: the
dovetailing search of case (C), a pure computability statement.  There is a partial computable
`F (q, l)` which, whenever some `s` is the output of the program `q` on more than `2^{l/2+1}`
inputs `0x` (`|x| = l`), or some `y` is such that on more than `2^{l/2+1}` of these inputs the
output is `1[y, z]` or `1[z, y]` with `|z| = l`, halts with such an `s` (as `Sum.inl s`) or such
a `y` (as `Sum.inr y`).  Proof: both properties are `Σ₁` (`P.lang` is partial computable: run it
on the `2^l` inputs `0x` for `τ = 0, 1, 2, …` steps with `Nat.Partrec.Code.evaln`, and count
the converged inputs with the output `s`, resp. with an output of the form `1[y, z]` / `1[z, y]`,
`|z| = l`, a decidable property of the output); search (`Nat.rfind`) for the first triple
`(τ, kind, candidate)` at which the count exceeds `2^{l/2+1}`. -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c1_search
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ F : BitString × ℕ →. BitString ⊕ BitString, Partrec F ∧
      ∀ (q : BitString) (l : ℕ),
        ((∃ s, exists_problems_problemK_eval_ge_of_countermodel_found P q l (fun s' => s' = s)) ∨
          ∃ y, exists_problems_problemK_eval_ge_of_countermodel_found P q l
            (exists_problems_problemK_eval_ge_of_countermodel_pairs P y l)) →
        ∃ v ∈ F (q, l),
          (∀ s, v = Sum.inl s →
            exists_problems_problemK_eval_ge_of_countermodel_found P q l (fun s' => s' = s)) ∧
          (∀ y, v = Sum.inr y → exists_problems_problemK_eval_ge_of_countermodel_found P q l
            (exists_problems_problemK_eval_ge_of_countermodel_pairs P y l)) := by
  have hL : Partrec P.lang := hP.2.2.2.2.2.1
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hL
  have hchk := exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_chk_computable P hP c
  have hdec : Computable (fun v : (BitString × ℕ) × ℕ =>
      Encodable.decode (α := Bool × BitString) v.2.unpair.2) :=
    Computable.decode.comp (Computable.snd.comp (Computable.unpair.comp Computable.snd))
  have hS : Computable₂ (fun (_ : (BitString × ℕ) × ℕ) (kw : Bool × BitString) =>
      (bif kw.1 then Sum.inr kw.2 else Sum.inl kw.2 : BitString ⊕ BitString)) := by
    refine Computable.cond ?_ ?_ ?_
    · exact Computable.fst.comp Computable.snd
    · exact Primrec.sumInr.to_comp.comp (Computable.snd.comp Computable.snd)
    · exact Primrec.sumInl.to_comp.comp (Computable.snd.comp Computable.snd)
  obtain ⟨G, hGdef⟩ : ∃ G : BitString × ℕ → ℕ → BitString ⊕ BitString,
      G = fun (_ : BitString × ℕ) (n : ℕ) =>
        ((Encodable.decode (α := Bool × BitString) n.unpair.2).map (fun kw =>
          (bif kw.1 then Sum.inr kw.2 else Sum.inl kw.2 : BitString ⊕ BitString))).getD
            (Sum.inl []) := ⟨_, rfl⟩
  have hG : Computable₂ G := by
    rw [hGdef]
    have := Computable.option_getD (Computable.option_map hdec hS)
      (Computable.const (Sum.inl [] : BitString ⊕ BitString))
    exact this
  have hrf : Partrec (fun a : BitString × ℕ =>
      (Nat.rfind (fun n => Part.some
          (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_chk P c a n))).map (G a))
          :=
    Partrec.map (Partrec.rfind hchk.partrec₂) hG
  refine ⟨fun a => (Nat.rfind (fun n => Part.some
      (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_chk P c a n))).map (G a),
      hrf, ?_⟩
  intro q l hex
  -- a candidate with enough converged inputs at some stage
  obtain ⟨kw, hkw⟩ : ∃ kw : Bool × BitString,
      2 ^ (l / 2 + 1) < {x : BitString | x.length = l ∧ ∃ s,
          exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test P kw l s = true ∧
        s ∈ P.lang (q, P.pair P.tag0 x)}.ncard := by
    rcases hex with ⟨s, hs⟩ | ⟨y, hy⟩
    · exact ⟨(false, s), (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_found_iff
        P (false, s) q l _ (fun s' =>
        exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test_false P s l s')).1 hs⟩
    · exact ⟨(true, y), (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_found_iff P
        (true, y) q l _ (fun s' =>
        exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_test_true P hP y l s')).1
        hy⟩
  obtain ⟨t, ht⟩ := exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt_ge P c hc kw
      q l hkw
  have hn0 : exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_chk P c (q, l)
      (Nat.pair t (Encodable.encode kw)) = true := by
    simp [exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_chk, Nat.unpair_pair,
        Encodable.encodek, ht]
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ →. Bool, p = fun n => Part.some
      (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_chk P c (q, l) n) := ⟨_, rfl⟩
  have hdom : (Nat.rfind p).Dom := by
    rw [Nat.rfind_dom]
    refine ⟨Nat.pair t (Encodable.encode kw), ?_, fun {m} _ => ?_⟩
    · rw [hpdef, Part.mem_some_iff]; exact hn0.symm
    · rw [hpdef]; exact Part.some_dom _
  obtain ⟨r, hr⟩ := Part.dom_iff_mem.mp hdom
  have hrt := Nat.rfind_spec hr
  rw [hpdef, Part.mem_some_iff] at hrt
  have hrt' := hrt.symm
  unfold exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_chk at hrt'
  cases hd : Encodable.decode (α := Bool × BitString) r.unpair.2 with
  | none => simp [hd] at hrt'
  | some kw' =>
    simp only [hd, Option.map_some, Option.getD_some, decide_eq_true_eq] at hrt'
    have hlt := lt_of_lt_of_le hrt'
        (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_cnt_le P c hc _ kw' q l)
    have hr' : r ∈ Nat.rfind (fun n => Part.some
        (exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_chk P c (q, l) n)) := by
      rw [hpdef] at hr; exact hr
    refine ⟨_, Part.mem_map _ hr', ?_⟩
    simp only [hGdef, hd, Option.map_some, Option.getD_some]
    exact exists_problems_problemK_eval_ge_of_countermodel_step9c1_search_kind P hP kw' q l hlt

/-- Step 2 of the proof of `exists_problems_problemK_eval_ge_of_countermodel_imp_hard`:
the world of a length is computable, uniformly in `n`: for a finite enumeration `e : W ≃ Fin M`,
the function `(n, l) ↦ (ω n l).map e` (an `Option ℕ`, the code of the world or `none`) is
computable.  Proof: each fibre `{ω n l = some w}` is decidable (`hω.1 w`), and there are finitely
many worlds. -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_cls
    {W : Type} [Finite W] [PartialOrder W] (r t : W) (ω : ℕ → ℕ → Option W)
    (hω : exists_problems_problemK_eval_ge_of_countermodel_family r t ω) {M : ℕ} (e : W ≃ Fin M) :
    Computable (fun p : ℕ × ℕ => (ω p.1 p.2).map (fun w => ((e w : Fin M) : ℕ))) := by
  classical
  have hfold : ∀ (ws : List W) (o : Option W),
      ws.foldr (fun w acc => if o = some w then some ((e w : Fin M) : ℕ) else acc) none =
        if ∃ w ∈ ws, o = some w then o.map (fun w => ((e w : Fin M) : ℕ)) else none := by
    intro ws o
    induction ws with
    | nil => simp
    | cons a ws ih =>
      rw [List.foldr_cons, ih]
      by_cases h : o = some a
      · subst h; simp
      · have : (∃ w ∈ a :: ws, o = some w) ↔ ∃ w ∈ ws, o = some w := by
          simp [List.mem_cons, h]
        simp [h]
  have hcomp : ∀ ws : List W, Computable (fun p : ℕ × ℕ =>
      ws.foldr (fun w acc => if ω p.1 p.2 = some w then some ((e w : Fin M) : ℕ) else acc)
        none) := by
    intro ws
    induction ws with
    | nil => exact Computable.const _
    | cons a ws ih =>
      obtain ⟨inst, hc⟩ := hω.1 a
      have := Computable.cond hc (Computable.const (some ((e a : Fin M) : ℕ))) ih
      refine this.of_eq fun p => ?_
      simp only [List.foldr_cons]
      by_cases h : ω p.1 p.2 = some a <;> simp [h]
  have : Fintype W := Fintype.ofFinite W
  refine (hcomp Finset.univ.toList).of_eq fun p => ?_
  rw [hfold]
  cases h : ω p.1 p.2 with
  | none => simp
  | some w => simp

/-- Step 3 of the proof of `exists_problems_problemK_eval_ge_of_countermodel_imp_hard`:
the computable round.  There is a partial computable `Rd (n, q, k)` such that, for `n ≥ 1`,
`q ∈ X_T → X_{T'}` and a non-root world `u` with `T u`, `¬ T' u` (given by its code
`k = e u`), `Rd (n, q, e u)` halts with `Sum.inl s` with `s ∈ X_{T'}` or with `Sum.inr y` with
`y` random from a world `v` incomparable with `u`.  Proof: with the search `F` of
`step9c1_search` (step 1) and the constant `c` of `step9a_search_exists`, `Nat.rfind` over the
lengths `l ≥ c + 5 |q|` with `ω n l = some u` (decidable by step 2; a solution exists since
`u ≠ r` has infinitely many lengths, `hω.2`), then run `F (q, l)`.  This is one round of the
algorithm: for every such `l` the search `F (q, l)` halts (`step9a_search_exists` and the
specification of `F`), and its value has the stated form (`step9b_search_sound`). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_step3_round
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible)
    {W : Type} [Finite W] [PartialOrder W] (r t : W) (hr : ∀ w, r ≤ w) (ω : ℕ → ℕ → Option W)
    (hω : exists_problems_problemK_eval_ge_of_countermodel_family r t ω) (T T' : W → Prop)
    (hT' : ∀ w w', w ≤ w' → T' w → T' w') {M : ℕ} (e : W ≃ Fin M) :
    ∃ Rd : ℕ × BitString × ℕ →. BitString ⊕ BitString, Partrec Rd ∧
      ∀ (n : ℕ) (q : BitString) (u : W), 1 ≤ n →
        q ∈ P.imp (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T)
          (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T') →
        u ≠ r → T u → ¬ T' u →
        ∃ v ∈ Rd (n, q, ((e u : Fin M) : ℕ)),
          (∀ s, v = Sum.inl s →
            s ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T') ∧
          (∀ y, v = Sum.inr y → exists_problems_problemK_eval_ge_of_countermodel_rand D y ∧
            ∃ v', ω n y.length = some v' ∧ ¬ u ≤ v' ∧ ¬ v' ≤ u) := by
  classical
  obtain ⟨F, hF, hFspec⟩ := exists_problems_problemK_eval_ge_of_countermodel_step9c1_search P hP
  obtain ⟨c, hc⟩ :=
    exists_problems_problemK_eval_ge_of_countermodel_search_exists D hD P hP r t hr ω hω
      T T' hT'
  have hcls := exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_cls r t ω hω e
  obtain ⟨chk, hchkdef⟩ : ∃ chk : ℕ × BitString × ℕ → ℕ → Bool,
      chk = fun a m => decide (c + 5 * a.2.1.length ≤ m) &&
        decide ((ω a.1 m).map (fun w => ((e w : Fin M) : ℕ)) = some a.2.2) := ⟨_, rfl⟩
  have hchk : Computable₂ chk := by
    rw [hchkdef]
    have h1 : Computable (fun v : (ℕ × BitString × ℕ) × ℕ =>
        decide (c + 5 * v.1.2.1.length ≤ v.2)) := by
      have hl : Computable (fun v : (ℕ × BitString × ℕ) × ℕ => c + 5 * v.1.2.1.length) :=
        (Primrec.nat_add.to_comp.comp (Computable.const c)
          (Primrec.nat_mul.to_comp.comp (Computable.const 5)
            (Computable.list_length.comp (Computable.fst.comp
              (Computable.snd.comp Computable.fst)))))
      exact (Primrec.nat_le.decide.to_comp).comp hl Computable.snd
    have h2 : Computable (fun v : (ℕ × BitString × ℕ) × ℕ =>
        decide ((ω v.1.1 v.2).map (fun w => ((e w : Fin M) : ℕ)) = some v.1.2.2)) := by
      have hp : Computable (fun v : (ℕ × BitString × ℕ) × ℕ => ((v.1.1, v.2) : ℕ × ℕ)) :=
        Computable.pair (Computable.fst.comp Computable.fst) Computable.snd
      have hx : Computable (fun v : (ℕ × BitString × ℕ) × ℕ =>
          (ω v.1.1 v.2).map (fun w => ((e w : Fin M) : ℕ))) :=
        Computable.comp (g := fun v : (ℕ × BitString × ℕ) × ℕ => ((v.1.1, v.2) : ℕ × ℕ))
          (f := fun p : ℕ × ℕ => (ω p.1 p.2).map (fun w => ((e w : Fin M) : ℕ))) hcls hp
      have hy : Computable (fun v : (ℕ × BitString × ℕ) × ℕ =>
          (some v.1.2.2 : Option ℕ)) :=
        Primrec.option_some.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
      exact (Primrec.eq.decide.to_comp).comp hx hy
    exact (Primrec.and.to_comp).comp h1 h2
  refine ⟨fun a => (Nat.rfind (fun m => Part.some (chk a m))).bind (fun l => F (a.2.1, l)),
    Partrec.bind (Partrec.rfind hchk.partrec₂)
      (hF.comp ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        Computable.snd)).to₂, ?_⟩
  intro n q u hn hq hur hTu hT'u
  have hinf := (hω.2 n hn).2.2.2.2.2 u hur
  obtain ⟨l, hlu, hlc⟩ : ∃ l, ω n l = some u ∧ c + 5 * q.length ≤ l := by
    obtain ⟨l, hl, hlb⟩ := hinf.exists_gt (c + 5 * q.length)
    exact ⟨l, hl, hlb.le⟩
  have hex : ∃ m, chk (n, q, ((e u : Fin M) : ℕ)) m = true := by
    refine ⟨l, ?_⟩
    rw [hchkdef]
    simp [hlu, hlc]
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ →. Bool,
      p = fun m => Part.some (chk (n, q, ((e u : Fin M) : ℕ)) m) := ⟨_, rfl⟩
  have hdom : (Nat.rfind p).Dom := by
    rw [Nat.rfind_dom]
    obtain ⟨m, hm⟩ := hex
    refine ⟨m, ?_, fun {_} _ => ?_⟩
    · rw [hpdef, Part.mem_some_iff]; exact hm.symm
    · rw [hpdef]; exact Part.some_dom _
  obtain ⟨l0, hl0⟩ := Part.dom_iff_mem.mp hdom
  have hspec := Nat.rfind_spec hl0
  rw [hpdef, Part.mem_some_iff] at hspec
  rw [hpdef] at hl0
  have hspec' := hspec.symm
  rw [hchkdef] at hspec'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hspec'
  obtain ⟨hlc0, hcl0⟩ := hspec'
  have hωl0 : ω n l0 = some u := by
    cases h : ω n l0 with
    | none => simp [h] at hcl0
    | some w =>
      simp only [h, Option.map_some, Option.some.injEq] at hcl0
      have := e.injective (Fin.ext hcl0)
      rw [this]
  obtain ⟨v, hv, hv1, hv2⟩ := hFspec q l0 (hc n q l0 u hn hq hωl0 hTu hT'u hlc0)
  have h9b := exists_problems_problemK_eval_ge_of_countermodel_search_sound D hD P hP r t ω
    hω T T' n q l0 u hn hq hωl0 hTu
  exact ⟨v, Part.mem_bind_iff.2 ⟨l0, hl0, hv⟩, fun s hs => h9b.1 s (hv1 s hs),
    fun y hy => h9b.2 y (hv2 y hy)⟩

/-- Step 4a of the proof of `exists_problems_problemK_eval_ge_of_countermodel_imp_hard`:
a function `ℕ → β` which is constant `d` from `M` on is computable (a finite table). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_tab1
    {β : Type} [Primcodable β] (M : ℕ) (g : ℕ → β) (d : β)
    (h : ∀ k, M ≤ k → g k = d) : Computable g := by
  have h0 : Computable (fun k : ℕ => ((List.range M).map g).getD k d) :=
    ((Primrec.list_getD d).comp (Primrec.const ((List.range M).map g)) Primrec.id).to_comp
  refine h0.of_eq fun k => ?_
  by_cases hk : k < M
  · simp [List.getD_eq_getElem?_getD, hk]
  · simp [List.getD_eq_getElem?_getD, hk, h k (not_lt.1 hk)]

/-- Step 4b of the proof of `exists_problems_problemK_eval_ge_of_countermodel_imp_hard`:
a two-variable finite table is computable. -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_tab2
    {β : Type} [Primcodable β] (M : ℕ) (g : ℕ → ℕ → β) (d : β)
    (h : ∀ a b, M ≤ a ∨ M ≤ b → g a b = d) :
    Computable (fun p : ℕ × ℕ => g p.1 p.2) := by
  have h1 : Computable (fun k : ℕ => g k.unpair.1 k.unpair.2) := by
    refine exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_tab1
      (M * M) _ d fun k hk => h _ _ ?_
    by_contra hc
    push Not at hc
    have h2 := Nat.pair_lt_max_add_one_sq k.unpair.1 k.unpair.2
    rw [Nat.pair_unpair] at h2
    have h3 : max k.unpair.1 k.unpair.2 + 1 ≤ M := by
      have := max_lt hc.1 hc.2
      omega
    have h4 : (max k.unpair.1 k.unpair.2 + 1) ^ 2 ≤ M * M := by
      rw [sq]; exact Nat.mul_le_mul h3 h3
    omega
  exact (h1.comp Primrec₂.natPair.to_comp).of_eq fun p => by simp

/-- The state of the iteration: the output (once found), the code of the current world `u_j`, the
previous random string `y_{j-1}` with the code of its world. -/
private abbrev exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St : Type
    :=
  Option BitString × ℕ × Option (BitString × ℕ)

/-- The decision after a round returned `inr y` with world code `vc`. -/
private def exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G2
    (P : ProblemCalculus) (inc : ℕ × ℕ → Bool) (impc : ℕ → Bool) (ut : ℕ → ℕ)
    (uc : ℕ) (prev : Option (BitString × ℕ)) (y : BitString) (vc : ℕ) :
    exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St :=
  Option.casesOn prev
    (cond (impc vc) (some (P.pair P.tag0 y), uc, none) (none, ut vc, some (y, vc)))
    (fun pv => cond (inc (pv.2, vc)) (some (P.pair P.tag1 (P.pair pv.1 y)), uc, none)
      (cond (impc vc) (some (P.pair P.tag0 y), uc, none) (none, ut vc, some (y, vc))))

/-- The new state after a round. -/
private def exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G
    (P : ProblemCalculus) (cls : ℕ × ℕ → Option ℕ) (inc : ℕ × ℕ → Bool)
    (impc : ℕ → Bool) (ut : ℕ → ℕ) (a : ℕ × BitString)
    (s : exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St)
    (v : BitString ⊕ BitString) :
    exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St :=
  Option.casesOn s.1
    (Sum.casesOn v (fun o => (some o, s.2))
      (fun y => exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G2
        P inc impc ut s.2.1 s.2.2 y ((cls (a.1, y.length)).getD 0)))
    (fun _ => s)

/-- One step of the iteration. -/
private def exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_step
    (P : ProblemCalculus) (cls : ℕ × ℕ → Option ℕ) (inc : ℕ × ℕ → Bool)
    (impc : ℕ → Bool) (ut : ℕ → ℕ) (Rd : ℕ × BitString × ℕ →. BitString ⊕ BitString)
    (a : ℕ × BitString)
    (s : exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St) :
    Part exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St :=
  (Option.casesOn (motive := fun _ => Part (BitString ⊕ BitString)) s.1
    (Rd (a.1, a.2, s.2.1)) (fun o => Part.some (Sum.inl o))).map
    (exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G
      P cls inc impc ut a s)

/-- `k` steps of the iteration from the state `(none, u0, none)`. -/
private def exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_iter
    (P : ProblemCalculus) (cls : ℕ × ℕ → Option ℕ) (inc : ℕ × ℕ → Bool)
    (impc : ℕ → Bool) (ut : ℕ → ℕ) (Rd : ℕ × BitString × ℕ →. BitString ⊕ BitString)
    (a : ℕ × BitString) (u0 : ℕ) (k : ℕ) :
    Part exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St :=
  Nat.rec (motive := fun _ => Part (Option BitString × ℕ × Option (BitString × ℕ)))
    (Part.some (none, u0, none)) (fun _ IH => IH.bind
    (exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_step
      P cls inc impc ut Rd a)) k

/-- Step 1 of the proof of
`exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_iter_partrec`:
the decision `G2` after a round returned `inr y` is computable. -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_G2
    (P : ProblemCalculus) (hP : P.Admissible) (inc : ℕ × ℕ → Bool) (hinc : Computable inc)
    (impc : ℕ → Bool) (himpc : Computable impc) (ut : ℕ → ℕ) (hut : Computable ut)
    {α : Type} [Primcodable α] (uc : α → ℕ) (prev : α → Option (BitString × ℕ))
    (y : α → BitString) (vc : α → ℕ)
    (huc : Computable uc) (hprev : Computable prev) (hy : Computable y) (hvc : Computable vc) :
    Computable (fun x : α =>
      exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G2
        P inc impc ut (uc x) (prev x) (y x) (vc x)) := by
  have hpair : Computable₂ P.pair := hP.1
  have hA : Computable (fun x : α =>
      cond (impc (vc x)) ((some (P.pair P.tag0 (y x)), uc x, none) :
        exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St)
        ((none, ut (vc x), some (y x, vc x)) :
        exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St)) := by
    refine Computable.cond (himpc.comp hvc) ?_ ?_
    · exact (Computable.option_some.comp
        (hpair.comp (Computable.const _) hy)).pair (huc.pair (Computable.const none))
    · exact (Computable.const none).pair ((hut.comp hvc).pair
        (Computable.option_some.comp (hy.pair hvc)))
  unfold exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G2
  refine Computable.option_casesOn hprev hA ?_
  have hx : Computable (fun p : α × (BitString × ℕ) => p.1) := Computable.fst
  have hpv : Computable (fun p : α × (BitString × ℕ) => p.2) := Computable.snd
  refine Computable.cond (hinc.comp (((Computable.snd.comp hpv).pair (hvc.comp hx)))) ?_
    (hA.comp hx)
  exact (Computable.option_some.comp
    (hpair.comp (Computable.const _)
      (hpair.comp (Computable.fst.comp hpv) (hy.comp hx)))).pair
    ((huc.comp hx).pair (Computable.const none))

/-- Step 4c of the proof of `exists_problems_problemK_eval_ge_of_countermodel_imp_hard`:
the iteration is partial computable. -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_iter_partrec
    (P : ProblemCalculus) (hP : P.Admissible)
    (cls : ℕ × ℕ → Option ℕ) (hcls : Computable cls) (inc : ℕ × ℕ → Bool) (hinc : Computable inc)
    (impc : ℕ → Bool) (himpc : Computable impc) (ut : ℕ → ℕ) (hut : Computable ut)
    (Rd : ℕ × BitString × ℕ →. BitString ⊕ BitString) (hRd : Partrec Rd) (u0 k : ℕ) :
    Partrec (fun a : ℕ × BitString =>
      exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_iter
        P cls inc impc ut Rd a u0 k) := by
  have hGc : Computable (fun p : (ℕ × BitString) ×
      exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St ×
      (BitString ⊕ BitString) =>
      exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G
        P cls inc impc ut p.1 p.2.1 p.2.2) := by
    unfold exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G
    have hs : Computable (fun p : (ℕ × BitString) ×
        exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St ×
        (BitString ⊕ BitString) => p.2.1) := Computable.fst.comp Computable.snd
    have hv : Computable (fun p : (ℕ × BitString) ×
        exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St ×
        (BitString ⊕ BitString) => p.2.2) := Computable.snd.comp Computable.snd
    refine Computable.option_casesOn (Computable.fst.comp hs) ?_ ?_
    · refine Computable.sumCasesOn hv ?_ ?_
      · exact ((Computable.option_some.comp Computable.snd).pair
          (Computable.snd.comp (hs.comp Computable.fst))).to₂
      · refine exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_G2
          P hP inc hinc impc himpc ut hut _ _ _ _ ?_ ?_ ?_ ?_
        · exact (Computable.fst.comp (Computable.snd.comp (hs.comp Computable.fst)))
        · exact (Computable.snd.comp (Computable.snd.comp (hs.comp Computable.fst)))
        · exact Computable.snd
        · refine Computable.option_getD (hcls.comp ((Computable.fst.comp
            (Computable.fst.comp Computable.fst)).pair (Computable.list_length.comp
              Computable.snd))) (Computable.const 0)
    · exact (hs.comp Computable.fst).to₂
  have hH : Partrec (fun p : (ℕ × BitString) ×
      exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St =>
      (Option.casesOn (motive := fun _ => Part (BitString ⊕ BitString)) p.2.1
        (Rd (p.1.1, p.1.2, p.2.2.1)) (fun o => Part.some (Sum.inl o)))) := by
    have hs : Computable (fun p : (ℕ × BitString) ×
        exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St =>
        p.2.1) := Computable.fst.comp Computable.snd
    refine (Partrec.cond (c := fun p : (ℕ × BitString) ×
        exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St =>
        p.2.1.isNone)
      ((Computable.option_casesOn hs (Computable.const true)
        (Computable.const false).to₂).of_eq fun p => by rcases p.2.1 <;> rfl)
      (f := fun p => Rd (p.1.1, p.1.2, p.2.2.1))
      (g := fun p => Part.some (Sum.inl (p.2.1.getD []))) ?_ ?_).of_eq ?_
    · exact hRd.comp (Computable.fst.comp (Computable.fst)|>.pair
        ((Computable.snd.comp Computable.fst).pair
          (Computable.fst.comp (Computable.snd.comp Computable.snd))))
    · exact (Computable.sumInl.comp (Computable.option_getD hs (Computable.const []))).partrec
    · intro p
      rcases h : p.2.1 with _ | o <;> simp
  have hstep : Partrec₂ (fun (a : ℕ × BitString)
      (s : exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St) =>
      exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_step
        P cls inc impc ut Rd a s) := by
    have hre : Computable (fun x : ((ℕ × BitString) ×
        exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St) ×
        (BitString ⊕ BitString) => (x.1.1, x.1.2, x.2)) :=
      (Computable.fst.comp Computable.fst).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd)
    have hG2 : Computable₂ (fun (p : (ℕ × BitString) ×
        exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St)
        (v : BitString ⊕ BitString) =>
        exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G
          P cls inc impc ut p.1 p.2 v) :=
      by have h := hGc.comp hre; exact h
    exact Partrec.map hH hG2
  induction k with
  | zero => exact (Computable.const _).partrec
  | succ k ih => exact Partrec.bind ih hstep

/-- Step 4d of the proof of `exists_problems_problemK_eval_ge_of_countermodel_imp_hard`:
the correctness of the iteration.  With the finite tables `ut` (the code of `u (w)`), `inc` (codes
of incomparable worlds), `impc` (codes of worlds in `T → T'`), `cls` (the world code of a length)
given by their specifications on codes of worlds, and `¬ T r`, `¬ (T → T') r`: after `M + 1`
steps from `(none, e (u r), none)` the iteration has halted with output `some o`, `o ∈ X_{T → T'}`.
Proof: by induction on the number of steps `j`: either the state is final with output in
`X_{T → T'}` (`[0, y]` with `y` random of a world in `T → T'`, or `s ∈ X_{T'} ⊆ X_{T→T'}`, or
`1[y_{j-1}, y_j] ∈ 1C`), or it is `(none, e u_j, prev)` with `u_j ≠ r`, `T u_j`, `¬ T' u_j`, and
either `prev = none`, or `prev = (y, e v)` with `y` random, `ω n |y| = some v`, `v ≤ u_j`, and the
number of worlds `≥ v` is at most `M + 1 - j`.  A round `inr y_j` of a world `v_j` incomparable with
`u_j` (so `v_j ≠ r`) is either incomparable with the previous world (output in `1C`), or
`v_j ≤ v_{j-1}` is impossible (it gives `v_j ≤ u_j`), so `v_{j-1} < v_j` (fewer worlds above).
After `M + 1` steps the counting forces the state to be final. -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_iter_spec
    (D : Map) (P : ProblemCalculus)
    {W : Type} [Finite W] [PartialOrder W] (r t : W) (hr : ∀ w, r ≤ w) (ω : ℕ → ℕ → Option W)
    (hω : exists_problems_problemK_eval_ge_of_countermodel_family r t ω) (T T' : W → Prop)
    (hT' : ∀ w w', w ≤ w' → T' w → T' w')
    {M : ℕ} (e : W ≃ Fin M)
    (cls : ℕ × ℕ → Option ℕ)
    (hcls : ∀ n l, cls (n, l) = (ω n l).map (fun w => ((e w : Fin M) : ℕ)))
    (Rd : ℕ × BitString × ℕ →. BitString ⊕ BitString)
    (hRdspec : ∀ (n : ℕ) (q : BitString) (u : W), 1 ≤ n →
        q ∈ P.imp (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T)
          (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T') →
        u ≠ r → T u → ¬ T' u →
        ∃ v ∈ Rd (n, q, ((e u : Fin M) : ℕ)),
          (∀ s, v = Sum.inl s →
            s ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T') ∧
          (∀ y, v = Sum.inr y → exists_problems_problemK_eval_ge_of_countermodel_rand D y ∧
            ∃ v', ω n y.length = some v' ∧ ¬ u ≤ v' ∧ ¬ v' ≤ u))
    (u : W → W)
    (hu : ∀ w, ¬ exists_problems_problemK_eval_ge_of_countermodel_impset T T' w →
      w ≤ u w ∧ T (u w) ∧ ¬ T' (u w))
    (ut : ℕ → ℕ) (hut : ∀ w, ut ((e w : Fin M) : ℕ) = ((e (u w) : Fin M) : ℕ))
    (inc : ℕ × ℕ → Bool)
    (hinc : ∀ w w', inc (((e w : Fin M) : ℕ), ((e w' : Fin M) : ℕ)) = true ↔
      (¬ w ≤ w' ∧ ¬ w' ≤ w))
    (impc : ℕ → Bool)
    (himpc : ∀ w, impc ((e w : Fin M) : ℕ) = true ↔
      exists_problems_problemK_eval_ge_of_countermodel_impset T T' w)
    (hTr : ¬ T r) (hnr : ¬ exists_problems_problemK_eval_ge_of_countermodel_impset T T' r) :
    ∀ n, 1 ≤ n →
      ∀ q ∈ P.imp (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T)
          (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T'),
        ∃ s ∈ exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_iter
            P cls inc impc ut Rd (n, q) ((e (u r) : Fin M) : ℕ) (M + 1),
          ∃ o, s.1 = some o ∧ o ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n)
            (exists_problems_problemK_eval_ge_of_countermodel_impset T T') := by
  classical
  have : Fintype W := Fintype.ofFinite W
  intro n hn q hq
  have hcard : Fintype.card W = M := by simpa using Fintype.card_congr e
  obtain ⟨c, hcdef⟩ : ∃ c : W → ℕ, ∀ v, c v = (Finset.univ.filter (fun w => v ≤ w)).card :=
    ⟨_, fun _ => rfl⟩
  have hc1 : ∀ v, 1 ≤ c v := fun v => by
    rw [hcdef]
    exact Finset.card_pos.2 ⟨v, by simp⟩
  have hcr : ∀ v, v ≠ r → c v + 1 ≤ M := by
    intro v hv
    have hsub : Finset.univ.filter (fun w => v ≤ w) ⊆ Finset.univ.erase r := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro hwr
      exact hv (le_antisymm (hwr ▸ hw) (hr v))
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard] at this
    have h1 := hc1 v
    rw [hcdef] at h1 ⊢
    omega
  have hclt : ∀ v v', v < v' → c v' < c v := by
    intro v v' hlt
    rw [hcdef, hcdef]
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hlt.le.trans hw
    · intro hsub
      have h0 := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ v, le_refl v⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h0
      exact absurd h0 (not_le_of_gt hlt)
  have hrt : ∀ w, T w → w ≠ r := fun w hw hwr => hTr (hwr ▸ hw)
  have hXmono : ∀ z, z ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T' →
      z ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n)
        (exists_problems_problemK_eval_ge_of_countermodel_impset T T') := fun z hz =>
    exists_problems_problemK_eval_ge_of_countermodel_xset_mono D P (ω n) T' _
      (fun w hw w' hww' _ => hT' w w' hww' hw) hz
  obtain ⟨Inv, hInv⟩ : ∃ Inv : ℕ →
      exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_St → Prop,
      ∀ j s, Inv j s ↔
        ((∃ o, s.1 = some o ∧ o ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n)
            (exists_problems_problemK_eval_ge_of_countermodel_impset T T')) ∨
          (s.1 = none ∧ ∃ w, s.2.1 = ((e w : Fin M) : ℕ) ∧ T w ∧ ¬ T' w ∧
            ((j = 0 ∧ s.2.2 = none) ∨
              ∃ y v, s.2.2 = some (y, ((e v : Fin M) : ℕ)) ∧
                exists_problems_problemK_eval_ge_of_countermodel_rand D y ∧
                ω n y.length = some v ∧ v ≤ w ∧ c v + j ≤ M))) := ⟨_, fun _ _ => Iff.rfl⟩
  have key : ∀ j, ∃ s ∈
      exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_iter
      P cls inc impc ut Rd (n, q) ((e (u r) : Fin M) : ℕ) j, Inv j s := by
    intro j
    induction j with
    | zero =>
      refine ⟨(none, ((e (u r) : Fin M) : ℕ), none), Part.mem_some _, ?_⟩
      obtain ⟨_, h2, h3⟩ := hu r hnr
      rw [hInv]
      exact Or.inr ⟨rfl, u r, rfl, h2, h3, Or.inl ⟨rfl, rfl⟩⟩
    | succ j ih =>
      obtain ⟨s, hs, hI⟩ := ih
      rw [hInv] at hI
      rcases hI with ⟨o, hso, ho⟩ | ⟨hs1, w, hs2, hTw, hT'w, hprev⟩
      · refine ⟨s, Part.mem_bind_iff.2 ⟨s, hs, ?_⟩, ?_⟩
        · obtain ⟨s1, s2, s3⟩ := s
          simp only at hso
          subst hso
          simp [exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_step,
            exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G]
        · rw [hInv]; exact Or.inl ⟨o, hso, ho⟩
      · have hwr : w ≠ r := hrt w hTw
        obtain ⟨v0, hv0, hv0s, hv0y⟩ := hRdspec n q w hn hq hwr hTw hT'w
        obtain ⟨s1, s2, s3⟩ := s
        simp only at hs1 hs2 hprev
        subst hs1
        subst hs2
        have hmem : ∀ v1 : BitString ⊕ BitString, v1 = v0 →
            exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G
              P cls inc impc ut (n, q) (none, ((e w : Fin M) : ℕ), s3) v1 ∈
            exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_iter
              P cls inc impc ut Rd (n, q) ((e (u r) : Fin M) : ℕ) (j + 1) := by
          rintro v1 rfl
          exact Part.mem_bind_iff.2 ⟨_, hs, Part.mem_map_iff _ |>.2 ⟨v1, hv0, rfl⟩⟩
        refine ⟨_, hmem v0 rfl, ?_⟩
        rw [hInv]
        cases v0 with
        | inl o =>
          refine Or.inl ⟨o, ?_, hXmono _ (hv0s o rfl)⟩
          rfl
        | inr y =>
          obtain ⟨hyr, v', hωy, hnle1, hnle2⟩ := hv0y y rfl
          have hvc : (cls (n, y.length)).getD 0 = ((e v' : Fin M) : ℕ) := by
            rw [hcls, hωy]; rfl
          have hv'r : v' ≠ r := by
            rintro rfl
            exact hnle2 (hr w)
          -- the output when `v'` is in `T → T'`
          have hout0 : impc ((e v' : Fin M) : ℕ) = true →
              P.pair P.tag0 y ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n)
                (exists_problems_problemK_eval_ge_of_countermodel_impset T T') := fun hi =>
            Or.inl ⟨y, ⟨hyr, v', hωy, (himpc v').1 hi⟩, rfl⟩
          -- the new state when `v'` is not in `T → T'`
          have hnext : ¬ impc ((e v' : Fin M) : ℕ) = true →
              ∃ w', ut ((e v' : Fin M) : ℕ) = ((e w' : Fin M) : ℕ) ∧ T w' ∧ ¬ T' w' ∧ v' ≤ w' := by
            intro hi
            have hn' : ¬ exists_problems_problemK_eval_ge_of_countermodel_impset T T' v' :=
              fun h => hi ((himpc v').2 h)
            obtain ⟨hle, hT2, hT2'⟩ := hu v' hn'
            exact ⟨u v', hut v', hT2, hT2', hle⟩
          cases s3 with
          | none =>
            rcases hprev with ⟨hj0, -⟩ | ⟨y0, v, h0, -⟩
            swap
            · simp at h0
            subst hj0
            by_cases hi : impc ((e v' : Fin M) : ℕ) = true
            · refine Or.inl ⟨_, ?_, hout0 hi⟩
              simp [exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G,
                exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G2,
                hvc, hi]
            · obtain ⟨w', hw'1, hw'2, hw'3, hw'4⟩ := hnext hi
              refine Or.inr ⟨?_, w', ?_, hw'2, hw'3, Or.inr ⟨y, v', ?_, hyr, hωy, hw'4, ?_⟩⟩
              · simp [exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G,
                  exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G2,
                  hvc, hi]
              · simp [exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G,
                  exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G2,
                  hvc, hi, hw'1]
              · simp [exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G,
                  exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G2,
                  hvc, hi]
              · have := hcr v' hv'r
                omega
          | some pv =>
            obtain ⟨y0, vc0⟩ := pv
            rcases hprev with ⟨-, h0⟩ | ⟨y1, v, h0, hy1r, hωy1, hvw, hcv⟩
            · simp at h0
            simp only [Option.some.injEq, Prod.mk.injEq] at h0
            obtain ⟨hya, hvb⟩ := h0
            subst hya
            subst hvb
            by_cases hinc1 : inc (((e v : Fin M) : ℕ), ((e v' : Fin M) : ℕ)) = true
            · obtain ⟨hi1, hi2⟩ := (hinc v v').1 hinc1
              refine Or.inl ⟨P.pair P.tag1 (P.pair y0 y), ?_,
                Or.inr ⟨P.pair y0 y, ⟨y0, y, v, v', hy1r, hyr, hωy1, hωy, hi1, hi2, rfl⟩, rfl⟩⟩
              simp [exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G,
                exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G2,
                hvc, hinc1]
            · by_cases hi : impc ((e v' : Fin M) : ℕ) = true
              · refine Or.inl ⟨_, ?_, hout0 hi⟩
                simp [exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G,
                  exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G2,
                  hvc, hinc1, hi]
              · obtain ⟨w', hw'1, hw'2, hw'3, hw'4⟩ := hnext hi
                have hcomp : v ≤ v' ∨ v' ≤ v := by
                  by_contra h
                  rw [not_or] at h
                  exact hinc1 ((hinc v v').2 h)
                have hlt : v < v' := by
                  rcases hcomp with h | h
                  · refine lt_of_le_of_ne h ?_
                    rintro rfl
                    exact hnle2 hvw
                  · exact absurd (h.trans hvw) hnle2
                have h1 := hclt v v' hlt
                refine Or.inr ⟨?_, w', ?_, hw'2, hw'3, Or.inr ⟨y, v', ?_, hyr, hωy, hw'4, ?_⟩⟩
                · simp [exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G,
                    exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G2,
                    hvc, hinc1, hi]
                · simp [exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G,
                    exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G2,
                    hvc, hinc1, hi, hw'1]
                · simp [exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G,
                    exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_G2,
                    hvc, hinc1, hi]
                · omega
  have hfin := key (M + 1)
  obtain ⟨s, hs, hI⟩ := hfin
  rw [hInv] at hI
  rcases hI with ⟨o, hso, ho⟩ | ⟨-, w, -, -, -, hprev⟩
  · exact ⟨s, hs, o, hso, ho⟩
  · exfalso
    rcases hprev with ⟨hj, -⟩ | ⟨y, v, -, -, -, -, hcv⟩
    · omega
    · have := hc1 v
      omega

/-- Step 9c of the proof of `exists_problems_problemK_eval_ge_of_countermodel`, case (C),
hard half, the algorithm: for upward closed `T`, `T'`, `X_T → X_{T'}` uniformly reduces to
`X_{T → T'}`.  Given `(n, q)`: if the root forces `T → T'` output `[0, Λ]` (`Λ` is random, of
the root length `0`).  If `T` holds at the root (so `T'` fails there, `T'` being upward
closed), output `q([0, Λ])`: it is defined and lies in `X_{T'} ⊆ X_{T→T'}`.  Otherwise start
with `u_0 = u(r)`, where `u` is a fixed table `w ↦ u(w) ≥ w` with `T (u w)`, `¬ T' (u w)` (for
the `w` where `T → T'` fails), and run the round of step 3 on `u_j`: find a length
`l ≥ c + 5|q|` of `u_j` (the sets of lengths are decidable, uniformly in `n`, and infinite for
non-root worlds) and run the search `F (q, l)` of `step9c1_search` (step 1; it halts by
`step9a_search_exists`).  In case `Sum.inl s` output `s ∈ X_{T'} ⊆ X_{T→T'}`; in case
`Sum.inr y_j` (`y_j` random, of a world `v_j` incomparable with `u_j`, so `v_j ≠ r`, by
`step9b_search_sound`; `v_j` is computed from `|y_j|` by step 2): if the previous `y_{j-1}`
exists and its world is incomparable with `v_j` output `1[y_{j-1}, y_j]` (an element of `1C`),
else if `(T → T')(v_j)` output `[0, y_j]`, else `u_{j+1} = u(v_j)` and repeat.  If `v_{j-1}`,
`v_j` are comparable then `v_{j-1} < v_j` (`v_j ≤ v_{j-1} ≤ u_j` would contradict that `v_j` is
incomparable with `u_j`), so the worlds strictly increase and at most `|W|` rounds occur.
Step 4 implements this as `|W| + 1` iterations of a partial computable step on a state
(`Partrec.nat_rec`): finite tables (steps 4a, 4b), computability (step 4c) and correctness
(step 4d) of the iteration. -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_imp_hard
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible)
    {W : Type} [Finite W] [PartialOrder W] (r t : W) (hr : ∀ w, r ≤ w) (ω : ℕ → ℕ → Option W)
    (hω : exists_problems_problemK_eval_ge_of_countermodel_family r t ω) (T T' : W → Prop)
    (_hT : ∀ w w', w ≤ w' → T w → T w') (hT' : ∀ w w', w ≤ w' → T' w → T' w') :
    exists_problems_problemK_eval_ge_of_countermodel_ured
      (fun n => P.imp (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T)
        (exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) T'))
      (fun n => exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n)
        (exists_problems_problemK_eval_ge_of_countermodel_impset T T')) := by
  classical
  have hrand0 : exists_problems_problemK_eval_ge_of_countermodel_rand D [] := by
    simp [exists_problems_problemK_eval_ge_of_countermodel_rand]
  by_cases h1 : exists_problems_problemK_eval_ge_of_countermodel_impset T T' r
  · refine ⟨fun _ => Part.some (P.pair P.tag0 []), (Computable.const _).partrec, ?_⟩
    intro n hn x _
    refine ⟨P.pair P.tag0 [], Or.inl ⟨[], ⟨hrand0, r, (hω.2 n hn).1, h1⟩, rfl⟩, ?_⟩
    exact Part.mem_some _
  by_cases h2 : T r
  · refine ⟨fun p => P.lang (p.2, P.pair P.tag0 []), ?_, ?_⟩
    · exact hP.2.2.2.2.2.1.comp (Computable.snd.pair (Computable.const _))
    · intro n hn q hq
      have hmem : P.pair P.tag0 [] ∈ exists_problems_problemK_eval_ge_of_countermodel_xset D P
          (ω n) T := Or.inl ⟨[], ⟨hrand0, r, (hω.2 n hn).1, h2⟩, rfl⟩
      obtain ⟨y, hy, hyl⟩ := hq _ hmem
      refine ⟨y, exists_problems_problemK_eval_ge_of_countermodel_xset_mono D P (ω n) T' _
        (fun w hw w' hww' _ => hT' w w' hww' hw) hy, ?_⟩
      exact hyl
  obtain ⟨M, ⟨e⟩⟩ := Finite.exists_equiv_fin W
  obtain ⟨Rd, hRd, hRdspec⟩ :=
    exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_step3_round D hD P hP r t hr ω
      hω T T' hT' e
  have hcls := exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_cls r t ω hω e
  have hex : ∀ w, ∃ w', ¬ exists_problems_problemK_eval_ge_of_countermodel_impset T T' w →
      w ≤ w' ∧ T w' ∧ ¬ T' w' := by
    intro w
    by_cases h : exists_problems_problemK_eval_ge_of_countermodel_impset T T' w
    · exact ⟨w, fun hh => absurd h hh⟩
    · unfold exists_problems_problemK_eval_ge_of_countermodel_impset at h
      push Not at h
      obtain ⟨w', hw', hTw, hT'w⟩ := h
      exact ⟨w', fun _ => ⟨hw', hTw, hT'w⟩⟩
  choose u hu using hex
  let ut : ℕ → ℕ := fun k => if h : k < M then ((e (u (e.symm ⟨k, h⟩)) : Fin M) : ℕ) else 0
  let inc : ℕ × ℕ → Bool := fun p => if h : p.1 < M ∧ p.2 < M then
    decide (¬ e.symm ⟨p.1, h.1⟩ ≤ e.symm ⟨p.2, h.2⟩ ∧ ¬ e.symm ⟨p.2, h.2⟩ ≤ e.symm ⟨p.1, h.1⟩)
    else false
  let impc : ℕ → Bool := fun k => if h : k < M then
    decide (exists_problems_problemK_eval_ge_of_countermodel_impset T T' (e.symm ⟨k, h⟩))
    else false
  have hutc : Computable ut :=
    exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_tab1 M ut 0
      (fun k hk => by simp [ut, not_lt.2 hk])
  have hincc : Computable inc :=
    exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_tab2 M
      (fun a b => inc (a, b)) false (fun a b hab => by
        simp only [inc]
        rw [dite_eq_right]
        rintro ⟨ha, hb⟩
        rcases hab with hab | hab <;> omega)
  have himpcc : Computable impc :=
    exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_tab1 M impc
      false (fun k hk => by simp [impc, not_lt.2 hk])
  have hut' : ∀ w, ut ((e w : Fin M) : ℕ) = ((e (u w) : Fin M) : ℕ) := by
    intro w; simp [ut]
  have hinc' : ∀ w w', inc (((e w : Fin M) : ℕ), ((e w' : Fin M) : ℕ)) = true ↔
      (¬ w ≤ w' ∧ ¬ w' ≤ w) := by
    intro w w'; simp [inc]
  have himpc' : ∀ w, impc ((e w : Fin M) : ℕ) = true ↔
      exists_problems_problemK_eval_ge_of_countermodel_impset T T' w := by
    intro w; simp [impc]
  have hpr :=
    exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_iter_partrec
      P hP _ hcls inc hincc impc himpcc ut hutc Rd hRd ((e (u r) : Fin M) : ℕ) (M + 1)
  refine ⟨fun a => (exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_loop_iter
      P (fun p : ℕ × ℕ => (ω p.1 p.2).map (fun w => ((e w : Fin M) : ℕ))) inc impc ut Rd a
      ((e (u r) : Fin M) : ℕ) (M + 1)).map (fun s => s.1.getD []),
    Partrec.map hpr (Computable.option_getD (Computable.fst.comp Computable.snd)
      (Computable.const [])).to₂, ?_⟩
  intro n hn q hq
  obtain ⟨s, hs, o, hso, ho⟩ :=
    exists_problems_problemK_eval_ge_of_countermodel_step9c2_iterate_iter_spec
      D P r t hr ω hω T T' hT' e
      (fun p : ℕ × ℕ => (ω p.1 p.2).map (fun w => ((e w : Fin M) : ℕ))) (fun n l => rfl) Rd
      hRdspec u hu ut hut' inc hinc' impc himpc' h2 h1 n hn q hq
  refine ⟨o, ho, Part.mem_map_iff _ |>.2 ⟨s, hs, by simp [hso]⟩⟩

/-- Step 10 of the proof of `exists_problems_problemK_eval_ge_of_countermodel`: the
induction on `Ψ`.  `Ψ(X₁, …, X_k)` and `X_Ψ` (`T = {w | Ψ true at w}`) are uniformly
algorithmically equivalent (both directions), where `X_i = X_{T_i}`.  Base: identity; steps:
steps 5-9 with `forces_mono` (truth sets are upward closed). -/
private theorem exists_problems_problemK_eval_ge_of_countermodel_induction
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) {k : ℕ}
    {W : Type} [Finite W] [PartialOrder W] (r t : W) (hr : ∀ w, r ≤ w)
    (V : W → Fin k → Prop) (hV : IsMonotoneValuation V) (ω : ℕ → ℕ → Option W)
    (hω : exists_problems_problemK_eval_ge_of_countermodel_family r t ω) (Ψ : PFormula (Fin k)) :
    exists_problems_problemK_eval_ge_of_countermodel_ured
      (fun n => Ψ.eval P (fun i =>
        exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) (fun w => V w i)))
      (fun n => exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n)
        (fun w => Forces V w Ψ)) ∧
    exists_problems_problemK_eval_ge_of_countermodel_ured
      (fun n => exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n)
        (fun w => Forces V w Ψ))
      (fun n => Ψ.eval P (fun i =>
        exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) (fun w => V w i))) := by
  induction Ψ with
  | var i =>
    exact ⟨exists_problems_problemK_eval_ge_of_countermodel_ured_refl _,
      exists_problems_problemK_eval_ge_of_countermodel_ured_refl _⟩
  | conj A B ihA ihB =>
    obtain ⟨h1, h2⟩ := exists_problems_problemK_eval_ge_of_countermodel_conj D P hP r t ω hω
      (fun w => Forces V w A) (fun w => Forces V w B)
      (fun _ _ h hw => forces_mono hV A h hw) (fun _ _ h hw => forces_mono hV B h hw)
    exact ⟨exists_problems_problemK_eval_ge_of_countermodel_ured_trans
        (exists_problems_problemK_eval_ge_of_countermodel_ured_conj P hP ihA.1 ihB.1) h1,
      exists_problems_problemK_eval_ge_of_countermodel_ured_trans h2
        (exists_problems_problemK_eval_ge_of_countermodel_ured_conj P hP ihA.2 ihB.2)⟩
  | disj A B ihA ihB =>
    obtain ⟨h1, h2⟩ := exists_problems_problemK_eval_ge_of_countermodel_disj D P hP r t ω hω
      (fun w => Forces V w A) (fun w => Forces V w B)
    exact ⟨exists_problems_problemK_eval_ge_of_countermodel_ured_trans
        (exists_problems_problemK_eval_ge_of_countermodel_ured_disj P hP ihA.1 ihB.1) h1,
      exists_problems_problemK_eval_ge_of_countermodel_ured_trans h2
        (exists_problems_problemK_eval_ge_of_countermodel_ured_disj P hP ihA.2 ihB.2)⟩
  | imp A B ihA ihB =>
    have hA : ∀ w w' : W, w ≤ w' → Forces V w A → Forces V w' A :=
      fun _ _ h hw => forces_mono hV A h hw
    have hB : ∀ w w' : W, w ≤ w' → Forces V w B → Forces V w' B :=
      fun _ _ h hw => forces_mono hV B h hw
    exact ⟨exists_problems_problemK_eval_ge_of_countermodel_ured_trans
        (exists_problems_problemK_eval_ge_of_countermodel_ured_imp P hP ihA.2 ihB.1)
        (exists_problems_problemK_eval_ge_of_countermodel_imp_hard D hD P hP r t hr ω hω
          _ _ hA hB),
      exists_problems_problemK_eval_ge_of_countermodel_ured_trans
        (exists_problems_problemK_eval_ge_of_countermodel_imp_easy D P hP r t ω hω
          _ _ hA hB)
        (exists_problems_problemK_eval_ge_of_countermodel_ured_imp P hP ihA.1 ihB.2)⟩

/-- SUV Theorem 246 (Section 13.5, printed p. 413), the proof proper: from a finite rooted
Kripke model (a partial order with least element `r` and a monotone valuation) refuting `Φ` at
the root, for all large `n` there are problems `X₁, …, X_k` of complexity `O(n)` with
`C(Φ(X₁, …, X_k)) ≥ n`.  Book's construction (printed pp. 414-417): lengths `L` (pairwise ten
times apart, nonzero ones much larger than `n`, `0` at the root, decidable infinite sets of
lengths per world; WLOG a top world where all variables are true); "random" means
complexity at least `length/10`.  (The book assigns the length `2n` to the top world, which
with the threshold `length/10` only gives `C(Φ(X)) ≳ n/5`; assign e.g. `20n` instead, still
`O(n)`, so that every random string of that length has complexity at least `2n`.)
`C` = pairs `[x, y]` of random strings from incomparable worlds; `X_i` = `0x` for random `x`
from worlds where `t_i` is true, plus `1y` for `y ∈ C`.  By induction `Ψ(X₁, …, X_k)` is
algorithmically equivalent to `X_Ψ` (cases (A)-(C), with `problemReduces_conj`,
`problemReduces_disj`, `problemReduces_imp`); `X_Φ` has only strings much longer than `n` and
random. -/
theorem exists_problems_problemK_eval_ge_of_countermodel (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) {k : ℕ}
    (Φ : PFormula (Fin k)) {W : Type} [Finite W] [PartialOrder W] (r : W)
    (V : W → Fin k → Prop) (hr : ∀ w, r ≤ w) (hV : IsMonotoneValuation V)
    (hΦ : ¬ Forces V r Φ) :
    ∃ c N : ℕ, ∀ n ≥ N, ∃ X : Fin k → Set BitString,
      (∀ i, problemK D (X i) ≤ ((c * (n + 1) : ℕ) : ℕ∞)) ∧
        (n : ℕ∞) ≤ problemK D (Φ.eval P X) := by
  obtain ⟨W', _, _, r', t', V', hr', ht', hrt, hVt, hV', hΦ'⟩ :=
    exists_problems_problemK_eval_ge_of_countermodel_top Φ r V hr hV hΦ
  obtain ⟨ω, hω⟩ :=
    exists_problems_problemK_eval_ge_of_countermodel_lengths r' t' hrt
  obtain ⟨c, hc⟩ :=
    exists_problems_problemK_eval_ge_of_countermodel_complexity D hD P hP r' t'
  obtain ⟨N, hN⟩ := exists_problems_problemK_eval_ge_of_countermodel_lower D hD P hP r' t'
    hr' ω hω (fun w => Forces V' w Φ) hΦ'
    (fun n => Φ.eval P (fun i =>
      exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) (fun w => V' w i)))
    (exists_problems_problemK_eval_ge_of_countermodel_induction D hD P hP r' t' hr' V'
      hV' ω hω Φ).1
  refine ⟨c, max N 1, fun n hn => ⟨fun i =>
    exists_problems_problemK_eval_ge_of_countermodel_xset D P (ω n) (fun w => V' w i),
    fun i => ?_, ?_⟩⟩
  · exact hc n (ω n) _ (le_trans (le_max_right _ _) hn) (hω.2 n (le_trans (le_max_right _ _) hn))
      (hVt i)
  · exact hN n (le_trans (le_max_left _ _) hn)

/-- SUV Theorem 246 (Section 13.5, printed p. 413), An. A. Muchnik: if `Φ(t₁, …, t_k)` with
`∧`, `∨`, `→` is not provable in IPC, then for every `n` there are problems `X₁ⁿ, …, X_kⁿ` of
complexity `O(n)` such that `C(Φ(X₁ⁿ, …, X_kⁿ)) ≥ n` for all sufficiently large `n`.  ("For
every `n` … for all sufficiently large `n`" is stated as `∃ c N, ∀ n ≥ N, ∃ X, …`, which is
equivalent.)  The sets are infinite, so this is weaker than Theorem 238.  Proof: the finite
countermodel (`exists_finite_kripke_countermodel`) and
`exists_problems_problemK_eval_ge_of_countermodel`. -/
theorem exists_problems_problemK_eval_ge (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) {k : ℕ} (Φ : PFormula (Fin k))
    (hΦ : ¬ Φ.Provable) :
    ∃ c N : ℕ, ∀ n ≥ N, ∃ X : Fin k → Set BitString,
      (∀ i, problemK D (X i) ≤ ((c * (n + 1) : ℕ) : ℕ∞)) ∧
        (n : ℕ∞) ≤ problemK D (Φ.eval P X) := by
  obtain ⟨W, _, _, r, V, hr, hV, hF⟩ := exists_finite_kripke_countermodel Φ hΦ
  exact exists_problems_problemK_eval_ge_of_countermodel D hD P hP Φ r V hr hV hF

end InformationLogic
end Kolmogorov
