import KolmogorovMathlib.InformationLogic.Bridges
import KolmogorovMathlib.InformationLogic.IntuitionisticBounds
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerBallModels

/-!
# Peirce Log Bound

This module proves that the complexity of the problem `((x → y) → x) → x` (Peirce's law on
singleton problems) is `O(log n)` for all strings `x`, `y` of length at most `n`.

The proof follows the book: from a solution `p` of `(x → y) → x` one enumerates the pairs
`(u, v)` of short strings that are compatible with `p` (that is, `[p](l_τ) = u` for every
length-bounded map `τ` with `τ(u) = v`), and outputs the first `u`.  The combinatorics of
compatible pairs and the search procedure are proved in private lemmas, and the algorithm, which
depends on `n` only, is turned into a program of complexity `O(log n)`.

## Main declarations

* `problemK_peirce_singleton_le_log`: SUV Theorem 239 (Section 13.3), the `O(log n)` bound on
  the complexity of Peirce's law on singletons.
-/

namespace Kolmogorov
namespace InformationLogic

open ProblemCalculus

/-- Compatibility in the proof of Theorem 239: the pair `(u, v) ∈ S × S` (`S` = strings of length
at most `n`) is compatible with `p` if `[p](l_τ) = u` for every `τ : S → S` with `τ(u) = v`,
where `lt n τ` is the program `l_τ` (it depends on `τ` only through its restriction to `S`). -/
private def problemK_peirce_singleton_le_log_compat (P : ProblemCalculus)
    (lt : ℕ → (BitString → BitString) → BitString) (n : ℕ) (p u v : BitString) : Prop :=
  u.length ≤ n ∧ v.length ≤ n ∧ ∀ τ : BitString → BitString,
    (∀ w, w.length ≤ n → (τ w).length ≤ n) → τ u = v → u ∈ P.lang (p, lt n τ)

/-- Step 1 of the proof of `problemK_peirce_singleton_le_log`: the combinatorics of
compatible pairs.  If `p` solves `(x → y) → x`, `x, y` have length at most `n` and `lt n τ`
computes `τ` on `S`, then `(x, y)` is compatible with `p` and every compatible pair `(u, v)` has
`u = x` (otherwise take `τ` with `τ(x) = y`, `τ(u) = v`: `[p](l_τ)` would be both `x` and `u`). -/
private theorem problemK_peirce_singleton_le_log_step1_compat (P : ProblemCalculus)
    (lt : ℕ → (BitString → BitString) → BitString) (n : ℕ)
    (hlt : ∀ τ w, w.length ≤ n → P.lang (lt n τ, w) = Part.some (τ w))
    (x y : BitString) (hx : x.length ≤ n) (hy : y.length ≤ n) (p : BitString)
    (hp : p ∈ P.imp (P.imp {x} {y}) {x}) :
    problemK_peirce_singleton_le_log_compat P lt n p x y ∧
      ∀ u v, problemK_peirce_singleton_le_log_compat P lt n p u v → u = x := by
  have key : ∀ τ : BitString → BitString, τ x = y → x ∈ P.lang (p, lt n τ) := by
    intro τ hτ
    have hmem : lt n τ ∈ P.imp {x} {y} := by
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨y, Set.mem_singleton y, by rw [hlt τ w hx, hτ]; exact Part.mem_some y⟩
    obtain ⟨x', hx', hmx⟩ := hp (lt n τ) hmem
    rw [Set.mem_singleton_iff] at hx'
    rwa [hx'] at hmx
  refine ⟨⟨hx, hy, fun τ _ hτ => key τ hτ⟩, ?_⟩
  rintro u v ⟨hu, hv, hcomp⟩
  by_contra hne
  let τ : BitString → BitString := fun w => if w = u then v else if w = x then y else []
  have hτS : ∀ w, w.length ≤ n → (τ w).length ≤ n := by
    intro w _
    simp only [τ]
    split_ifs <;> simp [hv, hy]
  have hτu : τ u = v := by simp [τ]
  have hτx : τ x = y := by simp [τ, Ne.symm hne]
  exact hne (Part.mem_unique (hcomp τ hτS hτu) (key τ hτx))

/-- The strings of length at most `n`. -/
private def problemK_peirce_singleton_le_log_search_strs (n : ℕ) : List BitString :=
  (List.range (n + 1)).flatMap allStrings

/-- The table of `τ` on the strings of length at most `n`, as an association list (keys in
reverse enumeration order). -/
private def problemK_peirce_singleton_le_log_search_tab (n : ℕ)
    (τ : BitString → BitString) : List (BitString × BitString) :=
  ((problemK_peirce_singleton_le_log_search_strs n).reverse).map fun w => (w, τ w)

/-- All tables `S → S` (association lists), `S` the strings of length at most `n`. -/
private def problemK_peirce_singleton_le_log_search_tabsAll (n : ℕ) :
    List (List (BitString × BitString)) :=
  (problemK_peirce_singleton_le_log_search_strs n).foldl
    (fun acc w => (problemK_peirce_singleton_le_log_search_strs n).flatMap
      fun v => acc.map fun T => (w, v) :: T) [[]]

/-- Compatibility in terms of tables: for all tables `T : S → S` with `T u = v`, `u ∈ [p](t T)`. -/
private def problemK_peirce_singleton_le_log_search_good (P : ProblemCalculus)
    (t : List (BitString × BitString) → BitString) (n : ℕ) (p u v : BitString) : Prop :=
  u.length ≤ n ∧ v.length ≤ n ∧
    ∀ T ∈ problemK_peirce_singleton_le_log_search_tabsAll n,
      T.lookup u = some v → u ∈ P.lang (p, t T)

/-- Step 1 of the proof of `problemK_peirce_singleton_le_log_step2_search`: the table of
`τ` on `S` returns `τ w` on every `w ∈ S`. -/
private theorem problemK_peirce_singleton_le_log_lookup (n : ℕ)
    (τ : BitString → BitString) (w : BitString) (hw : w.length ≤ n) :
    (problemK_peirce_singleton_le_log_search_tab n τ).lookup w = some (τ w) := by
  have key : ∀ l : List BitString, w ∈ l → (l.map fun w => (w, τ w)).lookup w = some (τ w) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hm
      by_cases h : a = w
      · subst h; simp
      · have : w ∈ l := by simpa [Ne.symm h] using hm
        have hne : (w == a) = false := beq_false_of_ne (Ne.symm h)
        simp [List.lookup, hne, ih this]
  unfold problemK_peirce_singleton_le_log_search_tab
  refine key _ ?_
  simp only [List.mem_reverse, problemK_peirce_singleton_le_log_search_strs,
    List.mem_flatMap, List.mem_range, mem_allStrings]
  exact ⟨w.length, by omega, rfl⟩

/-- Membership in the fold defining `tabsAll`, for an arbitrary key list `L`. -/
private theorem problemK_peirce_singleton_le_log_tabsAll_mem_aux_fold
    (S : List BitString) (L : List BitString) (acc : List (List (BitString × BitString)))
    (T : List (BitString × BitString)) :
    T ∈ L.foldl (fun acc w => S.flatMap fun v => acc.map fun T => (w, v) :: T) acc ↔
      ∃ T0 ∈ acc, ∃ vs : List BitString, vs.length = L.length ∧ (∀ v ∈ vs, v ∈ S) ∧
        T = (L.zip vs).reverse ++ T0 := by
  induction L generalizing acc with
  | nil =>
    simp only [List.foldl_nil, List.length_nil, List.length_eq_zero_iff]
    constructor
    · intro h; exact ⟨T, h, [], rfl, by simp, by simp⟩
    · rintro ⟨T0, h0, vs, rfl, -, rfl⟩; simpa using h0
  | cons a L ih =>
    simp only [List.foldl_cons, ih]
    constructor
    · rintro ⟨T1, h1, vs, hlen, hvs, rfl⟩
      simp only [List.mem_flatMap, List.mem_map] at h1
      obtain ⟨v, hv, T0, h0, rfl⟩ := h1
      refine ⟨T0, h0, v :: vs, by simp [hlen], ?_, by simp [List.reverse_cons, List.append_assoc]⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hv
      · exact hvs x hx
    · rintro ⟨T0, h0, vs, hlen, hvs, rfl⟩
      cases vs with
      | nil => simp at hlen
      | cons v vs =>
        refine ⟨(a, v) :: T0, ?_, vs, by simpa using hlen,
          fun x hx => hvs x (List.mem_cons_of_mem _ hx), by simp⟩
        simp only [List.mem_flatMap, List.mem_map]
        exact ⟨v, hvs v (List.mem_cons_self), T0, h0, rfl⟩

/-- Zipping a duplicate-free key list with values is the table of the lookup function. -/
private theorem problemK_peirce_singleton_le_log_tabsAll_mem_aux_zip
    (L : List BitString) (hL : L.Nodup) (vs : List BitString) (hlen : vs.length = L.length) :
    L.zip vs = L.map fun w => (w, ((L.zip vs).lookup w).getD []) := by
  induction L generalizing vs with
  | nil => simp
  | cons a L ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      have hnd := List.nodup_cons.1 hL
      have h1 := ih hnd.2 vs (by simpa using hlen)
      simp only [List.zip_cons_cons, List.map_cons, List.lookup, beq_self_eq_true,
        Option.getD_some]
      refine congrArg _ ?_
      conv_lhs => rw [h1]
      refine List.map_congr_left fun w hw => ?_
      have : (w == a) = false := beq_false_of_ne (fun h => hnd.1 (h ▸ hw))
      simp [this]

/-- A lookup in a zipped table returns one of the values. -/
private theorem problemK_peirce_singleton_le_log_tabsAll_mem_aux_lookup
    (L vs : List BitString) (w v : BitString) (h : (L.zip vs).lookup w = some v) : v ∈ vs := by
  induction L generalizing vs with
  | nil => simp at h
  | cons a L ih =>
    cases vs with
    | nil => simp at h
    | cons b vs =>
      simp only [List.zip_cons_cons, List.lookup] at h
      by_cases hw : (w == a) = true
      · rw [hw] at h; simp at h; simp [h]
      · rw [Bool.not_eq_true] at hw
        rw [hw] at h
        exact List.mem_cons_of_mem _ (ih vs h)

/-- Step 2 of the proof of `problemK_peirce_singleton_le_log_step2_search`: the finite
list of tables is exactly the list of the tables of the maps `τ` with `τ(S) ⊆ S`. -/
private theorem problemK_peirce_singleton_le_log_tabsAll_mem (n : ℕ)
    (T : List (BitString × BitString)) :
    T ∈ problemK_peirce_singleton_le_log_search_tabsAll n ↔
      ∃ τ : BitString → BitString, (∀ w, w.length ≤ n → (τ w).length ≤ n) ∧
        T = problemK_peirce_singleton_le_log_search_tab n τ := by
  classical
  have hmemL : ∀ w, w ∈ problemK_peirce_singleton_le_log_search_strs n ↔
      w.length ≤ n := by
    intro w
    simp only [problemK_peirce_singleton_le_log_search_strs, List.mem_flatMap,
      List.mem_range, mem_allStrings]
    constructor
    · rintro ⟨k, hk, rfl⟩; omega
    · intro h; exact ⟨w.length, by omega, rfl⟩
  have hnd : (problemK_peirce_singleton_le_log_search_strs n).Nodup := by
    unfold problemK_peirce_singleton_le_log_search_strs
    refine List.nodup_flatMap.2 ⟨fun k _ => allStrings_nodup k, ?_⟩
    refine (List.nodup_range).imp fun {a b} hab => ?_
    simp only [Function.onFun, List.disjoint_left, mem_allStrings]
    intro x hx hx'
    exact hab (hx.symm.trans hx')
  unfold problemK_peirce_singleton_le_log_search_tabsAll
  rw [problemK_peirce_singleton_le_log_tabsAll_mem_aux_fold]
  unfold problemK_peirce_singleton_le_log_search_tab
  constructor
  · rintro ⟨T0, h0, vs, hlen, hvs, rfl⟩
    have h0' : T0 = [] := by simpa using h0
    subst h0'
    set L := problemK_peirce_singleton_le_log_search_strs n
    refine ⟨fun w => ((L.zip vs).lookup w).getD [], ?_, ?_⟩
    · intro w _
      cases hlk : (L.zip vs).lookup w with
      | none => simp only [hlk, Option.getD_none, List.length_nil]; omega
      | some v =>
        have := (hmemL v).1
          (problemK_peirce_singleton_le_log_tabsAll_mem_aux_lookup L vs w v hlk
            |> hvs v)
        simpa only [hlk, Option.getD_some] using this
    · rw [List.append_nil, List.map_reverse,
        ← problemK_peirce_singleton_le_log_tabsAll_mem_aux_zip L hnd vs hlen]
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨[], by simp, (problemK_peirce_singleton_le_log_search_strs n).map τ,
      by simp, ?_, ?_⟩
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
      exact (hmemL _).2 (hτ w ((hmemL w).1 hw))
    · have hz : ∀ L : List BitString, L.zip (L.map τ) = L.map fun w => (w, τ w) := by
        intro L
        induction L with
        | nil => rfl
        | cons a L ih => simp [ih]
      rw [List.append_nil, hz, List.map_reverse]

/-- Step 3 of the proof of `problemK_peirce_singleton_le_log_step2_search`: the list of
tables is computable from `n`. -/
private theorem problemK_peirce_singleton_le_log_tabsAll_primrec :
    Primrec problemK_peirce_singleton_le_log_search_tabsAll := by
  have hs : Primrec problemK_peirce_singleton_le_log_search_strs :=
    Primrec.list_flatMap (Primrec.list_range.comp Primrec.succ)
      (CodedFiniteDistribution.allStrings_primrec.comp Primrec.snd).to₂
  unfold problemK_peirce_singleton_le_log_search_tabsAll
  refine Primrec.list_foldl (h := fun (n : ℕ) (q : List (List (BitString × BitString)) × BitString)
      =>
      (problemK_peirce_singleton_le_log_search_strs n).flatMap
        fun v => q.1.map fun T => (q.2, v) :: T) hs
    (Primrec.const ([[]] : List (List (BitString × BitString)))) ?_
  refine Primrec.list_flatMap (hs.comp Primrec.fst) ?_
  refine Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) ?_
  exact Primrec.list_cons.comp (Primrec.pair
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) (Primrec.snd.comp
        Primrec.fst))
    Primrec.snd

/-- Step 4 of the proof of `problemK_peirce_singleton_le_log_step2_search`: the Gödel
property gives a total computable map `t` from (finite) tables to programs, such that the program
`t T` returns `y` on `w` whenever the table `T` has `y` as the first entry for `w`. -/
private theorem problemK_peirce_singleton_le_log_programs
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ t : List (BitString × BitString) → BitString, Computable t ∧
      ∀ (T : List (BitString × BitString)) (w y : BitString),
        T.lookup w = some y → P.lang (t T, w) = Part.some y := by
  obtain ⟨-, -, -, -, -, -, hG⟩ := hP
  let V : Map := fun q =>
    ↑((Encodable.decode (α := List (BitString × BitString)) q.1.length).bind
      fun T => T.lookup q.2)
  have hV : Partrec V := by
    refine Computable.ofOption ?_
    refine Computable.option_bind (Computable.decode.comp (Computable.list_length.comp
      Computable.fst)) ?_
    have hb : ∀ (a : BitString) (l : List (BitString × BitString)),
        @List.lookup _ _ instBEqOfDecidableEq a l = l.lookup a := by
      intro a l
      induction l with
      | nil => rfl
      | cons x l ih =>
        obtain ⟨k, b⟩ := x
        by_cases h : a = k
        · subst h; simp [List.lookup]
        · have h1 : (a == k) = false := beq_false_of_ne h
          have h2 : @BEq.beq _ instBEqOfDecidableEq a k = false := by simp [h]
          simp only [List.lookup, h1, h2]
          exact ih
    have hp : Primrec (fun x : (BitString × BitString) × List (BitString × BitString) =>
        @List.lookup _ _ instBEqOfDecidableEq x.1.2 x.2) :=
      Primrec.listLookup.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
    exact (hp.of_eq fun x => hb _ _).to_comp
  obtain ⟨t0, ht0, hts⟩ := hG V hV
  have hrep : Computable (fun m : ℕ => (List.replicate m false : BitString)) := by
    have : Primrec (fun m : ℕ => (List.range m).map (fun _ => false)) :=
      Primrec.list_map Primrec.list_range (Primrec.const false).to₂
    refine this.to_comp.of_eq fun m => ?_
    simp [List.map_const', List.length_range]
  refine ⟨fun T => t0 (List.replicate (Encodable.encode T) false),
    ht0.comp (hrep.comp Computable.encode), fun T w y hT => ?_⟩
  rw [hts]
  change (↑((Encodable.decode (α := List (BitString × BitString))
    (List.replicate (Encodable.encode T) false).length).bind fun T => T.lookup w) : Part BitString)
    = _
  simp [hT]

/-- Dovetailed search for a witness (as `problemK_disj_le_imp_pdisj_disj_search`): if
`chk (a, b) s` is a computable test, there is a partial computable `f` returning, on `a`, some
`b` for which the test succeeds at some stage, and defined whenever such a `b` exists. -/
private lemma problemK_peirce_singleton_le_log_search_select {α β : Type*}
    [Primcodable α] [Primcodable β] (chk : α × β → ℕ → Bool) (hchk : Computable₂ chk) :
    ∃ f : α →. β, Partrec f ∧ (∀ a b, b ∈ f a → ∃ s, chk (a, b) s = true) ∧
      ∀ a b s, chk (a, b) s = true → (f a).Dom := by
  let g : α → ℕ → Option β := fun a k =>
    (Encodable.decode (α := β) k.unpair.1).bind fun b =>
      bif chk (a, b) k.unpair.2 then some b else none
  have hk1 : Computable fun p : α × ℕ => p.2.unpair.1 :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hk2 : Computable fun p : α × ℕ => p.2.unpair.2 :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hg : Computable₂ g := by
    refine Computable.option_bind (Computable.decode.comp hk1) ?_
    have hc : Computable fun q : (α × ℕ) × β => chk (q.1.1, q.2) q.1.2.unpair.2 :=
      hchk.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
        (hk2.comp Computable.fst)
    have hs : Computable fun q : (α × ℕ) × β => (some q.2 : Option β) :=
      (Computable.option_some (α := β)).comp Computable.snd
    exact (Computable.cond hc hs (Computable.const (none : Option β))).to₂
  refine ⟨fun a => Nat.rfindOpt (g a), Partrec.rfindOpt hg, ?_, ?_⟩
  · intro a b hb
    obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hb
    simp only [g, Option.mem_def] at hk
    cases hd : Encodable.decode (α := β) k.unpair.1 with
    | none => simp [hd] at hk
    | some b0 =>
      simp only [hd, Option.bind_some] at hk
      cases hc : chk (a, b0) k.unpair.2 with
      | false => simp [hc] at hk
      | true =>
        simp only [hc, Bool.cond_true, Option.some.injEq] at hk
        subst hk
        exact ⟨_, hc⟩
  · intro a b s hs
    change (Nat.rfindOpt (g a)).Dom
    rw [Nat.rfindOpt_dom]
    refine ⟨Nat.pair (Encodable.encode b) s, b, ?_⟩
    simp [g, hs]

/-- A finite list of monotone stage conditions holds at a common stage. -/
private lemma problemK_peirce_singleton_le_log_search_stage {β : Type*}
    (Q : β → ℕ → Prop) (hmono : ∀ x s t, s ≤ t → Q x s → Q x t) :
    ∀ l : List β, (∀ x ∈ l, ∃ s, Q x s) → ∃ s, ∀ x ∈ l, Q x s := by
  intro l
  induction l with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons x t ih =>
    intro h
    obtain ⟨s1, hs1⟩ := h x (by simp)
    obtain ⟨s2, hs2⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨max s1 s2, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hmono _ _ _ (le_max_left _ _) hs1
    · exact hmono _ _ _ (le_max_right _ _) (hs2 y hy)

/-- The table lookup `T.lookup w` is primitive recursive in `(w, T)`. -/
private lemma problemK_peirce_singleton_le_log_search_lookup :
    Primrec₂ (fun (w : BitString) (T : List (BitString × BitString)) => T.lookup w) := by
  have hb : ∀ (a : BitString) (l : List (BitString × BitString)),
      @List.lookup _ _ instBEqOfDecidableEq a l = l.lookup a := by
    intro a l
    induction l with
    | nil => rfl
    | cons x l ih =>
      obtain ⟨k, b⟩ := x
      by_cases h : a = k
      · subst h; simp [List.lookup]
      · have h1 : (a == k) = false := beq_false_of_ne h
        have h2 : @BEq.beq _ instBEqOfDecidableEq a k = false := by simp [h]
        simp only [List.lookup, h1, h2]
        exact ih
  have hp : Primrec₂ (fun (w : BitString) (T : List (BitString × BitString)) =>
      @List.lookup _ _ instBEqOfDecidableEq w T) :=
    Primrec.listLookup
  exact hp.of_eq fun w T => hb w T

/-- Step 5 of the proof of `problemK_peirce_singleton_le_log_step2_search`: the
dovetailed search.  For a computable `t` there is a partial computable `Φ (n, p)` whose every value
`u` comes from a pair `(u, v)` with `u, v ∈ S` and `u ∈ [p](t T)` for all tables `T : S → S`
(`problemK_peirce_singleton_le_log_search_tabsAll`) with `T u = v`, and which is defined
whenever such a pair exists.  (Use `P.lang` partial computable: the relation `u ∈ [p](t T)` is
r.e., `IsRE.exists_stageApprox`; check the finitely many tables of a candidate pair at one common
stage, dovetail over candidates and stages with `Nat.rfindOpt`.) -/
private theorem problemK_peirce_singleton_le_log_search
    (P : ProblemCalculus) (hP : P.Admissible)
    (t : List (BitString × BitString) → BitString) (ht : Computable t) :
    ∃ Φ : ℕ × BitString →. BitString, Partrec Φ ∧
      (∀ n p u, u ∈ Φ (n, p) → ∃ v,
        problemK_peirce_singleton_le_log_search_good P t n p u v) ∧
      (∀ n p u v, problemK_peirce_singleton_le_log_search_good P t n p u v →
        (Φ (n, p)).Dom) := by
  have hL : Partrec P.lang := hP.2.2.2.2.2.1
  -- the r.e. relation `u ∈ [p](t T)` and its stage approximation
  obtain ⟨chkR, hchkR, hmonoR, hiffR⟩ := IsRE.exists_stageApprox
    ((Partrec.graphIsRe P.lang hL).comp_computable
      (g := fun q : (BitString × List (BitString × BitString)) × BitString =>
        ((q.1.1, t q.1.2), q.2))
      (((Computable.fst.comp Computable.fst).pair
        (ht.comp (Computable.snd.comp Computable.fst))).pair Computable.snd))
  -- a table `T : S → S` is bad at stage `s` for the candidate `(u, v)` if `T u = v` but
  -- `u ∈ [p](t T)` is not yet confirmed
  let bad : ((ℕ × BitString) × (BitString × BitString)) × ℕ →
      List (BitString × BitString) → Bool :=
    fun x T => decide (T.lookup x.1.2.1 = some x.1.2.2) && !chkR ((x.1.1.2, T), x.1.2.1) x.2
  let chk : (ℕ × BitString) × (BitString × BitString) → ℕ → Bool := fun z s =>
    decide (z.2.1.length ≤ z.1.1) && decide (z.2.2.length ≤ z.1.1) &&
      !((problemK_peirce_singleton_le_log_search_tabsAll z.1.1).any (bad (z, s)))
  have hchk : Computable₂ chk := by
    have hbad : Computable₂ bad := by
      have hlk : Computable (fun y : (((ℕ × BitString) × (BitString × BitString)) × ℕ) ×
          List (BitString × BitString) => y.2.lookup y.1.1.2.1) :=
        problemK_peirce_singleton_le_log_search_lookup.to_comp.comp
          (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))
          Computable.snd
      have h1 : Computable (fun y : (((ℕ × BitString) × (BitString × BitString)) × ℕ) ×
          List (BitString × BitString) => decide (y.2.lookup y.1.1.2.1 = some y.1.1.2.2)) :=
        primrec_decideEq.to_comp.comp hlk (Computable.option_some.comp
          (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))))
      have h2 : Computable (fun y : (((ℕ × BitString) × (BitString × BitString)) × ℕ) ×
          List (BitString × BitString) => chkR ((y.1.1.1.2, y.2), y.1.1.2.1) y.1.2) :=
        hchkR.comp (((Computable.snd.comp (Computable.fst.comp (Computable.fst.comp
          Computable.fst))).pair Computable.snd).pair (Computable.fst.comp
            (Computable.snd.comp (Computable.fst.comp Computable.fst))))
          (Computable.snd.comp Computable.fst)
      exact (Primrec.and.to_comp.comp h1 (Primrec.not.to_comp.comp h2)).to₂
    have htabs : Computable (fun x : ((ℕ × BitString) × (BitString × BitString)) × ℕ =>
        problemK_peirce_singleton_le_log_search_tabsAll x.1.1.1) :=
      problemK_peirce_singleton_le_log_tabsAll_primrec.to_comp.comp
        (Computable.fst.comp (Computable.fst.comp Computable.fst))
    have hany : Computable (fun x : ((ℕ × BitString) × (BitString × BitString)) × ℕ =>
        (problemK_peirce_singleton_le_log_search_tabsAll x.1.1.1).any (bad x)) :=
      computable_list_any (f := fun x : ((ℕ × BitString) × (BitString × BitString)) × ℕ =>
        problemK_peirce_singleton_le_log_search_tabsAll x.1.1.1) (p := bad) htabs hbad
    have e1 : Computable (fun x : ((ℕ × BitString) × (BitString × BitString)) × ℕ =>
        decide (x.1.2.1.length ≤ x.1.1.1)) :=
      (Primrec.nat_le.decide.to_comp).comp
        (Primrec.list_length.to_comp.comp (Computable.fst.comp (Computable.snd.comp
          Computable.fst)))
        (Computable.fst.comp (Computable.fst.comp Computable.fst))
    have e2 : Computable (fun x : ((ℕ × BitString) × (BitString × BitString)) × ℕ =>
        decide (x.1.2.2.length ≤ x.1.1.1)) :=
      (Primrec.nat_le.decide.to_comp).comp
        (Primrec.list_length.to_comp.comp (Computable.snd.comp (Computable.snd.comp
          Computable.fst)))
        (Computable.fst.comp (Computable.fst.comp Computable.fst))
    exact Primrec.and.to_comp.comp (Primrec.and.to_comp.comp e1 e2)
      (Primrec.not.to_comp.comp hany)
  have hspec : ∀ (z : (ℕ × BitString) × (BitString × BitString)) (s : ℕ),
      chk z s = true ↔ z.2.1.length ≤ z.1.1 ∧ z.2.2.length ≤ z.1.1 ∧
        ∀ T ∈ problemK_peirce_singleton_le_log_search_tabsAll z.1.1,
          T.lookup z.2.1 = some z.2.2 → chkR ((z.1.2, T), z.2.1) s = true := by
    intro z s
    simp only [chk, bad, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      List.any_eq_false, and_assoc]
    refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
    refine forall_congr' fun T => imp_congr_right fun _ => ?_
    constructor
    · intro h hlk
      by_contra hne
      exact h ⟨hlk, by simpa using hne⟩
    · rintro h ⟨hlk, hf⟩
      rw [h hlk] at hf
      exact Bool.noConfusion hf
  obtain ⟨f, hf, hsound, hdom⟩ :=
    problemK_peirce_singleton_le_log_search_select chk hchk
  refine ⟨fun a => (f a).map Prod.fst, hf.map (Computable.fst.comp Computable.snd).to₂, ?_, ?_⟩
  · intro n p u hu
    obtain ⟨r, hr, rfl⟩ := (Part.mem_map_iff _).1 hu
    obtain ⟨s, hs⟩ := hsound (n, p) r hr
    obtain ⟨h1, h2, h3⟩ := (hspec _ _).1 hs
    exact ⟨r.2, h1, h2, fun T hT hlk => (hiffR ((p, T), r.1)).2 ⟨s, h3 T hT hlk⟩⟩
  · rintro n p u v ⟨hu, hv, hgood⟩
    obtain ⟨s, hs⟩ := problemK_peirce_singleton_le_log_search_stage
      (fun (T : List (BitString × BitString)) (s : ℕ) =>
        T.lookup u = some v → chkR ((p, T), u) s = true)
      (by intro T s s' hss' h hlk; exact hmonoR _ _ _ hss' (h hlk))
      (problemK_peirce_singleton_le_log_search_tabsAll n)
      (fun T hT => by
        by_cases hlk : T.lookup u = some v
        · obtain ⟨s, hs⟩ := (hiffR ((p, T), u)).1 (hgood T hT hlk)
          exact ⟨s, fun _ => hs⟩
        · exact ⟨0, fun h => absurd h hlk⟩)
    exact hdom (n, p) (u, v) s ((hspec _ _).2 ⟨hu, hv, hs⟩)

/-- Step 2 of the proof of `problemK_peirce_singleton_le_log`: the search algorithm.
Fix `n` and let `S` be the strings of length at most `n`.  For every total `τ : BitString →
BitString` a program `lt n τ` is found effectively from the (finite) table of `τ|S` such that
`[lt n τ](w) = τ w` for `w ∈ S` (Gödel property, `P.Admissible`; the program depends only on the
table of `τ` on `S`).  Then a partial computable `Φ (n, p)` dovetails the finitely many
candidates `(u, v) ∈ S × S`, and for each of them the finitely many tables `τ : S → S` with
`τ u = v` and the computations `[p](lt n τ)` (call `(u, v)` compatible with `p` if
`u ∈ [p](lt n τ)` for all such `τ`, `problemK_peirce_singleton_le_log_compat`); it outputs `u`
for the first candidate for which all these computations have halted with value `u`.  So `Φ`
is sound (an output `u` comes from a compatible pair) and complete (if a compatible pair exists
then `Φ (n, p)` halts).  Only the computability of `Φ` and of the table-to-program map is new
here (partial recursive functions, `evaln`/`Partrec.rfind` for the dovetailing, the finite list
of all tables `S → S`). -/
private theorem problemK_peirce_singleton_le_log_step2_search (P : ProblemCalculus)
    (hP : P.Admissible) :
    ∃ (lt : ℕ → (BitString → BitString) → BitString) (Φ : ℕ × BitString →. BitString),
      Partrec Φ ∧
      (∀ n τ w, w.length ≤ n → P.lang (lt n τ, w) = Part.some (τ w)) ∧
      (∀ n p u, u ∈ Φ (n, p) →
        ∃ v, problemK_peirce_singleton_le_log_compat P lt n p u v) ∧
      (∀ n p u v, problemK_peirce_singleton_le_log_compat P lt n p u v → (Φ (n, p)).Dom) := by
  obtain ⟨t, ht, htspec⟩ := problemK_peirce_singleton_le_log_programs P hP
  obtain ⟨Φ, hΦ, hsound, hcomp⟩ :=
    problemK_peirce_singleton_le_log_search P hP t ht
  have hiff : ∀ n p u v, problemK_peirce_singleton_le_log_compat P
      (fun n τ => t (problemK_peirce_singleton_le_log_search_tab n τ)) n p u v ↔
      problemK_peirce_singleton_le_log_search_good P t n p u v := by
    intro n p u v
    unfold problemK_peirce_singleton_le_log_compat
      problemK_peirce_singleton_le_log_search_good
    refine and_congr_right fun hu => and_congr_right fun hv => ?_
    constructor
    · intro h T hT hlk
      obtain ⟨τ, hτ, rfl⟩ :=
        (problemK_peirce_singleton_le_log_tabsAll_mem n T).1 hT
      rw [problemK_peirce_singleton_le_log_lookup n τ u hu] at hlk
      exact h τ hτ (Option.some.inj hlk)
    · intro h τ hτ hτu
      refine h _ ((problemK_peirce_singleton_le_log_tabsAll_mem n _).2
        ⟨τ, hτ, rfl⟩) ?_
      rw [problemK_peirce_singleton_le_log_lookup n τ u hu, hτu]
  refine ⟨fun n τ => t (problemK_peirce_singleton_le_log_search_tab n τ), Φ, hΦ, ?_, ?_, ?_⟩
  · intro n τ w hw
    exact htspec _ w _ (problemK_peirce_singleton_le_log_lookup n τ w hw)
  · intro n p u hu
    obtain ⟨v, hv⟩ := hsound n p u hu
    exact ⟨v, (hiff n p u v).2 hv⟩
  · intro n p u v h
    exact hcomp n p u v ((hiff n p u v).1 h)

/-- Step 3 of the proof of `problemK_peirce_singleton_le_log`: the algorithm `Φ` of
step 2 depends on `n` only, so by the Gödel property it becomes a program `t (0^n)` and then
`problemK_le_of_partrec_advice` (applied to the one-element problem `{[]}`) gives the bound:
if `Φ` solves, for all `x, y` of length at most `n` and every solution `p` of `(x → y) → x`,
`x ∈ Φ (n, p)`, then the complexity is `O(log n)`. -/
private theorem problemK_peirce_singleton_le_log_advice (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible)
    (Φ : ℕ × BitString →. BitString) (hΦ : Partrec Φ)
    (hsol : ∀ (n : ℕ) (x y : BitString), x.length ≤ n → y.length ≤ n →
      ∀ p ∈ P.imp (P.imp {x} {y}) {x}, x ∈ Φ (n, p)) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y : BitString), x.length ≤ n → y.length ≤ n →
      problemK D (P.imp (P.imp (P.imp {x} {y}) {x}) {x}) ≤ (logSlack k n : ℕ∞) := by
  obtain ⟨-, -, -, -, -, hL, hG⟩ := hP
  have hV : Partrec (fun q : BitString × BitString => Φ (q.1.length, q.2)) :=
    hΦ.comp ((Computable.list_length.comp Computable.fst).pair Computable.snd)
  obtain ⟨t, ht, hts⟩ := hG _ hV
  let f : BitString × (ℕ × Bool) →. BitString := fun a => Part.some (t (List.replicate a.2.1 false))
  have hf : Partrec f := by
    have : Computable (fun a : BitString × (ℕ × Bool) => t (List.replicate a.2.1 false)) :=
      ht.comp ((Primrec.list_replicate.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.const false)).to_comp)
    exact this.partrec
  obtain ⟨c, hc⟩ := problemK_le_of_partrec_advice D hD f hf
  obtain ⟨c0, hc0⟩ := exists_problemK_le_of_mem D hD ([] : BitString)
  refine ⟨c + c0, fun n x y hx hy => ?_⟩
  have hY : ∀ x' ∈ ({[]} : Set BitString), ∃ b : Bool,
      ∃ y' ∈ P.imp (P.imp (P.imp {x} {y}) {x}) {x}, y' ∈ f (x', n, b) := by
    intro x' _
    refine ⟨false, t (List.replicate n false), ?_, Part.mem_some _⟩
    intro p hp
    refine ⟨x, Set.mem_singleton x, ?_⟩
    rw [hts]
    simpa using hsol n x y hx hy p hp
  have h1 := hc {[]} _ n hY
  have h2 := hc0 {[]} rfl
  rw [problemK_singleton] at h1 h2
  calc _ ≤ _ := h1
    _ ≤ (c0 : ℕ∞) + (logSlack c n : ℕ∞) := by gcongr
    _ ≤ (logSlack (c + c0) n : ℕ∞) := by
        rw [logSlack_add_constants]
        have : c0 ≤ logSlack c0 n := Nat.le_add_left _ _
        rw [add_comm]
        exact_mod_cast Nat.add_le_add_left this _

/-- SUV Theorem 239 (Section 13.3, printed p. 405).  The complexity of the problem
`((x → y) → x) → x` (Peirce's law on singletons) is `O(log n)` for all strings `x`, `y` of
length at most `n`.  Book's proof: given `n` and a solution `p` of `(x → y) → x`, enumerate the
pairs `(u, v) ∈ S × S` with `[p](l_τ) = u` for all `τ` with `τ(u) = v`; `(x, y)` is one of
them, and every compatible pair has `u = x` (otherwise some `τ` maps `x ↦ y` and `u ↦ v`, and
`[p](l_τ)` would equal both `x` and `u`).  Output the first `u`.  This algorithm depends on `n`
only, so by the Gödel property it is a program of complexity `C(n) + O(1) = O(log n)` (e.g.
`problemK_le_of_partrec_advice` applied to a fixed one-element problem `X`). -/
theorem problemK_peirce_singleton_le_log (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y : BitString), x.length ≤ n → y.length ≤ n →
      problemK D (P.imp (P.imp (P.imp {x} {y}) {x}) {x}) ≤ (logSlack k n : ℕ∞) := by
  obtain ⟨lt, Φ, hΦ, hlt, hsound, hcomplete⟩ :=
    problemK_peirce_singleton_le_log_step2_search P hP
  refine problemK_peirce_singleton_le_log_advice D hD P hP Φ hΦ ?_
  intro n x y hx hy p hp
  obtain ⟨hxy, huniq⟩ := problemK_peirce_singleton_le_log_step1_compat P lt n (hlt n) x y hx hy p hp
  obtain ⟨u, hu⟩ := Part.dom_iff_mem.1 (hcomplete n p x y hxy)
  obtain ⟨v, hv⟩ := hsound n p u hu
  rwa [huniq u v hv] at hu

end InformationLogic
end Kolmogorov
