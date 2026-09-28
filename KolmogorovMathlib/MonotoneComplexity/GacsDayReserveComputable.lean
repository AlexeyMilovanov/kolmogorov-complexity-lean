import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwoComputable
import KolmogorovMathlib.Complexity.Incompressibility

/-!
# The reserved-interval test of SUV p. 142 is primitive recursive

`GacsDayLadderStep` defines the reserved-interval predicate `hasReserve` of the
half-step (a cylinder of measure `epsilon` that already covers allocated space
of the son `x`, avoids the unavailable set `A`, and avoids the allocation of
every vertex incomparable to `x`) and gives it a decision procedure through
`getReserve`.

Day's half-step has to *decide* that predicate while it plays, uniformly in the
scale, the unavailable set, the server move and the son.  This file supplies
that: a Boolean test `hasReserveB`, proved equal to `decide (hasReserve ...)`
and proved primitive recursive jointly in all four arguments.  It also records
the finite form of the predicate: the quantifier over cylinders ranges over the
finite set `stringsOfLength e`.
-/

namespace Kolmogorov

open Primrec

/-! ### Two generic list primitives -/

/-- `List.all` is the failure of a `List.find?` for the negated predicate. -/
theorem all_eq_not_isSome_find? {α : Type*} (p : α → Bool) (l : List α) :
    l.all p = !(l.find? (fun a => !p a)).isSome := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.all_cons, List.find?_cons]
    cases h : p a <;> simp [ih]

/-- `List.isPrefixOf` is primitive recursive over any primitively codable
alphabet, not only over the bits (`primrec₂_isPrefixOf`): the half-step tests
prefixes both of bit strings and of tree addresses. -/
theorem primrec₂_isPrefixOf_gen {α : Type*} [Primcodable α] [BEq α] [LawfulBEq α] :
    Primrec₂ (fun l1 l2 : List α => l1.isPrefixOf l2) := by
  classical
  have htake : Primrec (fun p : List α × List α => p.2.take p.1.length) :=
    Primrec.list_take.comp Primrec.snd (Primrec.list_length.comp Primrec.fst)
  have hrel : PrimrecPred (fun p : List α × List α => p.2.take p.1.length = p.1) :=
    PrimrecRel.comp Primrec.eq htake Primrec.fst
  exact (Primrec.ite hrel (Primrec.const true) (Primrec.const false)).of_eq fun p => by
    dsimp only
    rw [isPrefixOf_eq_beq]
    by_cases h : p.2.take p.1.length = p.1 <;> simp [h]

/-- Being a prefix is decided by `List.isPrefixOf`. -/
lemma isPrefixOf_eq_decide {α : Type*} [DecidableEq α] [BEq α] [LawfulBEq α] (l1 l2 : List α) :
    l1.isPrefixOf l2 = decide (l1 <+: l2) := by
  rw [Bool.eq_iff_iff]
  simp [List.isPrefixOf_iff_prefix]

/-! ### The Boolean reserve test -/

/-- Two cylinders are disjoint exactly when neither is a prefix of the other. -/
def cylDisjointB (R c : BitString) : Bool := !(R.isPrefixOf c || c.isPrefixOf R)

/-- The cylinder disjointness test decides incomparability of the two strings. -/
lemma cylDisjointB_eq_decide (R c : BitString) :
    cylDisjointB R c = decide (¬ (R <+: c ∨ c <+: R)) := by
  simp [cylDisjointB, isPrefixOf_eq_decide]

/-- The cylinder disjointness test is primitive recursive. -/
theorem primrec₂_cylDisjointB : Primrec₂ cylDisjointB :=
  Primrec.not.comp (Primrec.or.comp
    (primrec₂_isPrefixOf_gen.comp Primrec.fst Primrec.snd)
    (primrec₂_isPrefixOf_gen.comp Primrec.snd Primrec.fst))

/-- The test that the length-`e` prefix of an allocated string `v` is a reserved
interval for `x`: it must avoid `A` and the allocation of every vertex
incomparable to `x`. -/
def reserveTest (e : ℕ) (A : Allocation) (m : ServerMove) (x : GacsDayNode)
    (v : BitString) : Bool :=
  if e ≤ v.length then
    A.all (fun a => cylDisjointB (v.take e) a) &&
      m.all (fun p => if x.isPrefixOf p.1 || p.1.isPrefixOf x then true
        else (getAlloc m p.1).all (fun c => cylDisjointB (v.take e) c))
  else false

/-- The reserve search returns the first allocated string passing the reserve test. -/
lemma getReserve_eq_find? (e : ℕ) (A : Allocation) (m : ServerMove) (x : GacsDayNode) :
    getReserve e A m x = (getAlloc m x).find? (reserveTest e A m x) := by
  unfold getReserve reserveTest
  congr 1
  funext v
  by_cases h : e ≤ v.length
  · simp [h, cylDisjointB_eq_decide, isPrefixOf_eq_decide]
  · simp [h]

/-- The parameters of the reserve test: the scale, the unavailable set, the
server move and the son. -/
abbrev ReserveParam := (ℕ × Allocation) × ServerMove × GacsDayNode

/-- The reserve test is primitive recursive in its parameters and the candidate string. -/
theorem primrec_reserveTest :
    Primrec (fun q : ReserveParam × BitString =>
      reserveTest q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2) := by
  have he : Primrec (fun q : ReserveParam × BitString => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hA : Primrec (fun q : ReserveParam × BitString => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hm : Primrec (fun q : ReserveParam × BitString => q.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hx : Primrec (fun q : ReserveParam × BitString => q.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hR : Primrec (fun q : ReserveParam × BitString => q.2.take q.1.1.1) :=
    Primrec.list_take.comp Primrec.snd he
  have hAall : Primrec (fun q : ReserveParam × BitString =>
      q.1.1.2.all (fun a => cylDisjointB (q.2.take q.1.1.1) a)) :=
    list_all_primrec hA (primrec₂_cylDisjointB.comp (hR.comp Primrec.fst) Primrec.snd)
  have hinner : Primrec (fun r : (ReserveParam × BitString) × (GacsDayNode × Allocation) =>
      (getAlloc r.1.1.2.1 r.2.1).all (fun c => cylDisjointB (r.1.2.take r.1.1.1.1) c)) := by
    have hlist : Primrec (fun r : (ReserveParam × BitString) × (GacsDayNode × Allocation) =>
        getAlloc r.1.1.2.1 r.2.1) :=
      primrec₂_getAlloc.comp (hm.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
    exact list_all_primrec hlist
      (primrec₂_cylDisjointB.comp ((hR.comp Primrec.fst).comp Primrec.fst) Primrec.snd)
  have hcond : Primrec (fun r : (ReserveParam × BitString) × (GacsDayNode × Allocation) =>
      r.1.1.2.2.isPrefixOf r.2.1 || (r.2.1).isPrefixOf r.1.1.2.2) :=
    Primrec.or.comp
      (primrec₂_isPrefixOf_gen.comp (hx.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (primrec₂_isPrefixOf_gen.comp (Primrec.fst.comp Primrec.snd) (hx.comp Primrec.fst))
  have hpred : Primrec₂ (fun (q : ReserveParam × BitString) (p : GacsDayNode × Allocation) =>
      if q.1.2.2.isPrefixOf p.1 || p.1.isPrefixOf q.1.2.2 then true
        else (getAlloc q.1.2.1 p.1).all (fun c => cylDisjointB (q.2.take q.1.1.1) c)) :=
    (Primrec.cond hcond (Primrec.const true) hinner).of_eq fun r => by
      dsimp only
      rw [Bool.cond_eq_ite]
  have hmall : Primrec (fun q : ReserveParam × BitString =>
      q.1.2.1.all (fun p => if q.1.2.2.isPrefixOf p.1 || p.1.isPrefixOf q.1.2.2 then true
        else (getAlloc q.1.2.1 p.1).all (fun c => cylDisjointB (q.2.take q.1.1.1) c))) :=
    list_all_primrec hm hpred
  have hle : PrimrecPred (fun q : ReserveParam × BitString => q.1.1.1 ≤ q.2.length) :=
    PrimrecRel.comp Primrec.nat_le he (Primrec.list_length.comp Primrec.snd)
  exact (Primrec.ite hle (Primrec.and.comp hAall hmall) (Primrec.const false)).of_eq fun q => by
    by_cases h : q.1.1.1 ≤ q.2.length <;> simp [reserveTest, h]

/-- The Boolean reserved-interval test: decides whether some string allocated at `x` passes
`reserveTest e A m x`, that is has a length-`e` prefix avoiding `A` and the allocations of every
vertex incomparable to `x`. -/
def hasReserveB (e : ℕ) (A : Allocation) (m : ServerMove) (x : GacsDayNode) : Bool :=
  ((getAlloc m x).find? (reserveTest e A m x)).isSome

/-- The Boolean test decides the reserve predicate. -/
theorem hasReserveB_iff (e : ℕ) (A : Allocation) (m : ServerMove) (x : GacsDayNode) :
    hasReserveB e A m x = true ↔ hasReserve e A m x := by
  rw [hasReserveB, ← getReserve_eq_find?]
  exact getReserve_isSome_iff

/-- The decidable reserve test agrees with the existence of a reserve. -/
theorem hasReserveB_eq_decide (e : ℕ) (A : Allocation) (m : ServerMove) (x : GacsDayNode) :
    hasReserveB e A m x = decide (hasReserve e A m x) := by
  rw [Bool.eq_iff_iff, hasReserveB_iff]
  simp

/-- **The reserve test is primitive recursive**, jointly in the scale, the
unavailable set, the server move and the son. -/
theorem primrec_hasReserveB :
    Primrec (fun p : ReserveParam => hasReserveB p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hlist : Primrec (fun p : ReserveParam => getAlloc p.2.1 p.2.2) :=
    primrec₂_getAlloc.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.option_isSome.comp (primrec_list_find? hlist primrec_reserveTest)

/-- The same test, as a computable function. -/
theorem computable_hasReserveB :
    Computable (fun p : ReserveParam => hasReserveB p.1.1 p.1.2 p.2.1 p.2.2) :=
  primrec_hasReserveB.to_comp

/-! ### The finite form of the predicate -/

/-- The cylinder quantified over in `hasReserve` ranges over the finite set
`stringsOfLength e`: this is the finite reserved-interval predicate of
SUV p. 142. -/
theorem hasReserve_iff_exists_stringsOfLength (e : ℕ) (A : Allocation) (m : ServerMove)
    (x : GacsDayNode) :
    hasReserve e A m x ↔
      ∃ R ∈ stringsOfLength e,
        (∃ v ∈ getAlloc m x, R <+: v) ∧
        (∀ y, ¬ (x <+: y ∨ y <+: x) → ∀ c ∈ getAlloc m y, ¬ (R <+: c ∨ c <+: R)) ∧
        (∀ a ∈ A, ¬ (R <+: a ∨ a <+: R)) := by
  constructor
  · rintro ⟨R, hlen, h1, h2, h3⟩
    exact ⟨R, (mem_stringsOfLength e R).mpr hlen, h1, h2, h3⟩
  · rintro ⟨R, hR, h1, h2, h3⟩
    exact ⟨R, (mem_stringsOfLength e R).mp hR, h1, h2, h3⟩

end Kolmogorov
