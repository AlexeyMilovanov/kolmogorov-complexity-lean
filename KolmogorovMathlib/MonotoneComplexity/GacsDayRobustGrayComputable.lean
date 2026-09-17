import KolmogorovMathlib.MonotoneComplexity.GacsDayRobustFamily
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayTestComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayReserveComputable
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools

/-!
# Computability of the robust (hereditary) gray certificate

`familyRobustGrayGoalAtB` is the Boolean test used by the tail controller to
decide whether the current round succeeded.  It is a conjunction of

* the aggregate test `familyGrayGoalAtB` (already known computable),
* a check of `familySubfamilyGrayAtB` over *all* sublists of `List.range n`,
* the pointwise test `familyPointwiseGrayAtB`.

The only new list combinator needed is primitive recursiveness of
`List.sublists`.
-/

namespace Kolmogorov

open Encodable

/-- `List.all` expressed through `List.any`, for the computable transfer. -/
theorem list_all_eq_not_any_not {β : Type*} (p : β → Bool) (l : List β) :
    l.all p = !(l.any fun b => !p b) := by
  exact List.all_eq_not_any_not

/-- Universal quantification over a computable list with a computable
predicate. -/
theorem computable_list_all {α β : Type*} [Primcodable α] [Primcodable β] [Inhabited β]
    {f : α → List β} {p : α → β → Bool} (hf : Computable f) (hp : Computable₂ p) :
    Computable fun a => (f a).all (p a) := by
  have hnot : Computable₂ fun (a : α) (b : β) => !p a b := Primrec.not.to_comp.comp hp
  exact (Primrec.not.to_comp.comp (computable_list_any hf hnot)).of_eq fun a =>
    (list_all_eq_not_any_not (p a) (f a)).symm

/-- The list of sublists is primitive recursive. -/
theorem primrec_list_sublists {α : Type*} [Primcodable α] :
    Primrec fun l : List α => l.sublists := by
  have hg : Primrec₂ fun (_ : List α) (p : α × List α × List (List α)) =>
      p.2.2.flatMap fun x => [x, p.1 :: x] := by
    have hf : Primrec fun w : List α × (α × List α × List (List α)) => w.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hinner : Primrec₂ fun (w : List α × (α × List α × List (List α))) (x : List α) =>
        [x, w.2.1 :: x] := by
      have h1 : Primrec fun z : (List α × (α × List α × List (List α))) × List α =>
          z.1.2.1 :: z.2 :=
        Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
      exact (Primrec.list_cons.comp Primrec.snd
        (Primrec.list_cons.comp h1 (Primrec.const []))).of_eq fun _ => rfl
    exact Primrec.list_flatMap hf hinner
  refine (Primrec.list_rec Primrec.id (Primrec.const [[]]) hg).of_eq fun l => ?_
  induction l with
  | nil => simp
  | cons a t ih =>
    simpa [List.sublists_cons, List.flatMap_def] using
      congrArg (fun s => s.flatMap fun x => [x, a :: x]) ih

/-- Reading one family component's root allocation is primitive recursive. -/
theorem primrec₂_familyRootAlloc :
    Primrec₂ fun (s : FamilyServerMove) (i : ℕ) => getFamilyAlloc s i [] :=
  (primrec₂_getAlloc.comp ((Primrec.list_getD ([] : ServerMove)).comp Primrec.fst Primrec.snd)
    (Primrec.const [])).of_eq fun _ => rfl

/-- Reading one family component's root request is primitive recursive. -/
theorem primrec₂_familyRootReq :
    Primrec₂ fun (c : FamilyClientMove) (i : ℕ) => getFamilyReq c i [] :=
  (primrec_getReq.comp ((Primrec.list_getD ([] : ClientMove)).comp Primrec.fst Primrec.snd)
    (Primrec.const [])).of_eq fun _ => rfl

/-- `familyAllocatedOnList` is computable jointly in its arguments. -/
theorem computable₂_familyAllocatedOnList :
    Computable₂ fun (indices : List ℕ) (s : FamilyServerMove) =>
      familyAllocatedOnList indices s := by
  have hf : Primrec fun z : List ℕ × FamilyServerMove => z.1 := Primrec.fst
  have hg : Primrec₂ fun (z : List ℕ × FamilyServerMove) (i : ℕ) =>
      getFamilyAlloc z.2 i [] :=
    primrec₂_familyRootAlloc.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact ((Primrec.list_flatMap hf hg).of_eq fun _ => rfl).to_comp

/-- `totalRootRequestOnList` is computable jointly in its arguments. -/
theorem computable₂_totalRootRequestOnList :
    Computable₂ fun (indices : List ℕ) (c : FamilyClientMove) =>
      totalRootRequestOnList indices c := by
  have hl : Computable fun z : List ℕ × FamilyClientMove => z.1 := Computable.fst
  have hg : Computable fun _ : List ℕ × FamilyClientMove => (0 : ℚ) := Computable.const 0
  have hh : Computable₂ fun (z : List ℕ × FamilyClientMove) (u : ℕ × ℚ) =>
      getFamilyReq z.2 u.1 [] + u.2 := by
    have h1 : Computable fun w : (List ℕ × FamilyClientMove) × (ℕ × ℚ) =>
        getFamilyReq w.1.2 w.2.1 [] :=
      primrec₂_familyRootReq.to_comp.comp (Computable.snd.comp Computable.fst)
        (Computable.fst.comp Computable.snd)
    have h2 : Computable fun w : (List ℕ × FamilyClientMove) × (ℕ × ℚ) => w.2.2 :=
      Computable.snd.comp Computable.snd
    exact computable₂_ratAdd.comp h1 h2
  exact (Computable.list_foldr hl hg hh).of_eq fun _ => rfl

/-- `familySubfamilyGrayAtB` is computable jointly in all its arguments. -/
theorem computable_familySubfamilyGrayAtB_joint :
    Computable fun x : (ℚ × ℕ × ℕ × ℕ) ×
        Allocation × FamilyClientMove × FamilyServerMove × List ℕ =>
      familySubfamilyGrayAtB x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2
        x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  have hkappa : Computable fun x : (ℚ × ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove × List ℕ => x.1.1 :=
    Computable.fst.comp Computable.fst
  have heps : Computable fun x : (ℚ × ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove × List ℕ => x.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hdelta : Computable fun x : (ℚ × ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove × List ℕ => x.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hn : Computable fun x : (ℚ × ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove × List ℕ => x.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hA : Computable fun x : (ℚ × ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove × List ℕ => x.2.1 :=
    Computable.fst.comp Computable.snd
  have hc : Computable fun x : (ℚ × ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove × List ℕ => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hs : Computable fun x : (ℚ × ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove × List ℕ => x.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hidx : Computable fun x : (ℚ × ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove × List ℕ => x.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have halloc := computable₂_familyAllocatedOnList.comp hidx hs
  have hcount := primrec_newGrayCount.to_comp.comp ((heps.pair hdelta).pair (halloc.pair hA))
  have hg := computable_grayMassOfCount.comp hdelta hcount
  have hsub := computable₂_totalRootRequestOnList.comp hidx hc
  have htot := computable₂_totalRootRequest.comp hn hc
  have htwo := computable₂_ratMul.comp (Computable.const (2 : ℚ)) hsub
  have hdiff := computable₂_ratSub.comp htwo htot
  have hlhs := computable₂_ratMul.comp hkappa hdiff
  exact (computable_ratLe.comp hlhs hg).of_eq fun _ => rfl

/-- `familyPointwiseGrayAtB` is computable jointly in all its arguments. -/
theorem computable_familyPointwiseGrayAtB_joint :
    Computable fun x : (ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
        Allocation × FamilyClientMove × FamilyServerMove =>
      familyPointwiseGrayAtB x.1.1 x.1.2 x.2.1.1 x.2.1.2.1 x.2.1.2.2
        x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  have hn : Computable fun x : (ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove => x.2.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
  have hlist := Primrec.list_range.to_comp.comp hn
  have hbody : Computable₂ fun (x : (ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove) (i : ℕ) =>
      decide (x.1.2 ≤ x.1.1 * getFamilyReq x.2.2.2.1 i []) &&
        decide (getFamilyReq x.2.2.2.1 i [] ≤ (4 / 3 : ℚ) * x.1.2) := by
    have hkappa : Computable fun w : ((ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
        Allocation × FamilyClientMove × FamilyServerMove) × ℕ => w.1.1.1 :=
      Computable.fst.comp (Computable.fst.comp Computable.fst)
    have hbeta : Computable fun w : ((ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
        Allocation × FamilyClientMove × FamilyServerMove) × ℕ => w.1.1.2 :=
      Computable.snd.comp (Computable.fst.comp Computable.fst)
    have hreq : Computable fun w : ((ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
        Allocation × FamilyClientMove × FamilyServerMove) × ℕ =>
        getFamilyReq w.1.2.2.2.1 w.2 [] :=
      primrec₂_familyRootReq.to_comp.comp
        (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
          (Computable.snd.comp Computable.fst)))) Computable.snd
    have h1 := computable_ratLe.comp hbeta (computable₂_ratMul.comp hkappa hreq)
    have h2 := computable_ratLe.comp hreq
      (computable₂_ratMul.comp (Computable.const ((4 : ℚ) / 3)) hbeta)
    exact ((Primrec.dom_bool₂ (fun a b => a && b)).to_comp.comp h1 h2).of_eq fun _ => rfl
  exact (computable_list_all hlist hbody).of_eq fun _ => rfl

/-- **The robust gray certificate is computable** jointly in all its
arguments. -/
theorem computable_familyRobustGrayGoalAtB_joint :
    Computable fun x : (ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
        Allocation × FamilyClientMove × FamilyServerMove =>
      familyRobustGrayGoalAtB x.1.1 x.1.2 x.2.1.1 x.2.1.2.1 x.2.1.2.2
        x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  have hkappa : Computable fun x : (ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove => x.1.1 :=
    Computable.fst.comp Computable.fst
  have hbeta : Computable fun x : (ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove => x.1.2 :=
    Computable.snd.comp Computable.fst
  have heps : Computable fun x : (ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove => x.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hdelta : Computable fun x : (ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove => x.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
  have hn : Computable fun x : (ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove => x.2.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
  have hA : Computable fun x : (ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hc : Computable fun x : (ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove => x.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hs : Computable fun x : (ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove => x.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hrange := Primrec.list_range.to_comp.comp hn
  have halloc := computable₂_familyAllocatedOnList.comp hrange hs
  have hagg := computable_familyGrayGoalAtB_joint.comp
    (((hkappa.pair hbeta).pair (heps.pair hdelta)).pair
      ((hn.pair hA).pair (hc.pair halloc)))
  have hsubs := primrec_list_sublists.to_comp.comp hrange
  have hall : Computable fun x : (ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
      Allocation × FamilyClientMove × FamilyServerMove =>
      (List.range x.2.1.2.2).sublists.all
        (familySubfamilyGrayAtB x.1.1 x.2.1.1 x.2.1.2.1 x.2.1.2.2 x.2.2.1 x.2.2.2.1
          x.2.2.2.2) := by
    have hbody : Computable₂ fun (x : (ℚ × ℚ) × (ℕ × ℕ × ℕ) ×
        Allocation × FamilyClientMove × FamilyServerMove) (t : List ℕ) =>
        familySubfamilyGrayAtB x.1.1 x.2.1.1 x.2.1.2.1 x.2.1.2.2 x.2.2.1 x.2.2.2.1
          x.2.2.2.2 t := by
      refine (computable_familySubfamilyGrayAtB_joint.comp
        (((hkappa.comp Computable.fst).pair
          ((heps.comp Computable.fst).pair
            ((hdelta.comp Computable.fst).pair (hn.comp Computable.fst)))).pair
          ((hA.comp Computable.fst).pair
            ((hc.comp Computable.fst).pair
              ((hs.comp Computable.fst).pair Computable.snd))))).of_eq fun _ => rfl
    exact (computable_list_all hsubs hbody).of_eq fun _ => rfl
  have hpt := computable_familyPointwiseGrayAtB_joint
  have hand : Computable₂ fun a b : Bool => a && b :=
    (Primrec.dom_bool₂ (fun a b => a && b)).to_comp
  exact (hand.comp hagg (hand.comp hall hpt)).of_eq fun _ => rfl

end Kolmogorov
