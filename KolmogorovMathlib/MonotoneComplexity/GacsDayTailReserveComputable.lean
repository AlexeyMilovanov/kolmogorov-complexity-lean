import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailConstruction
import KolmogorovMathlib.MonotoneComplexity.GacsDayReserveComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwoComputable

/-!
# Computability of the tail reserve search

The tail controller retires a slot as soon as the finite search
`getTailFamilyReserve` finds a source-faithful reserve for it.  That search is
a `List.find?` over the finite list `allStrings e` of a Boolean test built from
`tailFamilyReserveAtB`, so it is computable; the proofs below simply assemble
the standard combinators.
-/

namespace Kolmogorov

open Encodable

/-- Reading one component of a family server move is primitive recursive. -/
theorem primrec₂_familyServerMoveAt : Primrec₂ familyServerMoveAt :=
  (Primrec.list_getD ([] : ServerMove)).of_eq fun _ _ => rfl

/-- Reading one root allocation of a family server move is primitive
recursive. -/
theorem primrec_getFamilyAlloc :
    Primrec fun z : FamilyServerMove × ℕ × GacsDayNode =>
      getFamilyAlloc z.1 z.2.1 z.2.2 :=
  primrec₂_getAlloc.comp
    (primrec₂_familyServerMoveAt.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

/-- Membership in the `b`-ary tree is primitive recursive. -/
theorem primrec₂_nodeInTreeB :
    Primrec₂ fun (b : ℕ) (x : GacsDayNode) => nodeInTreeB b x := by
  have hp : Primrec₂ fun (z : ℕ × GacsDayNode) (d : ℕ) => decide (d < z.1) := by
    obtain ⟨_, h⟩ :=
      Primrec.nat_lt.comp (Primrec.snd : Primrec fun p : (ℕ × GacsDayNode) × ℕ => p.2)
        (Primrec.fst.comp Primrec.fst)
    exact h.of_eq fun _ => by simp
  exact (list_all_primrec Primrec.snd hp).of_eq fun _ => rfl

/-- Prefix comparability of vertices is primitive recursive. -/
theorem primrec₂_nodeComparableB : Primrec₂ nodeComparableB :=
  ((Primrec.dom_bool₂ (fun a b => a || b)).comp
    (primrec₂_isPrefixOf_gen.comp Primrec.fst Primrec.snd)
    (primrec₂_isPrefixOf_gen.comp Primrec.snd Primrec.fst)).of_eq fun _ => rfl

/-- The same-tree exclusion test is computable jointly in its arguments. -/
theorem primrec_tailAvoidsOthersB :
    Primrec fun x : ℕ × ServerMove × GacsDayNode × BitString =>
      tailAvoidsOthersB x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  have hm : Primrec fun x : ℕ × ServerMove × GacsDayNode × BitString => x.2.1 :=
    Primrec.fst.comp Primrec.snd
  -- the guard, as a function of the outer data and the entry
  have hguard : Primrec₂ fun (x : ℕ × ServerMove × GacsDayNode × BitString)
      (pr : GacsDayNode × Allocation) =>
      nodeInTreeB x.1 pr.1 && !nodeComparableB x.2.2.1 pr.1 :=
    (Primrec.dom_bool₂ (fun a b => a && b)).comp
      (primrec₂_nodeInTreeB.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.not.comp (primrec₂_nodeComparableB.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.fst.comp Primrec.snd)))
  have hthen : Primrec₂ fun (x : ℕ × ServerMove × GacsDayNode × BitString)
      (pr : GacsDayNode × Allocation) =>
      !comparableB (getAlloc x.2.1 pr.1) x.2.2.2 :=
    Primrec.not.comp (primrec₂_comparableB.comp
      (primrec₂_getAlloc.comp (hm.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hbody : Primrec₂ fun (x : ℕ × ServerMove × GacsDayNode × BitString)
      (pr : GacsDayNode × Allocation) =>
      if nodeInTreeB x.1 pr.1 && !nodeComparableB x.2.2.1 pr.1 then
        !comparableB (getAlloc x.2.1 pr.1) x.2.2.2 else true := by
    refine (Primrec.cond hguard hthen (Primrec.const true)).of_eq fun z => ?_
    cases hg : nodeInTreeB z.1.1 z.2.1 && !nodeComparableB z.1.2.2.1 z.2.1 <;> simp [hg]
  exact (list_all_primrec hm hbody).of_eq fun _ => rfl

/-- The one-tree reserve test is computable jointly in its arguments. -/
theorem primrec_tailReserveAtB :
    Primrec fun x : (ℕ × ℕ) × Allocation × ServerMove × GacsDayNode × BitString =>
      tailReserveAtB x.1.1 x.1.2 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  have he : Primrec fun x : (ℕ × ℕ) × Allocation × ServerMove × GacsDayNode × BitString =>
      x.1.1 := Primrec.fst.comp Primrec.fst
  have hb : Primrec fun x : (ℕ × ℕ) × Allocation × ServerMove × GacsDayNode × BitString =>
      x.1.2 := Primrec.snd.comp Primrec.fst
  have hA : Primrec fun x : (ℕ × ℕ) × Allocation × ServerMove × GacsDayNode × BitString =>
      x.2.1 := Primrec.fst.comp Primrec.snd
  have hm : Primrec fun x : (ℕ × ℕ) × Allocation × ServerMove × GacsDayNode × BitString =>
      x.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hx : Primrec fun x : (ℕ × ℕ) × Allocation × ServerMove × GacsDayNode × BitString =>
      x.2.2.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hR : Primrec fun x : (ℕ × ℕ) × Allocation × ServerMove × GacsDayNode × BitString =>
      x.2.2.2.2 := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have h1 : Primrec fun x : (ℕ × ℕ) × Allocation × ServerMove × GacsDayNode × BitString =>
      decide (x.2.2.2.2.length = x.1.1) := by
    obtain ⟨_, h⟩ := Primrec.eq.comp (Primrec.list_length.comp hR) he
    exact h.of_eq fun _ => by simp
  have h2 : Primrec fun x : (ℕ × ℕ) × Allocation × ServerMove × GacsDayNode × BitString =>
      comparableB (getAlloc x.2.2.1 x.2.2.2.1) x.2.2.2.2 :=
    primrec₂_comparableB.comp (primrec₂_getAlloc.comp hm hx) hR
  have h3 : Primrec fun x : (ℕ × ℕ) × Allocation × ServerMove × GacsDayNode × BitString =>
      tailAvoidsOthersB x.1.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2 :=
    primrec_tailAvoidsOthersB.comp (hb.pair (hm.pair (hx.pair hR)))
  have h4 : Primrec fun x : (ℕ × ℕ) × Allocation × ServerMove × GacsDayNode × BitString =>
      !comparableB x.2.1 x.2.2.2.2 :=
    Primrec.not.comp (primrec₂_comparableB.comp hA hR)
  have hand : Primrec₂ fun a b : Bool => a && b := Primrec.dom_bool₂ (fun a b => a && b)
  exact (hand.comp (hand.comp (hand.comp h1 h2) h3) h4).of_eq fun _ => rfl

/-- The family reserve test is computable jointly in its arguments. -/
theorem primrec_tailFamilyReserveAtB :
    Primrec fun x : (ℕ × ℕ) × Allocation × (ℕ × ℕ) ×
        FamilyServerMove × GacsDayNode × BitString =>
      tailFamilyReserveAtB x.1.1 x.1.2 x.2.1 x.2.2.1.1 x.2.2.1.2
        x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 := by
  set T := (ℕ × ℕ) × Allocation × (ℕ × ℕ) × FamilyServerMove × GacsDayNode × BitString with hT
  have he : Primrec fun x : T => x.1.1 := Primrec.fst.comp Primrec.fst
  have hb : Primrec fun x : T => x.1.2 := Primrec.snd.comp Primrec.fst
  have hA : Primrec fun x : T => x.2.1 := Primrec.fst.comp Primrec.snd
  have hn : Primrec fun x : T => x.2.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hi : Primrec fun x : T => x.2.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hsm : Primrec fun x : T => x.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hx : Primrec fun x : T => x.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hR : Primrec fun x : T => x.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have h1 : Primrec fun x : T =>
      tailReserveAtB x.1.1 x.1.2 x.2.1 (familyServerMoveAt x.2.2.2.1 x.2.2.1.2)
        x.2.2.2.2.1 x.2.2.2.2.2 :=
    primrec_tailReserveAtB.comp
      ((he.pair hb).pair (hA.pair ((primrec₂_familyServerMoveAt.comp hsm hi).pair
        (hx.pair hR))))
  have hbody : Primrec₂ fun (x : T) (j : ℕ) =>
      if j = x.2.2.1.2 then true else !comparableB (getFamilyAlloc x.2.2.2.1 j []) x.2.2.2.2.2 := by
    have hcond : PrimrecPred fun z : T × ℕ => z.2 = z.1.2.2.1.2 :=
      Primrec.eq.comp Primrec.snd (hi.comp Primrec.fst)
    have helse : Primrec fun z : T × ℕ =>
        !comparableB (getFamilyAlloc z.1.2.2.2.1 z.2 []) z.1.2.2.2.2.2 :=
      Primrec.not.comp (primrec₂_comparableB.comp
        (primrec_getFamilyAlloc.comp
          ((hsm.comp Primrec.fst).pair (Primrec.snd.pair (Primrec.const []))))
        (hR.comp Primrec.fst))
    exact Primrec.ite hcond (Primrec.const true) helse
  have h2 : Primrec fun x : T =>
      (List.range x.2.2.1.1).all fun j =>
        if j = x.2.2.1.2 then true
        else !comparableB (getFamilyAlloc x.2.2.2.1 j []) x.2.2.2.2.2 :=
    list_all_primrec (Primrec.list_range.comp hn) hbody
  exact ((Primrec.dom_bool₂ (fun a b => a && b)).comp h1 h2).of_eq fun _ => rfl

/-- **The bounded reserve search is primitive recursive** jointly in all its
arguments. -/
theorem primrec_getTailFamilyReserve_joint :
    Primrec fun x : (ℕ × ℕ) × Allocation × (ℕ × ℕ) ×
        FamilyServerMove × GacsDayNode =>
      getTailFamilyReserve x.1.1 x.1.2 x.2.1 x.2.2.1.1 x.2.2.1.2
        x.2.2.2.1 x.2.2.2.2 := by
  have hlist : Primrec fun x : (ℕ × ℕ) × Allocation × (ℕ × ℕ) ×
      FamilyServerMove × GacsDayNode => allStrings x.1.1 :=
    CodedFiniteDistribution.allStrings_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hp : Primrec₂ fun (x : (ℕ × ℕ) × Allocation × (ℕ × ℕ) × FamilyServerMove ×
        GacsDayNode) (R : BitString) =>
      tailFamilyReserveAtB x.1.1 x.1.2 x.2.1 x.2.2.1.1 x.2.2.1.2
        x.2.2.2.1 x.2.2.2.2 R := by
    have hz : Primrec fun z : ((ℕ × ℕ) × Allocation × (ℕ × ℕ) × FamilyServerMove ×
        GacsDayNode) × BitString =>
        ((z.1.1, z.1.2.1, z.1.2.2.1, z.1.2.2.2.1, z.1.2.2.2.2, z.2) :
          (ℕ × ℕ) × Allocation × (ℕ × ℕ) × FamilyServerMove × GacsDayNode × BitString) :=
      (Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
          ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
            ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp Primrec.fst)))).pair
              ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.snd.comp Primrec.fst)))).pair Primrec.snd))))
    exact (primrec_tailFamilyReserveAtB.comp hz).of_eq fun _ => rfl
  exact (primrec_list_find? hlist hp).of_eq fun _ => rfl

/-- **The reserve search is computable** jointly in all its arguments. -/
theorem computable_getTailFamilyReserve_joint :
    Computable fun x : (ℕ × ℕ) × Allocation × (ℕ × ℕ) ×
        FamilyServerMove × GacsDayNode =>
      getTailFamilyReserve x.1.1 x.1.2 x.2.1 x.2.2.1.1 x.2.2.1.2
        x.2.2.2.1 x.2.2.2.2 :=
  primrec_getTailFamilyReserve_joint.to_comp

end Kolmogorov
