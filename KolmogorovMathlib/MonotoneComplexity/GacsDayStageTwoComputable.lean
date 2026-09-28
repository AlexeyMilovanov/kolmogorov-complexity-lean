import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwo.ArithmeticRequests
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwo

/-!
# Computability of the stage-two family strategy

`GacsDayStageTwo` proves that the reactive probe-and-raise client wins the
family game with amplification `2`.  To feed that win into the packaged lane
`GrayFamilyInductionStatement 2` one also has to know that the client is
computable, uniformly in the two dyadic depths, the unavailable set, the family
size and the finite history.

This file supplies the missing primitive-recursion bookkeeping.  It first proves
a few generic list primitives (`List.find?`, `List.lookup`, `List.isPrefixOf`)
and then walks up the stage-two definitions.
-/

namespace Kolmogorov

open Primrec

/-! ### Generic list primitives -/

/-- `List.find?` reads off the element at the index found by `List.findIdx`. -/
theorem find?_eq_getElem?_findIdx {α : Type*} (p : α → Bool) (l : List α) :
    l.find? p = l[l.findIdx p]? := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.findIdx_cons, List.find?_cons]
    by_cases h : p a <;> simp [h, ih]

/-- `List.find?` is primitive recursive in the list and in the predicate. -/
theorem primrec_list_find? {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).find? (p a) :=
  (Primrec.list_getElem?.comp hf (Primrec.list_findIdx hf hp)).of_eq fun a =>
    (find?_eq_getElem?_findIdx (p a) (f a)).symm

/-- `List.lookup` returns the value of the first matching key. -/
theorem lookup_eq_find? {α β : Type*} [BEq α] (a : α) (l : List (α × β)) :
    l.lookup a = (l.find? (fun p => a == p.1)).map Prod.snd := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.lookup, List.find?_cons]
    by_cases h : a == hd.1 <;> simp [h, ih]

/-- `List.lookup` is primitive recursive. -/
theorem primrec_list_lookup {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    [BEq β] [LawfulBEq β] {f : σ → List (β × α)} {g : σ → β}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun s => (f s).lookup (g s) := by
  classical
  have hrel : PrimrecPred (fun a : σ × (β × α) => g a.1 = a.2.1) :=
    PrimrecRel.comp Primrec.eq (hg.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have hp : Primrec₂ (fun (s : σ) (p : β × α) => g s == p.1) :=
    (Primrec.ite hrel (Primrec.const true) (Primrec.const false)).of_eq
      fun a => by by_cases h : g a.1 = a.2.1 <;> simp [h]
  exact (Primrec.option_map (primrec_list_find? hf hp)
    (Primrec.snd.comp Primrec.snd).to₂).of_eq fun s => (lookup_eq_find? _ _).symm

/-- Being a prefix is testable against the corresponding initial segment. -/
theorem isPrefixOf_eq_beq {α : Type*} [BEq α] [LawfulBEq α] (l1 l2 : List α) :
    l1.isPrefixOf l2 = (l2.take l1.length == l1) := by
  rw [Bool.eq_iff_iff, List.isPrefixOf_iff_prefix, beq_iff_eq, eq_comm]
  exact List.prefix_iff_eq_take

/-- `List.isPrefixOf` on bit strings is primitive recursive. -/
theorem primrec₂_isPrefixOf : Primrec₂ (fun l1 l2 : BitString => l1.isPrefixOf l2) := by
  have htake : Primrec (fun p : BitString × BitString => p.2.take p.1.length) :=
    Primrec.list_take.comp Primrec.snd (Primrec.list_length.comp Primrec.fst)
  have hrel : PrimrecPred (fun p : BitString × BitString => p.2.take p.1.length = p.1) :=
    PrimrecRel.comp Primrec.eq htake Primrec.fst
  exact (Primrec.ite hrel (Primrec.const true) (Primrec.const false)).of_eq fun p => by
    dsimp only
    rw [isPrefixOf_eq_beq]
    by_cases h : p.2.take p.1.length = p.1 <;> simp [h]

/-- `List.ofFn` over `Fin n` with a varying `n` is a `List.range` map. -/
theorem ofFn_eq_map_range {σ : Type*} (n : ℕ) (g : ℕ → σ) :
    List.ofFn (fun i : Fin n => g i.val) = (List.range n).map g := by
  apply List.ext_getElem <;> simp

/-! ### The stage-two game primitives -/

/-- Reading a node's allocation out of a server move is primitive recursive. -/
theorem primrec₂_getAlloc : Primrec₂ getAlloc := by
  have hl : Primrec (fun p : ServerMove × GacsDayNode => p.1.lookup p.2) :=
    primrec_list_lookup Primrec.fst Primrec.snd
  exact (Primrec.option_getD.comp hl (Primrec.const [])).of_eq fun p => by
    unfold getAlloc
    cases p.1.lookup p.2 <;> simp

/-- Finding the first short allocated cylinder is primitive recursive. -/
theorem primrec₂_shortCyl : Primrec₂ shortCyl := by
  have hp : Primrec₂ (fun (p : ℕ × Allocation) (c : BitString) => decide (c.length ≤ p.1)) := by
    have hrel : PrimrecPred (fun q : (ℕ × Allocation) × BitString => q.2.length ≤ q.1.1) :=
      PrimrecRel.comp Primrec.nat_le (Primrec.list_length.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst)
    exact (Primrec.ite hrel (Primrec.const true) (Primrec.const false)).of_eq fun q => by
      by_cases h : q.2.length ≤ q.1.1 <;> simp [h]
  exact primrec_list_find? Primrec.snd hp

/-- The root probe answer is primitive recursive. -/
theorem primrec₂_probeRoot : Primrec₂ probeRoot :=
  primrec₂_shortCyl.comp Primrec.fst (primrec₂_getAlloc.comp Primrec.snd (Primrec.const []))

/-- The child probe answer is primitive recursive. -/
theorem primrec_probeChild :
    Primrec (fun p : (ℕ × ServerMove) × ℕ => probeChild p.1.1 p.1.2 p.2) := by
  have hnode : Primrec (fun p : (ℕ × ServerMove) × ℕ => ([p.2] : GacsDayNode)) :=
    Primrec.list_cons.comp Primrec.snd (Primrec.const [])
  exact primrec₂_shortCyl.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
    (primrec₂_getAlloc.comp (Primrec.snd.comp Primrec.fst) hnode)

/-- The probe-completeness test is primitive recursive. -/
theorem primrec₂_probeReady : Primrec₂ probeReady := by
  have hroot : Primrec (fun p : ℕ × ServerMove => (probeRoot p.1 p.2).isSome) :=
    Primrec.option_isSome.comp primrec₂_probeRoot
  have hc : ∀ i : ℕ, Primrec (fun p : ℕ × ServerMove => (probeChild p.1 p.2 i).isSome) := by
    intro i
    exact Primrec.option_isSome.comp (primrec_probeChild.comp (Primrec.id.pair (Primrec.const i)))
  exact Primrec.and.comp (Primrec.and.comp hroot (hc 0)) (hc 1)

/-- The raised child, packaged so that `Option` matching becomes `bind`. -/
theorem raisedChild_eq_bind (a : ℕ) (sm : ServerMove) :
    raisedChild a sm =
      ((probeRoot a sm).bind (fun R =>
        (probeChild a sm 1).map (fun c1 =>
          if R.isPrefixOf c1 || c1.isPrefixOf R then 0 else 1))).getD 0 := by
  unfold raisedChild
  cases probeRoot a sm <;> cases probeChild a sm 1 <;> simp

/-- The choice of raised child is primitive recursive. -/
theorem primrec₂_raisedChild : Primrec₂ raisedChild := by
  have hchild : Primrec (fun p : ℕ × ServerMove => probeChild p.1 p.2 1) :=
    primrec_probeChild.comp (Primrec.id.pair (Primrec.const 1))
  have hcmp : Primrec (fun q : ((ℕ × ServerMove) × BitString) × BitString =>
      if q.1.2.isPrefixOf q.2 || q.2.isPrefixOf q.1.2 then (0 : ℕ) else 1) := by
    have h1 : Primrec (fun q : ((ℕ × ServerMove) × BitString) × BitString =>
        q.1.2.isPrefixOf q.2) := primrec₂_isPrefixOf.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
    have h2 : Primrec (fun q : ((ℕ × ServerMove) × BitString) × BitString =>
        q.2.isPrefixOf q.1.2) := primrec₂_isPrefixOf.comp Primrec.snd (Primrec.snd.comp Primrec.fst)
    exact (Primrec.cond (Primrec.or.comp h1 h2) (Primrec.const 0)
      (Primrec.const 1)).of_eq fun _ => Bool.cond_eq_ite _ _ _
  have hmap : Primrec (fun q : (ℕ × ServerMove) × BitString =>
      (probeChild q.1.1 q.1.2 1).map (fun c1 =>
        if q.2.isPrefixOf c1 || c1.isPrefixOf q.2 then (0 : ℕ) else 1)) :=
    Primrec.option_map (hchild.comp Primrec.fst) hcmp.to₂
  have hbind : Primrec (fun p : ℕ × ServerMove =>
      (probeRoot p.1 p.2).bind (fun R =>
        (probeChild p.1 p.2 1).map (fun c1 =>
          if R.isPrefixOf c1 || c1.isPrefixOf R then (0 : ℕ) else 1))) :=
    Primrec.option_bind primrec₂_probeRoot hmap.to₂
  exact (Primrec.option_getD.comp hbind (Primrec.const 0)).of_eq fun p =>
    (raisedChild_eq_bind p.1 p.2).symm

/-- `firstProbe` is a `List.find?`. -/
theorem firstProbe_eq_find? (a : ℕ) (l : List ServerMove) :
    firstProbe a l = l.find? (probeReady a) := by
  induction l with
  | nil => rfl
  | cons m ms ih =>
    rw [firstProbe, List.find?_cons]
    by_cases h : probeReady a m <;> simp [h, ih]

/-- Locating the first server move that answers the probe is primitive recursive. -/
theorem primrec₂_firstProbe : Primrec₂ firstProbe := by
  have hp : Primrec₂ (fun (p : ℕ × List ServerMove) (m : ServerMove) => probeReady p.1 m) :=
    primrec₂_probeReady.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact (primrec_list_find? Primrec.snd hp).of_eq fun p => (firstProbe_eq_find? p.1 p.2).symm

/-- The raised-child choice read off a tree's own history is primitive recursive. -/
theorem primrec₂_stageTwoChoice : Primrec₂ stageTwoChoice :=
  Primrec.option_map primrec₂_firstProbe
    (primrec₂_raisedChild.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

/-! ### The stage-two client move -/

/-- The corrected half request, with the sign pulled out of the sum. -/
theorem stageTwoReq_eq_ite (a D : ℕ) (j : Option ℕ) (i : ℕ) :
    stageTwoReq a D j i =
      if j = some i then (1 / 2 : ℚ) ^ (a + 1) + (1 / 2 : ℚ) ^ D
      else (1 / 2 : ℚ) ^ (a + 1) - (1 / 2 : ℚ) ^ D := by
  unfold stageTwoReq
  split <;> ring

/-- Each child request of the stage-two client is computable. -/
theorem computable_stageTwoReq {X : Type} [Primcodable X] {fa fD : X → ℕ} {fj : X → Option ℕ}
    (i : ℕ) (ha : Computable fa) (hD : Computable fD) (hj : Computable fj) :
    Computable fun x => stageTwoReq (fa x) (fD x) (fj x) i := by
  have hq1 : Computable (fun x => (1 / 2 : ℚ) ^ (fa x + 1)) :=
    computable_half_pow.comp (Computable.succ.comp ha)
  have hq2 : Computable (fun x => (1 / 2 : ℚ) ^ fD x) := computable_half_pow.comp hD
  have hadd := Computable₂.comp computable₂_ratAdd hq1 hq2
  have hsub := Computable₂.comp computable₂_ratSub hq1 hq2
  have hrel : PrimrecPred (fun p : Option ℕ × Option ℕ => p.1 = p.2) :=
    PrimrecRel.comp Primrec.eq Primrec.fst Primrec.snd
  have heq : Primrec (fun p : Option ℕ × Option ℕ => decide (p.1 = p.2)) :=
    (Primrec.ite hrel (Primrec.const true) (Primrec.const false)).of_eq fun p => by
      by_cases h : p.1 = p.2 <;> simp [h]
  have hb : Computable (fun x => decide (fj x = some i)) :=
    heq.to_comp.comp (hj.pair (Computable.const (some i)))
  exact (Computable.cond hb hadd hsub).of_eq fun x => by
    rw [stageTwoReq_eq_ite]
    by_cases h : fj x = some i <;> simp [h]

/-- The whole stage-two client move is computable. -/
theorem computable_stageTwoMove {X : Type} [Primcodable X] {fa fD : X → ℕ} {fj : X → Option ℕ}
    (ha : Computable fa) (hD : Computable fD) (hj : Computable fj) :
    Computable fun x => stageTwoMove (fa x) (fD x) (fj x) := by
  have hroot : Computable (fun x => (([] : GacsDayNode), (1 / 2 : ℚ) ^ fa x)) :=
    (Computable.const ([] : GacsDayNode)).pair (computable_half_pow.comp ha)
  have h0 : Computable (fun x => (([0] : GacsDayNode), stageTwoReq (fa x) (fD x) (fj x) 0)) :=
    (Computable.const ([0] : GacsDayNode)).pair (computable_stageTwoReq 0 ha hD hj)
  have h1 : Computable (fun x => (([1] : GacsDayNode), stageTwoReq (fa x) (fD x) (fj x) 1)) :=
    (Computable.const ([1] : GacsDayNode)).pair (computable_stageTwoReq 1 ha hD hj)
  have l1 := Computable₂.comp Primrec.list_cons.to_comp h1 (Computable.const [])
  have l0 := Computable₂.comp Primrec.list_cons.to_comp h0 l1
  exact Computable₂.comp Primrec.list_cons.to_comp hroot l0

/-! ### The stage-two family strategy scheme -/

/-- The stage-two scheme is computable, uniformly in the two dyadic depths, the
unavailable set, the family size and the finite history. -/
theorem computable_stageTwoFamilyScheme :
    FamilyStrategySchemeComputable (fun a e => stageTwoFamilyStrategy a (e + 3)) := by
  have ha : Computable (fun x : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) => x.1.1) :=
    Computable.fst.comp Computable.fst
  have hD : Computable
      (fun x : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) => x.1.2 + 3) :=
    Computable.succ.comp (Computable.succ.comp
      (Computable.succ.comp (Computable.snd.comp Computable.fst)))
  have hn : Computable (fun x : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) => x.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hhist : Computable
      (fun x : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) => x.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hgetD : Computable₂
      (fun (q : ((ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory))) × ℕ)
        (m : FamilyServerMove) => familyServerMoveAt m q.2) :=
    (Primrec.list_getD ([] : ServerMove)).to_comp.comp Computable.snd
      (Computable.snd.comp Computable.fst)
  have hmaps : Computable
      (fun q : ((ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory))) × ℕ =>
        q.1.2.2.2.2.map (fun m => familyServerMoveAt m q.2)) :=
    Computable.list_map (hhist.comp Computable.fst) hgetD
  have hchoice : Computable
      (fun q : ((ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory))) × ℕ =>
        stageTwoChoice q.1.1.1 (q.1.2.2.2.2.map (fun m => familyServerMoveAt m q.2))) :=
    Computable₂.comp primrec₂_stageTwoChoice.to_comp (ha.comp Computable.fst) hmaps
  have hmove : Computable₂
      (fun (x : (ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory))) (i : ℕ) =>
        stageTwoTreeMove x.1.1 (x.1.2 + 3)
          (x.2.2.2.2.map (fun m => familyServerMoveAt m i))) :=
    computable_stageTwoMove (ha.comp Computable.fst) (hD.comp Computable.fst) hchoice
  exact (Computable.list_map (Primrec.list_range.to_comp.comp hn) hmove).of_eq fun x => by
    unfold stageTwoFamilyStrategy
    exact (ofFn_eq_map_range _ _).symm

/-- **The second amplification stage in the packaged form of the game lane.**
Amplification `2`, height `4`, branching `2`, depth loss `e + 3`, with a
computable strategy scheme. -/
theorem grayFamilyInductionStatement_two : GrayFamilyInductionStatement 2 := by
  refine ⟨fun _a e => e + 3, fun _a _e => 2, fun a e => stageTwoFamilyStrategy a (e + 3),
    ?_, ?_, fun _a _e => le_rfl, computable_stageTwoFamilyScheme, grayFamilyStageSpec_two⟩
  · exact Computable.succ.comp (Computable.succ.comp (Computable.succ.comp Computable.snd))
  · exact Computable.const 2

end Kolmogorov
