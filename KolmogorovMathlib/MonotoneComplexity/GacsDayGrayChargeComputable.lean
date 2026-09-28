import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedFamily
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayCharge
import KolmogorovMathlib.MonotoneComplexity.GacsDayRobustGrayComputable

/-!
# Computability of designated-gray certificates

The controller searches a finite powerset for the first valid charge.  This
module proves that the universe, the certificate checks, and the search are
computable in the existing `Primcodable` model.
-/

namespace Kolmogorov

open Encodable

private theorem primrec_chargeCells :
    Primrec (fun G : FamilyGrayCharge => G.map Prod.snd) := by
  exact Primrec.list_map Primrec.id
    ((Primrec.snd.comp Primrec.snd).to₂)

/-- The uniqueness test on charges is primitive recursive. -/
theorem primrec_grayChargeCellsUniqueB :
    Primrec grayChargeCellsUniqueB := by
  have hd := dedup_primrec.comp primrec_chargeCells
  have heq : PrimrecPred fun G : FamilyGrayCharge =>
      (G.map Prod.snd).dedup = G.map Prod.snd :=
    Primrec.eq.comp hd primrec_chargeCells
  exact (primrecPred_iff_primrec_decide.mp heq).of_eq fun _ => rfl

/-- The charge universe is primitive recursive in the client count and the depth. -/
theorem primrec_familyGrayChargeUniverse :
    Primrec fun q : Nat × Nat => familyGrayChargeUniverse q.1 q.2 := by
  have hrange : Primrec fun q : Nat × Nat => List.range q.1 :=
    Primrec.list_range.comp Primrec.fst
  have hbody : Primrec₂ fun (q : Nat × Nat) (i : Nat) =>
      (allStrings q.2).map fun p => (i, p) := by
    change Primrec fun w : (Nat × Nat) × Nat =>
      (allStrings w.1.2).map fun p => (w.2, p)
    have hstrings : Primrec fun w : (Nat × Nat) × Nat => allStrings w.1.2 :=
      CodedFiniteDistribution.allStrings_primrec.comp (Primrec.snd.comp Primrec.fst)
    have hpair : Primrec₂ fun (w : (Nat × Nat) × Nat) (p : BitString) =>
        (w.2, p) := by
      exact (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
    exact Primrec.list_map hstrings hpair
  exact (Primrec.list_flatMap hrange hbody).of_eq fun _ => rfl

/-- Selecting the charge at a root is primitive recursive. -/
theorem primrec₂_grayChargeAtRoot :
    Primrec₂ grayChargeAtRoot := by
  change Primrec fun w : Nat × FamilyGrayCharge => grayChargeAtRoot w.1 w.2
  have hpred : Primrec₂ fun (w : Nat × FamilyGrayCharge)
      (z : Nat × BitString) => z.1 == w.1 := by
    exact (Primrec.beq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)).to₂
  exact (list_filter_primrec Primrec.snd hpred).of_eq fun _ => rfl

/-- Selecting the cells of a charge at a root is primitive recursive. -/
theorem primrec₂_grayChargeCellsAtRoot :
    Primrec₂ grayChargeCellsAtRoot := by
  change Primrec fun w : Nat × FamilyGrayCharge => grayChargeCellsAtRoot w.1 w.2
  have hroot : Primrec fun w : Nat × FamilyGrayCharge =>
      grayChargeAtRoot w.1 w.2 := primrec₂_grayChargeAtRoot
  exact (Primrec.list_map hroot
    ((Primrec.snd.comp Primrec.snd).to₂)).of_eq fun _ => rfl

/-- The mass of a charge is computable in the depth and the charge. -/
theorem computable₂_grayChargeMass : Computable₂ grayChargeMass := by
  change Computable fun w : Nat × FamilyGrayCharge => grayChargeMass w.1 w.2
  exact (computable_grayMassOfCount.comp Computable.fst
    (Primrec.list_length.to_comp.comp Computable.snd)).of_eq fun _ => rfl

/-- Enumerating the candidate charges, the sublists of the charge universe, is primitive
recursive. -/
theorem primrec_familyGrayChargeCandidates :
    Primrec fun q : Nat × Nat =>
      (familyGrayChargeUniverse q.1 q.2).sublists := by
  exact (primrec_list_sublists.comp primrec_familyGrayChargeUniverse).of_eq
    fun _ => rfl

/-- All parameters of the designated-charge validity test. -/
abbrev GrayChargeParam :=
  (Rat × Rat × Rat × Rat) ×
    ((Nat × Nat × Nat) ×
      (Allocation × FamilyClientMove × FamilyServerMove × FamilyGrayCharge))

/-- The conjuncts of `familyGrayChargeAtB` are jointly computable. -/
theorem computable_familyGrayChargeAtB_joint :
    Computable fun q : GrayChargeParam =>
      familyGrayChargeAtB q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2
        q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1
        q.2.2.2.2.1 q.2.2.2.2.2 := by
  have heta : Computable fun q : GrayChargeParam => q.1.1 :=
    Computable.fst.comp Computable.fst
  have hkappa : Computable fun q : GrayChargeParam => q.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have halpha : Computable fun q : GrayChargeParam => q.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hbeta : Computable fun q : GrayChargeParam => q.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have heps : Computable fun q : GrayChargeParam => q.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hdelta : Computable fun q : GrayChargeParam => q.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
  have hn : Computable fun q : GrayChargeParam => q.2.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
  have hA : Computable fun q : GrayChargeParam => q.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hc : Computable fun q : GrayChargeParam => q.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hs : Computable fun q : GrayChargeParam => q.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.snd)))
  have hG : Computable fun q : GrayChargeParam => q.2.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.snd)))
  have hunique := primrec_grayChargeCellsUniqueB.to_comp.comp hG
  have hcells : Computable fun q : GrayChargeParam => q.2.2.2.2.2.all (fun z =>
      decide (z.1 < q.2.1.2.2) &&
        decide (z.2 ∈ newGrayCellsList q.2.1.1 q.2.1.2.1
          (getFamilyAlloc q.2.2.2.2.1 z.1 []) q.2.2.1)) := by
    have hbody : Computable₂ fun (q : GrayChargeParam) (z : Nat × BitString) =>
        decide (z.1 < q.2.1.2.2) &&
          decide (z.2 ∈ newGrayCellsList q.2.1.1 q.2.1.2.1
            (getFamilyAlloc q.2.2.2.2.1 z.1 []) q.2.2.1) := by
      have hroot : Computable fun w : GrayChargeParam × (Nat × BitString) =>
          w.2.1 := Computable.fst.comp Computable.snd
      have hcell : Computable fun w : GrayChargeParam × (Nat × BitString) =>
          w.2.2 := Computable.snd.comp Computable.snd
      have hlt := Primrec.nat_lt.decide.to_comp.comp hroot (hn.comp Computable.fst)
      have halloc := primrec₂_familyRootAlloc.to_comp.comp
        (hs.comp Computable.fst) hroot
      have hnew := primrec_newGrayCellsList.to_comp.comp
        (((heps.comp Computable.fst).pair (hdelta.comp Computable.fst)).pair
          (halloc.pair (hA.comp Computable.fst)))
      have hmem : Computable fun w : GrayChargeParam × (Nat × BitString) =>
          decide (w.2.2 ∈ newGrayCellsList w.1.2.1.1 w.1.2.1.2.1
            (getFamilyAlloc w.1.2.2.2.2.1 w.2.1 []) w.1.2.2.1) :=
        (mem_decide_primrec.to_comp.comp hnew hcell).of_eq fun _ =>
          decide_eq_decide.mpr Iff.rfl
      exact ((Primrec.dom_bool₂ (fun a b => a && b)).to_comp.comp hlt hmem).of_eq
        fun _ => rfl
    exact (computable_list_all hG hbody).of_eq fun _ => rfl
  have hroots : Computable fun q : GrayChargeParam => (List.range q.2.1.2.2).all
      (fun i =>
        decide (q.1.2.2.1 / 2 ≤ getFamilyReq q.2.2.2.1 i []) &&
          decide (getFamilyReq q.2.2.2.1 i [] ≤ q.1.2.2.1) &&
          decide (grayChargeMass q.2.1.2.1
            (grayChargeAtRoot i q.2.2.2.2.2) ≤
              q.1.1 * q.1.2.1 * getFamilyReq q.2.2.2.1 i [])) := by
    have hrange := Primrec.list_range.to_comp.comp hn
    have hbody : Computable₂ fun (q : GrayChargeParam) (i : Nat) =>
        decide (q.1.2.2.1 / 2 ≤ getFamilyReq q.2.2.2.1 i []) &&
          decide (getFamilyReq q.2.2.2.1 i [] ≤ q.1.2.2.1) &&
          decide (grayChargeMass q.2.1.2.1
            (grayChargeAtRoot i q.2.2.2.2.2) ≤
              q.1.1 * q.1.2.1 * getFamilyReq q.2.2.2.1 i []) := by
      have hreq : Computable fun w : GrayChargeParam × Nat =>
          getFamilyReq w.1.2.2.2.1 w.2 [] :=
        primrec₂_familyRootReq.to_comp.comp (hc.comp Computable.fst) Computable.snd
      have hahalf : Computable fun w : GrayChargeParam × Nat =>
          w.1.1.2.2.1 / 2 :=
        computable_ratHalf.comp (halpha.comp Computable.fst)
      have hlow := computable_ratLe.comp hahalf hreq
      have hhigh := computable_ratLe.comp hreq (halpha.comp Computable.fst)
      have hcharge := primrec₂_grayChargeAtRoot.to_comp.comp Computable.snd
        (hG.comp Computable.fst)
      have hmass := computable₂_grayChargeMass.comp
        (hdelta.comp Computable.fst) hcharge
      have hcap := computable₂_ratMul.comp
        (computable₂_ratMul.comp (heta.comp Computable.fst)
          (hkappa.comp Computable.fst)) hreq
      have hupper := computable_ratLe.comp hmass hcap
      have hand := (Primrec.dom_bool₂ (fun a b => a && b)).to_comp
      exact (hand.comp (hand.comp hlow hhigh) hupper).of_eq fun _ => rfl
    exact (computable_list_all hrange hbody).of_eq fun _ => rfl
  have hmass := computable₂_grayChargeMass.comp hdelta hG
  have hnrat := computable_nat_to_rat.comp hn
  have hagg1 := computable_ratLe.comp
    (computable₂_ratMul.comp hnrat hbeta) hmass
  have hreq := computable₂_totalRootRequest.comp hn hc
  have hagg2 := computable_ratLe.comp
    (computable₂_ratMul.comp hkappa hreq) hmass
  have hsubfam : Computable fun q : GrayChargeParam =>
      (List.range q.2.1.2.2).sublists.all (fun I =>
        decide (q.1.2.1 *
          (2 * totalRootRequestOnList I q.2.2.2.1 -
            totalRootRequest q.2.1.2.2 q.2.2.2.1) ≤
              grayChargeMass q.2.1.2.1
                (q.2.2.2.2.2.filter fun z => decide (z.1 ∈ I)))) := by
    have hsubl : Computable fun q : GrayChargeParam =>
        (List.range q.2.1.2.2).sublists :=
      ((primrec_list_sublists.comp Primrec.list_range).to_comp.comp hn).of_eq
        fun _ => rfl
    have hbody : Computable₂ fun (q : GrayChargeParam) (I : List Nat) =>
        decide (q.1.2.1 *
          (2 * totalRootRequestOnList I q.2.2.2.1 -
            totalRootRequest q.2.1.2.2 q.2.2.2.1) ≤
              grayChargeMass q.2.1.2.1
                (q.2.2.2.2.2.filter fun z => decide (z.1 ∈ I))) := by
      have hI : Computable fun w : GrayChargeParam × List Nat => w.2 :=
        Computable.snd
      have hreqI : Computable fun w : GrayChargeParam × List Nat =>
          totalRootRequestOnList w.2 w.1.2.2.2.1 :=
        computable₂_totalRootRequestOnList.comp hI (hc.comp Computable.fst)
      have htot : Computable fun w : GrayChargeParam × List Nat =>
          totalRootRequest w.1.2.1.2.2 w.1.2.2.2.1 :=
        computable₂_totalRootRequest.comp (hn.comp Computable.fst)
          (hc.comp Computable.fst)
      have hlhs : Computable fun w : GrayChargeParam × List Nat =>
          w.1.1.2.1 * (2 * totalRootRequestOnList w.2 w.1.2.2.2.1 -
            totalRootRequest w.1.2.1.2.2 w.1.2.2.2.1) :=
        computable₂_ratMul.comp (hkappa.comp Computable.fst)
          (computable₂_ratSub.comp
            (computable₂_ratMul.comp (Computable.const (2 : Rat)) hreqI) htot)
      have hfilter : Computable fun w : GrayChargeParam × List Nat =>
          w.1.2.2.2.2.2.filter fun z => decide (z.1 ∈ w.2) := by
        have hp : Computable₂ fun (w : GrayChargeParam × List Nat)
            (z : Nat × BitString) => decide (z.1 ∈ w.2) :=
          ((mem_decide_primrec.to_comp.comp
            (hI.comp Computable.fst)
            (Computable.fst.comp Computable.snd)).of_eq fun _ =>
              decide_eq_decide.mpr Iff.rfl).to₂
        exact computable_list_filter (hG.comp Computable.fst) hp
      have hmassI := computable₂_grayChargeMass.comp
        (hdelta.comp Computable.fst) hfilter
      exact (computable_ratLe.comp hlhs hmassI).of_eq fun _ => rfl
    exact (computable_list_all hsubl hbody).of_eq fun _ => rfl
  have hand := (Primrec.dom_bool₂ (fun a b => a && b)).to_comp
  exact (hand.comp
    (hand.comp (hand.comp (hand.comp (hand.comp hunique hcells) hroots) hagg1)
      hagg2) hsubfam).of_eq fun _ => rfl

/-- All parameters of the finite charged-goal search. -/
abbrev ChargedGrayGoalParam :=
  (Rat × Rat × Rat × Rat) ×
    ((Nat × Nat × Nat) ×
      (Allocation × FamilyClientMove × FamilyServerMove))

/-- The charged gray goal is decidable by exhaustive finite search. -/
theorem computable_familyChargedGrayGoalAtB_joint :
    Computable fun q : ChargedGrayGoalParam =>
      familyChargedGrayGoalAtB q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2
        q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1 q.2.2.2.2 := by
  have heta : Computable fun q : ChargedGrayGoalParam => q.1.1 :=
    Computable.fst.comp Computable.fst
  have hkappa : Computable fun q : ChargedGrayGoalParam => q.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have halpha : Computable fun q : ChargedGrayGoalParam => q.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hbeta : Computable fun q : ChargedGrayGoalParam => q.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have heps : Computable fun q : ChargedGrayGoalParam => q.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hdelta : Computable fun q : ChargedGrayGoalParam => q.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
  have hn : Computable fun q : ChargedGrayGoalParam => q.2.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
  have hA : Computable fun q : ChargedGrayGoalParam => q.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hc : Computable fun q : ChargedGrayGoalParam => q.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hs : Computable fun q : ChargedGrayGoalParam => q.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hrange := Primrec.list_range.to_comp.comp hn
  have halloc := computable₂_familyAllocatedOnList.comp hrange hs
  have hweak := computable_familyGrayGoalAtB_joint.comp
    (((hkappa.pair hbeta).pair (heps.pair hdelta)).pair
      ((hn.pair hA).pair (hc.pair halloc)))
  have hcandidates := primrec_familyGrayChargeCandidates.to_comp.comp
    (hn.pair hdelta)
  have hbody : Computable₂ fun (q : ChargedGrayGoalParam) (G : FamilyGrayCharge) =>
      familyGrayChargeAtB q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2
        q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1 q.2.2.2.2 G := by
    have hrat : Computable fun w : ChargedGrayGoalParam × FamilyGrayCharge =>
        w.1.1 := Computable.fst.comp Computable.fst
    have hnat : Computable fun w : ChargedGrayGoalParam × FamilyGrayCharge =>
        w.1.2.1 := Computable.fst.comp (Computable.snd.comp Computable.fst)
    have hclient : Computable fun w : ChargedGrayGoalParam × FamilyGrayCharge =>
        w.1.2.2.2.1 := hc.comp Computable.fst
    have hserver : Computable fun w : ChargedGrayGoalParam × FamilyGrayCharge =>
        w.1.2.2.2.2 := hs.comp Computable.fst
    have htail : Computable fun w : ChargedGrayGoalParam × FamilyGrayCharge =>
        (w.1.2.2.2.1, w.1.2.2.2.2, w.2) :=
      hclient.pair (hserver.pair Computable.snd)
    have hdata : Computable fun w : ChargedGrayGoalParam × FamilyGrayCharge =>
        (w.1.2.2.1, w.1.2.2.2.1, w.1.2.2.2.2, w.2) :=
      (hA.comp Computable.fst).pair htail
    have hargs : Computable fun w : ChargedGrayGoalParam × FamilyGrayCharge =>
        (w.1.1, (w.1.2.1, (w.1.2.2.1, w.1.2.2.2.1,
          w.1.2.2.2.2, w.2))) := hrat.pair (hnat.pair hdata)
    exact (computable_familyGrayChargeAtB_joint.comp hargs).of_eq fun _ => rfl
  have hsearch := computable_list_any hcandidates hbody
  exact ((Primrec.dom_bool₂ (fun a b => a && b)).to_comp.comp hweak hsearch).of_eq
    fun _ => rfl

end Kolmogorov
