import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ProgressBase
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Closure.Part01
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Closure

/-!
# v15 support: the snapshot identity of every frozen round

Along the V2 charged run, every frozen round `p` (advantage or spend) records
as its `unavailable` list the ambient list plus the foreign harvest of the
round's own slots at the round's fine depth, taken at an admissible snapshot
(v15.1 A7, `GrayTailSnapOKV2`): the empty server move only for the first
round, otherwise a server time after every earlier round's exchange and
before the round's own — the predecessor's exchange for advantage rounds and
the later spend passes, the raised-service wait exit for pass 0.  This is the
core certificate's harvest chain `frozen_chain`; the module exposes it under
its historical name and discharges the `hsnap` hypothesis of the spend-round
kills (`GacsDayV2SpendKill`).
-/

namespace Kolmogorov

/-- The snapshot identity of every frozen round of a frozen list: the harvest
chain with admissible snapshots. -/
abbrev GrayChargedFrozenSnapV2 {b : Nat} (n : Nat) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (frozen : List (GrayTailRoundV2 n b)) : Prop :=
  GrayTailHarvestChainV2 n A sm frozen

/-- **The snapshot identity holds for every frozen round of the V2 run.** -/
theorem grayChargedRunStateV2_frozenSnap {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedFrozenSnapV2 n A sm
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen :=
  (grayChargedRunStateV2_coreCertified q L a e sigma A sm t).frozen_chain

/-- Every frozen round records a harvest of its own slots at its fine depth
taken at some snapshot server move. -/
theorem grayChargedRunStateV2_frozen_unavailable_snap {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen) :
    ∃ smSnap : FamilyServerMove,
      p.unavailable = A ++ grayHarvest p.fineEnd p.slots n smSnap := by
  obtain ⟨k, hk, hpk⟩ := List.mem_iff_getElem.mp hp
  obtain ⟨s, -, hsnap⟩ := grayChargedRunStateV2_frozenSnap q L a e sigma A sm t k hk
  rw [hpk] at hsnap
  exact ⟨_, hsnap⟩

end Kolmogorov
