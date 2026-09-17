import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChargedOracle
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderCodeStep

/-!
# The V2 executable tail transformer (code level)

The V2 twin of `grayCharged_exists_code_step`
(`GacsDayChargedClosureLeaves.lean`): from the partial recursive oracle
procedure `chargedPhiV2` the s-m-n theorem
(`exists_codeTransformer_of_partrec`) produces a *computable transformer of
codes* which sends a code for the previous scheme to a code for the V2 charged
strategy, and hence the computability of the V2 charged strategy scheme itself.

This is the last controller-specific link of V1's computability chain
```
canonicalGrayScheme_computable
 └ grayCharged_exists_code_step  ←  THE TAIL STEP
     └ partrec_chargedPhi
```
transplanted to V2; what remains for a full V2 ladder is the canonical V2
scheme over `grayFootprint` (there is no `canonicalGraySchemeV2` yet) and its
schedule proofs.
-/

namespace Kolmogorov

open Encodable

/-- **The V2 executable tail transformer.**  V2 twin of
`grayCharged_exists_code_step`. -/
theorem grayChargedV2_exists_code_step :
    Exists fun G : Nat -> Nat -> Nat.Partrec.Code -> Nat.Partrec.Code =>
      And
        (Computable (fun p : (Nat × Nat) × Nat.Partrec.Code =>
          G p.1.1 p.1.2 p.2))
        (forall (q L : Nat) (code : Nat.Partrec.Code)
            (sigma : FamilyStrategyScheme),
            CodeComputesScheme code sigma ->
            CodeComputesScheme (G q L code)
              (fun a e => grayChargedStrategyV2 q L a e sigma)) := by
  have hpack : Computable
      (fun x : Nat × Nat.Partrec.Code × SchemeInput =>
        (((x.1.unpair.1, x.1.unpair.2), x.2.1, x.2.2) : ChargedOracleInput)) :=
    (((Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.fst).pair
        ((Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.fst)).pair
      Computable.snd
  obtain ⟨G, hG, heval⟩ :=
    exists_codeTransformer_of_partrec (α := SchemeInput)
      (partrec_chargedPhiV2.comp hpack)
  refine ⟨fun q L code => G (Nat.pair q L) code, ?_, ?_⟩
  · exact hG.comp
      ((Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.fst)
        (Computable.snd.comp Computable.fst))) Computable.snd
  · intro q L code sigma hcode p
    have h := heval (Nat.pair q L) code p
    simp only [Nat.unpair_pair] at h
    rw [h, chargedPhiV2_eq q L code sigma hcode p]

/-- **The V2 charged strategy scheme is computable** whenever the child scheme
is.  V2 twin of `grayChargedStrategyScheme_computable`. -/
theorem grayChargedStrategySchemeV2_computable
    (q L : Nat) (sigma : FamilyStrategyScheme)
    (hsigma : FamilyStrategySchemeComputable sigma) :
    FamilyStrategySchemeComputable
      (fun a e => grayChargedStrategyV2 q L a e sigma) := by
  obtain ⟨G, _hGcomp, hG⟩ := grayChargedV2_exists_code_step
  obtain ⟨code, hcode⟩ :=
    exists_code_of_familyStrategySchemeComputable hsigma
  exact familyStrategySchemeComputable_of_code (hG q L code sigma hcode)

end Kolmogorov
