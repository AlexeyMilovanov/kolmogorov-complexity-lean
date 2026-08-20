import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseFibres
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.OmegaEquivalence

/-!
# Finite-set symmetry for the heavy first-coordinate truncation

The rounded heavy truncation `finiteSetFstHeavyTruncation B l` is computable
from the canonical code of `B` together with the threshold `l`.  Plain symmetry
of information therefore bounds the complexity of the heavy truncation plus the
information needed to reconstruct `B` from it, which is the exact shape used by
the low-coordinate branch of VS40 `rem:add-noise`.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- The heavy truncation costs only its logarithmic threshold advice, given the
canonical code of the original finite set. -/
theorem finiteSetFstHeavyTruncation_condK_from_B
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ (B : Finset BitString) (hB : B.Nonempty) (l : Nat)
        (hH : (finiteSetFstHeavyTruncation B l).Nonempty),
      condK V
        (codedUniformOn (finiteSetFstHeavyTruncation B l) hH).code
        (codedUniformOn B hB).code ≤
      (((Nat.bits l).length + C : Nat) : ENat) := by
  let g : BitString → BitString →. BitString := fun y p ↦
    Part.some (finiteSetFstHeavyTruncationCode y p)
  have hg : Partrec (fun q : BitString × BitString ↦ g q.1 q.2) := by
    have h1 : Computable (fun q : BitString × BitString ↦
        finiteSetFstHeavyTruncationCode q.1 q.2) :=
      finiteSetFstHeavyTruncationCode_computable.comp Computable.fst Computable.snd
    exact h1.partrec
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le V hV g hg
  refine ⟨C, fun B hB l hH ↦ ?_⟩
  have h_some :
      finiteSetFstHeavyTruncationCode (codedUniformOn B hB).code (Nat.bits l) ∈
        g (codedUniformOn B hB).code (Nat.bits l) := ⟨trivial, rfl⟩
  have h_bound := hC (codedUniformOn B hB).code (Nat.bits l)
    (finiteSetFstHeavyTruncationCode (codedUniformOn B hB).code (Nat.bits l)) h_some
  rw [finiteSetFstHeavyTruncationCode_codedUniformOn B hB l hH] at h_bound
  refine h_bound.trans ?_
  norm_cast

/-- Finite-set Kolmogorov–Levin inequality for the heavy truncation
`H = finiteSetFstHeavyTruncation B l`:
`C(H) + C(B | [H]) ≤ C(B) + O(log N)` whenever `C(B) ≤ N` and `l ≤ N`. -/
theorem finiteSetFstHeavyTruncation_plainSetComplexity_symmetry
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (B : Finset BitString) (hB : B.Nonempty) (l N : Nat)
        (hH : (finiteSetFstHeavyTruncation B l).Nonempty),
      plainSetComplexity V B hB ≤ (N : ENat) →
      l ≤ N →
      plainSetComplexity V (finiteSetFstHeavyTruncation B l) hH +
        condK V (codedUniformOn B hB).code
          (codedUniformOn (finiteSetFstHeavyTruncation B l) hH).code ≤
      plainSetComplexity V B hB + (logSlack c N : ENat) := by
  obtain ⟨C1, hC1⟩ := plainK_add_condK_symmetry V U hV hU
  obtain ⟨C2, hC2⟩ := finiteSetFstHeavyTruncation_condK_from_B V hV
  obtain ⟨C3, hC3⟩ := finiteSetFstHeavyTruncation_plainSetComplexity_le V hV
  obtain ⟨bAdv, hbAdv⟩ := logSlack_le_add_const (C2 + 2)
  obtain ⟨bHeavy, hbHeavy⟩ := logSlack_le_add_const C3
  obtain ⟨C, hC⟩ := logSlack_linear_bound C1 (1 + (C2 + 2) + C3) (bAdv + bHeavy)
  refine ⟨C + C2 + 2 + C3, fun B hB l N hH hN hlN ↦ ?_⟩
  set H := finiteSetFstHeavyTruncation B l with hHdef
  -- The advice bound `(Nat.bits l).length + C2` is logarithmic in `N`.
  have hadv : (Nat.bits l).length + C2 ≤ logSlack (C2 + 2) N := by
    have hmono : (Nat.bits l).length ≤ (Nat.bits N).length :=
      length_natBits_mono hlN
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits N).length)]
  have hcondBH : condK V (codedUniformOn H hH).code (codedUniformOn B hB).code ≤
      ((logSlack (C2 + 2) N : Nat) : ENat) := by
    refine (hC2 B hB l hH).trans ?_
    exact_mod_cast hadv
  have hHcomp : plainSetComplexity V H hH ≤
      plainSetComplexity V B hB + ((logSlack C3 N : Nat) : ENat) := by
    refine (hC3 B hB l hH).trans ?_
    gcongr
    exact_mod_cast logSlack_mono_right C3 hlN
  -- Budget for the symmetry theorem.
  set N' := N + logSlack (C2 + 2) N + logSlack C3 N with hN'
  have hBN' : plainSetComplexity V B hB ≤ (N' : ENat) := by
    refine hN.trans ?_
    exact_mod_cast (by omega : N ≤ N')
  have hHN' : plainSetComplexity V H hH ≤ (N' : ENat) := by
    refine hHcomp.trans ?_
    calc
      plainSetComplexity V B hB + ((logSlack C3 N : Nat) : ENat)
          ≤ (N : ENat) + ((logSlack C3 N : Nat) : ENat) := by gcongr
      _ = ((N + logSlack C3 N : Nat) : ENat) := by push_cast; ring
      _ ≤ (N' : ENat) := by exact_mod_cast (by omega : N + logSlack C3 N ≤ N')
  have hcondN' : condK V (codedUniformOn H hH).code (codedUniformOn B hB).code ≤
      (N' : ENat) := by
    refine hcondBH.trans ?_
    exact_mod_cast (by omega : logSlack (C2 + 2) N ≤ N')
  have hsymm := hC1 (codedUniformOn B hB).code (codedUniformOn H hH).code N'
    hBN' hHN' hcondN'
  -- Absorb the two logarithmic terms into a single slack.
  have hslackN' : logSlack C1 N' ≤ logSlack C N := by
    have hle : N' ≤ (1 + (C2 + 2) + C3) * N + (bAdv + bHeavy) := by
      have h1 := hbAdv N
      have h2 := hbHeavy N
      have : N' = N + logSlack (C2 + 2) N + logSlack C3 N := hN'
      nlinarith
    exact (logSlack_mono_right C1 hle).trans (hC N)
  have habsorb :
      ((logSlack (C2 + 2) N : Nat) : ENat) + ((logSlack C1 N' : Nat) : ENat) ≤
        ((logSlack (C + C2 + 2 + C3) N : Nat) : ENat) := by
    have h : logSlack (C2 + 2) N + logSlack C1 N' ≤ logSlack (C + C2 + 2 + C3) N := by
      have h1 : logSlack (C2 + 2) N + logSlack C N ≤ logSlack (C + C2 + 2) N := by
        rw [Nat.add_comm (logSlack (C2 + 2) N), logSlack_add_const]
        exact logSlack_mono_left (by omega) N
      have h2 : logSlack (C + C2 + 2) N ≤ logSlack (C + C2 + 2 + C3) N :=
        logSlack_mono_left (by omega) N
      omega
    exact_mod_cast h
  calc
    plainSetComplexity V H hH +
          condK V (codedUniformOn B hB).code (codedUniformOn H hH).code
        ≤ plainSetComplexity V B hB +
            condK V (codedUniformOn H hH).code (codedUniformOn B hB).code +
            (logSlack C1 N' : ENat) := hsymm
    _ ≤ plainSetComplexity V B hB + ((logSlack (C2 + 2) N : Nat) : ENat) +
          (logSlack C1 N' : ENat) := by gcongr
    _ = plainSetComplexity V B hB +
          (((logSlack (C2 + 2) N : Nat) : ENat) + ((logSlack C1 N' : Nat) : ENat)) := by
        rw [add_assoc]
    _ ≤ plainSetComplexity V B hB + (logSlack (C + C2 + 2 + C3) N : ENat) := by
        gcongr

end Kolmogorov
