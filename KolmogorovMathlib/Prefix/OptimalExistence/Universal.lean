/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.OptimalExistence.Computability
import KolmogorovMathlib.Prefix.Combinators
import KolmogorovMathlib.AlgorithmicProbability.SimulationComplexity
import KolmogorovMathlib.AlgorithmicProbability.TaggedUnionUniversal
import KolmogorovMathlib.Core.Invariance
import Mathlib

namespace Kolmogorov

open Nat.Partrec (Code)


/-- Enumerated family of prefix decompressors. -/
def enumeratedPrefixMachine (i : ℕ) : Map :=
  match Encodable.decode i with
  | some c => prefixFiltered c
  | none => fun _ => Part.none

theorem enumeratedPrefixMachine_isPrefixDecompressor (i : ℕ) :
    IsPrefixDecompressor (enumeratedPrefixMachine i) := by
  unfold enumeratedPrefixMachine
  cases (Encodable.decode i : Option Code) with
  | none =>
    exact ⟨Partrec.none, by
      intro y p hp q hq hpre
      exact False.elim hp⟩
  | some c =>
    exact prefixFiltered_isPrefixDecompressor c

theorem exists_enumeratedPrefixMachine_eq {M : Map} (hM : IsPrefixDecompressor M) :
    ∃ i, enumeratedPrefixMachine i = M := by
  obtain ⟨c, hc⟩ := existsCodeOfIsDecompressor M hM.isDecompressor
  use Encodable.encode c
  unfold enumeratedPrefixMachine
  rw [Encodable.encodek]
  exact prefixFiltered_eq_of_isPrefixDecompressor c hM hc

/-- The enumerated family, rewritten as an option-bind on the decoded code. -/
theorem enumeratedPrefixMachine_eq_bind (i : ℕ) (z : BitString × BitString) :
    enumeratedPrefixMachine i z =
      (Part.ofOption (Encodable.decode i : Option Code)).bind
        (fun c => prefixFiltered c z) := by
  unfold enumeratedPrefixMachine
  cases (Encodable.decode i : Option Code) with
  | none => simp
  | some c => simp

/-- The enumerated family is uniformly partial recursive in the index and input. -/
theorem enumeratedPrefixMachine_uniform_partrec :
    Partrec (fun t : ℕ × BitString × BitString => enumeratedPrefixMachine t.1 t.2) := by
  have hrw : (fun t : ℕ × BitString × BitString => enumeratedPrefixMachine t.1 t.2)
      = fun t => (Part.ofOption (Encodable.decode t.1 : Option Code)).bind
          (fun c => prefixFiltered c t.2) :=
    funext fun t => enumeratedPrefixMachine_eq_bind t.1 t.2
  rw [hrw]
  apply Partrec.bind
  · exact Computable.ofOption (Computable.decode.comp Computable.fst)
  · have hmap : Computable (fun s : (ℕ × BitString × BitString) × Code =>
        ((s.2, s.1.2) : Code × BitString × BitString)) :=
      Computable.snd.pair (Computable.snd.comp Computable.fst)
    exact (prefixFiltered_uniform_partrec.comp hmap).of_eq (fun s => rfl)

/-! ### The universal prefix machine -/

/-- A tagged union of a uniformly partial-recursive family is partial recursive. -/
theorem taggedUnion_isDecompressor_of_uniform {M : ℕ → Map}
    (hM : Partrec (fun t : ℕ × BitString × BitString => M t.1 t.2)) :
    isDecompressor (taggedUnion M) := by
  have hidxP : Primrec (fun pr : BitString × BitString => (pr.1.takeWhile id).length) :=
    (Primrec.list_findIdx Primrec.fst (Primrec.not.comp Primrec.snd).to₂).of_eq
      (fun pr => (takeWhile_id_length_eq_findIdx pr.1).symm)
  have hdropP : Primrec (fun pr : BitString × BitString =>
      pr.1.drop ((pr.1.takeWhile id).length + 1)) :=
    primrec_bitString_drop.comp Primrec.fst (Primrec.succ.comp hidxP)
  have hguard : Computable (fun pr : BitString × BitString =>
      decide ((pr.1.takeWhile id).length < pr.1.length)) :=
    (Primrec.to_comp primrec_decide_lt).comp
      ((Primrec.to_comp hidxP).pair (Primrec.to_comp (Primrec.list_length.comp Primrec.fst)))
  have hcall : Partrec (fun pr : BitString × BitString =>
      M ((pr.1.takeWhile id).length) (pr.1.drop ((pr.1.takeWhile id).length + 1), pr.2)) := by
    have hmap : Computable (fun pr : BitString × BitString =>
        (((pr.1.takeWhile id).length, (pr.1.drop ((pr.1.takeWhile id).length + 1), pr.2)) :
          ℕ × BitString × BitString)) :=
      (Primrec.to_comp hidxP).pair ((Primrec.to_comp hdropP).pair Computable.snd)
    exact (hM.comp hmap).of_eq (fun pr => rfl)
  refine (Partrec.cond hguard hcall Partrec.none).of_eq (fun pr => ?_)
  simp only [taggedUnion]
  by_cases h : (pr.1.takeWhile id).length < pr.1.length <;> simp [h]

/-- The universal prefix machine. -/
def universalPrefixMachine : Map := taggedUnion enumeratedPrefixMachine

/-- The effective tagged union of the enumerated filtered machines is partial
recursive. -/
theorem universalPrefixMachine_isDecompressor :
    isDecompressor universalPrefixMachine :=
  taggedUnion_isDecompressor_of_uniform enumeratedPrefixMachine_uniform_partrec

theorem universalPrefixMachine_isPrefixDecompressor :
    IsPrefixDecompressor universalPrefixMachine := by
  exact ⟨universalPrefixMachine_isDecompressor,
    taggedUnion_isPrefixMachine
      (fun i => (enumeratedPrefixMachine_isPrefixDecompressor i).isPrefixMachine)⟩

/-! ### Universal machine simulation -/

theorem universalPrefixMachine_isSimulationUniversal :
    IsSimulationUniversal universalPrefixMachine := by
  refine ⟨universalPrefixMachine_isPrefixDecompressor, fun M hM => ?_⟩
  obtain ⟨i, hi⟩ := exists_enumeratedPrefixMachine_eq hM
  use i + 1
  have h_sim := taggedUnionSimulation enumeratedPrefixMachine i
  rw [hi] at h_sim
  exact ⟨h_sim⟩

/-! ### Final existence theorems -/

theorem exists_isSimulationUniversal : Exists fun U : Map => IsSimulationUniversal U :=
  ⟨universalPrefixMachine, universalPrefixMachine_isSimulationUniversal⟩

theorem exists_isOptimalPrefixConditional : Exists fun U : Map => IsOptimalPrefixConditional U := by
  obtain ⟨U, hU⟩ := exists_isSimulationUniversal
  exact ⟨U, hU.isOptimalPrefixConditional⟩

end Kolmogorov
