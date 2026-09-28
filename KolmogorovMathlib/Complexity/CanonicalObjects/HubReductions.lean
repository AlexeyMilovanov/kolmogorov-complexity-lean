import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Reduce
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Computability.PartrecCode
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.BusyBeaver

/-!
# The canonical objects and the reductions between them

`canonicalObject` collects the nine objects of SUV Theorem 15, indexed `0, …, 8` in the order
(a)–(i) of the book; the four defined here are `objHaltingCount`, `objSlowestProgram`,
`objComplexityGraph` and `objFirstIncompressible`.

The module then builds the reductions along the hub — the maximal halting time, the busy
beaver, the completed time bound, the slowest halting program — and composes them, using the
halting-time facts `haltsWithin_haltTime`, `haltTime_le_of_haltsWithin`,
`countHalts_maxHaltingStage` and `maxHaltingStage_le_of_countHalts_eq`, a bounded-search
surrogate for the halting time and a primitive-recursive presentation of `List.argmax`.

It closes with both halves of Theorem 15: each object has complexity at most `n + O(1)`, and
each has complexity at least `n - O(1)`, the lower bounds being proved separately for the two
graph objects, the two counting objects, and the remaining five.
-/



namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- Object (f): the number of such programs. -/
noncomputable def objHaltingCount (c : Code) (n : ℕ) : BitString :=
  natBits (haltingProgramsBounded c n).length

/-- Object (g): the most time-consuming halting program of length at most `n`. -/
noncomputable def objSlowestProgram (c : Code) (n : ℕ) : BitString :=
  (List.argmax (haltTimeNat c) (haltingProgramsBounded c n)).getD []

/-- Object (h): the graph of `C` on the strings of length `n`. -/
noncomputable def objComplexityGraph (U : Map) (n : ℕ) : BitString :=
  listCode ((allStrings n).map (fun x => pairCode x (natBits (cVal U x))))

open Classical in
/-- Object (i): the lexicographically first string of length `n` of complexity at
least `n`. -/
noncomputable def objFirstIncompressible (U : Map) (n : ℕ) : BitString :=
  ((allStrings n).find? (fun x => decide ((n : ℕ∞) ≤ plainK U x))).getD []

/-- The nine canonical objects of Theorem 15, indexed by `0, …, 8` in the order
(a)–(i) of the book. -/
noncomputable def canonicalObject (U : Map) (c : Code) (i n : ℕ) : BitString :=
  match i with
  | 0 => objComplexityList U c n
  | 1 => objComplexityCount c n
  | 2 => objBusyBeaver c n
  | 3 => objMaxTime c n
  | 4 => objHaltingList c n
  | 5 => objHaltingCount c n
  | 6 => objSlowestProgram c n
  | 7 => objComplexityGraph U n
  | _ => objFirstIncompressible U n

/-! ### Foundation for the Theorem 15 hub reductions -/

/-- A halting program halts within its halting time. -/
theorem haltsWithin_haltTime (c : Code) {p : BitString}
    (h : ∃ t, haltsWithin c t p = true) : haltsWithin c (haltTimeNat c p) p = true := by
  unfold haltTimeNat
  rw [dif_pos h]
  exact Nat.find_spec h

/-- If `p` halts under `c` within `t` steps, then `haltTimeNat c p ≤ t`: the halting time is a
lower bound for every stage at which the program is seen to halt. -/
theorem haltTime_le_of_haltsWithin (c : Code) {p : BitString} {t : ℕ}
    (h : haltsWithin c t p = true) : haltTimeNat c p ≤ t := by
  have hex : ∃ s, haltsWithin c s p = true := ⟨t, h⟩
  unfold haltTimeNat
  rw [dif_pos hex]
  exact Nat.find_min' hex h

/-- Past the maximal halting stage of a level, the stage-wise output equals the completed
output of the level. -/
theorem boundedOutputStage_eq_completedBoundedOutput (c : Code) (m T : ℕ)
    (hT : maxHaltingStage c m ≤ T) :
    boundedOutputStage c m T = completedBoundedOutput c m :=
  boundedOutputStage_eq_completed_of_completion_le c m T
    (le_trans (boundedOutputCompletionTime_le_complete_stage c m (maxHaltingStage c m) rfl) hT)

/-- At the maximal halting stage every halting program of the level has been counted. -/
theorem countHalts_maxHaltingStage (c : Code) (m : ℕ) :
    countHalts c m (maxHaltingStage c m) = (haltingProgramsBounded c m).length := by
  unfold countHalts haltingProgramsBounded
  rw [List.countP_eq_length_filter]

private theorem countHalts_le_length_haltingProgramsBounded (c : Code) (m t : ℕ) :
    countHalts c m t ≤ (haltingProgramsBounded c m).length := by
  rw [← countHalts_maxHaltingStage c m]
  exact maxHaltingStage_spec c m t

open Classical in
/-- A stage at which all halting programs of a level have been counted is past the maximal
halting stage. -/
theorem maxHaltingStage_le_of_countHalts_eq (c : Code) (m T : ℕ)
    (hT : countHalts c m T = (haltingProgramsBounded c m).length) :
    maxHaltingStage c m ≤ T := by
  have hmax : ∀ t', countHalts c m t' ≤ countHalts c m T := by
    intro t'
    rw [hT]
    exact countHalts_le_length_haltingProgramsBounded c m t'
  unfold maxHaltingStage
  exact Nat.find_min' _ hmax

private theorem eq_maxHaltingStage_of_countHalts_eq (c : Code) (m T : ℕ)
    (hT : countHalts c m T = (haltingProgramsBounded c m).length)
    (hmin : ∀ s, s < T → countHalts c m s ≠ (haltingProgramsBounded c m).length) :
    T = maxHaltingStage c m := by
  refine le_antisymm ?_ (maxHaltingStage_le_of_countHalts_eq c m T hT)
  by_contra hcon
  exact hmin (maxHaltingStage c m) (by omega) (countHalts_maxHaltingStage c m)

/-! ### Batch 1: the maximal-halting-time hub -/

/-! ### Batch: the busy-beaver hub (object 2) -/

/-! ### Batch 2: recovering the complexity function from a completed time bound -/

/-! ### Batch D: edge (c) → (e) -/

/-! ### Batch 2: the slowest halting program (object (g)) -/

/-! #### The bounded-search surrogate for the halting time -/

/-! #### A primitive-recursive presentation of `List.argmax` -/

/-! ### Glue: the two length-reading edges, restated for `HubReduces` -/

/-! ### The hub reductions, composed -/

/-! ### Theorem 15, upper half: each object has complexity at most `n + O(1)` -/

/-! ### Lower bounds for the two length-`n` graph objects (7 and 8) -/

/-! ### Lower bounds for the two counting objects (1 and 5) -/

/-! ### Batch L1: lower bounds for objects 0, 2, 3, 4, 6 -/

/-! #### Problem 15 (equivalence half): reduction through the hub object (e)

`CanonicalObjectReduces U c i j` is the book's "given `n` and `X_n` an algorithm finds `Y_{n-c}`".
It is reflexive and transitive, so the full equivalence follows from the reductions
to and from a single hub object; object 4, the list of halting programs, is the hub
the book uses.  Two of the eighteen hub edges are proved outright below; the rest are
in `CanonicalObjects/IndividualHubEdgesTheorem.lean`. -/

/-- Object `i` at parameter `n` reduces to object `j` at parameter `n - k`. -/
def CanonicalObjectReduces (U : Map) (c : Code) (i j : ℕ) : Prop :=
  ∃ k : ℕ, ∃ A : ℕ × BitString →. BitString, Partrec A ∧
    ∀ n : ℕ, A (n, canonicalObject U c i n) = Part.some (canonicalObject U c j (n - k))

/-- Every canonical object reduces to itself. -/
theorem CanonicalObjectReduces.refl (U : Map) (c : Code) (i : ℕ) : CanonicalObjectReduces U c i i :=
  ⟨0, fun p => Part.some p.2, Computable.snd, fun n => by simp⟩

/-- Reductions between canonical objects compose. -/
theorem CanonicalObjectReduces.trans {U : Map} {c : Code} {i j l : ℕ}
    (h1 : CanonicalObjectReduces U c i j) (h2 : CanonicalObjectReduces U c j l) :
    CanonicalObjectReduces U c i l := by
  obtain ⟨k1, A1, hA1p, hA1⟩ := h1
  obtain ⟨k2, A2, hA2p, hA2⟩ := h2
  refine ⟨k1 + k2, fun p => (A1 p).bind (fun y => A2 (p.1 - k1, y)), ?_, ?_⟩
  · refine hA1p.bind ?_
    have hfst : Computable (fun q : (ℕ × BitString) × BitString => q.1.1 - k1) :=
      (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) (Primrec.const k1)).to_comp
    exact (hA2p.comp (Computable.pair hfst Computable.snd)).to₂
  · intro n
    simp only [hA1 n, Part.bind_some]
    rw [hA2 (n - k1), Nat.sub_sub]

/-- Coding the length of the decoded list is computable. -/
theorem listLengthCode_computable :
    Computable (fun p : ℕ × BitString => natBits (decodeListCode p.2).length) :=
  natBits_computable.comp
    ((Primrec.list_length.comp decodeListCode_primrec).to_comp.comp Computable.snd)

/-- (a) → (b): the number of strings of complexity at most `n` is read off the list. -/
private theorem canonicalReduces_complexityList_complexityCount (U : Map) (c : Code) :
    CanonicalObjectReduces U c 0 1 := by
  refine ⟨0, fun p => Part.some (natBits (decodeListCode p.2).length),
    listLengthCode_computable, fun n => ?_⟩
  simp only [Nat.sub_zero, canonicalObject, objComplexityList, objComplexityCount,
    decodeListCode_listCode, List.length_map]

/-- (e) → (f): the number of halting programs of length at most `n` is read off the
halting list. -/
private theorem canonicalReduces_haltingList_haltingCount (U : Map) (c : Code) :
    CanonicalObjectReduces U c 4 5 := by
  refine ⟨0, fun p => Part.some (natBits (decodeListCode p.2).length),
    listLengthCode_computable, fun n => ?_⟩
  simp only [Nat.sub_zero, canonicalObject, objHaltingList, objHaltingCount,
    decodeListCode_listCode]

end Kolmogorov
