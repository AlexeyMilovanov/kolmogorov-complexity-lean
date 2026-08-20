import KolmogorovMathlib.Core.Invariance
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic

/-!
# Total Conditional Complexity

The foundational definitions for VS40 Section 7.  Unlike ordinary conditional
complexity, a program counted here must halt on every possible condition.
-/

namespace Kolmogorov

/-- A program is total in its condition for the decompressor `D`. -/
def IsTotalProgram (D : Map) (p : BitString) : Prop :=
  forall y : BitString, (D (p, y)).Dom

/-- Candidate lengths for total programs producing `x` from `y`. -/
abbrev totalCandidateLengths (D : Map) (x y : BitString) : Set ENat :=
  {n | exists p, IsTotalProgram D p /\ produces D p y x /\
    (programLength p : ENat) = n}

/-- Total conditional complexity relative to `D`. -/
noncomputable def totalCondK (D : Map) (x y : BitString) : ENat :=
  sInf (totalCandidateLengths D x y)

/-- Optimality for total conditional complexity. -/
def IsOptimalTotalConditional (U : Map) : Prop :=
  isDecompressor U /\
    forall D, isDecompressor D ->
      exists c : Nat, forall x y,
        totalCondK U x y <= totalCondK D x y + (c : ENat)

/-- Two strings carry the same information up to `epsilon` via total programs. -/
def TotalEquivalentWithin (U : Map) (x y : BitString) (epsilon : Nat) : Prop :=
  totalCondK U x y <= (epsilon : ENat) /\
    totalCondK U y x <= (epsilon : ENat)

/-- A finite-set model is strong when its canonical code is total-computable
from the data string with the stated budget. -/
noncomputable def IsStrongSetModel (U : Map) (x : BitString)
    (S : Finset BitString) (hS : S.Nonempty) (epsilon : Nat) : Prop :=
  totalCondK U (codedUniformOn S hS).code x <= (epsilon : ENat)

lemma totalCondK_le_programLength
    {D : Map} {p x y : BitString}
    (htotal : IsTotalProgram D p)
    (hprod : produces D p y x) :
    totalCondK D x y ≤ (programLength p : ENat) := by
  apply sInf_le
  exact ⟨p, htotal, hprod, rfl⟩

private lemma totalCandidateLengths_ge_succ_of_no_short
    (D : Map) (x y : BitString) (n : Nat)
    (hnone : ¬ ∃ p, IsTotalProgram D p ∧
      programLength p ≤ n ∧ produces D p y x) :
    ∀ m ∈ totalCandidateLengths D x y,
      ((n + 1 : Nat) : ENat) ≤ m := by
  rintro m ⟨p, hp_tot, hp_prod, rfl⟩
  have hlen : n < programLength p := by
    contrapose! hnone
    exact ⟨p, hp_tot, hnone, hp_prod⟩
  exact_mod_cast hlen

/-- Finite bounds for total conditional complexity are witnessed by actual
programs that are total in every condition. -/
theorem totalCondK_le_iff (D : Map) (x y : BitString) (n : Nat) :
    totalCondK D x y ≤ (n : ENat) ↔
      ∃ p, IsTotalProgram D p ∧ programLength p ≤ n ∧ produces D p y x := by
  constructor
  · intro h
    by_contra hnone
    have hbound : ((n + 1 : Nat) : ENat) ≤ totalCondK D x y :=
      le_sInf (totalCandidateLengths_ge_succ_of_no_short D x y n hnone)
    have h_contra : ((n + 1 : Nat) : ENat) ≤ (n : ENat) := hbound.trans h
    norm_cast at h_contra
    omega
  · rintro ⟨p, hp_tot, hlen, hp_prod⟩
    exact (totalCondK_le_programLength hp_tot hp_prod).trans (by exact_mod_cast hlen)

lemma universalPrefix_total
    (D : Map) (code : Nat.Partrec.Code)
    (hc : ∀ p y,
      (code.eval (Encodable.encode (p, y))).map
        (fun r => (Encodable.decode r : Option BitString).getD []) =
          D (p, y))
    (p : BitString)
    (hp : IsTotalProgram D p) :
    IsTotalProgram universalDecompressor
      (unaryPrefix (Encodable.encode code) ++ p) := by
  intro y
  rw [universalSimulation, hc]
  exact hp y

lemma universalPrefix_produces
    (D : Map) (code : Nat.Partrec.Code)
    (hc : ∀ p y,
      (code.eval (Encodable.encode (p, y))).map
        (fun r => (Encodable.decode r : Option BitString).getD []) =
          D (p, y))
    {p x y : BitString}
    (hp : produces D p y x) :
    produces universalDecompressor
      (unaryPrefix (Encodable.encode code) ++ p) y x := by
  change x ∈ universalDecompressor _
  rw [universalSimulation, hc]
  exact hp

lemma totalCandidateLengths_universalPrefix
    (D : Map) (code : Nat.Partrec.Code)
    (hc : ∀ p y,
      (code.eval (Encodable.encode (p, y))).map
        (fun r => (Encodable.decode r : Option BitString).getD []) =
          D (p, y))
    (x y : BitString) :
    ∀ s ∈ totalCandidateLengths D x y,
      ∃ s' ∈ totalCandidateLengths universalDecompressor x y,
        s' ≤ s +
          ((unaryPrefix (Encodable.encode code)).length : ENat) := by
  rintro len_p ⟨p, hp_tot, hp_out, rfl⟩
  refine ⟨(programLength (unaryPrefix (Encodable.encode code) ++ p) : ENat), ?_, ?_⟩
  · refine ⟨unaryPrefix (Encodable.encode code) ++ p, ?_, ?_, rfl⟩
    · exact universalPrefix_total D code hc p hp_tot
    · exact universalPrefix_produces D code hc hp_out
  · dsimp [programLength]
    rw [List.length_append]
    push_cast
    rw [add_comm]

/-- An optimal decompressor for total conditional complexity exists. -/
theorem exists_isOptimalTotalConditional :
    ∃ U : Map, IsOptimalTotalConditional U := by
  refine ⟨universalDecompressor, isDecompressorUniversalDecompressor, fun D hD => ?_⟩
  obtain ⟨code, hc⟩ := existsCodeOfIsDecompressor D hD
  refine ⟨(unaryPrefix (Encodable.encode code)).length, fun x y => ?_⟩
  apply sInfLeSInfAdd
  exact totalCandidateLengths_universalPrefix D code hc x y

theorem IsStrongSetModel.mono {U : Map} {x : BitString}
    {S : Finset BitString} {hS : S.Nonempty} {epsilon epsilon' : Nat}
    (h : epsilon <= epsilon') (hstrong : IsStrongSetModel U x S hS epsilon) :
    IsStrongSetModel U x S hS epsilon' := by
  exact hstrong.trans (by exact_mod_cast h)

end Kolmogorov
