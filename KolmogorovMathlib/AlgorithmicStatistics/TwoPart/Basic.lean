/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.AlgorithmicStatistics.Basic
import KolmogorovMathlib.AlgorithmicStatistics.CodedFiniteDistribution
import KolmogorovMathlib.Prefix.Symmetry

/-!
# Two-Part Stochasticity Basics
-/

namespace Kolmogorov

/-- Logarithmic slack with constant `c`. -/
def logSlack (c n : Nat) : Nat := c * (Nat.bits n).length + c

/-- The slack is monotone in its constant `c`: a larger constant only widens the
allowed logarithmic budget. -/
theorem logSlack_mono_left {c c' : Nat} (h : c ≤ c') (n : Nat) :
    logSlack c n ≤ logSlack c' n := by
  unfold logSlack
  exact Nat.add_le_add (Nat.mul_le_mul_right _ h) h

/-- The binary length `(Nat.bits ·).length` is monotone: it equals `Nat.size`,
which is monotone. -/
theorem length_natBits_mono {n m : Nat} (h : n ≤ m) :
    (Nat.bits n).length ≤ (Nat.bits m).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  exact Nat.size_le_size h

/-- The slack is monotone in its argument `n`: enlarging the visible parameter
budget only widens the logarithmic slack. -/
theorem logSlack_mono_right (c : Nat) {n m : Nat} (h : n ≤ m) :
    logSlack c n ≤ logSlack c m := by
  unfold logSlack
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (length_natBits_mono h)) c

/-- Adding to the visible parameter budget can only widen the slack. -/
theorem logSlack_le_logSlack_add_right (c n m : Nat) :
    logSlack c n ≤ logSlack c (n + m) :=
  logSlack_mono_right c (Nat.le_add_right n m)

/-- Adding to the visible parameter budget (on the left) can only widen the slack. -/
theorem logSlack_le_logSlack_add_left (c n m : Nat) :
    logSlack c n ≤ logSlack c (m + n) :=
  logSlack_mono_right c (Nat.le_add_left n m)

/-- The binary length of a sum is at most one more than the sum of the binary
lengths.  This is the carry bound `size (a + b) ≤ max (size a) (size b) + 1`. -/
theorem length_natBits_add_le (a b : Nat) :
    (Nat.bits (a + b)).length ≤ (Nat.bits a).length + (Nat.bits b).length + 1 := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  rw [Nat.size_le]
  calc a + b
      < 2 ^ Nat.size a + 2 ^ Nat.size b := Nat.add_lt_add (Nat.lt_size_self a) (Nat.lt_size_self b)
    _ ≤ 2 ^ (Nat.size a + Nat.size b) + 2 ^ (Nat.size a + Nat.size b) :=
        Nat.add_le_add
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _))
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _))
    _ = 2 ^ (Nat.size a + Nat.size b + 1) := by rw [pow_succ]; ring

/-- The slack is subadditive in its argument: encoding two visible parameters
costs no more than the sum of their separate slacks.  This is the key absorption
lemma for folding a `logSlack c (n + i + j)` term into a single visible-parameter
slack once `i` and `j` have been bounded by the available parameters. -/
theorem logSlack_add_le (c a b : Nat) :
    logSlack c (a + b) ≤ logSlack c a + logSlack c b := by
  unfold logSlack
  have h := length_natBits_add_le a b
  nlinarith [Nat.mul_le_mul_left c h, Nat.zero_le ((Nat.bits a).length),
    Nat.zero_le ((Nat.bits b).length)]

/-- Set complexity using the canonical finite rational list code. -/
noncomputable def setComplexity (U : Map) (S : Finset BitString) (hS : S.Nonempty) : ENat :=
  KPPlain U (codedUniformOn S hS).code

/-- Optimality deficiency for a probability model. -/
noncomputable def OptimalityDeficiencyLe (U : Map) (P : CodedFiniteDistribution) (x : BitString) (beta : Nat) : Prop :=
  complexityWeight (KPPlain U x) ≤ (2 : ENNReal) ^ beta * (complexityWeight (P.complexity U) * P.mass x)

/-- Optimality deficiency for a finite-set uniform model. -/
noncomputable def SetOptimalityDeficiencyLe (U : Map) (S : Finset BitString) (hS : S.Nonempty) (x : BitString) (beta : Nat) : Prop :=
  OptimalityDeficiencyLe U (codedUniformOn S hS) x beta

/-- The tight realized finite-set optimality gap. -/
def RealizedSetOptimalityGap (U : Map) (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (delta i j kx : ℕ) : Prop :=
  x ∈ A ∧
  setComplexity U A hA = (i : ENat) ∧
  A.card ≤ 2 ^ j ∧
  (2 : ENNReal) ^ j / 2 ≤ (A.card : ENNReal) ∧
  HasPrefixComplexityValue U x kx ∧
  delta = i + j - kx

/-- A model `S` is an `(i,j)`-description for `x`. -/
noncomputable def IsIJDescription (U : Map) (x : BitString) (S : Finset BitString) (hS : S.Nonempty) (i j : Nat) : Prop :=
  x ∈ S ∧ setComplexity U S hS ≤ (i : ENat) ∧ S.card ≤ 2 ^ j

/-- The description profile predicate `InDescriptionProfile U x i j`. -/
noncomputable def InDescriptionProfile (U : Map) (x : BitString) (i j : Nat) : Prop :=
  ∃ (S : Finset BitString) (hS : S.Nonempty), IsIJDescription U x S hS i j

/-- The `x` is `(alpha, beta)`-stochastic with respect to optimality deficiency. -/
noncomputable def IsOptimalStochastic (U : Map) (x : BitString) (alpha beta : Nat) : Prop :=
  ∃ P : CodedFiniteDistribution, P.IsProbability ∧ P.complexity U ≤ (alpha : ENat) ∧ OptimalityDeficiencyLe U P x beta

/-- The `x` is `(alpha, beta)`-stochastic via a set model. -/
noncomputable def IsOptimalSetStochastic (U : Map) (x : BitString) (alpha beta : Nat) : Prop :=
  ∃ (S : Finset BitString) (hS : S.Nonempty), x ∈ S ∧ setComplexity U S hS ≤ (alpha : ENat) ∧ SetOptimalityDeficiencyLe U S hS x beta
/-! ### Monotonicity lemmas -/
theorem OptimalityDeficiencyLe.mono_beta {U : Map} {P : CodedFiniteDistribution} {x : BitString} {beta beta' : Nat} (h : beta ≤ beta') (hdef : OptimalityDeficiencyLe U P x beta) : OptimalityDeficiencyLe U P x beta' := by
  unfold OptimalityDeficiencyLe at *
  calc
    _ ≤ (2 : ENNReal) ^ beta * (complexityWeight (P.complexity U) * P.mass x) := hdef
    _ ≤ (2 : ENNReal) ^ beta' * (complexityWeight (P.complexity U) * P.mass x) := by
      exact mul_le_mul_left (pow_le_pow_right₀ (by norm_num) h) _

theorem SetOptimalityDeficiencyLe.mono_beta {U : Map} {S : Finset BitString} {hS : S.Nonempty} {x : BitString} {beta beta' : Nat} (h : beta ≤ beta') (hdef : SetOptimalityDeficiencyLe U S hS x beta) : SetOptimalityDeficiencyLe U S hS x beta' :=
  OptimalityDeficiencyLe.mono_beta h hdef

theorem IsIJDescription.mono_i {U : Map} {x : BitString} {S : Finset BitString} {hS : S.Nonempty} {i i' j : Nat} (h : i ≤ i') (hdesc : IsIJDescription U x S hS i j) : IsIJDescription U x S hS i' j := by
  unfold IsIJDescription at *
  rcases hdesc with ⟨hx, hcomp, hcard⟩
  exact ⟨hx, hcomp.trans (by exact_mod_cast h), hcard⟩

theorem IsIJDescription.mono_j {U : Map} {x : BitString} {S : Finset BitString} {hS : S.Nonempty} {i j j' : Nat} (h : j ≤ j') (hdesc : IsIJDescription U x S hS i j) : IsIJDescription U x S hS i j' := by
  unfold IsIJDescription at *
  rcases hdesc with ⟨hx, hcomp, hcard⟩
  exact ⟨hx, hcomp, hcard.trans (Nat.pow_le_pow_right (by decide) h)⟩

theorem InDescriptionProfile.mono_i {U : Map} {x : BitString} {i i' j : Nat} (h : i ≤ i') (hprof : InDescriptionProfile U x i j) : InDescriptionProfile U x i' j := by
  rcases hprof with ⟨S, hS, hdesc⟩
  exact ⟨S, hS, hdesc.mono_i h⟩

theorem InDescriptionProfile.mono_j {U : Map} {x : BitString} {i j j' : Nat} (h : j ≤ j') (hprof : InDescriptionProfile U x i j) : InDescriptionProfile U x i j' := by
  rcases hprof with ⟨S, hS, hdesc⟩
  exact ⟨S, hS, hdesc.mono_j h⟩

theorem IsOptimalStochastic.mono_alpha {U : Map} {x : BitString} {alpha alpha' beta : Nat} (h : alpha ≤ alpha') (hstoch : IsOptimalStochastic U x alpha beta) : IsOptimalStochastic U x alpha' beta := by
  rcases hstoch with ⟨P, hP, hcomp, hdef⟩
  exact ⟨P, hP, hcomp.trans (by exact_mod_cast h), hdef⟩

theorem IsOptimalStochastic.mono_beta {U : Map} {x : BitString} {alpha beta beta' : Nat} (h : beta ≤ beta') (hstoch : IsOptimalStochastic U x alpha beta) : IsOptimalStochastic U x alpha beta' := by
  rcases hstoch with ⟨P, hP, hcomp, hdef⟩
  exact ⟨P, hP, hcomp, hdef.mono_beta h⟩

theorem IsOptimalSetStochastic.mono_alpha {U : Map} {x : BitString} {alpha alpha' beta : Nat} (h : alpha ≤ alpha') (hstoch : IsOptimalSetStochastic U x alpha beta) : IsOptimalSetStochastic U x alpha' beta := by
  rcases hstoch with ⟨S, hS, hx, hcomp, hdef⟩
  exact ⟨S, hS, hx, hcomp.trans (by exact_mod_cast h), hdef⟩

theorem IsOptimalSetStochastic.mono_beta {U : Map} {x : BitString} {alpha beta beta' : Nat} (h : beta ≤ beta') (hstoch : IsOptimalSetStochastic U x alpha beta) : IsOptimalSetStochastic U x alpha beta' := by
  rcases hstoch with ⟨S, hS, hx, hcomp, hdef⟩
  exact ⟨S, hS, hx, hcomp, hdef.mono_beta h⟩

theorem setOptimalityDeficiencyLe_iff_of_mem {U : Map} {S : Finset BitString} {hS : S.Nonempty} {x : BitString} (hx : x ∈ S) {beta : Nat} :
  SetOptimalityDeficiencyLe U S hS x beta ↔ complexityWeight (KPPlain U x) ≤ (2 : ENNReal)^beta * (complexityWeight (setComplexity U S hS) * (S.card : ENNReal)⁻¹) := by
  unfold SetOptimalityDeficiencyLe OptimalityDeficiencyLe setComplexity
  rw [codedUniformOn_mass_of_mem S hS x hx]
  rfl

/-! ### Endpoint witnesses for `P_x` -/

theorem inDescriptionProfile_singleton {U : Map} {x : BitString} {i : Nat}
    (h_comp : setComplexity U {x} (Finset.singleton_nonempty x) ≤ (i : ENat)) :
    InDescriptionProfile U x i 0 := by
  refine ⟨{x}, Finset.singleton_nonempty x, ?_⟩
  unfold IsIJDescription
  simp only [Finset.mem_singleton, true_and, Finset.card_singleton]
  exact ⟨h_comp, le_rfl⟩

theorem inDescriptionProfile_lengthUniform {U : Map} {x : BitString} {i : Nat}
    (h_comp : setComplexity U (stringsOfLength x.length) (codedStringsOfLength_nonempty x.length) ≤ (i : ENat)) :
    InDescriptionProfile U x i x.length := by
  refine ⟨stringsOfLength x.length, codedStringsOfLength_nonempty x.length, ?_⟩
  unfold IsIJDescription
  simp only [memStringsOfLength, true_and]
  refine ⟨h_comp, ?_⟩
  rw [cardStringsOfLength]

end Kolmogorov
