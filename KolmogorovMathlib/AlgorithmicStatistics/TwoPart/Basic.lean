import KolmogorovMathlib.AlgorithmicStatistics.Basic
import KolmogorovMathlib.AlgorithmicStatistics.CodedFiniteDistribution
import KolmogorovMathlib.Prefix.Symmetry

/-!
# Two-part descriptions: the vocabulary

The definitions the algorithmic-statistics layer is phrased in.

`logSlack c n = c * |bits n| + c` is the explicit `O(log n)` allowance and `sqrtSlack` the
`O(√(n log n))` one used for curve realization; their monotonicity, subadditivity and
absorption lemmas (`logSlack_add_constants`, `logSlack_mono_left`, `monotone_logSlack`,
`logSlack_add_le`, and the `sqrtSlack_*` counterparts) are proved here, with the arithmetic of
chaining slacks continued in `SlackArith`.

`setComplexity` is the complexity of a finite set through its canonical code.
`OptimalityDeficiencyLe` and `SetOptimalityDeficiencyLe` are the multiplicative form of the
optimality deficiency of `x` in a model, `IsIJDescription` and `InDescriptionProfile` the
two-part description of `x` by a set of complexity `i` and size `2 ^ j`,
`RealizedSetOptimalityGap` the tight realization of a gap, and `IsOptimalStochastic` and
`IsOptimalSetStochastic` the stochasticity notions built on them.  Each comes with its
monotonicity lemmas, and the module ends with the two endpoint witnesses of the profile — the
singleton and the full cube.
-/

namespace Kolmogorov

open CodedFiniteDistribution
/-- The logarithmic slack term `c * |bits n| + c`, the standard `O(log n)` allowance with
constant `c`. -/
def logSlack (c n : Nat) : Nat := c * (Nat.bits n).length + c

/-- The slack constant is additive: the slack of a sum of constants is the sum of the
slacks.  Every "two slacks at the same budget combine into one" lemma of the library is an
instance of this identity. -/
theorem logSlack_add_constants (c c' n : Nat) :
    logSlack (c + c') n = logSlack c n + logSlack c' n := by
  unfold logSlack; ring

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

/-- The slack is monotone in its visible-budget argument.  Every monotonicity lemma of the
library in that argument is an instance of this one. -/
theorem monotone_logSlack (c : Nat) : Monotone (logSlack c) := fun _ _ h => by
  unfold logSlack
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (length_natBits_mono h)) c

/-- The slack is monotone in its argument `n`: enlarging the visible parameter
budget only widens the logarithmic slack. -/
theorem logSlack_mono_right (c : Nat) {n m : Nat} (h : n ≤ m) :
    logSlack c n ≤ logSlack c m := monotone_logSlack c h

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

/-! ### Square-root slack for curve realization -/

/-- The square-root slack term `c * sqrt (n * |bits n|) + c`, an `O(sqrt (n log n))` allowance
with constant `c`. -/
def sqrtSlack (c n : Nat) : Nat := c * Nat.sqrt (n * (Nat.bits n).length) + c

/-- The square-root slack term is monotone in its constant. -/
theorem sqrtSlack_mono_left {c c' : Nat} (h : c ≤ c') (n : Nat) :
    sqrtSlack c n ≤ sqrtSlack c' n := by
  unfold sqrtSlack
  exact Nat.add_le_add (Nat.mul_le_mul_right _ h) h

/-- The square-root slack term is monotone in its argument. -/
theorem sqrtSlack_mono_right (c : Nat) {n m : Nat} (h : n ≤ m) :
    sqrtSlack c n ≤ sqrtSlack c m := by
  unfold sqrtSlack
  have h_inner : n * (Nat.bits n).length ≤ m * (Nat.bits m).length :=
    Nat.mul_le_mul h (length_natBits_mono h)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sqrt_le_sqrt h_inner)) c

/-- Enlarging the argument on the right does not decrease the square-root slack. -/
theorem sqrtSlack_le_sqrtSlack_add_right (c n m : Nat) :
    sqrtSlack c n ≤ sqrtSlack c (n + m) :=
  sqrtSlack_mono_right c (Nat.le_add_right n m)

/-- Enlarging the argument on the left does not decrease the square-root slack. -/
theorem sqrtSlack_le_sqrtSlack_add_left (c n m : Nat) :
    sqrtSlack c n ≤ sqrtSlack c (m + n) :=
  sqrtSlack_mono_right c (Nat.le_add_left n m)

/-- Set complexity using the canonical finite rational list code. -/
noncomputable def setComplexity (U : Map) (S : Finset BitString) (hS : S.Nonempty) : ENat :=
  KPPlain U (codedUniformOn S hS).code

/-- The optimality deficiency of `x` in the model `P` is at most `beta`, multiplicatively:
`2 ^ (-K(x)) ≤ 2 ^ beta * 2 ^ (-K(P.code)) * P.mass x`. -/
noncomputable def OptimalityDeficiencyLe (U : Map) (P : CodedFiniteDistribution) (x : BitString)
    (beta : Nat) : Prop :=
  complexityWeight (KPPlain U x) ≤ (2 : ENNReal) ^ beta *
      (complexityWeight (P.complexity U) * P.mass x)

/-- The optimality deficiency of `x` in the uniform model on the finite set `S` is at most
`beta`, i.e. `OptimalityDeficiencyLe` for `codedUniformOn S hS`. -/
noncomputable def SetOptimalityDeficiencyLe (U : Map) (S : Finset BitString) (hS : S.Nonempty)
    (x : BitString) (beta : Nat) : Prop :=
  OptimalityDeficiencyLe U (codedUniformOn S hS) x beta

/-- `x` lies in `A`, the set complexity of `A` is exactly `i`, its cardinality lies in
`[2 ^ j / 2, 2 ^ j]`, the prefix complexity of `x` is exactly `kx`, and `delta = i + j - kx`:
the optimality gap `delta` is realized tightly by the model `A`. -/
def RealizedSetOptimalityGap (U : Map) (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
    (delta i j kx : ℕ) : Prop :=
  x ∈ A ∧
  setComplexity U A hA = (i : ENat) ∧
  A.card ≤ 2 ^ j ∧
  (2 : ENNReal) ^ j / 2 ≤ (A.card : ENNReal) ∧
  HasPrefixComplexityValue U x kx ∧
  delta = i + j - kx

/-- `S` is an `(i, j)`-description of `x`: it contains `x`, its set complexity is at most `i`,
and it has at most `2 ^ j` elements. -/
noncomputable def IsIJDescription (U : Map) (x : BitString) (S : Finset BitString)
    (hS : S.Nonempty) (i j : Nat) : Prop :=
  x ∈ S ∧ setComplexity U S hS ≤ (i : ENat) ∧ S.card ≤ 2 ^ j

/-- `(i, j)` lies in the description profile of `x`: some nonempty finite set is an
`(i, j)`-description of `x`. -/
noncomputable def InDescriptionProfile (U : Map) (x : BitString) (i j : Nat) : Prop :=
  ∃ (S : Finset BitString) (hS : S.Nonempty), IsIJDescription U x S hS i j

/-- The `x` is `(alpha, beta)`-stochastic with respect to optimality deficiency. -/
noncomputable def IsOptimalStochastic (U : Map) (x : BitString) (alpha beta : Nat) : Prop :=
  ∃ P : CodedFiniteDistribution, P.IsProbability ∧ P.complexity U ≤ (alpha : ENat) ∧
      OptimalityDeficiencyLe U P x beta

/-- The `x` is `(alpha, beta)`-stochastic via a set model. -/
noncomputable def IsOptimalSetStochastic (U : Map) (x : BitString) (alpha beta : Nat) : Prop :=
  ∃ (S : Finset BitString) (hS : S.Nonempty), x ∈ S ∧ setComplexity U S hS ≤ (alpha : ENat) ∧
      SetOptimalityDeficiencyLe U S hS x beta

/-! ### Monotonicity lemmas -/

/-- Optimality deficiency at most `beta` implies optimality deficiency at most any
larger bound. -/
theorem OptimalityDeficiencyLe.mono_beta {U : Map} {P : CodedFiniteDistribution} {x : BitString}
    {beta beta' : Nat} (h : beta ≤ beta') (hdef : OptimalityDeficiencyLe U P x beta) :
        OptimalityDeficiencyLe U P x beta' := by
  unfold OptimalityDeficiencyLe at *
  calc
    _ ≤ (2 : ENNReal) ^ beta * (complexityWeight (P.complexity U) * P.mass x) := hdef
    _ ≤ (2 : ENNReal) ^ beta' * (complexityWeight (P.complexity U) * P.mass x) := by
      exact mul_le_mul_left (pow_le_pow_right₀ (by norm_num) h) _

/-- Set-optimality deficiency at most `beta` implies the same for any larger bound. -/
theorem SetOptimalityDeficiencyLe.mono_beta {U : Map} {S : Finset BitString} {hS : S.Nonempty}
    {x : BitString} {beta beta' : Nat} (h : beta ≤ beta')
        (hdef : SetOptimalityDeficiencyLe U S hS x beta) : SetOptimalityDeficiencyLe U S hS x beta'
            :=
  OptimalityDeficiencyLe.mono_beta h hdef

/-- An `(i, j)`-description is an `(i', j)`-description for `i ≤ i'`. -/
theorem IsIJDescription.mono_i {U : Map} {x : BitString} {S : Finset BitString} {hS : S.Nonempty}
    {i i' j : Nat} (h : i ≤ i') (hdesc : IsIJDescription U x S hS i j) : IsIJDescription U x S hS
        i' j := by
  unfold IsIJDescription at *
  rcases hdesc with ⟨hx, hcomp, hcard⟩
  exact ⟨hx, hcomp.trans (by exact_mod_cast h), hcard⟩

/-- An `(i, j)`-description is an `(i, j')`-description for `j ≤ j'`. -/
theorem IsIJDescription.mono_j {U : Map} {x : BitString} {S : Finset BitString} {hS : S.Nonempty}
    {i j j' : Nat} (h : j ≤ j') (hdesc : IsIJDescription U x S hS i j) : IsIJDescription U x S hS i
        j' := by
  unfold IsIJDescription at *
  rcases hdesc with ⟨hx, hcomp, hcard⟩
  exact ⟨hx, hcomp, hcard.trans (Nat.pow_le_pow_right (by decide) h)⟩

/-- The description profile is upward closed in the complexity coordinate. -/
theorem InDescriptionProfile.mono_i {U : Map} {x : BitString} {i i' j : Nat} (h : i ≤ i')
    (hprof : InDescriptionProfile U x i j) : InDescriptionProfile U x i' j := by
  rcases hprof with ⟨S, hS, hdesc⟩
  exact ⟨S, hS, hdesc.mono_i h⟩

/-- The description profile is upward closed in the size coordinate. -/
theorem InDescriptionProfile.mono_j {U : Map} {x : BitString} {i j j' : Nat} (h : j ≤ j')
    (hprof : InDescriptionProfile U x i j) : InDescriptionProfile U x i j' := by
  rcases hprof with ⟨S, hS, hdesc⟩
  exact ⟨S, hS, hdesc.mono_j h⟩

/-- Optimal stochasticity is preserved when the complexity bound is raised. -/
theorem IsOptimalStochastic.mono_alpha {U : Map} {x : BitString} {alpha alpha' beta : Nat}
    (h : alpha ≤ alpha') (hstoch : IsOptimalStochastic U x alpha beta) : IsOptimalStochastic U x
        alpha' beta := by
  rcases hstoch with ⟨P, hP, hcomp, hdef⟩
  exact ⟨P, hP, hcomp.trans (by exact_mod_cast h), hdef⟩

/-- Optimal stochasticity is preserved when the deficiency bound is raised. -/
theorem IsOptimalStochastic.mono_beta {U : Map} {x : BitString} {alpha beta beta' : Nat}
    (h : beta ≤ beta') (hstoch : IsOptimalStochastic U x alpha beta) : IsOptimalStochastic U x
        alpha beta' := by
  rcases hstoch with ⟨P, hP, hcomp, hdef⟩
  exact ⟨P, hP, hcomp, hdef.mono_beta h⟩

/-- Optimal set stochasticity is preserved when the complexity bound is raised. -/
theorem IsOptimalSetStochastic.mono_alpha {U : Map} {x : BitString} {alpha alpha' beta : Nat}
    (h : alpha ≤ alpha') (hstoch : IsOptimalSetStochastic U x alpha beta) : IsOptimalSetStochastic
        U x alpha' beta := by
  rcases hstoch with ⟨S, hS, hx, hcomp, hdef⟩
  exact ⟨S, hS, hx, hcomp.trans (by exact_mod_cast h), hdef⟩

/-- Optimal set stochasticity is preserved when the deficiency bound is raised. -/
theorem IsOptimalSetStochastic.mono_beta {U : Map} {x : BitString} {alpha beta beta' : Nat}
    (h : beta ≤ beta') (hstoch : IsOptimalSetStochastic U x alpha beta) : IsOptimalSetStochastic U
        x alpha beta' := by
  rcases hstoch with ⟨S, hS, hx, hcomp, hdef⟩
  exact ⟨S, hS, hx, hcomp, hdef.mono_beta h⟩

/-- For a member of the set, set-optimality deficiency at most `beta` is the
inequality between the weight of `KPPlain U x` and `2 ^ beta` times the uniform
weight of the model. -/
theorem setOptimalityDeficiencyLe_iff_of_mem {U : Map} {S : Finset BitString} {hS : S.Nonempty}
    {x : BitString} (hx : x ∈ S) {beta : Nat} :
  SetOptimalityDeficiencyLe U S hS x beta ↔ complexityWeight (KPPlain U x) ≤ (2 : ENNReal)^beta *
      (complexityWeight (setComplexity U S hS) * (S.card : ENNReal)⁻¹) := by
  unfold SetOptimalityDeficiencyLe OptimalityDeficiencyLe setComplexity
  rw [codedUniformOn_mass_of_mem S hS x hx]
  rfl

/-! ### Endpoint witnesses for `P_x` -/

/-- The singleton `{x}` puts `x` in the profile at size coordinate `0`, provided its
set complexity is at most `i`. -/
theorem inDescriptionProfile_singleton {U : Map} {x : BitString} {i : Nat}
    (h_comp : setComplexity U {x} (Finset.singleton_nonempty x) ≤ (i : ENat)) :
    InDescriptionProfile U x i 0 := by
  refine ⟨{x}, Finset.singleton_nonempty x, ?_⟩
  unfold IsIJDescription
  simp only [Finset.mem_singleton, true_and, Finset.card_singleton]
  exact ⟨h_comp, le_rfl⟩

/-- The set of strings of the length of `x` puts `x` in the profile at size
coordinate `|x|`, provided its set complexity is at most `i`. -/
theorem inDescriptionProfile_lengthUniform {U : Map} {x : BitString} {i : Nat}
    (h_comp : setComplexity U (stringsOfLength x.length) (codedStringsOfLength_nonempty x.length) ≤
        (i : ENat)) :
    InDescriptionProfile U x i x.length := by
  refine ⟨stringsOfLength x.length, codedStringsOfLength_nonempty x.length, ?_⟩
  unfold IsIJDescription
  simp only [mem_stringsOfLength, true_and]
  refine ⟨h_comp, ?_⟩
  rw [card_stringsOfLength]

end Kolmogorov
