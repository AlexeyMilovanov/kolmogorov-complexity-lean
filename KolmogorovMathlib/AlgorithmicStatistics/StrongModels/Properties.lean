import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongProfile
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.OmegaCount
import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.OrdinalBits

/-!
# Properties of strong models: total equivalence with the ordinal pair `(A,u)`

VS40 Section 7 ("Properties of strong models") opens with the observation that
an `ε`-strong model `A` for an `n`-bit string `x`, together with the ordinal
number `u` of `x` in `A`, is total-`(ε+O(1))`-equivalent to `x`:

* `KT(x | A,u) = O(1)` — given `(A,u)` a total program returns the `u`-th
  element of `A`;
* `KT(A,u | x) ≤ ε + O(1)` — given `x`, the strong program yields `A` and the
  ordinal `u` of `x` in `A` is then found by a total post-processing step.

Hence `x ≡^{ε+O(1)} (A,u)`.  The source uses this as an alternative route to
Proposition `part`.  This file formalizes the equivalence itself with explicit
uniform constants, keeping plain and total conditional complexity distinct.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution


/-- The stochasticity profile `Q_x`: the upward-closed set of all pairs
`(alpha, beta)` for which `x` is `(alpha, beta)`-stochastic. -/
def stochasticityProfileSet (U : Map) (x : BitString) : Set (Nat × Nat) :=
  {q | IsStochastic U x q.1 q.2}

/-- The stochasticity profile is coordinatewise upward closed. -/
theorem stochasticityProfileSet_isUpperSet
    (U : Map) (x : BitString) :
    IsUpperSet (stochasticityProfileSet U x) := by
  intro a b hab ha
  exact isStochastic_mono hab.1 hab.2 ha

/-- Source-faithful interface for VS40 Theorem `prop:add-noise`.

The source hypothesis is ordinary plain conditional randomness
`C(y | x) ≥ |y| - epsilon`; it is deliberately not replaced by prefix
randomness or by randomness conditional on a stochasticity-witness code.
The conclusion compares the complete stochasticity profiles of `x` and the
canonical pair `(x,y)`, with the stated
`O(epsilon + log |x| + log |y|)` radius. -/
def PropAddNoiseStatement (V U : Map) : Prop :=
  ∃ c : Nat, ∀ (x y : BitString) (epsilon : Nat),
    (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
    ProfileSetsWithinNeighborhood
      (stochasticityProfileSet U x)
      (stochasticityProfileSet U (pairCode x y))
      (c * epsilon + logSlack c x.length + logSlack c y.length)


/-- The coefficient is bounded by the standard add-noise radius. -/
theorem const_le_addNoiseRadius
    (d epsilon nx ny : Nat) :
    d ≤ d * epsilon + logSlack d nx + logSlack d ny := by
  simp [logSlack]
  omega

/-- Add-noise radii are additive in their coefficient. -/
theorem addNoiseRadius_add
    (c₁ c₂ epsilon nx ny : Nat) :
    (c₁ * epsilon + logSlack c₁ nx + logSlack c₁ ny) +
      (c₂ * epsilon + logSlack c₂ nx + logSlack c₂ ny) =
    (c₁ + c₂) * epsilon +
      logSlack (c₁ + c₂) nx + logSlack (c₁ + c₂) ny := by
  unfold logSlack
  ring

/-- Ordinary conditional randomness implies the corresponding conditional
prefix-randomness lower bound, up to the uniform machine-invariance constant.
This is the sound bridge from the hypothesis of `prop:add-noise` to the prefix
complexity used in randomness deficiency. -/
theorem prefix_randomness_of_plain_randomness
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon : Nat),
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      (y.length : ENat) ≤ KP U y x + (epsilon + c : Nat) := by
  obtain ⟨c, hc⟩ := condK_le_KP V U hV hU.isPrefixDecompressor
  refine ⟨c, fun x y epsilon hrandom => ?_⟩
  calc
    (y.length : ENat) ≤ condK V y x + (epsilon : ENat) := hrandom
    _ ≤ (KP U y x + (c : ENat)) + (epsilon : ENat) := by
      gcongr
      exact hc y x
    _ = KP U y x + (epsilon + c : Nat) := by
      rw [Nat.cast_add]
      ac_rfl

/-- A low-deficiency member cannot have an arbitrarily wide ordinal in its
finite-set model.  This bounds the noise width used in `prop:upward` by the
visible string length and deficiency budget. -/
theorem finiteSetLogCard_le_length_add_deficiency_log
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ A (hA : A.Nonempty) x n epsilon,
      x.length = n →
      x ∈ A →
      DeficiencyLe U (codedUniformOn A hA) x epsilon →
      finiteSetLogCard A ≤ n + epsilon + logSlack c n := by
  obtain ⟨cCond, hCond⟩ := KP_le_KPPlain U hU
  obtain ⟨cLen, hLen⟩ := KPPlain_le_length_add_log U hU
  refine ⟨cCond + cLen + 2, ?_⟩
  intro A hA x n epsilon hxn hx hdef
  have hcard := finiteSetLogCard_le_condKP_add_of_deficiency hx hdef
  have hbound :
      (finiteSetLogCard A : ENat) ≤
        ((n + epsilon + logSlack (cCond + cLen + 2) n : Nat) : ENat) := by
    calc
      (finiteSetLogCard A : ENat)
          ≤ KP U x (codedUniformOn A hA).code + (epsilon : ENat) := hcard
      _ ≤ (KPPlain U x + (cCond : ENat)) + (epsilon : ENat) := by
            gcongr
            exact hCond x (codedUniformOn A hA).code
      _ ≤ ((n + 2 * (Nat.bits n).length + cLen : Nat) : ENat) +
            (cCond : ENat) + (epsilon : ENat) := by
            gcongr
            simpa [hxn] using hLen x
      _ = ((n + 2 * (Nat.bits n).length + cLen + cCond + epsilon : Nat) :
            ENat) := by
            push_cast
            rfl
      _ ≤ ((n + epsilon + logSlack (cCond + cLen + 2) n : Nat) : ENat) := by
            apply Nat.cast_le.mpr
            unfold logSlack
            have hmul :
                2 * (Nat.bits n).length ≤
                  (cCond + cLen + 2) * (Nat.bits n).length :=
              Nat.mul_le_mul_right _ (by omega)
            omega
  exact_mod_cast hbound

/-- Two directed stochasticity transports with the same coordinate slack
assemble into the corresponding symmetric profile neighborhood. -/
theorem stochasticityProfileSet_neighborhood_of_uniform_shifts
    (U : Map) (x y : BitString) (delta : Nat)
    (hxy : ∀ alpha beta,
      IsStochastic U x alpha beta →
        IsStochastic U y (alpha + delta) (beta + delta))
    (hyx : ∀ alpha beta,
      IsStochastic U y alpha beta →
        IsStochastic U x (alpha + delta) (beta + delta)) :
    ProfileSetsWithinNeighborhood
      (stochasticityProfileSet U x)
      (stochasticityProfileSet U y) delta := by
  constructor
  · rintro ⟨alpha, beta⟩ hstoch
    refine ⟨(alpha + delta, beta + delta), hxy alpha beta hstoch, ?_⟩
    simp [natPairLInfDistance]
  · rintro ⟨alpha, beta⟩ hstoch
    refine ⟨(alpha + delta, beta + delta), hyx alpha beta hstoch, ?_⟩
    simp [natPairLInfDistance]

/-- Source-faithful interface for VS40 Proposition `prop:upward`.

The ordinary add-noise endpoint and total-equivalence arguments are proved.
The unconditional upward endpoint still requires the budget-scale
charged-heavy transport recorded in `UpwardConditional.lean`. -/
def PropUpwardStatement (U T : Map) : Prop :=
  ∃ c : Nat, ∀ x A (hA : A.Nonempty) n epsilon,
    x.length = n →
    x ∈ A →
    IsStrongSetModel T x A hA epsilon →
    DeficiencyLe U (codedUniformOn A hA) x epsilon →
    ProfileSetsWithinNeighborhood
      (stochasticityProfileSet U x)
      (stochasticityProfileSet U (codedUniformOn A hA).code)
      (c * epsilon + logSlack c n)

/-- The explicit uniform budget for the hereditary theorem's
`O(delta + (epsilon + log n) * sqrt n)` error. -/
def hereditarySlack (c delta epsilon n : Nat) : Nat :=
  c * delta + c * (epsilon + (Nat.bits n).length) * Nat.sqrt n + c

theorem hereditarySlack_mono_c {c1 c2 delta epsilon n : Nat} (h : c1 ≤ c2) :
    hereditarySlack c1 delta epsilon n ≤ hereditarySlack c2 delta epsilon n := by
  unfold hereditarySlack
  gcongr

theorem hereditarySlack_mono_delta {c delta1 delta2 epsilon n : Nat} (h : delta1 ≤ delta2) :
    hereditarySlack c delta1 epsilon n ≤ hereditarySlack c delta2 epsilon n := by
  unfold hereditarySlack
  gcongr

theorem hereditarySlack_mono_epsilon {c delta epsilon1 epsilon2 n : Nat} (h : epsilon1 ≤ epsilon2) :
    hereditarySlack c delta epsilon1 n ≤ hereditarySlack c delta epsilon2 n := by
  unfold hereditarySlack
  gcongr

theorem hereditarySlack_mono_n {c delta epsilon n1 n2 : Nat} (h : n1 ≤ n2) :
    hereditarySlack c delta epsilon n1 ≤ hereditarySlack c delta epsilon n2 := by
  unfold hereditarySlack
  gcongr
  · exact length_natBits_mono h

theorem hereditarySlack_mono
    {c₁ c₂ delta₁ delta₂ epsilon₁ epsilon₂ n₁ n₂ : Nat}
    (hc : c₁ ≤ c₂) (hδ : delta₁ ≤ delta₂)
    (hε : epsilon₁ ≤ epsilon₂) (hn : n₁ ≤ n₂) :
    hereditarySlack c₁ delta₁ epsilon₁ n₁ ≤
      hereditarySlack c₂ delta₂ epsilon₂ n₂ := by
  calc
    hereditarySlack c₁ delta₁ epsilon₁ n₁
      ≤ hereditarySlack c₂ delta₁ epsilon₁ n₁ := hereditarySlack_mono_c hc
    _ ≤ hereditarySlack c₂ delta₂ epsilon₁ n₁ := hereditarySlack_mono_delta hδ
    _ ≤ hereditarySlack c₂ delta₂ epsilon₂ n₁ := hereditarySlack_mono_epsilon hε
    _ ≤ hereditarySlack c₂ delta₂ epsilon₂ n₂ := hereditarySlack_mono_n hn

/-- Rigorous interface for VS40 Lemma `prop:min_hereditary`.
It bounds `K(Omega_{K(A)} | A)` for a minimal statistic `A`. -/
def PropMinHereditaryStatement (V : Map) : Prop :=
  ∃ cKappa cOut : Nat,
    ∀ x n A (hA : A.Nonempty) delta (q : Nat.Partrec.Code),
      IsCodeFor q V →
      x.length = n →
      IsMinimalModel V x A hA delta (logSlack cKappa n) →
      condK V (omegaFixedCode q (plainK V (codedUniformOn A hA).code).toNat)
        (codedUniformOn A hA).code ≤ (cOut * delta + logSlack cOut n : ENat)

/-- Rigorous interface for VS40 Lemma `lch`.
The third conclusion is `C(H | Ω_{C(H)})`, correcting a typo in some drafts that
had it backwards. -/
def LemmaLchStatement (V T : Map) : Prop :=
  ∃ c : Nat,
    ∀ x n A (hA : A.Nonempty) epsilon alpha (q : Nat.Partrec.Code),
      IsCodeFor q V →
      x.length = n →
      x ∈ A →
      epsilon ≤ n →
      alpha * 2 < n.sqrt →
      IsNormalString V T x epsilon alpha →
      ∃ H, ∃ hH : H.Nonempty,
        x ∈ H ∧
        IsStrongSetModel T x H hH epsilon ∧
        plainSetComplexity V H hH + (finiteSetLogCard H : ENat) ≤
          plainSetComplexity V A hA + (finiteSetLogCard A : ENat) +
            (c * (alpha + logSlack c n) * Nat.sqrt n : ENat) ∧
        condK V (codedUniformOn H hH).code
          (omegaFixedCode q (plainK V (codedUniformOn H hH).code).toNat) ≤
            (c * Nat.sqrt n + logSlack c n : ENat) ∧
        plainSetComplexity V H hH ≤ plainSetComplexity V A hA + (alpha : ENat)

/-- Source-faithful interface for VS40 Theorem `thm:hereditary`. -/
def ThmHereditaryStatement (V T : Map) : Prop :=
  ∃ cKappa cNormal : Nat,
    ∀ x n A (hA : A.Nonempty) epsilon delta,
      x.length = n →
      IsStrongSetModel T x A hA epsilon →
      IsSufficientStatistic V x A hA epsilon →
      IsNormalString V T x epsilon epsilon →
      IsMinimalModel V x A hA delta (logSlack cKappa n) →
      IsNormalString V T (codedUniformOn A hA).code
        (hereditarySlack cNormal delta epsilon n)
        (hereditarySlack cNormal delta epsilon n)

/-- Source-faithful interface for VS40 Theorem `thm:step-wise`, keeping its
ordinary plain and total conditional conclusions distinct. -/
def ThmStepWiseStatement (V T : Map) : Prop :=
  ∃ cKappa cPlain cTotal : Nat,
    ∀ x n A (hA : A.Nonempty) B (hB : B.Nonempty)
        epsilon delta,
      x.length = n →
      IsSufficientStatistic V x A hA epsilon →
      IsSufficientStatistic V x B hB epsilon →
      IsMinimalModel V x A hA delta
        (epsilon + logSlack cKappa n) →
      condK V (codedUniformOn A hA).code
          (codedUniformOn B hB).code ≤
        (cPlain * delta + logSlack cPlain n : ENat) ∧
      (IsStrongSetModel T x A hA epsilon →
        totalCondK T (codedUniformOn A hA).code
            (codedUniformOn B hB).code ≤
          (cTotal * (epsilon + delta) +
            logSlack cTotal n : ENat))

end Kolmogorov
