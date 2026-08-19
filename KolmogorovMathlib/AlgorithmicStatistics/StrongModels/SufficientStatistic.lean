import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainProfile

/-!
# Strong sufficient statistics and minimal models
-/

namespace Kolmogorov

/-- The fixed integer convention for `log #S`: the least `j` such that
`#S ≤ 2^j`.  This is `⌈log₂ #S⌉`; in particular, a singleton has value zero. -/
def finiteSetLogCard (S : Finset BitString) : Nat :=
  Nat.clog 2 S.card

/-- A finite set `S` is an `epsilon`-sufficient statistic for `x` if its
ordinary plain optimality deficiency is at most `epsilon`:
`C(S) + ⌈log₂ #S⌉ ≤ C(x) + epsilon`. -/
def IsSufficientStatistic
    (V : Map) (x : BitString) (S : Finset BitString) (hS : S.Nonempty)
    (epsilon : Nat) : Prop :=
  x ∈ S ∧
  plainSetComplexity V S hS + (finiteSetLogCard S : ENat) ≤
    plainK V x + (epsilon : ENat)

/-- A model `S` for `x` is `(delta, kappa)`-minimal in the source's sense:
there is no competing model `B` whose plain set complexity improves on that of
`S` by at least `delta` while its ordinary optimality deficiency is at most
`kappa` worse.

The common `C(x)` term has been cancelled from the deficiency comparison, so
the latter is written as
`C(B) + log #B ≤ C(S) + log #S + kappa`.  This definition intentionally does
not assume that `S` is sufficient; sufficiency is a separate hypothesis in the
source theorems. -/
def IsMinimalModel
    (V : Map) (x : BitString) (S : Finset BitString) (hS : S.Nonempty)
    (delta kappa : Nat) : Prop :=
  x ∈ S ∧
  ∀ (B : Finset BitString) (hB : B.Nonempty),
    x ∈ B →
    plainSetComplexity V B hB + (finiteSetLogCard B : ENat) ≤
      plainSetComplexity V S hS + (finiteSetLogCard S : ENat) +
        (kappa : ENat) →
    ¬ plainSetComplexity V B hB + (delta : ENat) ≤
      plainSetComplexity V S hS

/-! ### Basic facts about the canonical log-cardinality convention -/

/-- The defining bracket of `finiteSetLogCard`: `#S ≤ 2 ^ ⌈log₂ #S⌉`. -/
theorem finiteSetLogCard_spec (S : Finset BitString) :
    S.card ≤ 2 ^ finiteSetLogCard S :=
  Nat.le_pow_clog (by norm_num) S.card

/-- Full specification of the ceiling convention: a size budget `j` contains
`S` exactly when it is at least `finiteSetLogCard S`. -/
theorem finiteSetLogCard_le_iff (S : Finset BitString) (j : Nat) :
    finiteSetLogCard S ≤ j ↔ S.card ≤ 2 ^ j := by
  unfold finiteSetLogCard
  exact Nat.clog_le_iff_le_pow (by norm_num)

/-- Tightness of `finiteSetLogCard` for sets with more than one element:
`2 ^ (⌈log₂ #S⌉ - 1) < #S`. -/
theorem finiteSetLogCard_pred_lt
    (S : Finset BitString) (h : 1 < S.card) :
    2 ^ (finiteSetLogCard S - 1) < S.card :=
  Nat.pow_pred_clog_lt_self (by norm_num) h

/-- A singleton has zero log-cardinality. -/
@[simp] theorem finiteSetLogCard_singleton (x : BitString) :
    finiteSetLogCard {x} = 0 := by
  unfold finiteSetLogCard
  simp

/-! ### Monotonicity of the S4 parameters

Sufficiency is monotone: enlarging the deficiency budget only weakens the
requirement.  Minimality is monotone in `delta` and antitone in `kappa`: as the
source notes, smaller `delta` and larger `kappa` give a stronger property, so a
`(delta, kappa)`-minimal model is also `(delta', kappa')`-minimal for
`delta ≤ delta'` and `kappa' ≤ kappa`. -/

theorem IsSufficientStatistic.mono
    {V : Map} {x : BitString} {S : Finset BitString} {hS : S.Nonempty}
    {epsilon epsilon' : Nat} (hε : epsilon ≤ epsilon')
    (h : IsSufficientStatistic V x S hS epsilon) :
    IsSufficientStatistic V x S hS epsilon' := by
  have hcast : (epsilon : ENat) ≤ (epsilon' : ENat) := Nat.cast_le.mpr hε
  exact ⟨h.1, h.2.trans (by gcongr)⟩

theorem IsMinimalModel.mono
    {V : Map} {x : BitString} {S : Finset BitString} {hS : S.Nonempty}
    {delta delta' kappa kappa' : Nat}
    (hδ : delta ≤ delta') (hκ : kappa' ≤ kappa)
    (h : IsMinimalModel V x S hS delta kappa) :
    IsMinimalModel V x S hS delta' kappa' := by
  have hδcast : (delta : ENat) ≤ (delta' : ENat) := Nat.cast_le.mpr hδ
  have hκcast : (kappa' : ENat) ≤ (kappa : ENat) := Nat.cast_le.mpr hκ
  refine ⟨h.1, ?_⟩
  intro B hB hxB hprem hconcl
  refine h.2 B hB hxB (hprem.trans (by gcongr)) ((?_ : _ ≤ _).trans hconcl)
  gcongr

theorem finiteSetLogCard_mono
    {S B : Finset BitString}
    (h : S.card ≤ B.card) :
    finiteSetLogCard S ≤ finiteSetLogCard B := by
  unfold finiteSetLogCard
  exact Nat.clog_mono_right 2 h

end Kolmogorov
