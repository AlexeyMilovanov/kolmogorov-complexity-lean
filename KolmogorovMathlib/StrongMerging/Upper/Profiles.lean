import Mathlib.Data.Set.Finite.List
import KolmogorovMathlib.StrongMerging.Basic
import KolmogorovMathlib.StrongMerging.Coding.Information

/-!
# Profiles of extractable common information (blueprint M06, `UpperCommonProfiles`)

`sublinear-merging.tex`, section `sec:extractability-envelope` (tex ~608–676), and the blueprint
paragraph "Portfolio and exact normalization" (tex ~4040–4058).  For two finite models `A, B` and
a nonnegative integer `r`:

* `ordinaryCommonProfile V A B r` is `𝓔_p(r) = max ({0} ∪ {C(P) : C(P | A) ≤ r, C(P | B) ≤ r})`;
* `totalCommonProfile V A B r` is `𝓔_T(r) = max ({0} ∪ {C(P) : CT(P | A) ≤ r, CT(P | B) ≤ r})`.

The objects `P` are arbitrary encoded objects (`BitString`s): they need not be models and need not
contain anything.  The conditions are the canonical model codes `canonicalFiniteSetCode A`,
`canonicalFiniteSetCode B`.  Complexities are the exact `ℕ∞` values, and `CT` is taken at the
canonical total interpreter `universalDecompressor` (S01).  The maxima are finite: each of the
finitely many programs of length at most `r` has at most one output on a fixed condition.
`ordinaryCommonProfile_spec` and `totalCommonProfile_spec` state that the `sSup` is that maximum.
The profiles are used only in the analysis; no computability is claimed.

The module also fixes the bounds of T06 and T07 that are built from the ordinary profile:

* `extractabilityEnvelope V n e A B` is the envelope
  `Φ = min_{0 ≤ r ≤ n} (H + r + √((H + r) max {0, I - 𝓔_p(r)}))`, with
  `H = e + ⌈log₂ (n + 2)⌉` and `I = I(A : B)` (`setMutualInfo`);
* `mutualInfoEnvelope V n e A B` is the mutual-information scale `H + √(H max {0, I})`;
* `baseBudget_le_extractabilityEnvelope` gives `H ≤ Φ`, and
  `extractabilityEnvelope_le_mutualInfoEnvelope` gives `Φ ≤ H + √(H max {0, I})` (the term
  `r = 0`, using only `𝓔_p(0) ≥ 0`).

The definitions live in `namespace Kolmogorov.StrongMerging`, next to the shared definitions of
`StrongMerging.Basic`, so the headline statements and the `Upper` proof modules both see them
unqualified.
-/

namespace Kolmogorov.StrongMerging

/-! ### Finiteness of the profile sets -/

/-- Only finitely many objects are produced from a fixed condition `y` by programs of length at
most `r`: each is the unique output of one of the finitely many such programs. -/
private theorem finite_produces_le (D : Map) (y : BitString) (r : ℕ) :
    {P : BitString | ∃ p : BitString, p.length ≤ r ∧ produces D p y P}.Finite := by
  refine ((List.finite_length_le Bool r).biUnion fun p _ =>
    (show {P : BitString | P ∈ D (p, y)}.Subsingleton from
      fun _ hP _ hQ => Part.mem_unique hP hQ).finite).subset ?_
  rintro P ⟨p, hp, hP⟩
  exact Set.mem_biUnion hp hP

/-- Only finitely many objects `P` have `C(P | y) ≤ r`. -/
private theorem finite_condK_le (D : Map) (y : BitString) (r : ℕ) :
    {P : BitString | condK D P y ≤ (r : ℕ∞)}.Finite :=
  (finite_produces_le D y r).subset fun P hP => by
    obtain ⟨p, hp, hP⟩ := (condK_le_iff D P y r).1 hP
    exact ⟨p, hp, hP⟩

/-- Only finitely many objects `P` have `CT(P | y) ≤ r`. -/
private theorem finite_totalCondK_le (D : Map) (y : BitString) (r : ℕ) :
    {P : BitString | totalCondK D P y ≤ (r : ℕ∞)}.Finite :=
  (finite_produces_le D y r).subset fun P hP => by
    obtain ⟨p, -, hp, hP⟩ := (totalCondK_le_iff D P y r).1 hP
    exact ⟨p, hp, hP⟩

/-- For a predicate `Q` with finitely many solutions, `sSup ({0} ∪ {C(P) : Q P})` bounds every
`C(P)` with `Q P` (for an optimal `V`), and is `0` or attained. -/
private theorem sSup_insert_zero_spec (V : Map) (hV : isOptimalConditional V)
    (Q : BitString → Prop) (hQ : {P | Q P}.Finite) :
    (∀ P, Q P → plainK V P ≤
        ((sSup (insert 0 {k : ℕ | ∃ P, plainK V P = (k : ℕ∞) ∧ Q P}) : ℕ) : ℕ∞)) ∧
      (sSup (insert 0 {k : ℕ | ∃ P, plainK V P = (k : ℕ∞) ∧ Q P}) = 0 ∨
        ∃ P, plainK V P =
          ((sSup (insert 0 {k : ℕ | ∃ P, plainK V P = (k : ℕ∞) ∧ Q P}) : ℕ) : ℕ∞) ∧ Q P) := by
  set K : Set ℕ := {k : ℕ | ∃ P, plainK V P = (k : ℕ∞) ∧ Q P} with hK
  have hKfin : K.Finite := by
    refine (hQ.image fun P => (plainK V P).toNat).subset ?_
    rintro k ⟨P, hPk, hQP⟩
    exact ⟨P, hQP, by simp only [hPk, ENat.toNat_natCast]⟩
  have hbdd : BddAbove (insert 0 K) := (hKfin.insert 0).bddAbove
  obtain ⟨cV, hcV⟩ := plainK_le_length V hV
  refine ⟨fun P hP => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_natCast_add (hcV P))
    have hkK : k ∈ insert 0 K := Set.mem_insert_of_mem _ ⟨P, hk.symm, hP⟩
    rw [← hk]
    exact_mod_cast le_csSup hbdd hkK
  · rcases Nat.sSup_mem (Set.insert_nonempty 0 K) hbdd with h | ⟨P, hP, hQP⟩
    · exact Or.inl h
    · exact Or.inr ⟨P, hP, hQP⟩

/-! ### M06: the two profiles -/

/-- **The ordinary common-information profile** `𝓔_p(r)` (blueprint node M06,
`UpperCommonProfiles`; section `sec:extractability-envelope`):
`𝓔_p(r) = max ({0} ∪ {C(P) : C(P | A) ≤ r, C(P | B) ≤ r})`.  It is the largest plain complexity of
an arbitrary encoded object `P` that has ordinary conditional descriptions of length at most `r`
from both models.  `P` need not be a model and need not contain anything.  Conditions are the
canonical model codes.  Complexities are the exact `ℕ∞` values, so an object of infinite
complexity contributes nothing.  The set is finite (`ordinaryCommonProfile_spec`), so `sSup` is its
maximum.  No computability is claimed. -/
noncomputable def ordinaryCommonProfile (V : Map) (A B : Finset BitString) (r : ℕ) : ℕ :=
  sSup (insert 0 {k : ℕ | ∃ P : BitString, plainK V P = (k : ℕ∞) ∧
    condK V P (canonicalFiniteSetCode A) ≤ (r : ℕ∞) ∧
    condK V P (canonicalFiniteSetCode B) ≤ (r : ℕ∞)})

/-- **The total common-information profile** `𝓔_T(r)` (blueprint node M06):
`𝓔_T(r) = max ({0} ∪ {C(P) : CT(P | A) ≤ r, CT(P | B) ≤ r})`.  `C(P)` is plain complexity, and the
conditional complexity is total, at the canonical interpreter `universalDecompressor`. -/
noncomputable def totalCommonProfile (V : Map) (A B : Finset BitString) (r : ℕ) : ℕ :=
  sSup (insert 0 {k : ℕ | ∃ P : BitString, plainK V P = (k : ℕ∞) ∧
    totalCondK universalDecompressor P (canonicalFiniteSetCode A) ≤ (r : ℕ∞) ∧
    totalCondK universalDecompressor P (canonicalFiniteSetCode B) ≤ (r : ℕ∞)})

/-- **`𝓔_p(r)` is a finite maximum with zero adjoined** (node M06, obligation "finiteness from
bounded program sets").  For an optimal `V`, every object `P` with `C(P | A), C(P | B) ≤ r` has
`C(P) ≤ 𝓔_p(r)`.  Moreover `𝓔_p(r)` is either `0` or attained by such an object.

Proof sketch: by `condK_le_iff`, every such `P` is the output on the condition `code A` of a
program of length at most `r`.  A `Part` has at most one output, so these `P` form a finite set,
and the set of their complexities is bounded above.  Then `le_csSup` gives the first claim and
`Nat.sSup_mem` the second.  `plainK V P ≠ ⊤` for optimal `V`. -/
theorem ordinaryCommonProfile_spec (V : Map) (hV : isOptimalConditional V)
    (A B : Finset BitString) (r : ℕ) :
    (∀ P : BitString, condK V P (canonicalFiniteSetCode A) ≤ (r : ℕ∞) →
        condK V P (canonicalFiniteSetCode B) ≤ (r : ℕ∞) →
          plainK V P ≤ (ordinaryCommonProfile V A B r : ℕ∞)) ∧
      (ordinaryCommonProfile V A B r = 0 ∨ ∃ P : BitString,
        plainK V P = (ordinaryCommonProfile V A B r : ℕ∞) ∧
        condK V P (canonicalFiniteSetCode A) ≤ (r : ℕ∞) ∧
        condK V P (canonicalFiniteSetCode B) ≤ (r : ℕ∞)) := by
  have hfin : {P : BitString | condK V P (canonicalFiniteSetCode A) ≤ (r : ℕ∞) ∧
      condK V P (canonicalFiniteSetCode B) ≤ (r : ℕ∞)}.Finite :=
    (finite_condK_le V (canonicalFiniteSetCode A) r).subset fun _ hP => hP.1
  obtain ⟨h1, h2⟩ := sSup_insert_zero_spec V hV _ hfin
  exact ⟨fun P hA hB => h1 P ⟨hA, hB⟩, h2⟩

/-- **`𝓔_T(r)` is a finite maximum with zero adjoined** (node M06).  For an optimal `V`, every
object `P` with `CT(P | A), CT(P | B) ≤ r` has `C(P) ≤ 𝓔_T(r)`.  Moreover `𝓔_T(r)` is either `0`
or attained by such an object.

Proof sketch: as for `ordinaryCommonProfile_spec`, with `totalCondK_le_iff`. -/
theorem totalCommonProfile_spec (V : Map) (hV : isOptimalConditional V)
    (A B : Finset BitString) (r : ℕ) :
    (∀ P : BitString,
        totalCondK universalDecompressor P (canonicalFiniteSetCode A) ≤ (r : ℕ∞) →
        totalCondK universalDecompressor P (canonicalFiniteSetCode B) ≤ (r : ℕ∞) →
          plainK V P ≤ (totalCommonProfile V A B r : ℕ∞)) ∧
      (totalCommonProfile V A B r = 0 ∨ ∃ P : BitString,
        plainK V P = (totalCommonProfile V A B r : ℕ∞) ∧
        totalCondK universalDecompressor P (canonicalFiniteSetCode A) ≤ (r : ℕ∞) ∧
        totalCondK universalDecompressor P (canonicalFiniteSetCode B) ≤ (r : ℕ∞)) := by
  have hfin : {P : BitString |
      totalCondK universalDecompressor P (canonicalFiniteSetCode A) ≤ (r : ℕ∞) ∧
      totalCondK universalDecompressor P (canonicalFiniteSetCode B) ≤ (r : ℕ∞)}.Finite :=
    (finite_totalCondK_le universalDecompressor (canonicalFiniteSetCode A) r).subset
      fun _ hP => hP.1
  obtain ⟨h1, h2⟩ := sSup_insert_zero_spec V hV _ hfin
  exact ⟨fun P hA hB => h1 P ⟨hA, hB⟩, h2⟩

/-! ### The envelopes of T06 and T07 -/

/-- **The extractability envelope** `Φ` (`eq:extractability-envelope`):
`Φ = min_{0 ≤ r ≤ n} (H + r + √((H + r) max {0, I - 𝓔_p(r)}))`.  The minimum is over the integers
`r ∈ {0, …, n}`.  Here `H = e + ⌈log₂ (n + 2)⌉` (`baseBudget n e`), `I = C(A) + C(B) - C(A, B)` is
the signed mutual information (`setMutualInfo`), and `𝓔_p` is `ordinaryCommonProfile`.  It is a
mathematical finite minimum and is never computed by a selector.  `Φ ≥ H ≥ 1`. -/
noncomputable def extractabilityEnvelope (V : Map) (n e : ℕ) (A B : Finset BitString) : ℝ :=
  (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one fun r =>
    ((baseBudget n e + r : ℕ) : ℝ) +
      Real.sqrt (((baseBudget n e + r : ℕ) : ℝ) *
        max 0 (setMutualInfo V A B - ordinaryCommonProfile V A B r))

/-- The envelope dominates the base budget: `H ≤ Φ`, because every term of the minimum is at
least `H`.  Since `H ≥ 1`, also `Φ ≥ 1`. -/
theorem baseBudget_le_extractabilityEnvelope (V : Map) (n e : ℕ) (A B : Finset BitString) :
    (baseBudget n e : ℝ) ≤ extractabilityEnvelope V n e A B := by
  unfold extractabilityEnvelope
  refine Finset.le_inf' _ _ fun r _ => ?_
  have h1 := Real.sqrt_nonneg (((baseBudget n e + r : ℕ) : ℝ) *
    max 0 (setMutualInfo V A B - ordinaryCommonProfile V A B r))
  have h2 : ((baseBudget n e : ℕ) : ℝ) ≤ ((baseBudget n e + r : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right _ _
  linarith

/-- **The mutual-information scale** `H + √(H max {0, I(A : B)})`
(`eq:mutual-information-refinement`).  Here `H = e + ⌈log₂ (n + 2)⌉` (`baseBudget n e`) and
`I(A : B) = C(A) + C(B) - C(A, B)` is the signed mutual information (`setMutualInfo`).  It is the
`r = 0` term of `extractabilityEnvelope`, with `𝓔_p(0)` replaced by `0`. -/
noncomputable def mutualInfoEnvelope (V : Map) (n e : ℕ) (A B : Finset BitString) : ℝ :=
  (baseBudget n e : ℝ) + Real.sqrt ((baseBudget n e : ℝ) * max 0 (setMutualInfo V A B))

/-- The envelope is at most the mutual-information scale, `Φ ≤ H + √(H max {0, I})`.  This is the
term `r = 0` of the minimum, with `𝓔_p(0) ≥ 0` (`eq:mutual-information-refinement`).  It is how
T07 follows from T06, and it needs no empty extraction program. -/
theorem extractabilityEnvelope_le_mutualInfoEnvelope (V : Map) (n e : ℕ)
    (A B : Finset BitString) :
    extractabilityEnvelope V n e A B ≤ mutualInfoEnvelope V n e A B := by
  have hE : (0 : ℝ) ≤ (ordinaryCommonProfile V A B 0 : ℝ) := Nat.cast_nonneg _
  have hm : max 0 (setMutualInfo V A B - ordinaryCommonProfile V A B 0) ≤
      max 0 (setMutualInfo V A B) := max_le_max le_rfl (by linarith)
  have hH : (0 : ℝ) ≤ (baseBudget n e : ℝ) := Nat.cast_nonneg _
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hm hH)
  unfold extractabilityEnvelope mutualInfoEnvelope
  refine (Finset.inf'_le _ (Finset.mem_range.mpr (Nat.succ_pos n))).trans ?_
  simp only [add_zero]
  linarith

end Kolmogorov.StrongMerging
