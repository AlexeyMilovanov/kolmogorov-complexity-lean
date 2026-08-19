import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Partition
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalMaps

/-!
# Strong description profiles

This file starts S3 of VS40 Section 7.  It keeps the ordinary plain-complexity
machine `V` separate from the optimal total-conditional machine `T`.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- A plain `(i,j)`-description whose model code is also total-computable from
the displayed string within `epsilon` bits. -/
noncomputable def IsStrongPlainIJDescription
    (V T : Map) (x : BitString) (S : Finset BitString)
    (hS : S.Nonempty) (epsilon i j : Nat) : Prop :=
  IsPlainIJDescription V x S hS i j ∧
    IsStrongSetModel T x S hS epsilon

/-- Membership in the source's strong profile `P_x(epsilon)`. -/
noncomputable def InStrongDescriptionProfile
    (V T : Map) (x : BitString) (epsilon i j : Nat) : Prop :=
  ∃ (S : Finset BitString) (hS : S.Nonempty),
    IsStrongPlainIJDescription V T x S hS epsilon i j

/-- The strong description profile as a subset of the parameter plane. -/
def strongDescriptionProfileSet
    (V T : Map) (x : BitString) (epsilon : Nat) :
    Set (Nat × Nat) :=
  {q | InStrongDescriptionProfile V T x epsilon q.1 q.2}

theorem IsStrongPlainIJDescription.mono_epsilon
    {V T : Map} {x : BitString} {S : Finset BitString}
    {hS : S.Nonempty} {epsilon epsilon' i j : Nat}
    (hε : epsilon ≤ epsilon')
    (h : IsStrongPlainIJDescription V T x S hS epsilon i j) :
    IsStrongPlainIJDescription V T x S hS epsilon' i j :=
  ⟨h.1, h.2.mono hε⟩

theorem IsStrongPlainIJDescription.mono_i
    {V T : Map} {x : BitString} {S : Finset BitString}
    {hS : S.Nonempty} {epsilon i i' j : Nat}
    (hii : i ≤ i')
    (h : IsStrongPlainIJDescription V T x S hS epsilon i j) :
    IsStrongPlainIJDescription V T x S hS epsilon i' j :=
  ⟨h.1.mono_i hii, h.2⟩

theorem IsStrongPlainIJDescription.mono_j
    {V T : Map} {x : BitString} {S : Finset BitString}
    {hS : S.Nonempty} {epsilon i j j' : Nat}
    (hjj : j ≤ j')
    (h : IsStrongPlainIJDescription V T x S hS epsilon i j) :
    IsStrongPlainIJDescription V T x S hS epsilon i j' :=
  ⟨h.1.mono_j hjj, h.2⟩

theorem InStrongDescriptionProfile.mono_epsilon
    {V T : Map} {x : BitString} {epsilon epsilon' i j : Nat}
    (hε : epsilon ≤ epsilon')
    (h : InStrongDescriptionProfile V T x epsilon i j) :
    InStrongDescriptionProfile V T x epsilon' i j := by
  obtain ⟨S, hS, hdesc⟩ := h
  exact ⟨S, hS, hdesc.mono_epsilon hε⟩

theorem InStrongDescriptionProfile.mono_i
    {V T : Map} {x : BitString} {epsilon i i' j : Nat}
    (hii : i ≤ i')
    (h : InStrongDescriptionProfile V T x epsilon i j) :
    InStrongDescriptionProfile V T x epsilon i' j := by
  obtain ⟨S, hS, hdesc⟩ := h
  exact ⟨S, hS, hdesc.mono_i hii⟩

theorem InStrongDescriptionProfile.mono_j
    {V T : Map} {x : BitString} {epsilon i j j' : Nat}
    (hjj : j ≤ j')
    (h : InStrongDescriptionProfile V T x epsilon i j) :
    InStrongDescriptionProfile V T x epsilon i j' := by
  obtain ⟨S, hS, hdesc⟩ := h
  exact ⟨S, hS, hdesc.mono_j hjj⟩

/-- The source's immediate inclusion `P_x(epsilon) ⊆ P_x`. -/
theorem inPlainDescriptionProfile_of_inStrongDescriptionProfile
    {V T : Map} {x : BitString} {epsilon i j : Nat}
    (h : InStrongDescriptionProfile V T x epsilon i j) :
    InPlainDescriptionProfile V x i j := by
  obtain ⟨S, hS, hdesc⟩ := h
  exact ⟨S, hS, hdesc.1⟩

theorem strongDescriptionProfileSet_subset_plain
    (V T : Map) (x : BitString) (epsilon : Nat) :
    strongDescriptionProfileSet V T x epsilon ⊆
      plainDescriptionProfileSet V x :=
  fun _ h => inPlainDescriptionProfile_of_inStrongDescriptionProfile h

theorem strongDescriptionProfileSet_mono_epsilon
    (V T : Map) (x : BitString) {epsilon epsilon' : Nat}
    (hε : epsilon ≤ epsilon') :
    strongDescriptionProfileSet V T x epsilon ⊆
      strongDescriptionProfileSet V T x epsilon' :=
  fun _ h => h.mono_epsilon hε

theorem strongDescriptionProfileSet_isUpperSet
    (V T : Map) (x : BitString) (epsilon : Nat) :
    IsUpperSet (strongDescriptionProfileSet V T x epsilon) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨hi, hj⟩ h
  exact h.mono_i hi |>.mono_j hj

/-- Canonical code of the singleton finite-set model. -/
noncomputable def canonicalSingletonSetCode (x : BitString) : BitString :=
  canonicalUniformCodeOfList [x]

theorem canonicalSingletonSetCode_computable :
    Computable canonicalSingletonSetCode :=
  canonicalUniformCodeOfList_computable.comp
    (Computable.list_cons.comp Computable.id (Computable.const []))

@[simp] theorem canonicalSingletonSetCode_eq (x : BitString) :
    canonicalSingletonSetCode x =
      (codedUniformOn {x} (Finset.singleton_nonempty x)).code := by
  unfold canonicalSingletonSetCode
  convert canonicalUniformCodeOfList_canonicalFinsetList
    {x} (Finset.singleton_nonempty x) using 1
  unfold canonicalFinsetList
  aesop

/-- A singleton model has ordinary plain complexity at most the plain complexity of its
member plus a uniform constant. -/
theorem plainSetComplexity_singleton_le_plainK
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x : BitString,
      plainSetComplexity V {x} (Finset.singleton_nonempty x) ≤
        plainK V x + (c : ENat) := by
  obtain ⟨cMap, hMap⟩ :=
    plainKMapLe V hV canonicalSingletonSetCode
      canonicalSingletonSetCode_computable
  refine ⟨cMap, fun x => ?_⟩
  unfold plainSetComplexity
  rw [← canonicalSingletonSetCode_eq]
  exact hMap x

/-- A singleton model has ordinary plain complexity at most the length of its
member plus a uniform constant. -/
theorem plainSetComplexity_singleton_le_length
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x : BitString,
      plainSetComplexity V {x} (Finset.singleton_nonempty x) ≤
        ((x.length + c : Nat) : ENat) := by
  obtain ⟨cMap, hMap⟩ :=
    plainKMapLe V hV canonicalSingletonSetCode
      canonicalSingletonSetCode_computable
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  refine ⟨cMap + cLen, fun x => ?_⟩
  unfold plainSetComplexity
  rw [← canonicalSingletonSetCode_eq]
  calc
    plainK V (canonicalSingletonSetCode x)
        ≤ plainK V x + (cMap : ENat) := hMap x
    _ ≤ ((x.length : Nat) : ENat) + (cLen : ENat) +
          (cMap : ENat) := by
      gcongr
      exact hLen x
    _ = ((x.length + (cMap + cLen) : Nat) : ENat) := by
      push_cast
      ac_rfl

/-- Singleton models are uniformly strong: their canonical code is a fixed
computable function of their member. -/
theorem singleton_isStrongSetModel
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ x : BitString,
      IsStrongSetModel T x {x} (Finset.singleton_nonempty x) c := by
  obtain ⟨c, hc⟩ :=
    totalCondK_map_self_le_const T hT canonicalSingletonSetCode
      canonicalSingletonSetCode_computable
  refine ⟨c, fun x => ?_⟩
  unfold IsStrongSetModel
  rw [← canonicalSingletonSetCode_eq]
  exact hc x

/-- The other immediate source identity: for a string of length `n`, allowing
`n + O(1)` total-description bits recovers the full ordinary profile exactly.

For low-complexity profile points, run the ordinary set-description program at
the empty context and ignore the varying condition.  For higher-complexity
points, replace the model by the singleton `{x}`. -/
theorem strongDescriptionProfile_eq_plain_of_length
    (V : Map) (hV : isOptimalConditional V)
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ (x : BitString) (n : Nat), x.length = n →
      strongDescriptionProfileSet V T x (n + c) =
        plainDescriptionProfileSet V x := by
  obtain ⟨cTotal, hTotal⟩ :=
    totalCondK_le_plainK V T hV.1 hT
  obtain ⟨cSingletonPlain, hSingletonPlain⟩ :=
    plainSetComplexity_singleton_le_length V hV
  obtain ⟨cSingletonTotal, hSingletonTotal⟩ :=
    singleton_isStrongSetModel T hT
  let c := cTotal + cSingletonPlain + cSingletonTotal + 1
  refine ⟨c, ?_⟩
  intro x n hn
  apply Set.Subset.antisymm
  · exact strongDescriptionProfileSet_subset_plain V T x (n + c)
  · rintro ⟨i, j⟩ hprofile
    obtain ⟨S, hS, hdesc⟩ := hprofile
    by_cases hi : i < n + cSingletonPlain
    · refine ⟨S, hS, hdesc, ?_⟩
      unfold IsStrongSetModel plainSetComplexity at *
      calc
        totalCondK T (codedUniformOn S hS).code x
            ≤ plainK V (codedUniformOn S hS).code +
                (cTotal : ENat) :=
          hTotal _ _
        _ ≤ (i : ENat) + (cTotal : ENat) := by
          gcongr
          exact hdesc.2.1
        _ ≤ ((n + c : Nat) : ENat) := by
          exact_mod_cast (show i + cTotal ≤ n + c by
            dsimp [c]
            omega)
    · let hSingleton : ({x} : Finset BitString).Nonempty :=
        Finset.singleton_nonempty x
      refine ⟨{x}, hSingleton, ?_, ?_⟩
      · refine ⟨Finset.mem_singleton.mpr rfl, ?_, ?_⟩
        · have hbound := hSingletonPlain x
          rw [hn] at hbound
          exact hbound.trans (by
            exact_mod_cast (show n + cSingletonPlain ≤ i by omega))
        · simpa using Nat.one_le_two_pow
      · exact (hSingletonTotal x).mono (by
          dsimp [c]
          omega)

/-- A string is `(epsilon,delta)`-normal when its ordinary profile and its
`epsilon`-strong profile are within `delta` in the concrete `ℓ∞` neighborhood. -/
def IsNormalString
    (V T : Map) (x : BitString) (epsilon delta : Nat) : Prop :=
  ProfileSetsWithinNeighborhood
    (plainDescriptionProfileSet V x)
    (strongDescriptionProfileSet V T x epsilon)
    delta

/-- A string is strange precisely when it is not normal at the displayed
parameters. -/
def IsStrangeString
    (V T : Map) (x : BitString) (epsilon delta : Nat) : Prop :=
  ¬ IsNormalString V T x epsilon delta

/-- With the length-level strength budget from
`strongDescriptionProfile_eq_plain_of_length`, every string is normal with
zero profile error. -/
theorem normal_of_length_strength
    (V : Map) (hV : isOptimalConditional V)
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ (x : BitString) (n : Nat), x.length = n →
      IsNormalString V T x (n + c) 0 := by
  obtain ⟨c, hc⟩ :=
    strongDescriptionProfile_eq_plain_of_length V hV T hT
  refine ⟨c, fun x n hn => ?_⟩
  unfold IsNormalString
  rw [hc x n hn]
  exact ProfileSetsWithinNeighborhood.refl _

theorem IsNormalString.mono_delta
    {V T : Map} {x : BitString} {epsilon delta delta' : Nat}
    (hδ : delta ≤ delta')
    (h : IsNormalString V T x epsilon delta) :
    IsNormalString V T x epsilon delta' :=
  h.mono hδ

/-- Increasing the permitted strength budget can only improve normality.  The
new strong-profile points already lie in the ordinary profile, while every old
strong-profile witness remains available. -/
theorem IsNormalString.mono_epsilon
    {V T : Map} {x : BitString} {epsilon epsilon' delta : Nat}
    (hε : epsilon ≤ epsilon')
    (h : IsNormalString V T x epsilon delta) :
    IsNormalString V T x epsilon' delta := by
  unfold IsNormalString at *
  constructor
  · intro q hq
    obtain ⟨q', hq', hdist⟩ := h.1 q hq
    exact ⟨q',
      strongDescriptionProfileSet_mono_epsilon V T x hε hq',
      hdist⟩
  · intro q hq
    exact ⟨q,
      strongDescriptionProfileSet_subset_plain V T x epsilon' hq,
      by simp [natPairLInfDistance]⟩

end Kolmogorov
