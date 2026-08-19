import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileCardinality
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.OrdinalPlainRandomness

/-!
# From a `ProfileBoundary` to a `ProfileCurve`

The Section 3 realization theorem `exists_string_with_profile` consumes a
`ProfileCurve`, whose complexity parameter `m` bounds the *prefix* complexity of
the boundary code.  A Section 7 `ProfileBoundary` carries the *plain* complexity
`KP` of the same code, and its shape fields (`slope`, `height_zero_of_ge`,
`height_zero`) are exactly the curve conditions.  This module supplies the two
missing ingredients:

* `ProfileBoundary.k_P_le_add_height`: the boundary lies above the sufficiency
  line `i + h i ≥ k_P` (a consequence of the strict slope);
* `profileBoundary_KPPlain_le`: the prefix complexity of the boundary code is
  linear in `KP`.
-/

namespace Kolmogorov

/-- A profile boundary never dips below the sufficiency line `i + h i ≥ k_P`.
This is the geometric content of the strict-slope field: the height must lose at
least one unit per step, so it cannot reach `0` before coordinate `k_P`. -/
theorem ProfileBoundary.k_P_le_add_height {V : Map} (b : ProfileBoundary V) (i : ℕ) :
    b.k_P ≤ i + b.height i := by
  have key : ∀ n i : ℕ, b.k_P ≤ i + n → b.k_P ≤ i + b.height i := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      rcases Nat.lt_or_ge i b.k_P with hlt | hge
      · have hstep := ih (i + 1) (by omega)
        have hpos := b.height_pos_of_lt i hlt
        rcases b.slope i with hzero | hdrop
        · omega
        · omega
      · omega
  exact key b.k_P i (by omega)

/-- The prefix complexity of a boundary code is bounded by a constant multiple
of the stored plain complexity `KP`. -/
theorem profileBoundary_KPPlain_le
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ b : ProfileBoundary V,
      KPPlain U b.code ≤ ((C * b.KP + C : ℕ) : ENat) := by
  obtain ⟨cExact, hExact⟩ :=
    KP_le_condK_given_plain_program_length V U hV hU
  obtain ⟨cRemove, hRemove⟩ := KP_cond_remove_short_info U hU
  obtain ⟨cLength, hLength⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨cExact + cRemove + cLength + 3, ?_⟩
  intro b
  have hbFinite : plainK V b.code ≠ ⊤ :=
    condK_ne_top_of_optimal V hV b.code []
  have hbValue : plainK V b.code = (b.KP : ENat) := by
    rw [b.h_KP]
    exact (ENat.natCast_toNat hbFinite).symm
  have hbExact : KP U b.code (pairCode [] (Nat.bits b.KP)) ≤
      ((b.KP + cExact : ℕ) : ENat) := by
    exact_mod_cast hExact b.code [] b.KP hbValue
  have hbBits : KPPlain U (Nat.bits b.KP) ≤
      ((2 * (Nat.bits b.KP).length + cLength : ℕ) : ENat) :=
    hLength (Nat.bits b.KP)
  have hbPrefix : KPPlain U b.code ≤
      ((b.KP + cExact + (2 * (Nat.bits b.KP).length + cLength) + cRemove : ℕ) :
        ENat) := by
    calc
      KPPlain U b.code
          ≤ KP U b.code (pairCode [] (Nat.bits b.KP)) +
              KPPlain U (Nat.bits b.KP) + (cRemove : ENat) :=
        hRemove b.code [] (Nat.bits b.KP)
      _ ≤ ((b.KP + cExact : ℕ) : ENat) +
          ((2 * (Nat.bits b.KP).length + cLength : ℕ) : ENat) +
            (cRemove : ENat) := by gcongr
      _ = _ := by push_cast; ring
  refine hbPrefix.trans ?_
  have hbits : (Nat.bits b.KP).length ≤ b.KP := length_natBits_le_self b.KP
  have : b.KP + cExact + (2 * (Nat.bits b.KP).length + cLength) + cRemove ≤
      (cExact + cRemove + cLength + 3) * b.KP + (cExact + cRemove + cLength + 3) := by
    nlinarith [Nat.zero_le b.KP]
  exact_mod_cast this

/-- Every profile boundary is a `ProfileCurve` (with zero slack constant) for the
length `n_P`, the endpoint `k_P` and a complexity parameter linear in `KP`. -/
theorem profileBoundary_profileCurve
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ b : ProfileBoundary V,
      Nonempty (ProfileCurve U 0 b.n_P b.k_P (C * b.KP + C) b.height) := by
  obtain ⟨C, hC⟩ := profileBoundary_KPPlain_le V U hV hU
  refine ⟨C, fun b => ⟨?_⟩⟩
  refine
    { code := b.code
      curveDecodes := b.decodeCurve_code
      curveComplexity := hC b
      antitone := b.antitone
      slope := b.slope
      top := by rw [b.height_zero]
      bottom := ?_
      sufficient := ?_ }
  · have : logSlack 0 b.n_P = 0 := by simp [logSlack]
    rw [this, Nat.add_zero]
    exact b.height_zero_of_ge b.k_P le_rfl
  · intro i
    have h := b.k_P_le_add_height i
    have : logSlack 0 (b.n_P + i + b.height i) = 0 := by simp [logSlack]
    omega

end Kolmogorov
