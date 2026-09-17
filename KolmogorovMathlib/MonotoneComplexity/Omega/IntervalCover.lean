/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealCantor

/-!
# Irredundant families of intervals (SUV p. 170, the measure estimate behind Theorem 115)

SUV p. 170 bounds the "bad" covering family of Theorem 115 by an elementary argument: a
*finite non-redundant* union of intervals may be split into two disjoint sub-families, so
the total length is at most twice what a single disjoint family gives.

What that argument really proves is that **an irredundant finite family of open intervals
has multiplicity at most two** — if a point belonged to three of them, the one with the
smallest left endpoint and the one with the largest right endpoint would already cover the
third.  This module proves that, and the estimate it yields: if every member `I` of the
family carries mass `ν(I) > (c/2)·|I|` for a measure `ν` of total mass at most `1` living on
the rationals, then the union has Lebesgue measure at most `4/c`.

Nothing here is effective; it is the measure-theoretic core of
`exists_const_apriori_neighbourhood_le`, isolated so that the remaining work on that leaf is
the enumeration only.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-! ### Irredundant families -/

/-- A finite family of rational intervals is *irredundant* if no member is contained in the
union of the others. -/
def Irredundant (G : Finset (ℚ × ℚ)) : Prop :=
  ∀ I ∈ G, ¬ (ratInterval I ⊆ ⋃ J ∈ G.erase I, ratInterval J)

/-- Every finite family of intervals has an irredundant subfamily with the same union. -/
theorem exists_irredundant_subfamily (F : Finset (ℚ × ℚ)) :
    ∃ G ⊆ F, Irredundant G ∧ (⋃ I ∈ G, ratInterval I) = ⋃ I ∈ F, ratInterval I := by
  classical
  induction F using Finset.strongInduction with
  | _ F ih =>
    by_cases hirr : Irredundant F
    · exact ⟨F, Finset.Subset.refl F, hirr, rfl⟩
    · rw [Irredundant] at hirr
      push Not at hirr
      obtain ⟨I, hIF, hIsub⟩ := hirr
      have hlt : F.erase I ⊂ F := Finset.erase_ssubset hIF
      obtain ⟨G, hGsub, hGirr, hGeq⟩ := ih (F.erase I) hlt
      refine ⟨G, hGsub.trans (Finset.erase_subset _ _), hGirr, ?_⟩
      rw [hGeq]
      refine le_antisymm ?_ ?_
      · exact Set.iUnion₂_subset fun J hJ =>
          Set.subset_iUnion₂ (s := fun J (_ : J ∈ F) => ratInterval J) J
            (Finset.mem_of_mem_erase hJ)
      · refine Set.iUnion₂_subset fun J hJ => ?_
        by_cases hJI : J = I
        · subst hJI
          exact hIsub
        · exact Set.subset_iUnion₂ (s := fun J (_ : J ∈ F.erase I) => ratInterval J) J
            (Finset.mem_erase.2 ⟨hJI, hJ⟩)

/-- If `C` starts no earlier than `A` and ends no later than `B`, and all three intervals
share a point, then `C` is covered by `A ∪ B`. -/
theorem ratInterval_subset_union {A B C : ℚ × ℚ} {x : ℝ}
    (hA : x ∈ ratInterval A) (hB : x ∈ ratInterval B)
    (hl : ((A.1 : ℚ) : ℝ) ≤ ((C.1 : ℚ) : ℝ)) (hr : ((C.2 : ℚ) : ℝ) ≤ ((B.2 : ℚ) : ℝ)) :
    ratInterval C ⊆ ratInterval A ∪ ratInterval B := by
  rw [ratInterval, Set.mem_Ioo] at hA hB
  intro y hy
  rw [ratInterval, Set.mem_Ioo] at hy
  by_cases hcase : y < ((A.2 : ℚ) : ℝ)
  · exact Or.inl (Set.mem_Ioo.2 ⟨lt_of_le_of_lt hl hy.1, hcase⟩)
  · push Not at hcase
    refine Or.inr (Set.mem_Ioo.2 ⟨?_, lt_of_lt_of_le hy.2 hr⟩)
    exact lt_of_lt_of_le hB.1 (le_trans hA.2.le hcase)

open scoped Classical in
/-- **Multiplicity two.**  An irredundant family of open intervals covers no point three
times. -/
theorem card_filter_le_two {G : Finset (ℚ × ℚ)} (hG : Irredundant G) (x : ℝ) :
    (G.filter (fun I => x ∈ ratInterval I)).card ≤ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨I₁, I₂, I₃, h1, h2, h3, h12, h13, h23⟩ := Finset.two_lt_card_iff.1 hcon
  have hx : ∀ I ∈ G.filter (fun I => x ∈ ratInterval I), x ∈ ratInterval I :=
    fun I hI => (Finset.mem_filter.1 hI).2
  have hmem : ∀ I ∈ G.filter (fun I => x ∈ ratInterval I), I ∈ G :=
    fun I hI => (Finset.mem_filter.1 hI).1
  have key : ∀ A B C : ℚ × ℚ, A ∈ G → B ∈ G → C ∈ G → A ≠ C → B ≠ C →
      x ∈ ratInterval A → x ∈ ratInterval B →
      ((A.1 : ℚ) : ℝ) ≤ ((C.1 : ℚ) : ℝ) → ((C.2 : ℚ) : ℝ) ≤ ((B.2 : ℚ) : ℝ) → False := by
    intro A B C hAG hBG hCG hAC hBC hAx hBx hl hr
    refine hG C hCG ?_
    refine (ratInterval_subset_union hAx hBx hl hr).trans (Set.union_subset ?_ ?_)
    · exact Set.subset_iUnion₂ (s := fun J (_ : J ∈ G.erase C) => ratInterval J) A
        (Finset.mem_erase.2 ⟨hAC, hAG⟩)
    · exact Set.subset_iUnion₂ (s := fun J (_ : J ∈ G.erase C) => ratInterval J) B
        (Finset.mem_erase.2 ⟨hBC, hBG⟩)
  have tri : ∀ P Q R : ℚ × ℚ, P ∈ G → Q ∈ G → R ∈ G → P ≠ Q → P ≠ R → Q ≠ R →
      x ∈ ratInterval P → x ∈ ratInterval Q → x ∈ ratInterval R →
      ((P.1 : ℚ) : ℝ) ≤ ((Q.1 : ℚ) : ℝ) → ((P.1 : ℚ) : ℝ) ≤ ((R.1 : ℚ) : ℝ) → False := by
    intro P Q R hP hQ hR hPQ hPR hQR hxP hxQ hxR hl1 hl2
    rcases le_total ((Q.2 : ℚ) : ℝ) ((R.2 : ℚ) : ℝ) with hqr | hqr
    · rcases le_total ((Q.2 : ℚ) : ℝ) ((P.2 : ℚ) : ℝ) with hqp | hqp
      · exact key P P Q hP hP hQ hPQ hPQ hxP hxP hl1 hqp
      · exact key P R Q hP hR hQ hPQ hQR.symm hxP hxR hl1 hqr
    · rcases le_total ((R.2 : ℚ) : ℝ) ((P.2 : ℚ) : ℝ) with hrp | hrp
      · exact key P P R hP hP hR hPR hPR hxP hxP hl2 hrp
      · exact key P Q R hP hQ hR hPR hQR hxP hxQ hl2 hqr
  have hx1 := hx I₁ h1
  have hx2 := hx I₂ h2
  have hx3 := hx I₃ h3
  have hg1 := hmem I₁ h1
  have hg2 := hmem I₂ h2
  have hg3 := hmem I₃ h3
  rcases le_total ((I₁.1 : ℚ) : ℝ) ((I₂.1 : ℚ) : ℝ) with a12 | a12
  · rcases le_total ((I₁.1 : ℚ) : ℝ) ((I₃.1 : ℚ) : ℝ) with a13 | a13
    · exact tri I₁ I₂ I₃ hg1 hg2 hg3 h12 h13 h23 hx1 hx2 hx3 a12 a13
    · exact tri I₃ I₁ I₂ hg3 hg1 hg2 h13.symm h23.symm h12 hx3 hx1 hx2 a13 (a13.trans a12)
  · rcases le_total ((I₂.1 : ℚ) : ℝ) ((I₃.1 : ℚ) : ℝ) with a23 | a23
    · exact tri I₂ I₁ I₃ hg2 hg1 hg3 h12.symm h23 h13 hx2 hx1 hx3 a12 a23
    · exact tri I₃ I₁ I₂ hg3 hg1 hg2 h13.symm h23.symm h12 hx3 hx1 hx2 (a23.trans a12) a23

/-! ### The measure estimate -/

/-- A finite sum of `ℝ≥0∞`-valued series may be taken inside the series. -/
theorem finsetSum_tsum_comm {α β : Type*} (s : Finset α) (f : α → β → ℝ≥0∞) :
    (∑ i ∈ s, ∑' b, f i b) = ∑' b, ∑ i ∈ s, f i b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, ih, ← ENNReal.tsum_add]
    exact tsum_congr fun b => (Finset.sum_insert (f := fun i => f i b) hi).symm

/-- The Lebesgue measure of a rational interval is its length. -/
theorem volume_ratInterval (I : ℚ × ℚ) : volume (ratInterval I) = ratIntervalLength I := by
  rw [ratInterval, Real.volume_Ioo, ratIntervalLength]

open scoped Classical in
/-- **SUV p. 170, the measure estimate.**  Let `ν` be a mass distribution on the rationals
of total mass at most `1`.  If every interval of a finite family `F` satisfies
`c·|I| ≤ 2·ν(I)` — the book's "the length is `c/2` times less than the sum of a priori
probabilities of the rationals inside it" — then `c·Leb(⋃ F) ≤ 4`. -/
theorem mul_volume_biUnion_le {ν : ℚ → ℝ≥0∞} (hν : (∑' q, ν q) ≤ 1) {c : ℝ≥0∞}
    (F : Finset (ℚ × ℚ))
    (hF : ∀ I ∈ F, c * ratIntervalLength I
      ≤ 2 * ∑' q : ℚ, (if ((q : ℚ) : ℝ) ∈ ratInterval I then ν q else 0)) :
    c * volume (⋃ I ∈ F, ratInterval I) ≤ 4 := by
  classical
  obtain ⟨G, hGF, hGirr, hGeq⟩ := exists_irredundant_subfamily F
  have hmult : (∑ I ∈ G, ∑' q : ℚ, (if ((q : ℚ) : ℝ) ∈ ratInterval I then ν q else 0))
      ≤ 2 * ∑' q, ν q := by
    have hswap : (∑ I ∈ G, ∑' q : ℚ, (if ((q : ℚ) : ℝ) ∈ ratInterval I then ν q else 0))
        = ∑' q : ℚ, ∑ I ∈ G, (if ((q : ℚ) : ℝ) ∈ ratInterval I then ν q else 0) :=
      finsetSum_tsum_comm G _
    rw [hswap, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun q => ?_
    have hcount : (∑ I ∈ G, (if ((q : ℚ) : ℝ) ∈ ratInterval I then ν q else 0))
        = ((G.filter (fun I => ((q : ℚ) : ℝ) ∈ ratInterval I)).card : ℝ≥0∞) * ν q := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
    rw [hcount]
    gcongr
    exact_mod_cast card_filter_le_two hGirr ((q : ℚ) : ℝ)
  calc c * volume (⋃ I ∈ F, ratInterval I)
      = c * volume (⋃ I ∈ G, ratInterval I) := by rw [hGeq]
    _ ≤ c * ∑ I ∈ G, volume (ratInterval I) := by
        gcongr
        exact measure_biUnion_finset_le G _
    _ = ∑ I ∈ G, c * ratIntervalLength I := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun I _ => by rw [volume_ratInterval]
    _ ≤ ∑ I ∈ G, 2 * ∑' q : ℚ, (if ((q : ℚ) : ℝ) ∈ ratInterval I then ν q else 0) :=
        Finset.sum_le_sum fun I hI => hF I (hGF hI)
    _ = 2 * ∑ I ∈ G, ∑' q : ℚ, (if ((q : ℚ) : ℝ) ∈ ratInterval I then ν q else 0) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * (2 * ∑' q, ν q) := by gcongr
    _ ≤ 2 * (2 * 1) := by gcongr
    _ = 4 := by norm_num

end Kolmogorov

